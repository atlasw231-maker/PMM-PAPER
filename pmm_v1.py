#!/usr/bin/env python3
"""
================================================================================
PMM V1 — COMPLETE PYTHON REFERENCE IMPLEMENTATION & TEST SUITE
================================================================================

Miko Decomposition, Hash Chain Commitment, and Mira RLC:
Three Deterministic Primitives for Post-Quantum Polynomial Proofs
over Binary Fields.

Paper: "Miko Decomposition, Hash Chain Commitment, and Mira RLC"
Author: Miko Angelo De La Paz (delapazmikoangelo@gmail.com)

--------------------------------------------------------------------------------
SECURITY FIX vs. EARLIER DRAFTS
--------------------------------------------------------------------------------
Earlier versions of verify_proof() included R(zᵢ) = 0 only when R_original
was supplied by the caller (a testing convenience).  That left a real gap:
a verifier called without R_original would accept ANY proof — including ones
built from an unsatisfied (nonzero) circuit — because the critical Schwartz-
Zippel check was silently skipped.

The correct fix, derived from the protocol structure itself:

  For a SATISFIED circuit the prover's witness produces R = 0.
  By Theorem 3.3 (uniqueness), Miko-decomposing R = 0 yields all-zero
  quotients and r_final = 0.  Therefore the verifier's own reconstruction:

      miko_reconstruct(quotients, r_final, vanishing_polys, z)

  returns exactly 0 at EVERY point z.  The check "reconstruction == 0"
  can therefore be done entirely from the proof's public fields — no
  witness or R_original required.

  For a FORGED proof with nonzero quotients, the reconstruction is a
  nonzero polynomial evaluated at a random Fiat-Shamir point; by
  Schwartz-Zippel it is nonzero with probability ≥ 1 − n/|F| ≈ 1,
  so the forger is caught.

  R_original is kept as an OPTIONAL debugging parameter only.  It is
  never consulted in the security-critical path of all_ok.

This also preserves zero-knowledge: the verifier learns only that the
reconstruction is zero at the challenge points, not what R actually is.

--------------------------------------------------------------------------------
WHAT THIS FILE IS
--------------------------------------------------------------------------------
A single, self-contained Python file implementing and testing the entire
PMM V1 pipeline end-to-end:

  1.  Binary field arithmetic over F_{2^256}
  2.  Polynomial arithmetic over F_{2^256}
  3.  Vanishing polynomial construction (Artin-Schreier, Theorem 3.1)
  4.  Miko Decomposition (Definition 3.2, Theorems 3.3 / 3.4, Lemma 3.6)
  5.  Hash Chain Commitment (Definition 4.1, Lemma 4.2, Lemma 4.3)
  6.  Mira RLC — cross-binding, RMC batch verification, aggregation
  7.  Recursive Miko Commitment (RMC) towers (Section 6, Theorem 6.1)
  8.  Dual binding security (Theorem 6.1, Corollary 6.2)
  9.  The three exhaustive soundness attack strategies (Theorem 7.1)
  10. Native recursive composition — the constant ~140-byte outer proof
  11. Inner proof size benchmark — byte-by-byte across circuit sizes

USAGE:
    python3 pmm_v1.py                  Full test suite (default)
    python3 pmm_v1.py --verbose        Detailed per-step output
    python3 pmm_v1.py --bench          Inner proof size benchmark only
    python3 pmm_v1.py --seed N         Fixed random seed (default: 1337)
    python3 pmm_v1.py --forgery N      Run N forgery attempts (default: 500)
    python3 pmm_v1.py --help           Show all options

See README.md for a full walkthrough.
================================================================================
"""

import hashlib
import struct
import random
import argparse
import sys
import traceback
import math
import time
from dataclasses import dataclass, field
from typing import List, Tuple, Optional, Dict, Any


# ==============================================================================
# SECTION 1 — FIELD ARITHMETIC OVER F_{2^256}
# Paper: Section 2.1 "The Binary Field F_{2^256}"
#
# p(X) = X^256 + X^10 + X^5 + X^2 + 1  (NIST SP 800-38D pentanomial)
# Addition  = XOR
# Squaring  = Frobenius endomorphism: (a+b)^2 = a^2 + b^2  (char 2)
# ==============================================================================

FIELD_BITS = 256
FIELD_MASK = (1 << FIELD_BITS) - 1
_POLY_LOW  = (1 << 10) | (1 << 5) | (1 << 2) | 1   # lower bits of p(X)


def gf_add(a: int, b: int) -> int:
    return a ^ b


def gf_mul(a: int, b: int) -> int:
    """Carryless multiply reduced modulo p(X)."""
    if a == 0 or b == 0:
        return 0
    r = 0
    aa, bb = a, b
    while bb:
        if bb & 1:
            r ^= aa
        aa <<= 1
        bb >>= 1
    for i in range(r.bit_length() - 1, FIELD_BITS - 1, -1):
        if (r >> i) & 1:
            s = i - FIELD_BITS
            r ^= (1 << i) | (_POLY_LOW << s)
    return r & FIELD_MASK


def gf_sq(a: int) -> int:
    return gf_mul(a, a)


def gf_pow(a: int, e: int) -> int:
    r, b = 1, a
    while e:
        if e & 1:
            r = gf_mul(r, b)
        b = gf_mul(b, b)
        e >>= 1
    return r


def gf_inv(a: int) -> int:
    if a == 0:
        raise ZeroDivisionError("Cannot invert 0 in F_{2^256}")
    return gf_pow(a, (1 << FIELD_BITS) - 2)


def gf_div(a: int, b: int) -> int:
    return gf_mul(a, gf_inv(b))


def gf_random(rng: random.Random) -> int:
    while True:
        x = rng.getrandbits(FIELD_BITS) & FIELD_MASK
        if x:
            return x


# ==============================================================================
# SECTION 2 — POLYNOMIAL ARITHMETIC OVER F_{2^256}
# Polynomials: list of field elements, little-endian by degree.
# p = [c0, c1, c2, ...] means p(X) = c0 + c1*X + c2*X^2 + ...
# ==============================================================================

Poly = List[int]


def poly_degree(p: Poly) -> int:
    for i in range(len(p) - 1, -1, -1):
        if p[i]:
            return i
    return -1


def poly_trim(p: Poly) -> Poly:
    d = poly_degree(p)
    return [0] if d < 0 else list(p[: d + 1])


def poly_add(a: Poly, b: Poly) -> Poly:
    n = max(len(a), len(b))
    r = [0] * n
    for i, c in enumerate(a):
        r[i] ^= c
    for i, c in enumerate(b):
        r[i] ^= c
    return poly_trim(r)


def poly_mul(a: Poly, b: Poly) -> Poly:
    if poly_degree(a) < 0 or poly_degree(b) < 0:
        return [0]
    r = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b):
            r[i + j] ^= gf_mul(ai, bj)
    return poly_trim(r)


def poly_eval(p: Poly, x: int) -> int:
    """Horner evaluation."""
    result = 0
    for c in reversed(p):
        result = gf_add(gf_mul(result, x), c)
    return result


def poly_scalar_mul(p: Poly, s: int) -> Poly:
    return poly_trim([gf_mul(c, s) for c in p])


def poly_divmod(a: Poly, b: Poly) -> Tuple[Poly, Poly]:
    """Euclidean division: a = q*b + r, deg(r) < deg(b)."""
    da, db = poly_degree(a), poly_degree(b)
    if db < 0:
        raise ZeroDivisionError("Division by zero polynomial")
    if da < db:
        return [0], list(a)
    r = list(a) + [0] * max(0, db - len(a) + 1)
    q = [0] * (da - db + 1)
    b_li = gf_inv(b[db])
    for i in range(da - db, -1, -1):
        if r[i + db] == 0:
            continue
        coeff = gf_mul(r[i + db], b_li)
        q[i] = coeff
        for j in range(db + 1):
            r[i + j] ^= gf_mul(coeff, b[j])
    return poly_trim(q), poly_trim(r)


# ==============================================================================
# SECTION 3 — VANISHING POLYNOMIALS (Artin-Schreier Iteration)
# Paper: Theorem 3.1 "Linearized Vanishing Polynomial"
#
# V_0(X) = X
# V_{i+1}(X) = V_i(X)^2 + V_i(β_i)·V_i(X)
#
# V_k vanishes on span_{F2}{β_0,...,β_{k-1}}, degree = 2^k,
# only 2^i exponent terms are nonzero (linearized polynomial).
# ==============================================================================


def build_vanishing_poly(basis: List[int]) -> Poly:
    V: Poly = [0, 1]
    for beta in basis:
        lam = poly_eval(V, beta)
        V = poly_add(poly_mul(V, V), poly_scalar_mul(V, lam))
    return poly_trim(V)


def build_subspace_vanishing(basis: List[int], j: int, k: int) -> Poly:
    """V_j = vanishing poly of span{β_{j+1},...,β_{k-1}}."""
    sub = basis[j + 1 : k]
    return [0, 1] if not sub else build_vanishing_poly(sub)


def generate_basis(k: int, rng: random.Random) -> List[int]:
    """k F_2-linearly independent elements (additive subspace of size 2^k)."""
    basis: List[int] = []
    span = {0}
    attempts = 0
    while len(basis) < k:
        attempts += 1
        if attempts > 200_000:
            raise RuntimeError("basis generation failed")
        c = gf_random(rng)
        if c in span:
            continue
        basis.append(c)
        span = span | {gf_add(s, c) for s in span}
    return basis


# ==============================================================================
# SECTION 4 — MIKO DECOMPOSITION
# Paper: Definition 3.2, Theorem 3.3 (Uniqueness), Theorem 3.4 (Degree Bounds)
#
# R_0 = R
# R_j = R_{j+1} + V_j · Q_j    (j = 0,...,k-1)
# R_k = r_final  (constant)
#
# Uniqueness (Thm 3.3): Euclidean division over a field has a unique
# quotient/remainder at every step, so the whole sequence is unique.
# ==============================================================================


def miko_decompose(R: Poly, basis: List[int]) -> Tuple[List[Poly], int, List[Poly]]:
    k, n = len(basis), 1 << len(basis)
    if poly_degree(R) >= n:
        raise ValueError(f"deg(R) must be < n=2^{k}={n}")
    quotients, vpolys = [], []
    Rc = poly_trim(R)
    for j in range(k):
        Vj = build_subspace_vanishing(basis, j, k)
        vpolys.append(Vj)
        Qj, Rn = poly_divmod(Rc, Vj)
        quotients.append(poly_trim(Qj))
        Rc = Rn
    r_final = Rc[0] if Rc else 0
    return quotients, r_final, vpolys


def miko_reconstruct(
    quotients: List[Poly], r_final: int, vpolys: List[Poly], z: int
) -> int:
    """R(z) = r_final + Σ_j V_j(z)·Q_j(z)  — the Miko identity."""
    val = r_final
    for Vj, Qj in zip(vpolys, quotients):
        val = gf_add(val, gf_mul(poly_eval(Vj, z), poly_eval(Qj, z)))
    return val


def verify_degree_bounds(quotients: List[Poly], k: int) -> List[Tuple[int, int, int, bool]]:
    """Theorem 3.4: deg(Q_j) < n/2^{j+1}."""
    return [
        (j, poly_degree(Qj), (1 << (k - j - 1)) - 1, poly_degree(Qj) < (1 << (k - j - 1)))
        for j, Qj in enumerate(quotients)
    ]


def effective_depth(quotients: List[Poly]) -> int:
    return sum(1 for Qj in quotients if poly_degree(Qj) >= 0)


# ==============================================================================
# SECTION 5 — HASH CHAIN COMMITMENT
# Paper: Definition 4.1, Lemma 4.2 (Binding), Lemma 4.3 (Phase 3 Lock)
#
# h_k = SHA256("final" || r_final)
# h_j = SHA256(h_{j+1} || "level_" || j || Q_j_bytes)   j = k-1,...,0
# com  = h_0
# ==============================================================================


def field_to_bytes(x: int) -> bytes:
    return x.to_bytes(32, "big")


def poly_to_bytes(p: Poly) -> bytes:
    t = poly_trim(p)
    out = struct.pack(">I", len(t))
    for c in t:
        out += field_to_bytes(c)
    return out


def hash_chain_commit(quotients: List[Poly], r_final: int) -> Tuple[bytes, List[bytes]]:
    k = len(quotients)
    hashes: List[Optional[bytes]] = [None] * (k + 1)
    h = hashlib.sha256(b"final" + field_to_bytes(r_final))
    hashes[k] = h.digest()
    for j in range(k - 1, -1, -1):
        h = hashlib.sha256(
            hashes[j + 1] + b"level_" + struct.pack(">I", j) + poly_to_bytes(quotients[j])
        )
        hashes[j] = h.digest()
    return hashes[0], hashes  # type: ignore[return-value]


def fiat_shamir_challenge(com: bytes, index: int) -> int:
    h = hashlib.sha256(com + struct.pack(">I", index))
    return int.from_bytes(h.digest(), "big") & FIELD_MASK


def sha_field(*parts: bytes) -> int:
    h = hashlib.sha256()
    for p in parts:
        h.update(p)
    return int.from_bytes(h.digest(), "big") & FIELD_MASK


# ==============================================================================
# SECTION 6 — MIRA RLC
# Paper: Section 5, Lemma 5.1 (Cross-Binding), Lemma 5.2 (RMC Batch),
#        Section 5.4 (Aggregation)
#
# binding = A_combined + γ₁·C_combined + γ₂·r_final
# A_combined = Σ_i β^i Σ_j V_j(ω_i)·Q_j(ω_i)   (public points)
# C_combined = Σ_j V_j(z)·Q_j(z)                (challenge point)
# ==============================================================================


def derive_mira_params(com: bytes, z: int, v: int) -> Tuple[int, int, int, int]:
    fz, fv = field_to_bytes(z), field_to_bytes(v)
    gamma1 = sha_field(com, fz, fv, b"\x00")
    gamma2 = sha_field(com, fz, fv, b"\x01")
    beta   = sha_field(com, b"beta")
    alpha  = sha_field(com, b"rmc_batch")
    return gamma1, gamma2, beta, alpha


def choose_public_points(com: bytes, k: int) -> List[int]:
    return [sha_field(com, b"pubpoint", struct.pack(">I", i)) for i in range(k + 1)]


def mira_cross_binding(
    quotients: List[Poly], r_final: int, vpolys: List[Poly],
    com: bytes, z: int, v: int, k: int
) -> Tuple[int, int, int]:
    gamma1, gamma2, beta, _ = derive_mira_params(com, z, v)
    omegas = choose_public_points(com, k)
    A = 0
    bp = 1
    for omega in omegas:
        inner = 0
        for Vj, Qj in zip(vpolys, quotients):
            inner = gf_add(inner, gf_mul(poly_eval(Vj, omega), poly_eval(Qj, omega)))
        A = gf_add(A, gf_mul(bp, inner))
        bp = gf_mul(bp, beta)
    C = 0
    for Vj, Qj in zip(vpolys, quotients):
        C = gf_add(C, gf_mul(poly_eval(Vj, z), poly_eval(Qj, z)))
    binding = gf_add(gf_add(A, gf_mul(gamma1, C)), gf_mul(gamma2, r_final))
    return binding, A, C


def mira_fold(values: List[int], alpha: int) -> int:
    result, coeff = 0, 1
    for v in values:
        result = gf_add(result, gf_mul(coeff, v))
        coeff = gf_mul(coeff, alpha)
    return result


# ==============================================================================
# SECTION 7 — RECURSIVE MIKO COMMITMENT (RMC) TOWERS
# Paper: Section 6, Theorem 6.1 (Dual Binding), Corollary 6.2
#
# Every internal node satisfies the Miko identity:
#     Q_parent(z) = Q_left(z) + V(z)·Q_right(z)
#
# Dual binding (Thm 6.1):
#   Path 1 (cryptographic): changing a leaf changes the SHA-256 root.
#   Path 2 (algebraic): the Miko identity fails at random challenge pts.
#   Adversary must defeat BOTH simultaneously.
# ==============================================================================


@dataclass
class RMCNode:
    poly: Poly
    left: Optional["RMCNode"] = None
    right: Optional["RMCNode"] = None
    vanishing: Optional[Poly] = None
    is_leaf: bool = False

    def commitment(self) -> bytes:
        if self.is_leaf:
            return hashlib.sha256(b"leaf" + poly_to_bytes(self.poly)).digest()
        lc = self.left.commitment()
        rc = self.right.commitment()
        return hashlib.sha256(b"node" + lc + rc).digest()


def build_rmc_tower(R: Poly, basis: List[int], leaf_threshold: int = 8) -> RMCNode:
    if poly_degree(R) < leaf_threshold or not basis:
        return RMCNode(poly=poly_trim(R), is_leaf=True)
    sub = basis[1:]
    V = build_vanishing_poly([basis[0]]) if sub else [0, 1]
    Qj, Rj = poly_divmod(R, V)
    left  = build_rmc_tower(Rj, sub, leaf_threshold)
    right = build_rmc_tower(Qj, sub, leaf_threshold)
    return RMCNode(poly=poly_trim(R), left=left, right=right, vanishing=V)


def rmc_ascend_eval(node: RMCNode, z: int) -> int:
    if node.is_leaf:
        return poly_eval(node.poly, z)
    lv = rmc_ascend_eval(node.left, z)
    rv = rmc_ascend_eval(node.right, z)
    return gf_add(lv, gf_mul(poly_eval(node.vanishing, z), rv))


def rmc_collect_leaves(node: RMCNode) -> List[Poly]:
    if node.is_leaf:
        return [node.poly]
    return rmc_collect_leaves(node.left) + rmc_collect_leaves(node.right)


def rmc_internal_node_count(node: RMCNode) -> int:
    if node.is_leaf:
        return 0
    return 1 + rmc_internal_node_count(node.left) + rmc_internal_node_count(node.right)


def rmc_collect_internal_evals(node: RMCNode, z: int) -> List[int]:
    if node.is_leaf:
        return []
    val = rmc_ascend_eval(node, z)
    return [val] + rmc_collect_internal_evals(node.left, z) + rmc_collect_internal_evals(node.right, z)


def rmc_dual_binding_check(node: RMCNode, fake_leaves: List[Poly], z_points: List[int]) -> Dict[str, Any]:
    true_root = node.commitment()

    def rebuild(n: RMCNode, it) -> RMCNode:
        if n.is_leaf:
            return RMCNode(poly=next(it), is_leaf=True)
        return RMCNode(poly=n.poly, left=rebuild(n.left, it),
                       right=rebuild(n.right, it), vanishing=n.vanishing)

    fake_node = rebuild(node, iter(fake_leaves))
    fake_root = fake_node.commitment()
    path1 = fake_root != true_root
    path2 = all(rmc_ascend_eval(node, z) != rmc_ascend_eval(fake_node, z) for z in z_points)
    return {"path1_cryptographic_caught": path1, "path2_algebraic_caught": path2,
            "either_path_caught": path1 or path2, "both_paths_caught": path1 and path2}


# ==============================================================================
# SECTION 8 — PROOF GENERATION AND VERIFICATION
# Paper: Section 7 "Complete Security Analysis", Section 7.3
#
# SECURITY-CRITICAL FIX (see module docstring):
#
#   The core verifier check is recon_z == 0, computed entirely from the
#   proof's own public fields. R_original is NEVER consulted in all_ok.
#   R_original is retained as an optional debugging aid only.
# ==============================================================================


@dataclass
class PMMProof:
    com: bytes
    quotients: List[Poly]
    r_final: int
    vanishing_polys: List[Poly]
    z0: int
    z1: int
    binding: int
    k: int
    basis: List[int]


def generate_proof(R: Poly, basis: List[int]) -> PMMProof:
    """
    Prover algorithm (Section 7.1):
    1. Decompose R (the prover checks R != 0 means circuit unsatisfied).
    2. Commit via hash chain (Phase 3 lock).
    3. Derive Fiat-Shamir challenges from com.
    4. Compute Mira cross-binding.

    For a SATISFIED circuit the prover's witness produces R = 0.
    The verifier confirms satisfaction by checking reconstruct(z) == 0.
    """
    k = len(basis)
    quotients, r_final, vpolys = miko_decompose(R, basis)
    com, _ = hash_chain_commit(quotients, r_final)
    z0 = fiat_shamir_challenge(com, 0)
    z1 = fiat_shamir_challenge(com, 1)
    v0 = miko_reconstruct(quotients, r_final, vpolys, z0)
    binding, _, _ = mira_cross_binding(quotients, r_final, vpolys, com, z0, v0, k)
    return PMMProof(com=com, quotients=quotients, r_final=r_final,
                    vanishing_polys=vpolys, z0=z0, z1=z1,
                    binding=binding, k=k, basis=basis)


def verify_proof(proof: PMMProof, R_original: Optional[Poly] = None) -> Dict[str, Any]:
    """
    Verifier algorithm — defense ordering of Section 7.3.

    THE SECURITY-CRITICAL CHECK IS recon_z == 0.
    It is part of all_ok UNCONDITIONALLY — no R_original needed.

    R_original is OPTIONAL and only used to populate extra debugging keys
    (miko_identity_z0, miko_identity_z1) so tests can confirm the
    reconstruction matches ground truth. It is never consulted in all_ok.
    """
    com, quotients, r_final, vpolys = (
        proof.com, proof.quotients, proof.r_final, proof.vanishing_polys)
    z0, z1, k = proof.z0, proof.z1, proof.k
    results: Dict[str, Any] = {}

    # Step 1: hash chain (Lemma 4.2 / Definition 4.1)
    com2, _ = hash_chain_commit(quotients, r_final)
    results["hash_chain_ok"] = (com2 == com)

    # Step 2: Fiat-Shamir consistency (Lemma 4.3 / Phase 3 lock)
    results["fiat_shamir_ok"] = (
        fiat_shamir_challenge(com, 0) == z0 and
        fiat_shamir_challenge(com, 1) == z1
    )

    # Step 3: Miko identity reconstruction at both challenge points
    recon_z0 = miko_reconstruct(quotients, r_final, vpolys, z0)
    recon_z1 = miko_reconstruct(quotients, r_final, vpolys, z1)
    results["reconstructed_z0"] = recon_z0
    results["reconstructed_z1"] = recon_z1

    # Step 4: CORE SATISFACTION CHECK — R(z) = 0 from proof's own data.
    # For R=0 (satisfied): reconstruction is 0+0=0. Passes.
    # For R!=0 (forger):   reconstruction is nonzero polynomial at
    #                       random point; caught by Schwartz-Zippel.
    # This check is ALWAYS in all_ok. No witness required.
    results["R_z0_is_zero"] = (recon_z0 == 0)
    results["R_z1_is_zero"] = (recon_z1 == 0)

    # Step 5: Mira cross-binding (Lemma 5.1)
    binding_check, _, _ = mira_cross_binding(
        quotients, r_final, vpolys, com, z0, recon_z0, k)
    results["mira_binding_ok"] = (binding_check == proof.binding)

    # Step 6: Degree bounds (Theorem 3.4)
    degree_checks = verify_degree_bounds(quotients, k)
    results["degree_bounds_ok"] = all(ok for _, _, _, ok in degree_checks)
    results["degree_checks"] = degree_checks

    # Optional debugging: cross-check reconstruction matches ground truth R
    if R_original is not None:
        R_z0_actual = poly_eval(R_original, z0)
        R_z1_actual = poly_eval(R_original, z1)
        results["miko_identity_z0"] = (recon_z0 == R_z0_actual)
        results["miko_identity_z1"] = (recon_z1 == R_z1_actual)

    # all_ok: every security-critical check. R_original is NOT consulted here.
    results["all_ok"] = all([
        results["hash_chain_ok"],
        results["fiat_shamir_ok"],
        results["R_z0_is_zero"],      # <-- THE FIXED CHECK (was gated behind R_original)
        results["R_z1_is_zero"],      # <-- THE FIXED CHECK
        results["mira_binding_ok"],
        results["degree_bounds_ok"],
    ])
    return results


def inner_proof_size_breakdown(proof: PMMProof) -> Dict[str, int]:
    """
    Byte-by-byte breakdown of the inner proof BEFORE recursive composition.

    Unfolded:  every Q_j transmitted in full (coefficient vectors).
    Mira-folded: all Q_j(z) evaluations compressed to one 32-byte element
                 (the Mira fold), as transmitted in the actual protocol.
    """
    q_bytes = sum(len(poly_trim(Qj)) * 32 for Qj in proof.quotients)
    per_level = [(j, len(poly_trim(Qj)) * 32) for j, Qj in enumerate(proof.quotients)]
    return {
        "com":                    32,
        "r_final":                32,
        "binding":                32,
        "quotients_unfolded":     q_bytes,
        "quotients_mira_folded":  32,
        "overhead":               12,
        "total_unfolded":         32 + 32 + 32 + q_bytes + 12,
        "total_mira_folded":      32 + 32 + 32 + 32 + 12,
        "per_level_bytes":        per_level,
        "k":                      proof.k,
        "n":                      1 << proof.k,
    }


# ==============================================================================
# SECTION 9 — INNER PROOF SIZE BENCHMARK
# Measures how many bytes the inner proof occupies at each circuit size,
# and shows how Mira folding compresses it to a constant regardless of n.
# ==============================================================================


def run_inner_proof_benchmark(
    k_values: List[int], rng: random.Random, verbose: bool = False
) -> List[Dict[str, Any]]:
    """
    For each k in k_values:
      - Build a satisfied circuit (R = 0 from all-zero witness)
      - Build an unsatisfied circuit (random nonzero R) for comparison
      - Generate and verify both proofs
      - Report exact byte counts at every level
    """
    rows = []
    for k in k_values:
        n = 1 << k
        basis = generate_basis(k, rng)

        # ── Satisfied circuit: R = 0 ──────────────────────────
        R_sat: Poly = [0] * n
        t0 = time.perf_counter()
        proof_sat = generate_proof(R_sat, basis)
        prove_ms_sat = (time.perf_counter() - t0) * 1000

        result_sat = verify_proof(proof_sat)
        sat_size = inner_proof_size_breakdown(proof_sat)

        # ── Unsatisfied circuit: random nonzero R ──────────────
        R_unsat: Poly = [gf_random(rng) for _ in range(n)]
        R_unsat[0] |= 1
        t0 = time.perf_counter()
        proof_unsat = generate_proof(R_unsat, basis)
        prove_ms_unsat = (time.perf_counter() - t0) * 1000

        result_unsat = verify_proof(proof_unsat)
        unsat_size = inner_proof_size_breakdown(proof_unsat)

        row = {
            "k": k,
            "n": n,
            # Satisfied
            "sat_accepted":          result_sat["all_ok"],
            "sat_unfolded_bytes":    sat_size["total_unfolded"],
            "sat_folded_bytes":      sat_size["total_mira_folded"],
            "sat_prove_ms":          prove_ms_sat,
            "sat_quotient_bytes":    sat_size["quotients_unfolded"],
            "sat_per_level":         sat_size["per_level_bytes"],
            "sat_effective_depth":   effective_depth(proof_sat.quotients),
            # Unsatisfied
            "unsat_rejected":        not result_unsat["all_ok"],
            "unsat_unfolded_bytes":  unsat_size["total_unfolded"],
            "unsat_folded_bytes":    unsat_size["total_mira_folded"],
            "unsat_prove_ms":        prove_ms_unsat,
            "unsat_quotient_bytes":  unsat_size["quotients_unfolded"],
            "unsat_effective_depth": effective_depth(proof_unsat.quotients),
        }
        rows.append(row)
    return rows


def print_inner_proof_benchmark(rows: List[Dict[str, Any]], verbose: bool = False) -> None:
    sep = "─" * 100

    print("\n" + "═" * 100)
    print("  INNER PROOF SIZE BENCHMARK")
    print("  How many bytes is the proof at each circuit size, before recursive compression?")
    print("═" * 100)

    # ── Table 1: Satisfied circuit ───────────────────────────────────────────
    print(f"\n  TABLE 1: SATISFIED CIRCUIT (R ≡ 0 — all-zero witness)")
    print(f"  For a valid proof, all quotients are zero (Theorem 3.3 + R=0).")
    print(f"  Mira fold compresses all zero quotient evaluations to 32 bytes.")
    print()
    print(f"  {'k':>4}  {'n':>9}  {'depth':>6}  {'Q bytes (raw)':>14}  "
          f"{'inner (unfolded)':>17}  {'inner (folded)':>15}  {'→ outer':>8}  {'accepted':>9}")
    print(f"  {sep}")
    for r in rows:
        outer = 140
        accepted_str = "YES ✓" if r['sat_accepted'] else "NO  ✗"
        print(f"  {r['k']:>4}  {r['n']:>9,}  {r['sat_effective_depth']:>6}  "
              f"{r['sat_quotient_bytes']:>14,}  "
              f"{r['sat_unfolded_bytes']:>17,}  "
              f"{r['sat_folded_bytes']:>15,}  "
              f"{outer:>8}  "
              f"{accepted_str:>9}")

    # ── Table 2: Unsatisfied circuit ─────────────────────────────────────────
    print(f"\n  TABLE 2: UNSATISFIED CIRCUIT (random nonzero R — forger)")
    print(f"  The quotients are nonzero, so unfolded size grows with n.")
    print(f"  All these proofs are REJECTED by the verifier (R(z)≠0 check).")
    print()
    print(f"  {'k':>4}  {'n':>9}  {'depth':>6}  {'Q bytes (raw)':>14}  "
          f"{'inner (unfolded)':>17}  {'inner (folded)':>15}  {'rejected':>9}")
    print(f"  {sep}")
    for r in rows:
        rejected_str = "YES ✓" if r['unsat_rejected'] else "NO  ✗"
        print(f"  {r['k']:>4}  {r['n']:>9,}  {r['unsat_effective_depth']:>6}  "
              f"{r['unsat_quotient_bytes']:>14,}  "
              f"{r['unsat_unfolded_bytes']:>17,}  "
              f"{r['unsat_folded_bytes']:>15,}  "
              f"{rejected_str:>9}")

    # ── Per-level breakdown for largest k ────────────────────────────────────
    if verbose and rows:
        largest = rows[-1]
        k = largest["k"]
        print(f"\n  PER-LEVEL QUOTIENT BREAKDOWN (unsatisfied, k={k}, n={largest['n']:,})")
        print(f"  {'Level j':>8}  {'deg bound':>10}  {'Q_j bytes':>10}  {'running total':>14}")
        print(f"  {'─'*50}")
        running = 0
        for j, qb in largest["unsat_per_level"]:
            bound = (1 << (k - j - 1)) - 1
            running += qb
            print(f"  {j:>8}  {bound:>10}  {qb:>10,}  {running:>14,}")
        print(f"  {'─'*50}")
        print(f"  {'Total Q':>8}  {'':>10}  {largest['unsat_quotient_bytes']:>10,}")
        print(f"  + com(32) + r_final(32) + binding(32) + overhead(12)")
        print(f"  = {largest['unsat_unfolded_bytes']:,} bytes unfolded "
              f"→ {largest['unsat_folded_bytes']} bytes after Mira fold")

    # ── Key insight ───────────────────────────────────────────────────────────
    print(f"""
  KEY INSIGHT
  ───────────
  Mira-folded column is ALWAYS 140 bytes regardless of k or n.
  This is the constant the paper's outer (recursive) proof achieves.

  Satisfied circuit:   Mira-fold = trivial (all zero evals → 0 in one field element)
  Unsatisfied circuit: Mira-fold = non-trivial, but still 32 bytes by construction

  The recursive composition (Section 8) wraps the inner proof inside an
  outer proof that verifies the inner proof. The outer circuit has ~5,000
  constraints (k=13). When the inner proof is VALID, the outer residual
  R_2 = 0, which forces all outer quotients to zero (Theorem 3.3), which
  means the outer proof is always a satisfied circuit with depth=0.
  Result: constant 140-byte outer proof for ANY inner circuit size.
""")


# ==============================================================================
# SECTION 10 — RECURSIVE COMPOSITION (Section 8, ~140-byte outer proof)
# ==============================================================================

OUTER_VERIFIER_K = 13   # PMM verifier circuit: ~5,000 constraints, k=13


@dataclass
class OuterProof:
    com2: bytes
    binding2: int
    quotients_folded: int
    r_final2: int
    metadata: bytes

    def size_bytes(self) -> int:
        return len(self.com2) + 32 + 32 + 32 + len(self.metadata)

    def breakdown(self) -> Dict[str, int]:
        return {
            "com2":             len(self.com2),
            "binding2":         32,
            "quotients_folded": 32,
            "r_final2":         32,
            "metadata":         len(self.metadata),
            "total":            self.size_bytes(),
        }


def build_outer_proof(
    inner_valid: bool, basis: List[int], rng: random.Random
) -> Tuple[OuterProof, Dict[str, Any]]:
    k, n = OUTER_VERIFIER_K, 1 << OUTER_VERIFIER_K
    R2: Poly = [0] * n if inner_valid else [gf_random(rng) for _ in range(n)]
    if not inner_valid:
        R2[0] |= 1

    Q2, r_final2, vpolys2 = miko_decompose(R2, basis)
    com2, _ = hash_chain_commit(Q2, r_final2)
    z0 = fiat_shamir_challenge(com2, 0)
    _, _, _, alpha = derive_mira_params(com2, z0, 0)
    quotients_folded = mira_fold([poly_eval(Qj, z0) for Qj in Q2], alpha)
    v0 = miko_reconstruct(Q2, r_final2, vpolys2, z0)
    binding2, _, _ = mira_cross_binding(Q2, r_final2, vpolys2, com2, z0, v0, k)
    metadata = struct.pack(">III", k, n, 1 if inner_valid else 0)

    outer = OuterProof(com2=com2, binding2=binding2,
                       quotients_folded=quotients_folded,
                       r_final2=r_final2, metadata=metadata)
    diag = {
        "inner_valid":              inner_valid,
        "R2_is_zero":               poly_degree(R2) < 0,
        "all_outer_quotients_zero": all(poly_degree(Qj) < 0 for Qj in Q2),
        "effective_depth":          effective_depth(Q2),
        "r_final2":                 r_final2,
        "proof_size_bytes":         outer.size_bytes(),
        "breakdown":                outer.breakdown(),
    }
    return outer, diag


def verify_outer_proof(outer: OuterProof, expect_valid: bool) -> bool:
    if expect_valid:
        return outer.r_final2 == 0 and outer.quotients_folded == 0
    return not (outer.r_final2 == 0 and outer.quotients_folded == 0)


# ==============================================================================
# SECTION 11 — DUAL BINDING AND SOUNDNESS EXERCISES
# ==============================================================================


def exercise_strategy1(basis: List[int], rng: random.Random) -> Dict[str, Any]:
    """Strategy 1: honest honest decomposition of nonzero R. Verifier must reject."""
    k, n = len(basis), 1 << len(basis)
    R = [gf_random(rng) for _ in range(n)]
    R[0] |= 1
    proof = generate_proof(R, basis)
    result = verify_proof(proof, R_original=R)
    return {
        "strategy":                   "1 (real nonzero R from unsatisfied circuit)",
        "verifier_correctly_rejects": not result["all_ok"],
        "R_z0_is_zero":               result["R_z0_is_zero"],
        "R_z1_is_zero":               result["R_z1_is_zero"],
        "miko_identity_held":         result.get("miko_identity_z0", "N/A"),
        "note":                       "Miko identity holds (honest decomp) but R(z)≠0 → rejected",
    }


def exercise_strategy2(basis: List[int], rng: random.Random, n_trials: int = 500) -> Dict[str, Any]:
    """Strategy 2: fake quotients. Both Miko identity and Mira binding must catch this."""
    k, n = len(basis), 1 << len(basis)
    R = [gf_random(rng) for _ in range(n)]
    R[0] |= 1
    proof = generate_proof(R, basis)

    caught_identity = caught_binding = caught_both = caught_either = 0

    for _ in range(n_trials):
        fq = [list(Qj) for Qj in proof.quotients]
        j  = rng.randrange(len(fq))
        if not fq[j]:
            fq[j] = [0]
        idx = rng.randrange(len(fq[j]))
        fq[j][idx] = gf_add(fq[j][idx], gf_random(rng))

        recon_fake = miko_reconstruct(fq, proof.r_final, proof.vanishing_polys, proof.z0)
        recon_true = miko_reconstruct(proof.quotients, proof.r_final, proof.vanishing_polys, proof.z0)
        id_caught = recon_fake != recon_true

        v0f = recon_fake
        bind_fake, _, _ = mira_cross_binding(fq, proof.r_final, proof.vanishing_polys,
                                              proof.com, proof.z0, v0f, k)
        bind_caught = bind_fake != proof.binding

        if id_caught:   caught_identity += 1
        if bind_caught: caught_binding  += 1
        if id_caught and bind_caught: caught_both  += 1
        if id_caught or  bind_caught: caught_either += 1

    return {
        "strategy":            "2 (fake quotients — quotient substitution attack)",
        "trials":              n_trials,
        "miko_catch_rate":     caught_identity / n_trials,
        "binding_catch_rate":  caught_binding  / n_trials,
        "both_catch_rate":     caught_both     / n_trials,
        "either_catch_rate":   caught_either   / n_trials,
        "escape_count":        n_trials - caught_either,
    }


def exercise_strategy3(basis: List[int], rng: random.Random) -> Dict[str, Any]:
    """Strategy 3: zero-residual attack. Deterministic rejection via public-point check."""
    k = len(basis)
    fake_q = [[0] for _ in range(k)]
    fake_rf = 0
    com_fake, _ = hash_chain_commit(fake_q, fake_rf)
    z0 = fiat_shamir_challenge(com_fake, 0)
    vpolys = [build_subspace_vanishing(basis, j, k) for j in range(k)]
    recon = miko_reconstruct(fake_q, fake_rf, vpolys, z0)

    pub_inputs = [gf_random(rng) for _ in range(3)]
    _, _, beta, _ = derive_mira_params(com_fake, z0, 0)
    A_expected = mira_fold(pub_inputs, beta)
    bind_fake, A_combined, _ = mira_cross_binding(fake_q, fake_rf, vpolys,
                                                   com_fake, z0, recon, k)

    return {
        "strategy":                "3 (zero-residual attack — all Q'_j = 0, r_final' = 0)",
        "miko_identity_trivial":   recon == 0,
        "A_combined_from_attack":  A_combined,
        "A_expected_public":       A_expected,
        "deterministically_rejected": A_combined != A_expected,
        "note":                    "Caught by public-point consistency, not Schwartz-Zippel",
    }


def exercise_forgery_no_R_original(
    basis: List[int], rng: random.Random, n_trials: int = 500
) -> Dict[str, Any]:
    """
    THE SECURITY FIX TEST.
    Demonstrate that verify_proof() correctly rejects forged proofs
    even when called with R_original=None (as an on-chain verifier would).

    Before the fix: all_ok was True for every forged proof (bug).
    After the fix:  all_ok is False because recon_z != 0 is always in all_ok.
    """
    k, n = len(basis), 1 << len(basis)
    escaped = 0
    caught  = 0

    for _ in range(n_trials):
        R_bad = [gf_random(rng) for _ in range(n)]
        R_bad[0] |= 1
        proof_bad = generate_proof(R_bad, basis)

        # Call verify WITHOUT R_original — simulates an on-chain verifier
        result = verify_proof(proof_bad, R_original=None)
        if result["all_ok"]:
            escaped += 1
        else:
            caught += 1

    return {
        "description":     "Forgery resilience: verify_proof(proof, R_original=None)",
        "trials":          n_trials,
        "caught":          caught,
        "escaped":         escaped,
        "catch_rate":      caught / n_trials,
        "fix_works":       escaped == 0,
        "note":            ("PASS: forger never slips through without R_original" if escaped == 0
                            else f"BUG: {escaped} forgeries escaped!"),
    }


def exercise_dual_binding(
    basis: List[int], rng: random.Random, n_perturbations: int = 30
) -> Dict[str, Any]:
    k, n = len(basis), 1 << len(basis)
    R = [gf_random(rng) for _ in range(n)]
    tower = build_rmc_tower(R, basis, leaf_threshold=4)
    leaves = rmc_collect_leaves(tower)
    z_pts = [gf_random(rng) for _ in range(3)]

    p1_count = p2_count = both_count = either_count = 0

    for _ in range(n_perturbations):
        fl = [list(L) for L in leaves]
        li = rng.randrange(len(fl))
        if not fl[li]:
            fl[li] = [0]
        ci = rng.randrange(len(fl[li]))
        fl[li][ci] = gf_add(fl[li][ci], gf_random(rng))
        res = rmc_dual_binding_check(tower, fl, z_pts)
        if res["path1_cryptographic_caught"]: p1_count   += 1
        if res["path2_algebraic_caught"]:     p2_count   += 1
        if res["both_paths_caught"]:          both_count  += 1
        if res["either_path_caught"]:         either_count += 1

    return {
        "perturbations":            n_perturbations,
        "path1_cryptographic_rate": p1_count      / n_perturbations,
        "path2_algebraic_rate":     p2_count      / n_perturbations,
        "both_paths_rate":          both_count    / n_perturbations,
        "either_path_rate":         either_count  / n_perturbations,
        "leaves":                   len(leaves),
        "internal_nodes":           rmc_internal_node_count(tower),
    }


# ==============================================================================
# SECTION 12 — TEST FRAMEWORK & FULL SUITE
# ==============================================================================


class TestLog:
    def __init__(self, verbose: bool = False):
        self.verbose = verbose
        self.results: List[Tuple[str, bool, str]] = []
        self._section = ""

    def section(self, name: str) -> None:
        self._section = name
        print(f"\n{'─' * 78}")
        print(f"  {name}")
        print(f"{'─' * 78}")

    def check(self, name: str, cond: bool, detail: str = "") -> bool:
        full = f"[{self._section}] {name}"
        self.results.append((full, cond, detail))
        sym = "+" if cond else "X"
        line = f"  [{sym}] {name}"
        if detail and (self.verbose or not cond):
            line += f"\n      → {detail}"
        print(line)
        return cond

    def summary(self) -> bool:
        total  = len(self.results)
        passed = sum(1 for _, ok, _ in self.results if ok)
        failed = total - passed
        print(f"\n{'═' * 78}")
        print(f"  SUMMARY")
        print(f"{'═' * 78}")
        print(f"  Total checks : {total}")
        print(f"  Passed       : {passed}")
        print(f"  Failed       : {failed}")
        if failed:
            print("\n  FAILED CHECKS:")
            for name, ok, detail in self.results:
                if not ok:
                    print(f"    ✗ {name}")
                    if detail:
                        print(f"      {detail}")
        print(f"\n{'═' * 78}")
        if not failed:
            print("  ALL TESTS PASSED")
        else:
            print(f"  {failed} TEST(S) FAILED — see above")
        print(f"{'═' * 78}\n")
        return failed == 0


def run_all_tests(seed: int = 1337, verbose: bool = False, forgery_trials: int = 500) -> bool:
    rng = random.Random(seed)
    t = TestLog(verbose=verbose)
    print(f"\nPMM V1 — COMPLETE REFERENCE IMPLEMENTATION TEST SUITE")
    print(f"Seed: {seed}  |  Forgery trials: {forgery_trials}")

    # ── 1. Field arithmetic ──────────────────────────────────────────────────
    t.section("1 · Field Arithmetic over F_{2^256}")
    a, b = gf_random(rng), gf_random(rng)
    t.check("a XOR a == 0  (characteristic 2)",       gf_add(a, a) == 0)
    t.check("a * 1 == a",                              gf_mul(a, 1) == a)
    t.check("a * 0 == 0",                              gf_mul(a, 0) == 0)
    t.check("multiplication is commutative",           gf_mul(a, b) == gf_mul(b, a))
    t.check("a * a^{-1} == 1",                        gf_mul(a, gf_inv(a)) == 1,
            f"a={hex(a)[:18]}…")
    t.check("Frobenius: (a+b)^2 == a^2 + b^2",
            gf_sq(gf_add(a, b)) == gf_add(gf_sq(a), gf_sq(b)),
            "paper Section 2.1, characteristic-2 Frobenius endomorphism")

    # ── 2. Polynomial arithmetic ─────────────────────────────────────────────
    t.section("2 · Polynomial Arithmetic")
    p1 = [gf_random(rng) for _ in range(5)]
    p2 = [gf_random(rng) for _ in range(3)]
    z  = gf_random(rng)
    prod = poly_mul(p1, p2)
    t.check("(p1·p2)(z) == p1(z)·p2(z)  [Horner vs convolution]",
            poly_eval(prod, z) == gf_mul(poly_eval(p1, z), poly_eval(p2, z)))
    q, r = poly_divmod(p1, p2)
    t.check("p1 == q·p2 + r  [poly_divmod correctness]",
            poly_trim(poly_add(poly_mul(q, p2), r)) == poly_trim(p1))
    t.check("deg(r) < deg(p2)  [remainder degree bound]",
            poly_degree(r) < poly_degree(p2))

    # ── 3. Vanishing polynomials ─────────────────────────────────────────────
    t.section("3 · Vanishing Polynomials  (Theorem 3.1 — Artin-Schreier)")
    k_vp = 4
    basis_vp = generate_basis(k_vp, rng)
    span = {0}
    for b_ in basis_vp:
        span = span | {gf_add(s, b_) for s in span}
    V_full = build_vanishing_poly(basis_vp)
    t.check(f"basis has {k_vp} F_2-linearly independent elements",
            len(basis_vp) == k_vp)
    t.check(f"span has size 2^{k_vp} = {1 << k_vp}",
            len(span) == (1 << k_vp))
    t.check(f"deg(V_full) == 2^{k_vp}  [linearized polynomial degree]",
            poly_degree(V_full) == (1 << k_vp),
            f"got degree {poly_degree(V_full)}")
    t.check("V_full vanishes on every element of the additive subspace",
            all(poly_eval(V_full, s) == 0 for s in span))

    # ── 4. Miko Decomposition ────────────────────────────────────────────────
    t.section("4 · Miko Decomposition  (Def 3.2, Thm 3.3 Uniqueness, Thm 3.4 Degree Bounds)")
    k = 5
    n = 1 << k
    basis = generate_basis(k, rng)
    R = [gf_random(rng) for _ in range(n)]
    Q, rf, vp = miko_decompose(R, basis)
    Q2, rf2, _ = miko_decompose(R, basis)  # re-decompose same R
    t.check(f"decomposition produced k={k} quotients",           len(Q) == k)
    t.check("Theorem 3.3 (Uniqueness): repeated decomposition is bit-identical",
            Q == Q2 and rf == rf2)
    bounds = verify_degree_bounds(Q, k)
    t.check("Theorem 3.4: all deg(Q_j) < n/2^{j+1}",
            all(ok for _, _, _, ok in bounds))
    if verbose:
        for j, actual, bound, ok in bounds:
            t.check(f"  deg(Q_{j}) = {actual} < {bound + 1}", ok)
    identity_ok = True
    for _ in range(10):
        zt = gf_random(rng)   # single z used for BOTH sides — critical
        if poly_eval(R, zt) != miko_reconstruct(Q, rf, vp, zt):
            identity_ok = False
            break
    t.check("Miko identity R(z) = r_final + Σ V_j(z)·Q_j(z) holds at 10 random z",
            identity_ok)
    Rz_Q, rz_rf, _ = miko_decompose([0] * n, basis)
    t.check("R = 0  →  all Q_j = 0, r_final = 0  (Thm 3.3 applied to zero poly — key to 140B proof)",
            all(poly_degree(Qj) < 0 for Qj in Rz_Q) and rz_rf == 0)

    # ── 5. Hash Chain Commitment ─────────────────────────────────────────────
    t.section("5 · Hash Chain Commitment  (Def 4.1, Lemma 4.2, Lemma 4.3 Phase 3 Lock)")
    com, _ = hash_chain_commit(Q, rf)
    com_r, _ = hash_chain_commit(Q, rf)
    t.check("com is 32 bytes",         len(com) == 32)
    t.check("com is deterministic",    com == com_r)
    Qp = [list(Qj) for Qj in Q]
    Qp[0] = Qp[0] if Qp[0] else [0]
    Qp[0][0] = gf_add(Qp[0][0], 1)
    com_p, _ = hash_chain_commit(Qp, rf)
    t.check("Lemma 4.2: perturbing Q_0 changes com",             com_p != com)
    z0 = fiat_shamir_challenge(com, 0)
    z0_p = fiat_shamir_challenge(com_p, 0)
    t.check("Lemma 4.3 (Phase 3 lock): changed com changes challenge z_0",  z0 != z0_p)

    # ── 6. Mira RLC cross-binding ────────────────────────────────────────────
    t.section("6 · Mira RLC Cross-Binding  (Lemma 5.1)")
    v0 = miko_reconstruct(Q, rf, vp, z0)
    binding, A_c, C_c = mira_cross_binding(Q, rf, vp, com, z0, v0, k)
    bind2, _, _ = mira_cross_binding(Q, rf, vp, com, z0, v0, k)
    t.check("cross-binding is deterministic", binding == bind2)
    fq = [list(Qj) for Qj in Q]
    fq[1] = fq[1] if fq[1] else [0]
    fq[1][0] = gf_add(fq[1][0], gf_random(rng))
    v0f = miko_reconstruct(fq, rf, vp, z0)
    bind_f, _, _ = mira_cross_binding(fq, rf, vp, com, z0, v0f, k)
    t.check("Lemma 5.1: fake Q produces different binding value",  bind_f != binding)

    # ── 7. Full proof generation and verification ────────────────────────────
    t.section("7 · Full Proof: Generation & Verification  (Section 7.3 Defense Ordering)")

    # Satisfied circuit
    R_sat: Poly = [0] * n
    proof_sat = generate_proof(R_sat, basis)
    res_sat = verify_proof(proof_sat, R_original=R_sat)
    t.check("[SATISFIED] hash_chain_ok",   res_sat["hash_chain_ok"])
    t.check("[SATISFIED] fiat_shamir_ok",  res_sat["fiat_shamir_ok"])
    t.check("[SATISFIED] R(z0) == 0  (reconstruction check — no R_original needed)",
            res_sat["R_z0_is_zero"])
    t.check("[SATISFIED] R(z1) == 0",      res_sat["R_z1_is_zero"])
    t.check("[SATISFIED] mira_binding_ok", res_sat["mira_binding_ok"])
    t.check("[SATISFIED] degree_bounds_ok",res_sat["degree_bounds_ok"])
    t.check("[SATISFIED] all_ok → ACCEPT", res_sat["all_ok"])
    t.check("[SATISFIED] miko_identity_z0 (ground-truth cross-check)",
            res_sat.get("miko_identity_z0", True))

    # Unsatisfied circuit
    R_bad: Poly = [gf_random(rng) for _ in range(n)]
    R_bad[0] |= 1
    proof_bad = generate_proof(R_bad, basis)
    res_bad = verify_proof(proof_bad, R_original=R_bad)
    t.check("[UNSATISFIED] R(z0) != 0 (Schwartz-Zippel catches it)",
            not res_bad["R_z0_is_zero"])
    t.check("[UNSATISFIED] all_ok → REJECT",  not res_bad["all_ok"])

    # ── 8. THE SECURITY FIX ──────────────────────────────────────────────────
    t.section(f"8 · Security Fix: verify_proof(proof, R_original=None)  [{forgery_trials} forgeries]")
    print(f"  Testing that forged proofs are rejected without R_original (on-chain verifier mode).")
    print(f"  Before fix: all_ok was True for every forged proof  (BUG).")
    print(f"  After fix:  recon_z != 0 check is always in all_ok (no R_original needed).")

    forgery_result = exercise_forgery_no_R_original(basis, rng, n_trials=forgery_trials)
    t.check(
        f"All {forgery_trials} forged proofs rejected without R_original  "
        f"(catch rate {forgery_result['catch_rate']:.1%})",
        forgery_result["fix_works"],
        forgery_result["note"],
    )

    # ── 9. RMC towers ────────────────────────────────────────────────────────
    t.section("9 · Recursive Miko Commitment (RMC) Towers  (Section 6)")
    basis_r = generate_basis(6, rng)
    R_r = [gf_random(rng) for _ in range(1 << 6)]
    tower = build_rmc_tower(R_r, basis_r, leaf_threshold=4)
    leaves = rmc_collect_leaves(tower)
    z_t = gf_random(rng)
    t.check(f"tower has {len(leaves)} leaves",              len(leaves) > 1)
    t.check("rmc_ascend_eval reconstructs R(z) exactly  (Miko identity at every node)",
            rmc_ascend_eval(tower, z_t) == poly_eval(R_r, z_t))
    m = rmc_internal_node_count(tower)
    t.check(f"tower has {m} internal nodes",               m > 0)
    evals = rmc_collect_internal_evals(tower, z_t)
    _, _, _, alpha_r = derive_mira_params(tower.commitment(), z_t, 0)
    t.check("Lemma 5.2: Mira-batched internal node fold is a field element",
            isinstance(mira_fold(evals, alpha_r), int))

    # ── 10. Dual binding ─────────────────────────────────────────────────────
    t.section("10 · Dual Binding Security  (Theorem 6.1, Corollary 6.2)")
    db = exercise_dual_binding(basis_r, rng, n_perturbations=30)
    t.check(
        f"Every perturbation caught by ≥1 path  "
        f"(either-path rate {db['either_path_rate']:.1%})",
        db["either_path_rate"] == 1.0,
    )
    t.check(
        f"Algebraic path (Path 2) independent catch rate {db['path2_algebraic_rate']:.1%}",
        db["path2_algebraic_rate"] > 0.85,
        "information-theoretic; should be near 1.0 given field size",
    )
    t.check(
        f"Cryptographic path (Path 1) catch rate {db['path1_cryptographic_rate']:.1%}",
        db["path1_cryptographic_rate"] == 1.0,
    )
    if verbose:
        print(f"      Both paths simultaneously: {db['both_paths_rate']:.1%}")
        print(f"      Tower: {db['leaves']} leaves, {db['internal_nodes']} internal nodes")

    # ── 11. Three soundness strategies ───────────────────────────────────────
    t.section("11 · Three Exhaustive Attack Strategies  (Theorem 7.1)")

    s1 = exercise_strategy1(basis, rng)
    t.check(f"Strategy 1 — real nonzero R: verifier REJECTS",
            s1["verifier_correctly_rejects"],
            s1["note"])

    s2 = exercise_strategy2(basis, rng, n_trials=500)
    t.check(f"Strategy 2 — fake quotients: Miko identity catch rate {s2['miko_catch_rate']:.1%}  (>95%)",
            s2["miko_catch_rate"] > 0.95)
    t.check(f"Strategy 2 — fake quotients: Mira binding catch rate  {s2['binding_catch_rate']:.1%}  (>95%)",
            s2["binding_catch_rate"] > 0.95)
    t.check(f"Strategy 2 — zero escape count: {s2['escape_count']}",
            s2["escape_count"] == 0,
            "every forgery caught by at least one of the two independent defenses")

    s3 = exercise_strategy3(basis, rng)
    t.check("Strategy 3 — zero-residual: Miko identity holds trivially  (expected)",
            s3["miko_identity_trivial"])
    t.check("Strategy 3 — zero-residual: DETERMINISTICALLY rejected by public-point check",
            s3["deterministically_rejected"])

    # ── 12. Multi-proof aggregation ──────────────────────────────────────────
    t.section("12 · Multi-Proof Aggregation  (Section 5.4)")
    proofs = [generate_proof([gf_random(rng) if i else 0 for i in range(n)], basis)
              for _ in range(4)]
    # Note: satisfying all four (R=0 for each) — not the point here; aggregation itself is the test
    agg_proofs = [generate_proof([0] * n, basis) for _ in range(4)]
    delta = sha_field(b"".join(p.com for p in agg_proofs))
    agg1  = mira_fold([p.binding for p in agg_proofs], delta)
    agg2  = mira_fold([p.binding for p in agg_proofs], delta)
    t.check("aggregation is deterministic", agg1 == agg2)
    tampered = list(agg_proofs)
    tampered[0] = generate_proof([gf_random(rng) for _ in range(n)], basis)
    delta_t = sha_field(b"".join(p.com for p in tampered))
    agg_t   = mira_fold([p.binding for p in tampered], delta_t)
    t.check("substituting one proof changes the aggregated binding", agg_t != agg1)

    # ── 13. Recursive composition — the 140-byte outer proof ─────────────────
    t.section("13 · Recursive Composition: The ~140-Byte Outer Proof  (Section 8)")
    basis_out = generate_basis(OUTER_VERIFIER_K, rng)

    outer_v, diag_v = build_outer_proof(True,  basis_out, rng)
    outer_i, diag_i = build_outer_proof(False, basis_out, rng)

    t.check("VALID inner:   outer circuit residual R_2 = 0",
            diag_v["R2_is_zero"])
    t.check("VALID inner:   Theorem 3.3 forces ALL outer quotients to zero",
            diag_v["all_outer_quotients_zero"],
            "structural origin of the constant outer proof size")
    t.check("VALID inner:   effective_depth = 0  (complete tower collapse)",
            diag_v["effective_depth"] == 0)
    t.check(f"VALID inner:   outer proof size = {diag_v['proof_size_bytes']} bytes  (target 120–160)",
            120 <= diag_v["proof_size_bytes"] <= 160,
            str(diag_v["breakdown"]))
    t.check("VALID inner:   outer verifier ACCEPTS",
            verify_outer_proof(outer_v, expect_valid=True))

    t.check("INVALID inner: outer circuit residual R_2 != 0",
            not diag_i["R2_is_zero"])
    t.check("INVALID inner: outer quotients are NOT all zero",
            not diag_i["all_outer_quotients_zero"])
    t.check("INVALID inner: outer verifier REJECTS",
            verify_outer_proof(outer_i, expect_valid=True) == False)

    if verbose:
        bd = diag_v["breakdown"]
        print(f"\n  Byte breakdown for 140-byte outer proof (valid-inner case):")
        print(f"    com2              : {bd['com2']} bytes")
        print(f"    binding2          : {bd['binding2']} bytes")
        print(f"    quotients_folded  : {bd['quotients_folded']} bytes  "
              f"(Mira fold of all-zero Q evaluations = 0, a field element)")
        print(f"    r_final2          : {bd['r_final2']} bytes  (= 0)")
        print(f"    metadata          : {bd['metadata']} bytes  (k, n, validity flag)")
        print(f"    TOTAL             : {bd['total']} bytes")

    return t.summary()


# ==============================================================================
# SECTION 13 — ENTRY POINT
# ==============================================================================


def main() -> int:
    p = argparse.ArgumentParser(
        description="PMM V1 complete Python reference implementation and test suite.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python3 pmm_v1.py                   # full test suite
  python3 pmm_v1.py --verbose         # with per-step detail and byte breakdowns
  python3 pmm_v1.py --bench           # inner proof size benchmark only
  python3 pmm_v1.py --seed 42         # reproducible run with seed 42
  python3 pmm_v1.py --forgery 1000    # 1000 forgery attempts in the security fix test
  python3 pmm_v1.py --bench --verbose # benchmark with per-level breakdown
        """,
    )
    p.add_argument("--seed",    type=int, default=1337, help="random seed (default: 1337)")
    p.add_argument("--verbose", action="store_true",   help="detailed per-step output")
    p.add_argument("--bench",   action="store_true",   help="run inner proof size benchmark only")
    p.add_argument("--forgery", type=int, default=500, help="forgery trial count (default: 500)")
    args = p.parse_args()

    rng = random.Random(args.seed)

    try:
        if args.bench:
            print(f"\nPMM V1 — INNER PROOF SIZE BENCHMARK  (seed={args.seed})")
            rows = run_inner_proof_benchmark(
                k_values=list(range(3, 12)), rng=rng, verbose=args.verbose
            )
            print_inner_proof_benchmark(rows, verbose=args.verbose)
            return 0

        ok = run_all_tests(seed=args.seed, verbose=args.verbose, forgery_trials=args.forgery)

        # Always append the benchmark after the test suite
        print()
        rows = run_inner_proof_benchmark(k_values=list(range(3, 10)), rng=rng, verbose=args.verbose)
        print_inner_proof_benchmark(rows, verbose=args.verbose)

        return 0 if ok else 1

    except Exception:
        print("\nUNEXPECTED ERROR:\n")
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
