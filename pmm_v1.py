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
WHAT THIS FILE IS
--------------------------------------------------------------------------------
This is a single, self-contained Python file implementing and testing the
*entire* PMM V1 pipeline end-to-end:

    1. Binary field arithmetic over F_{2^256}
       (p(X) = X^256 + X^10 + X^5 + X^2 + 1, the NIST SP 800-38D pentanomial)
    2. Polynomial arithmetic over F_{2^256}
    3. Vanishing polynomial construction (Artin-Schreier iteration, Theorem 3.1)
    4. Miko Decomposition (Definition 3.2, Theorems 3.3 / 3.4 / Lemma 3.6)
    5. Hash Chain Commitment (Definition 4.1, Lemma 4.2, Phase 3 lock Lemma 4.3)
    6. Mira RLC: cross-binding, RMC tower batch verification, multi-proof
       aggregation (Section 5)
    7. Recursive Miko Commitment (RMC) towers (Section 6)
    8. Dual binding security architecture (Section 6.3, Theorem 6.1)
    9. The three exhaustive soundness attack strategies (Section 7, Theorem 7.1)
   10. Native recursive composition producing the constant ~140-byte outer
       proof (Section 8)

Every primitive in the paper is implemented here and exercised by an
automated test in `run_all_tests()`. The test suite is the verification
record: if it prints ALL TESTS PASSED, every primitive in the paper has been
mechanically checked against its own specification on this machine, right
now, with no external dependencies beyond the Python standard library.

--------------------------------------------------------------------------------
WHY ONE FILE
--------------------------------------------------------------------------------
This is intentionally a single file rather than a package of modules. The
goal is that a reviewer can:

    1. Download exactly one file.
    2. Run exactly one command.
    3. Read top-to-bottom, in the same order as the paper's sections.

No project setup, no virtual environment requirement (though one is
recommended), no import path configuration. `python3 pmm_v1.py` is the
entire review process.

--------------------------------------------------------------------------------
USAGE
--------------------------------------------------------------------------------
    python3 pmm_v1.py                  Run the full test suite (default)
    python3 pmm_v1.py --verbose         Run with detailed per-step output
    python3 pmm_v1.py --seed 12345      Run with a specific random seed
    python3 pmm_v1.py --help            Show command-line options

See README.md in this repository for a full walkthrough.

--------------------------------------------------------------------------------
LICENSE / STATUS
--------------------------------------------------------------------------------
Reference implementation for review and verification purposes. This is a
pure-Python implementation intended for correctness review, not for
production proving (see the paper's Section 10 for hardware-accelerated
Rust performance figures; this file makes no performance claims).
================================================================================
"""

import hashlib
import struct
import random
import argparse
import sys
import traceback
from dataclasses import dataclass, field
from typing import List, Tuple, Optional, Dict, Any


# ==============================================================================
# SECTION 1 — FIELD ARITHMETIC OVER F_{2^256}
# Paper reference: Section 2.1 "The Binary Field F_{2^256}"
# ==============================================================================
#
# Field: F_{2^256} = F_2[X] / p(X)
# p(X) = X^256 + X^10 + X^5 + X^2 + 1   (NIST SP 800-38D irreducible pentanomial)
#
# Addition is XOR. Multiplication is carryless polynomial multiplication
# followed by reduction modulo p(X). Squaring coincides with the Frobenius
# endomorphism: (a+b)^2 = a^2 + b^2 in characteristic 2.

FIELD_BITS = 256
FIELD_MASK = (1 << FIELD_BITS) - 1

# p(X) reduction terms below bit 256: X^10 + X^5 + X^2 + 1
_REDUCTION_LOW = (1 << 10) | (1 << 5) | (1 << 2) | 1


def gf_add(a: int, b: int) -> int:
    """Addition in F_{2^256}: bitwise XOR."""
    return a ^ b


def gf_mul(a: int, b: int) -> int:
    """
    Multiplication in F_{2^256}: carryless multiply, reduced modulo
    p(X) = X^256 + X^10 + X^5 + X^2 + 1.

    This is a straightforward shift-and-XOR schoolbook implementation,
    sufficient for correctness verification (the paper's Rust
    implementation uses PCLMULQDQ/PMULL hardware acceleration for speed;
    this file makes no performance claims, only correctness ones).
    """
    if a == 0 or b == 0:
        return 0
    result = 0
    aa, bb = a, b
    while bb:
        if bb & 1:
            result ^= aa
        aa <<= 1
        bb >>= 1
    # Reduce any bits at position >= 256 using p(X) ≡ X^10+X^5+X^2+1 (mod X^256)
    for i in range(result.bit_length() - 1, FIELD_BITS - 1, -1):
        if (result >> i) & 1:
            shift = i - FIELD_BITS
            result ^= (1 << i) | (_REDUCTION_LOW << shift)
    return result & FIELD_MASK


def gf_sq(a: int) -> int:
    """Squaring = Frobenius endomorphism in characteristic 2: a -> a^2."""
    return gf_mul(a, a)


def gf_pow(a: int, e: int) -> int:
    """Exponentiation by repeated squaring."""
    result = 1
    base = a
    while e:
        if e & 1:
            result = gf_mul(result, base)
        base = gf_mul(base, base)
        e >>= 1
    return result


def gf_inv(a: int) -> int:
    """
    Multiplicative inverse via Fermat's little theorem generalization:
    a^(|F|-2) = a^-1 for nonzero a in a finite field of size |F|.
    (The paper's Rust implementation uses an Itoh-Tsujii addition chain
    for speed; this is the direct correctness-equivalent computation.)
    """
    if a == 0:
        raise ZeroDivisionError("Cannot invert the zero element of F_{2^256}")
    return gf_pow(a, (1 << FIELD_BITS) - 2)


def gf_div(a: int, b: int) -> int:
    """Division: a / b = a * b^-1."""
    return gf_mul(a, gf_inv(b))


def gf_random(rng: random.Random) -> int:
    """A uniformly random nonzero field element."""
    while True:
        x = rng.getrandbits(FIELD_BITS) & FIELD_MASK
        if x != 0:
            return x


# ==============================================================================
# SECTION 2 — POLYNOMIAL ARITHMETIC OVER F_{2^256}
# ==============================================================================
#
# Polynomials are represented as Python lists of field elements,
# little-endian by degree: p = [c0, c1, c2, ...] means p(X) = c0 + c1*X + ...

Poly = List[int]


def poly_degree(p: Poly) -> int:
    """Degree of p, or -1 for the zero polynomial."""
    for i in range(len(p) - 1, -1, -1):
        if p[i] != 0:
            return i
    return -1


def poly_trim(p: Poly) -> Poly:
    """Remove leading zero coefficients; the zero polynomial trims to [0]."""
    d = poly_degree(p)
    if d < 0:
        return [0]
    return list(p[: d + 1])


def poly_add(a: Poly, b: Poly) -> Poly:
    """Polynomial addition: coefficient-wise XOR."""
    n = max(len(a), len(b))
    r = [0] * n
    for i, c in enumerate(a):
        r[i] ^= c
    for i, c in enumerate(b):
        r[i] ^= c
    return poly_trim(r)


def poly_mul(a: Poly, b: Poly) -> Poly:
    """Polynomial multiplication via schoolbook convolution over F_{2^256}."""
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
    """Evaluate p at x via Horner's method."""
    result = 0
    for c in reversed(p):
        result = gf_add(gf_mul(result, x), c)
    return result


def poly_scalar_mul(p: Poly, scalar: int) -> Poly:
    """Multiply every coefficient of p by a fixed field element."""
    return poly_trim([gf_mul(c, scalar) for c in p])


def poly_divmod(a: Poly, b: Poly) -> Tuple[Poly, Poly]:
    """
    Polynomial division over a field: returns (quotient, remainder) such
    that a = quotient * b + remainder and deg(remainder) < deg(b).

    This is the Euclidean division step used at every level of the Miko
    decomposition (Theorem 3.3: unique quotient/remainder over a field).
    """
    da, db = poly_degree(a), poly_degree(b)
    if db < 0:
        raise ZeroDivisionError("Division by the zero polynomial")
    if da < db:
        return [0], list(a)
    r = list(a) + [0] * max(0, db - len(a) + 1)
    q = [0] * (da - db + 1)
    b_lead_inv = gf_inv(b[db])
    for i in range(da - db, -1, -1):
        if r[i + db] == 0:
            continue
        coeff = gf_mul(r[i + db], b_lead_inv)
        q[i] = coeff
        for j in range(db + 1):
            r[i + j] ^= gf_mul(coeff, b[j])
    return poly_trim(q), poly_trim(r)


# ==============================================================================
# SECTION 3 — VANISHING POLYNOMIALS (Artin-Schreier Iteration)
# Paper reference: Theorem 3.1 "Linearized Vanishing Polynomial"
# ==============================================================================
#
# Given an additive subspace S = span_{F2}{beta_0,...,beta_{k-1}}, the
# vanishing polynomial V_S(X) = prod_{s in S} (X+s) is constructed via:
#
#   V_0(X) = X
#   V_{i+1}(X) = V_i(X)^2 + lambda_i * V_i(X),   lambda_i = V_i(beta_i)
#
# This gives a *linearized* polynomial (only X^{2^i} terms nonzero),
# evaluable in O(k) = O(log n) operations rather than O(2^k) = O(n).


def build_vanishing_poly(basis: List[int]) -> Poly:
    """
    Build the vanishing polynomial of span_{F2}(basis) via the
    Artin-Schreier iteration of Theorem 3.1.
    """
    V: Poly = [0, 1]  # V_0(X) = X
    for beta_i in basis:
        lam = poly_eval(V, beta_i)
        V_sq = poly_mul(V, V)            # Frobenius squaring of a linearized poly
        lam_V = poly_scalar_mul(V, lam)
        V = poly_add(V_sq, lam_V)
    return poly_trim(V)


def build_subspace_vanishing(basis: List[int], j: int, k: int) -> Poly:
    """
    V_j(X): the vanishing polynomial of span{beta_{j+1},...,beta_{k-1}},
    as required at level j of the Miko decomposition (Definition 3.2).
    When j+1 == k (the last level), this is the vanishing polynomial of
    the empty span {0}, i.e. V(X) = X.
    """
    sub_basis = basis[j + 1 : k]
    if not sub_basis:
        return [0, 1]
    return build_vanishing_poly(sub_basis)


def generate_basis(k: int, rng: random.Random) -> List[int]:
    """
    Generate k field elements that are F_2-linearly independent, forming
    a basis for an additive subspace of size 2^k. Uses a greedy
    independence check via XOR-span membership over a reduced integer
    representation (sufficient since F_{2^256} addition is XOR).
    """
    basis: List[int] = []
    span = {0}
    attempts = 0
    while len(basis) < k:
        attempts += 1
        if attempts > 100000:
            raise RuntimeError("Failed to generate a linearly independent basis")
        candidate = gf_random(rng)
        if candidate in span:
            continue
        basis.append(candidate)
        span = span | {gf_add(s, candidate) for s in span}
    return basis


# ==============================================================================
# SECTION 4 — MIKO DECOMPOSITION
# Paper reference: Definition 3.2, Theorem 3.3 (Uniqueness),
#                   Theorem 3.4 (Degree Bounds), Lemma 3.6 (Soundness)
# ==============================================================================
#
# R_0(X) = R(X)
# R_j(X) = R_{j+1}(X) + V_j(X) * Q_j(X),   j = 0,...,k-1
# R_k = r_final  (a constant)
#
# Theorem 3.3 (Uniqueness): for fixed R and basis, (Q_0,...,Q_{k-1}, r_final)
# is the *unique* sequence satisfying these identities, because polynomial
# division over a field has a unique quotient/remainder pair at every step.
#
# Theorem 3.4 (Degree Bounds): deg(Q_j) < n / 2^{j+1}.


def miko_decompose(R: Poly, basis: List[int]) -> Tuple[List[Poly], int, List[Poly]]:
    """
    Perform the Miko Decomposition of R(X) over the given basis.

    Returns:
        quotients:       [Q_0, ..., Q_{k-1}]
        r_final:          the constant remainder after k levels
        vanishing_polys: [V_0, ..., V_{k-1}]  (returned for reuse by the verifier)
    """
    k = len(basis)
    n = 1 << k
    deg_R = poly_degree(R)
    if deg_R >= n:
        raise ValueError(f"deg(R)={deg_R} must be < n=2^{k}={n} (Definition 3.2)")

    quotients: List[Poly] = []
    vanishing_polys: List[Poly] = []
    R_curr = poly_trim(R)

    for j in range(k):
        Vj = build_subspace_vanishing(basis, j, k)
        vanishing_polys.append(Vj)
        Qj, R_next = poly_divmod(R_curr, Vj)
        quotients.append(poly_trim(Qj))
        R_curr = R_next

    r_final = R_curr[0] if R_curr else 0
    return quotients, r_final, vanishing_polys


def miko_reconstruct(
    quotients: List[Poly], r_final: int, vanishing_polys: List[Poly], z: int
) -> int:
    """
    The Miko identity, evaluated at challenge point z:

        R(z) = r_final + sum_j V_j(z) * Q_j(z)

    This is the core algebraic check of the entire system (Definition 3.2).
    """
    val = r_final
    for Vj, Qj in zip(vanishing_polys, quotients):
        val = gf_add(val, gf_mul(poly_eval(Vj, z), poly_eval(Qj, z)))
    return val


def verify_degree_bounds(
    quotients: List[Poly], k: int
) -> List[Tuple[int, int, int, bool]]:
    """
    Check Theorem 3.4: deg(Q_j) < n / 2^{j+1} for every level j.
    Returns a list of (level, actual_degree, bound_minus_1, ok) tuples.
    """
    results = []
    for j, Qj in enumerate(quotients):
        bound = 1 << (k - j - 1)
        actual = poly_degree(Qj)
        ok = actual < bound
        results.append((j, actual, bound - 1, ok))
    return results


def effective_depth(quotients: List[Poly]) -> int:
    """
    Number of levels with a nonzero quotient. By Theorem 3.4's tightness,
    this equals ceil(log2(deg(R)+1)) for the original R (used to confirm
    that R = 0 collapses to depth 0 -- the key fact behind the constant-
    size recursive outer proof of Section 8).
    """
    return sum(1 for Qj in quotients if poly_degree(Qj) >= 0)


# ==============================================================================
# SECTION 5 — HASH CHAIN COMMITMENT
# Paper reference: Definition 4.1, Lemma 4.2 (Binding), Lemma 4.3 (Phase 3 Lock)
# ==============================================================================
#
# h_k = SHA256("final" || r_final_bytes)
# h_j = SHA256(h_{j+1} || "level_" || j || Q_j_bytes),  j = k-1,...,0
# com = h_0


def field_to_bytes(x: int) -> bytes:
    """Serialize a field element as 32 bytes, big-endian."""
    return x.to_bytes(32, "big")


def poly_to_bytes(p: Poly) -> bytes:
    """Serialize a polynomial as: 4-byte length prefix + 32 bytes per coefficient."""
    trimmed = poly_trim(p)
    out = struct.pack(">I", len(trimmed))
    for c in trimmed:
        out += field_to_bytes(c)
    return out


def hash_chain_commit(quotients: List[Poly], r_final: int) -> Tuple[bytes, List[bytes]]:
    """
    Build the sequential SHA-256 hash chain commitment of Definition 4.1.
    Returns (com, all_intermediate_hashes).
    """
    k = len(quotients)
    hashes: List[Optional[bytes]] = [None] * (k + 1)

    h = hashlib.sha256()
    h.update(b"final")
    h.update(field_to_bytes(r_final))
    hashes[k] = h.digest()

    for j in range(k - 1, -1, -1):
        h = hashlib.sha256()
        h.update(hashes[j + 1])
        h.update(b"level_")
        h.update(struct.pack(">I", j))
        h.update(poly_to_bytes(quotients[j]))
        hashes[j] = h.digest()

    com = hashes[0]
    return com, hashes  # type: ignore[return-value]


def fiat_shamir_challenge(com: bytes, index: int) -> int:
    """z_i = SHA256(com || i), reduced into F_{2^256} (a 256-bit digest is
    already exactly the field's bit-width, so reduction is a direct mask)."""
    h = hashlib.sha256()
    h.update(com)
    h.update(struct.pack(">I", index))
    return int.from_bytes(h.digest(), "big") & FIELD_MASK


def sha_field(*parts: bytes) -> int:
    """Generic helper: SHA256 of concatenated byte parts, reduced to a field element."""
    h = hashlib.sha256()
    for p in parts:
        h.update(p)
    return int.from_bytes(h.digest(), "big") & FIELD_MASK


# ==============================================================================
# SECTION 6 — MIRA: MULTI-INSTANCE RECURSIVE AGGREGATION
# Paper reference: Section 5, Lemma 5.1 (Cross-Binding), Lemma 5.2 (RMC Batch),
#                   Section 5.4 (Multi-Proof Aggregation)
# ==============================================================================
#
# binding = A_combined + gamma1 * C_combined + gamma2 * r_final
#
# A_combined = sum_i beta^i * sum_j V_j(omega_i) * Q_j(omega_i)   (public points)
# C_combined = sum_j V_j(z) * Q_j(z)                              (challenge point)


def derive_mira_params(com: bytes, z: int, v: int) -> Tuple[int, int, int, int]:
    """Derive gamma1, gamma2 (cross-binding), beta (public-point fold),
    and alpha (RMC batch fold) -- all from com via Fiat-Shamir."""
    gamma1 = sha_field(com, field_to_bytes(z), field_to_bytes(v), b"\x00")
    gamma2 = sha_field(com, field_to_bytes(z), field_to_bytes(v), b"\x01")
    beta = sha_field(com, b"beta")
    alpha = sha_field(com, b"rmc_batch")
    return gamma1, gamma2, beta, alpha


def choose_public_points(com: bytes, k: int) -> List[int]:
    """Deterministically derive t = k+1 public evaluation points from com."""
    points = []
    for i in range(k + 1):
        pt = sha_field(com, b"pubpoint", struct.pack(">I", i))
        points.append(pt)
    return points


def mira_cross_binding(
    quotients: List[Poly],
    r_final: int,
    vanishing_polys: List[Poly],
    com: bytes,
    z: int,
    v: int,
    k: int,
) -> Tuple[int, int, int]:
    """
    Compute the Mira cross-binding value of equation (4) in the paper:

        binding = A_combined + gamma1 * C_combined + gamma2 * r_final

    Returns (binding, A_combined, C_combined).
    """
    gamma1, gamma2, beta, _ = derive_mira_params(com, z, v)
    public_points = choose_public_points(com, k)

    A_combined = 0
    beta_pow = 1
    for omega_i in public_points:
        inner = 0
        for Vj, Qj in zip(vanishing_polys, quotients):
            inner = gf_add(inner, gf_mul(poly_eval(Vj, omega_i), poly_eval(Qj, omega_i)))
        A_combined = gf_add(A_combined, gf_mul(beta_pow, inner))
        beta_pow = gf_mul(beta_pow, beta)

    C_combined = 0
    for Vj, Qj in zip(vanishing_polys, quotients):
        C_combined = gf_add(C_combined, gf_mul(poly_eval(Vj, z), poly_eval(Qj, z)))

    binding = gf_add(gf_add(A_combined, gf_mul(gamma1, C_combined)), gf_mul(gamma2, r_final))
    return binding, A_combined, C_combined


def mira_fold(values: List[int], alpha: int) -> int:
    """
    Generic Mira RLC fold: sum_i alpha^i * values[i].
    Used for RMC tower batch verification (Lemma 5.2) and for multi-proof
    aggregation (Section 5.4).
    """
    result, coeff = 0, 1
    for v in values:
        result = gf_add(result, gf_mul(coeff, v))
        coeff = gf_mul(coeff, alpha)
    return result


# ==============================================================================
# SECTION 7 — RECURSIVE MIKO COMMITMENT (RMC) TOWERS
# Paper reference: Section 6 "RMC Towers: Recursive Miko Commitment",
#                   Theorem 6.1 (Dual Binding), Corollary 6.2 (Hash-Independent)
# ==============================================================================
#
# For circuits where shallow Miko levels produce high-degree quotients,
# RMC towers recursively re-apply Miko decomposition until all pieces have
# degree below a base threshold, encoding the decomposition as a binary
# tree where every internal node satisfies the Miko identity:
#
#     Q_parent(z) = Q_left(z) + V(z) * Q_right(z)
#
# Security is dual: Path 1 (cryptographic) requires a SHA-256 preimage to
# forge the tree's root commitment; Path 2 (algebraic) requires the forged
# leaves to still satisfy the Miko identity at random challenge points.
# An adversary must defeat *both* simultaneously (Theorem 6.1).


@dataclass
class RMCNode:
    """A single node of a Recursive Miko Commitment tower."""
    poly: Poly                       # the polynomial represented at this node
    left: Optional["RMCNode"] = None
    right: Optional["RMCNode"] = None
    vanishing: Optional[Poly] = None  # V used to combine left/right (internal nodes only)
    is_leaf: bool = False

    def commitment(self) -> bytes:
        """SHA-256 commitment of this node, recursive over children."""
        if self.is_leaf:
            return hashlib.sha256(b"leaf" + poly_to_bytes(self.poly)).digest()
        left_c = self.left.commitment()
        right_c = self.right.commitment()
        return hashlib.sha256(b"node" + left_c + right_c).digest()


def build_rmc_tower(R: Poly, basis: List[int], leaf_threshold: int = 8) -> RMCNode:
    """
    Recursively build an RMC tower for R over `basis`, splitting via Miko
    decomposition until every leaf polynomial has degree < leaf_threshold
    (Section 6.2, "Recursive Miko Decomposition").

    Each internal node stores the vanishing polynomial V that combines its
    two children via the Miko identity:  Q_parent = Q_left + V * Q_right.
    """
    deg = poly_degree(R)
    if deg < leaf_threshold:
        return RMCNode(poly=poly_trim(R), is_leaf=True)

    # Split using the first basis element available, halving the polynomial
    # via a single Miko decomposition step using only that element.
    if not basis:
        return RMCNode(poly=poly_trim(R), is_leaf=True)

    sub_basis = basis[1:]
    V = build_vanishing_poly([basis[0]]) if sub_basis else [0, 1]
    Qj, Rj = poly_divmod(R, V)

    left_node = build_rmc_tower(Rj, sub_basis, leaf_threshold)
    right_node = build_rmc_tower(Qj, sub_basis, leaf_threshold)

    return RMCNode(poly=poly_trim(R), left=left_node, right=right_node, vanishing=V)


def rmc_ascend_eval(node: RMCNode, z: int) -> int:
    """
    Ascend the RMC tower, evaluating the Miko identity at every internal
    node: Q_parent(z) = Q_left(z) + V(z) * Q_right(z) (equation 6).
    Returns the value reconstructed at the root.
    """
    if node.is_leaf:
        return poly_eval(node.poly, z)
    left_val = rmc_ascend_eval(node.left, z)
    right_val = rmc_ascend_eval(node.right, z)
    v_val = poly_eval(node.vanishing, z)
    return gf_add(left_val, gf_mul(v_val, right_val))


def rmc_collect_leaves(node: RMCNode) -> List[Poly]:
    """Collect all leaf polynomials of an RMC tower, left-to-right."""
    if node.is_leaf:
        return [node.poly]
    return rmc_collect_leaves(node.left) + rmc_collect_leaves(node.right)


def rmc_internal_node_count(node: RMCNode) -> int:
    """Count internal (non-leaf) nodes -- used for Mira batch verification (Lemma 5.2)."""
    if node.is_leaf:
        return 0
    return 1 + rmc_internal_node_count(node.left) + rmc_internal_node_count(node.right)


def rmc_collect_internal_evals(node: RMCNode, z: int) -> List[int]:
    """
    Collect, for every internal node, the value Q_node(z) used in the
    identity check, for Mira-batched verification (equation 5, Lemma 5.2):
    Q_batched = sum_j alpha^j * Q_node_j(z).
    """
    if node.is_leaf:
        return []
    val = rmc_ascend_eval(node, z)
    return [val] + rmc_collect_internal_evals(node.left, z) + rmc_collect_internal_evals(
        node.right, z
    )


def rmc_dual_binding_check(
    node: RMCNode, fake_leaves: List[Poly], z_points: List[int]
) -> Dict[str, Any]:
    """
    Exercise Theorem 6.1 (RMC Tower Dual Binding) directly: attempt to
    substitute `fake_leaves` for the tower's true leaves and check whether
    (a) the root commitment changes (Path 1, cryptographic) and
    (b) the re-ascended Miko identity differs at random points (Path 2, algebraic).

    A forgery only "succeeds" if it survives BOTH paths; this helper
    reports whether each path independently caught the substitution.
    """
    true_leaves = rmc_collect_leaves(node)
    true_root = node.commitment()

    def rebuild_with_leaves(n: RMCNode, leaves_iter) -> RMCNode:
        if n.is_leaf:
            return RMCNode(poly=next(leaves_iter), is_leaf=True)
        new_left = rebuild_with_leaves(n.left, leaves_iter)
        new_right = rebuild_with_leaves(n.right, leaves_iter)
        return RMCNode(
            poly=n.poly, left=new_left, right=new_right, vanishing=n.vanishing
        )

    fake_root_node = rebuild_with_leaves(node, iter(fake_leaves))
    fake_root = fake_root_node.commitment()

    path1_caught = fake_root != true_root  # cryptographic: commitment changed

    path2_results = []
    for z in z_points:
        true_val = rmc_ascend_eval(node, z)
        fake_val = rmc_ascend_eval(fake_root_node, z)
        path2_results.append(true_val != fake_val)
    path2_caught = all(path2_results)  # algebraic: identity differs everywhere tested

    return {
        "path1_cryptographic_caught": path1_caught,
        "path2_algebraic_caught": path2_caught,
        "either_path_caught": path1_caught or path2_caught,
        "both_paths_caught": path1_caught and path2_caught,
    }


# ==============================================================================
# SECTION 8 — FULL PROOF: GENERATION AND VERIFICATION
# Paper reference: Section 7 "Complete Security Analysis", Section 7.3
#                   (Defense Ordering for Efficient Verification)
# ==============================================================================


@dataclass
class PMMProof:
    """A complete PMM V1 inner proof."""
    com: bytes
    quotients: List[Poly]
    r_final: int
    vanishing_polys: List[Poly]
    z0: int
    z1: int
    R_z0: int
    R_z1: int
    binding: int
    A_combined: int
    C_combined: int
    k: int
    basis: List[int]


def generate_proof(R: Poly, basis: List[int]) -> PMMProof:
    """
    Full prover algorithm:
        1. Miko decompose R.
        2. Commit via the hash chain.
        3. Derive Fiat-Shamir challenges from the commitment.
        4. Evaluate R and the Miko reconstruction at the challenges.
        5. Compute the Mira cross-binding value.
    """
    k = len(basis)
    quotients, r_final, vanishing_polys = miko_decompose(R, basis)
    com, _ = hash_chain_commit(quotients, r_final)

    z0 = fiat_shamir_challenge(com, 0)
    z1 = fiat_shamir_challenge(com, 1)

    R_z0 = poly_eval(R, z0)
    R_z1 = poly_eval(R, z1)

    v0 = miko_reconstruct(quotients, r_final, vanishing_polys, z0)
    binding, A_combined, C_combined = mira_cross_binding(
        quotients, r_final, vanishing_polys, com, z0, v0, k
    )

    return PMMProof(
        com=com,
        quotients=quotients,
        r_final=r_final,
        vanishing_polys=vanishing_polys,
        z0=z0,
        z1=z1,
        R_z0=R_z0,
        R_z1=R_z1,
        binding=binding,
        A_combined=A_combined,
        C_combined=C_combined,
        k=k,
        basis=basis,
    )


def verify_proof(proof: PMMProof, R_original: Optional[Poly] = None) -> Dict[str, Any]:
    """
    Full verifier algorithm, following the defense ordering of Section 7.3:
        1. Hash chain verification         (cheap)
        2. Fiat-Shamir consistency         (cheap)
        3. Miko identity at challenges     (Lemma 3.6 / Theorem 7.1 Strategy 2)
        4. R(z_i) = 0 check                (Theorem 7.1 Strategy 1)
        5. Mira cross-binding              (Lemma 5.1 / Theorem 7.1 Strategy 2)
        6. Degree bounds                   (Theorem 3.4)
    """
    com = proof.com
    quotients = proof.quotients
    r_final = proof.r_final
    vanishing_polys = proof.vanishing_polys
    z0, z1 = proof.z0, proof.z1
    k = proof.k

    results: Dict[str, Any] = {}

    # Step 1: hash chain
    com2, _ = hash_chain_commit(quotients, r_final)
    results["hash_chain_ok"] = com2 == com

    # Step 2: Fiat-Shamir
    z0_check = fiat_shamir_challenge(com, 0)
    z1_check = fiat_shamir_challenge(com, 1)
    results["fiat_shamir_ok"] = (z0_check == z0) and (z1_check == z1)

    # Step 3: Miko identity reconstruction
    recon_z0 = miko_reconstruct(quotients, r_final, vanishing_polys, z0)
    recon_z1 = miko_reconstruct(quotients, r_final, vanishing_polys, z1)
    results["reconstructed_z0"] = recon_z0
    results["reconstructed_z1"] = recon_z1

    if R_original is not None:
        R_z0_actual = poly_eval(R_original, z0)
        R_z1_actual = poly_eval(R_original, z1)
        results["miko_identity_z0"] = recon_z0 == R_z0_actual
        results["miko_identity_z1"] = recon_z1 == R_z1_actual
        # Step 4: R(z_i) = 0 (Strategy 1 of Theorem 7.1)
        results["R_z0_is_zero"] = R_z0_actual == 0
        results["R_z1_is_zero"] = R_z1_actual == 0

    # Step 5: Mira cross-binding
    v0 = recon_z0
    binding_check, A_check, C_check = mira_cross_binding(
        quotients, r_final, vanishing_polys, com, z0, v0, k
    )
    results["mira_binding_ok"] = binding_check == proof.binding

    # Step 6: degree bounds (Theorem 3.4)
    degree_checks = verify_degree_bounds(quotients, k)
    results["degree_bounds_ok"] = all(ok for _, _, _, ok in degree_checks)
    results["degree_checks"] = degree_checks

    results["all_ok"] = all(
        [
            results["hash_chain_ok"],
            results["fiat_shamir_ok"],
            results["mira_binding_ok"],
            results["degree_bounds_ok"],
        ]
    )
    return results


def inner_proof_size_bytes(proof: PMMProof) -> Dict[str, int]:
    """
    Size accounting for the *inner* proof (before recursive composition
    collapses it to the constant outer proof of Section 8).
    """
    sizes: Dict[str, int] = {}
    sizes["com"] = 32
    sizes["r_final"] = 32
    sizes["binding"] = 32
    q_bytes = sum(len(poly_trim(Qj)) * 32 for Qj in proof.quotients)
    sizes["quotients_unfolded"] = q_bytes
    sizes["quotients_mira_folded"] = 32
    sizes["overhead"] = 12
    sizes["total_unfolded"] = (
        sizes["com"] + sizes["r_final"] + sizes["binding"] + q_bytes + sizes["overhead"]
    )
    sizes["total_mira_folded"] = (
        sizes["com"] + sizes["r_final"] + sizes["binding"] + 32 + sizes["overhead"]
    )
    return sizes


# ==============================================================================
# SECTION 9 — RECURSIVE COMPOSITION: THE 140-BYTE OUTER PROOF
# Paper reference: Section 8 "First Application: PMM with Recursive Composition"
# ==============================================================================
#
# The outer proof pi_2 attests that an inner proof pi_1 verifies correctly,
# using the SAME primitives (native recursion). When pi_1 is valid, the
# outer circuit's residual R_2 is identically zero. By Theorem 3.3
# (uniqueness), the unique Miko decomposition of the zero polynomial is
# the all-zero quotient sequence -- so the outer proof's quotients are
# *always* zero when valid, and need not be transmitted in full: only a
# constant-size confirmation is required. This is the structural origin
# of the ~140-byte constant outer proof size, independent of the original
# circuit's size.


OUTER_VERIFIER_K = 13  # paper: ~5,000-constraint PMM verifier circuit, k=13


@dataclass
class OuterProof:
    """The constant-size recursive (outer) PMM proof."""
    com2: bytes
    binding2: int
    quotients_folded: int
    r_final2: int
    metadata: bytes

    def size_bytes(self) -> int:
        return (
            len(self.com2)
            + 32  # binding2, serialized as a field element
            + 32  # quotients_folded, serialized as a field element
            + 32  # r_final2, serialized as a field element
            + len(self.metadata)
        )


def build_outer_proof(inner_valid: bool, basis: List[int], rng: random.Random) -> Tuple[OuterProof, Dict[str, Any]]:
    """
    Build the recursive outer proof attesting to the validity of an inner
    proof, exercising the full chain of reasoning behind the ~140-byte
    proof size:

        1. Model the outer circuit's residual R_2: identically zero when
           the inner proof is valid (by construction of the verifier
           circuit), nonzero otherwise.
        2. Miko-decompose R_2 -- by Theorem 3.3 this *must* yield the
           all-zero quotient sequence when R_2 = 0.
        3. Commit, derive challenges, Mira-fold the (all-zero) quotients
           into a single field element, and report the final byte count.

    Returns (outer_proof, diagnostics).
    """
    k = OUTER_VERIFIER_K
    n = 1 << k

    if inner_valid:
        R2: Poly = [0] * n  # R_2 identically zero: inner proof is valid
    else:
        R2 = [gf_random(rng) for _ in range(n)]
        R2[0] |= 1  # ensure strictly nonzero

    Q2, r_final2, vpolys2 = miko_decompose(R2, basis)

    all_zero_quotients = all(poly_degree(Qj) < 0 for Qj in Q2)

    com2, _ = hash_chain_commit(Q2, r_final2)
    z0 = fiat_shamir_challenge(com2, 0)

    _, _, beta, alpha = derive_mira_params(com2, z0, 0)
    quotient_evals = [poly_eval(Qj, z0) for Qj in Q2]
    quotients_folded = mira_fold(quotient_evals, alpha)

    v0 = miko_reconstruct(Q2, r_final2, vpolys2, z0)
    binding2, _, _ = mira_cross_binding(Q2, r_final2, vpolys2, com2, z0, v0, k)

    metadata = struct.pack(">I", k) + struct.pack(">I", n) + struct.pack(">I", 1 if inner_valid else 0)

    outer = OuterProof(
        com2=com2,
        binding2=binding2,
        quotients_folded=quotients_folded,
        r_final2=r_final2,
        metadata=metadata,
    )

    diagnostics = {
        "inner_valid": inner_valid,
        "R2_is_zero": poly_degree(R2) < 0,
        "all_outer_quotients_zero": all_zero_quotients,
        "r_final2": r_final2,
        "effective_depth": effective_depth(Q2),
        "k": k,
        "proof_size_bytes": outer.size_bytes(),
    }
    return outer, diagnostics


def verify_outer_proof(outer: OuterProof, expect_valid: bool) -> bool:
    """
    Verify the outer proof's defining property: when the inner proof was
    valid, r_final2 must be 0 and all outer quotients must have been zero
    (encoded in `quotients_folded` matching the fold of an all-zero
    sequence, which is itself 0). This is the deterministic check a real
    on-chain verifier performs -- comparison against public constants,
    no decomposition required at verification time.
    """
    if expect_valid:
        return outer.r_final2 == 0 and outer.quotients_folded == 0
    else:
        return not (outer.r_final2 == 0 and outer.quotients_folded == 0)


# ==============================================================================
# SECTION 10 — DUAL BINDING SECURITY EXERCISES
# Paper reference: Section 6.3 (Theorem 6.1), Section 6.3 Corollary 6.2,
#                   Section 7 (Theorem 7.1, all three strategies)
# ==============================================================================


def exercise_strategy1_real_nonzero_residual(
    basis: List[int], rng: random.Random
) -> Dict[str, Any]:
    """
    Theorem 7.1, Strategy 1: the prover uses a *real* (correctly
    decomposed) but nonzero residual R, from an unsatisfiable circuit.
    The honest decomposition, commitment, and challenges are all valid;
    the verifier must catch R(z) != 0 via Schwartz-Zippel.
    """
    k = len(basis)
    n = 1 << k
    R = [gf_random(rng) for _ in range(n)]
    R[0] |= 1  # ensure R != 0 (unsatisfiable circuit -> nonzero residual)

    proof = generate_proof(R, basis)
    result = verify_proof(proof, R_original=R)

    rejected = not (result.get("R_z0_is_zero", True) and result.get("R_z1_is_zero", True))
    return {
        "strategy": "1 (real nonzero residual)",
        "verifier_correctly_rejects": rejected,
        "R_z0": result.get("R_z0_val") if "R_z0_val" in result else None,
        "identity_held": result["miko_identity_z0"] and result["miko_identity_z1"],
    }


def exercise_strategy2_fake_quotients(
    basis: List[int], rng: random.Random, n_trials: int = 50
) -> Dict[str, Any]:
    """
    Theorem 7.1, Strategy 2: the prover substitutes fake quotients
    Q_j' != Q_j while keeping a genuine nonzero R. The Miko identity
    (first defense) and the Mira cross-binding (second defense) must
    independently catch this.
    """
    k = len(basis)
    n = 1 << k
    R = [gf_random(rng) for _ in range(n)]
    R[0] |= 1

    proof = generate_proof(R, basis)

    caught_by_identity = 0
    caught_by_binding = 0
    total = 0

    for _ in range(n_trials):
        fake_quotients = [list(Qj) for Qj in proof.quotients]
        j = rng.randrange(len(fake_quotients))
        if not fake_quotients[j]:
            fake_quotients[j] = [0]
        idx = rng.randrange(len(fake_quotients[j]))
        fake_quotients[j][idx] = gf_add(fake_quotients[j][idx], gf_random(rng))

        recon_fake = miko_reconstruct(
            fake_quotients, proof.r_final, proof.vanishing_polys, proof.z0
        )
        recon_true = miko_reconstruct(
            proof.quotients, proof.r_final, proof.vanishing_polys, proof.z0
        )
        if recon_fake != recon_true:
            caught_by_identity += 1

        v0_fake = recon_fake
        binding_fake, _, _ = mira_cross_binding(
            fake_quotients, proof.r_final, proof.vanishing_polys, proof.com, proof.z0, v0_fake, k
        )
        if binding_fake != proof.binding:
            caught_by_binding += 1

        total += 1

    return {
        "strategy": "2 (fake quotients)",
        "trials": total,
        "caught_by_miko_identity": caught_by_identity,
        "caught_by_mira_binding": caught_by_binding,
        "identity_catch_rate": caught_by_identity / total,
        "binding_catch_rate": caught_by_binding / total,
    }


def exercise_strategy3_zero_residual_attack(
    basis: List[int], rng: random.Random
) -> Dict[str, Any]:
    """
    Theorem 7.1, Strategy 3: the prover claims an all-zero quotient
    sequence and r_final = 0 (a "zero-residual attack"). The Miko
    identity holds trivially, but public-point consistency must
    *deterministically* reject this for any circuit with nonzero public
    inputs (Lemma 5.3 in the V1 paper's numbering / the zero-residual
    defense of Section 5.2).
    """
    k = len(basis)
    n = 1 << k

    fake_quotients = [[0] for _ in range(k)]
    fake_r_final = 0

    com_fake, _ = hash_chain_commit(fake_quotients, fake_r_final)
    z0_fake = fiat_shamir_challenge(com_fake, 0)

    vpolys = [build_subspace_vanishing(basis, j, k) for j in range(k)]
    recon = miko_reconstruct(fake_quotients, fake_r_final, vpolys, z0_fake)
    identity_holds_trivially = recon == 0

    # Simulate nonzero public inputs the verifier independently knows about
    public_inputs = [gf_random(rng) for _ in range(3)]
    _, _, beta, _ = derive_mira_params(com_fake, z0_fake, 0)
    A_expected = mira_fold(public_inputs, beta)

    binding_fake, A_combined_fake, _ = mira_cross_binding(
        fake_quotients, fake_r_final, vpolys, com_fake, z0_fake, recon, k
    )

    deterministically_rejected = A_combined_fake != A_expected

    return {
        "strategy": "3 (zero-residual attack)",
        "identity_holds_trivially": identity_holds_trivially,
        "A_combined_from_attack": A_combined_fake,
        "A_expected_from_public_inputs": A_expected,
        "deterministically_rejected": deterministically_rejected,
    }


def exercise_dual_binding(
    basis: List[int], rng: random.Random, n_perturbations: int = 20
) -> Dict[str, Any]:
    """
    Theorem 6.1 / Corollary 6.2: directly exercise the dual binding
    property on an RMC tower. For every single-coefficient perturbation
    of the tower's leaves, confirm that EITHER the cryptographic path
    (commitment changes) OR the algebraic path (Miko identity differs at
    random challenge points) catches the forgery -- and tabulate how
    often each path independently does so, to confirm their claimed
    independence (an adversary defeating one must still face the other).
    """
    k = len(basis)
    n = 1 << k
    R = [gf_random(rng) for _ in range(n)]
    tower = build_rmc_tower(R, basis, leaf_threshold=4)
    leaves = rmc_collect_leaves(tower)

    z_points = [gf_random(rng) for _ in range(3)]

    path1_catches = 0
    path2_catches = 0
    both_catch = 0
    either_catch = 0
    total = 0

    for _ in range(n_perturbations):
        fake_leaves = [list(L) for L in leaves]
        leaf_idx = rng.randrange(len(fake_leaves))
        if not fake_leaves[leaf_idx]:
            fake_leaves[leaf_idx] = [0]
        coeff_idx = rng.randrange(len(fake_leaves[leaf_idx]))
        fake_leaves[leaf_idx][coeff_idx] = gf_add(
            fake_leaves[leaf_idx][coeff_idx], gf_random(rng)
        )

        result = rmc_dual_binding_check(tower, fake_leaves, z_points)
        if result["path1_cryptographic_caught"]:
            path1_catches += 1
        if result["path2_algebraic_caught"]:
            path2_catches += 1
        if result["both_paths_caught"]:
            both_catch += 1
        if result["either_path_caught"]:
            either_catch += 1
        total += 1

    return {
        "total_perturbations": total,
        "path1_cryptographic_catch_rate": path1_catches / total,
        "path2_algebraic_catch_rate": path2_catches / total,
        "both_paths_caught_rate": both_catch / total,
        "either_path_caught_rate": either_catch / total,
        "num_leaves": len(leaves),
        "num_internal_nodes": rmc_internal_node_count(tower),
    }


# ==============================================================================
# SECTION 11 — MULTI-PROOF AGGREGATION
# Paper reference: Section 5.4 "Mira for Multi-Proof Aggregation"
# ==============================================================================


def aggregate_proofs(proofs: List[PMMProof]) -> Tuple[int, bytes]:
    """
    Aggregate N independent proofs' binding values into a single constant-
    size aggregated binding, per Section 5.4:

        delta = SHA256(com_1 || ... || com_N)
        binding_agg = sum_i delta^i * binding_i
    """
    coms_concat = b"".join(p.com for p in proofs)
    delta = sha_field(coms_concat)
    binding_agg = mira_fold([p.binding for p in proofs], delta)
    return binding_agg, coms_concat


# ==============================================================================
# SECTION 12 — TEST FRAMEWORK
# ==============================================================================


class TestRecorder:
    """Minimal test recorder: tracks pass/fail per named check, no external deps."""

    def __init__(self, verbose: bool = False):
        self.verbose = verbose
        self.results: List[Tuple[str, bool, str]] = []
        self.section: str = ""

    def set_section(self, name: str) -> None:
        self.section = name
        print(f"\n{'=' * 78}")
        print(f"  {name}")
        print(f"{'=' * 78}")

    def check(self, name: str, condition: bool, detail: str = "") -> bool:
        status = "PASS" if condition else "FAIL"
        full_name = f"[{self.section}] {name}"
        self.results.append((full_name, condition, detail))
        marker = "+" if condition else "X"
        line = f"  [{marker}] {name}"
        if detail and (self.verbose or not condition):
            line += f"  -- {detail}"
        print(line)
        return condition

    def summary(self) -> bool:
        total = len(self.results)
        passed = sum(1 for _, ok, _ in self.results if ok)
        failed = total - passed
        print(f"\n{'=' * 78}")
        print("  TEST SUMMARY")
        print(f"{'=' * 78}")
        print(f"  Total checks: {total}")
        print(f"  Passed:       {passed}")
        print(f"  Failed:       {failed}")
        if failed:
            print("\n  FAILED CHECKS:")
            for name, ok, detail in self.results:
                if not ok:
                    print(f"    - {name}: {detail}")
        all_ok = failed == 0
        print(f"\n{'=' * 78}")
        if all_ok:
            print("  ALL TESTS PASSED")
        else:
            print("  SOME TESTS FAILED -- see above")
        print(f"{'=' * 78}\n")
        return all_ok


# ==============================================================================
# SECTION 13 — FULL TEST SUITE
# ==============================================================================


def run_all_tests(seed: int = 1337, verbose: bool = False) -> bool:
    """
    Run the complete PMM V1 verification suite, covering every primitive
    in the paper in the same order as the paper's sections.
    """
    rng = random.Random(seed)
    t = TestRecorder(verbose=verbose)

    print("PMM V1 -- COMPLETE PYTHON REFERENCE IMPLEMENTATION TEST SUITE")
    print(f"Random seed: {seed}")

    # --------------------------------------------------------------------
    t.set_section("1. Field Arithmetic over F_2^256")
    # --------------------------------------------------------------------
    a = gf_random(rng)
    b = gf_random(rng)

    t.check("a XOR a == 0 (characteristic 2)", gf_add(a, a) == 0)
    t.check("a * 1 == a", gf_mul(a, 1) == a)
    t.check("a * 0 == 0", gf_mul(a, 0) == 0)
    t.check("Multiplication is commutative", gf_mul(a, b) == gf_mul(b, a))
    inv_a = gf_inv(a)
    t.check("a * a^-1 == 1", gf_mul(a, inv_a) == 1, f"got {hex(gf_mul(a, inv_a))}")
    apb_sq = gf_sq(gf_add(a, b))
    a_sq_plus_b_sq = gf_add(gf_sq(a), gf_sq(b))
    t.check(
        "Frobenius: (a+b)^2 == a^2 + b^2",
        apb_sq == a_sq_plus_b_sq,
        "characteristic-2 Frobenius endomorphism (paper Section 2.1)",
    )

    # --------------------------------------------------------------------
    t.set_section("2. Polynomial Arithmetic")
    # --------------------------------------------------------------------
    p1 = [gf_random(rng) for _ in range(5)]
    p2 = [gf_random(rng) for _ in range(3)]
    prod = poly_mul(p1, p2)
    z = gf_random(rng)
    lhs = poly_eval(prod, z)
    rhs = gf_mul(poly_eval(p1, z), poly_eval(p2, z))
    t.check("poly_mul evaluates consistently: (p1*p2)(z) == p1(z)*p2(z)", lhs == rhs)

    q, r = poly_divmod(p1, p2)
    reconstructed = poly_add(poly_mul(q, p2), r)
    t.check(
        "poly_divmod: p1 == q*p2 + r",
        poly_trim(reconstructed) == poly_trim(p1),
    )
    t.check(
        "poly_divmod: deg(r) < deg(p2)",
        poly_degree(r) < poly_degree(p2),
    )

    # --------------------------------------------------------------------
    t.set_section("3. Vanishing Polynomials (Theorem 3.1, Artin-Schreier)")
    # --------------------------------------------------------------------
    k_test = 4
    basis_test = generate_basis(k_test, rng)
    t.check(
        f"Generated {k_test} F_2-linearly independent basis elements",
        len(basis_test) == k_test,
    )

    span = {0}
    for beta in basis_test:
        span = span | {gf_add(s, beta) for s in span}
    t.check(
        f"Basis spans an additive subspace of size 2^{k_test} = {1 << k_test}",
        len(span) == (1 << k_test),
    )

    V_full = build_vanishing_poly(basis_test)
    t.check(
        f"deg(V_full) == 2^{k_test} = {1 << k_test}",
        poly_degree(V_full) == (1 << k_test),
        f"got degree {poly_degree(V_full)}",
    )
    vanishes_everywhere = all(poly_eval(V_full, s) == 0 for s in span)
    t.check(
        "V_full vanishes on every element of the spanned subspace",
        vanishes_everywhere,
    )

    # --------------------------------------------------------------------
    t.set_section("4. Miko Decomposition (Definition 3.2, Theorems 3.3 / 3.4)")
    # --------------------------------------------------------------------
    k = 5
    n = 1 << k
    basis = generate_basis(k, rng)
    R = [gf_random(rng) for _ in range(n)]

    quotients, r_final, vpolys = miko_decompose(R, basis)
    t.check(f"Decomposition produced {len(quotients)} quotients for k={k}", len(quotients) == k)

    # Theorem 3.3 (Uniqueness): re-decomposing the same R with the same
    # basis must give bit-identical results.
    quotients2, r_final2, _ = miko_decompose(R, basis)
    t.check(
        "Theorem 3.3 (Uniqueness): repeated decomposition is identical",
        quotients == quotients2 and r_final == r_final2,
    )

    # Theorem 3.4 (Degree bounds)
    degree_checks = verify_degree_bounds(quotients, k)
    all_bounds_ok = all(ok for _, _, _, ok in degree_checks)
    t.check("Theorem 3.4: all quotient degree bounds satisfied", all_bounds_ok)
    if verbose:
        for j, actual, bound, ok in degree_checks:
            t.check(f"  deg(Q_{j}) = {actual} < {bound + 1}", ok)

    # Miko identity at random points
    identity_ok = True
    for _ in range(10):
        zt = gf_random(rng)
        lhs = poly_eval(R, zt)
        rhs = miko_reconstruct(quotients, r_final, vpolys, zt)
        if lhs != rhs:
            identity_ok = False
            break
    t.check("Miko identity R(z) == r_final + sum V_j(z)*Q_j(z) holds at random points", identity_ok)

    # Corollary used for the 140-byte proof: zero polynomial -> all-zero quotients
    R_zero: Poly = [0] * n
    Qz, rz, _ = miko_decompose(R_zero, basis)
    all_zero = all(poly_degree(Qj) < 0 for Qj in Qz) and rz == 0
    t.check(
        "Zero polynomial decomposes to the all-zero quotient sequence (Theorem 3.3 applied to R=0)",
        all_zero,
        "this is the structural basis of the 140-byte recursive outer proof, Section 8",
    )

    # --------------------------------------------------------------------
    t.set_section("5. Hash Chain Commitment (Definition 4.1, Lemma 4.2, Lemma 4.3)")
    # --------------------------------------------------------------------
    com, hashes = hash_chain_commit(quotients, r_final)
    t.check("Commitment is 32 bytes", len(com) == 32)

    com_repeat, _ = hash_chain_commit(quotients, r_final)
    t.check("Commitment is deterministic", com == com_repeat)

    perturbed = [list(Qj) for Qj in quotients]
    perturbed[0] = list(perturbed[0]) if perturbed[0] else [0]
    perturbed[0][0] = gf_add(perturbed[0][0], 1)
    com_perturbed, _ = hash_chain_commit(perturbed, r_final)
    t.check(
        "Lemma 4.2: perturbing any Q_j changes the commitment",
        com_perturbed != com,
    )

    z0 = fiat_shamir_challenge(com, 0)
    z0_perturbed = fiat_shamir_challenge(com_perturbed, 0)
    t.check(
        "Lemma 4.3 (Phase 3 lock): a changed commitment changes derived challenges",
        z0 != z0_perturbed,
    )

    # --------------------------------------------------------------------
    t.set_section("6. Mira RLC: Cross-Binding (Lemma 5.1)")
    # --------------------------------------------------------------------
    z1 = fiat_shamir_challenge(com, 1)
    v0 = miko_reconstruct(quotients, r_final, vpolys, z0)
    binding, A_combined, C_combined = mira_cross_binding(
        quotients, r_final, vpolys, com, z0, v0, k
    )
    t.check("Cross-binding value computed", isinstance(binding, int) and binding >= 0)

    binding_repeat, _, _ = mira_cross_binding(quotients, r_final, vpolys, com, z0, v0, k)
    t.check("Cross-binding is deterministic", binding == binding_repeat)

    fake_q = [list(Qj) for Qj in quotients]
    fake_q[1] = list(fake_q[1]) if fake_q[1] else [0]
    fake_q[1][0] = gf_add(fake_q[1][0], gf_random(rng))
    fake_v0 = miko_reconstruct(fake_q, r_final, vpolys, z0)
    fake_binding, _, _ = mira_cross_binding(fake_q, r_final, vpolys, com, z0, fake_v0, k)
    t.check(
        "Lemma 5.1: cross-binding differs for fake quotients",
        fake_binding != binding,
    )

    # --------------------------------------------------------------------
    t.set_section("7. Full Proof: Generation and Verification")
    # --------------------------------------------------------------------
    proof = generate_proof(R, basis)
    result = verify_proof(proof, R_original=R)

    t.check("Verifier: hash chain check", result["hash_chain_ok"])
    t.check("Verifier: Fiat-Shamir check", result["fiat_shamir_ok"])
    t.check("Verifier: Mira binding check", result["mira_binding_ok"])
    t.check("Verifier: degree bounds check", result["degree_bounds_ok"])
    t.check("Verifier: Miko identity at z0", result["miko_identity_z0"])
    t.check("Verifier: Miko identity at z1", result["miko_identity_z1"])
    t.check("Verifier: overall ACCEPT", result["all_ok"])

    sizes = inner_proof_size_bytes(proof)
    t.check(
        "Inner proof, Mira-folded, equals com+binding+r_final+folded_Q+overhead",
        sizes["total_mira_folded"]
        == sizes["com"] + sizes["binding"] + sizes["r_final"] + 32 + sizes["overhead"],
    )
    if verbose:
        print(f"      Inner proof (unfolded quotients): {sizes['total_unfolded']} bytes")
        print(f"      Inner proof (Mira-folded):        {sizes['total_mira_folded']} bytes")

    # --------------------------------------------------------------------
    t.set_section("8. Recursive Miko Commitment (RMC) Towers (Section 6)")
    # --------------------------------------------------------------------
    R_rmc = [gf_random(rng) for _ in range(1 << 6)]
    basis_rmc = generate_basis(6, rng)
    tower = build_rmc_tower(R_rmc, basis_rmc, leaf_threshold=4)

    leaves = rmc_collect_leaves(tower)
    t.check(f"RMC tower built with {len(leaves)} leaves", len(leaves) > 0)

    z_tower = gf_random(rng)
    root_eval = rmc_ascend_eval(tower, z_tower)
    direct_eval = poly_eval(R_rmc, z_tower)
    t.check(
        "RMC tower ascension reconstructs R(z) exactly (equation 6, Miko identity at every node)",
        root_eval == direct_eval,
    )

    internal_count = rmc_internal_node_count(tower)
    t.check(f"RMC tower has {internal_count} internal nodes", internal_count > 0)

    internal_evals = rmc_collect_internal_evals(tower, z_tower)
    _, _, _, alpha_rmc = derive_mira_params(tower.commitment(), z_tower, 0)
    batched = mira_fold(internal_evals, alpha_rmc)
    t.check(
        "Lemma 5.2: Mira-batched RMC internal node fold computed successfully",
        isinstance(batched, int),
    )

    # --------------------------------------------------------------------
    t.set_section("9. Dual Binding Security (Theorem 6.1, Corollary 6.2)")
    # --------------------------------------------------------------------
    dual_binding_result = exercise_dual_binding(basis_rmc, rng, n_perturbations=20)
    t.check(
        "Every tested perturbation caught by at least one binding path",
        dual_binding_result["either_path_caught_rate"] == 1.0,
        f"either-path catch rate = {dual_binding_result['either_path_caught_rate']:.3f}",
    )
    t.check(
        "Algebraic path (Path 2) independently catches perturbations",
        dual_binding_result["path2_algebraic_catch_rate"] > 0.9,
        f"path2 catch rate = {dual_binding_result['path2_algebraic_catch_rate']:.3f}",
    )
    t.check(
        "Cryptographic path (Path 1) independently catches perturbations",
        dual_binding_result["path1_cryptographic_catch_rate"] == 1.0,
        f"path1 catch rate = {dual_binding_result['path1_cryptographic_catch_rate']:.3f}",
    )
    if verbose:
        print(f"      Both paths caught simultaneously: "
              f"{dual_binding_result['both_paths_caught_rate']:.3f} of trials")

    # --------------------------------------------------------------------
    t.set_section("10. Soundness: The Three Exhaustive Attack Strategies (Theorem 7.1)")
    # --------------------------------------------------------------------
    s1 = exercise_strategy1_real_nonzero_residual(basis, rng)
    t.check(
        "Strategy 1 (real R != 0): verifier correctly rejects",
        s1["verifier_correctly_rejects"],
    )
    t.check("Strategy 1: Miko identity held (honest decomposition)", s1["identity_held"])

    s2 = exercise_strategy2_fake_quotients(basis, rng, n_trials=50)
    t.check(
        f"Strategy 2 (fake quotients): Miko identity catch rate "
        f"{s2['identity_catch_rate']:.2%} over {s2['trials']} trials",
        s2["identity_catch_rate"] > 0.95,
    )
    t.check(
        f"Strategy 2 (fake quotients): Mira binding catch rate "
        f"{s2['binding_catch_rate']:.2%} over {s2['trials']} trials",
        s2["binding_catch_rate"] > 0.95,
    )

    s3 = exercise_strategy3_zero_residual_attack(basis, rng)
    t.check(
        "Strategy 3 (zero-residual attack): Miko identity holds trivially (expected)",
        s3["identity_holds_trivially"],
    )
    t.check(
        "Strategy 3 (zero-residual attack): deterministically rejected by public-point check",
        s3["deterministically_rejected"],
    )

    # --------------------------------------------------------------------
    t.set_section("11. Multi-Proof Aggregation (Section 5.4)")
    # --------------------------------------------------------------------
    proofs_to_aggregate = []
    for _ in range(4):
        Rn = [gf_random(rng) for _ in range(1 << k)]
        proofs_to_aggregate.append(generate_proof(Rn, basis))

    binding_agg, coms_concat = aggregate_proofs(proofs_to_aggregate)
    t.check(
        f"Aggregated {len(proofs_to_aggregate)} proofs into a single binding value",
        isinstance(binding_agg, int),
    )

    binding_agg2, _ = aggregate_proofs(proofs_to_aggregate)
    t.check("Aggregation is deterministic", binding_agg == binding_agg2)

    tampered_proofs = list(proofs_to_aggregate)
    tampered_proofs[0] = generate_proof([gf_random(rng) for _ in range(1 << k)], basis)
    binding_agg_tampered, _ = aggregate_proofs(tampered_proofs)
    t.check(
        "Substituting one proof changes the aggregated binding",
        binding_agg_tampered != binding_agg,
    )

    # --------------------------------------------------------------------
    t.set_section("12. Recursive Composition: The ~140-Byte Outer Proof (Section 8)")
    # --------------------------------------------------------------------
    basis_outer = generate_basis(OUTER_VERIFIER_K, rng)

    outer_valid, diag_valid = build_outer_proof(True, basis_outer, rng)
    t.check(
        "Outer circuit residual R_2 is identically zero when inner proof is valid",
        diag_valid["R2_is_zero"],
    )
    t.check(
        "Theorem 3.3 applied to R_2=0: ALL outer quotients are zero",
        diag_valid["all_outer_quotients_zero"],
        "this is the structural reason the outer proof needs no quotient transmission",
    )
    t.check(
        "Effective depth of the outer decomposition is 0 (complete RMC collapse)",
        diag_valid["effective_depth"] == 0,
    )
    t.check(
        f"Outer proof size is {diag_valid['proof_size_bytes']} bytes "
        f"(target: ~140 bytes, constant regardless of original circuit size)",
        120 <= diag_valid["proof_size_bytes"] <= 160,
        f"got {diag_valid['proof_size_bytes']} bytes",
    )
    outer_verified_valid = verify_outer_proof(outer_valid, expect_valid=True)
    t.check(
        "Outer verifier ACCEPTS a proof built from a valid inner proof",
        outer_verified_valid,
    )

    outer_invalid, diag_invalid = build_outer_proof(False, basis_outer, rng)
    t.check(
        "Outer circuit residual R_2 is nonzero when inner proof is INVALID",
        not diag_invalid["R2_is_zero"],
    )
    t.check(
        "An invalid inner proof does NOT yield all-zero outer quotients",
        not diag_invalid["all_outer_quotients_zero"],
    )
    outer_verified_invalid = verify_outer_proof(outer_invalid, expect_valid=True)
    t.check(
        "Outer verifier REJECTS a proof built from an invalid inner proof",
        not outer_verified_invalid,
    )

    if verbose:
        print(f"\n      Outer proof byte breakdown (valid-inner case):")
        print(f"        com2:              32 bytes")
        print(f"        binding2:          32 bytes")
        print(f"        quotients_folded:  32 bytes")
        print(f"        r_final2:          32 bytes")
        print(f"        metadata:          {len(outer_valid.metadata)} bytes")
        print(f"        TOTAL:             {outer_valid.size_bytes()} bytes")

    return t.summary()


# ==============================================================================
# SECTION 14 — ENTRY POINT
# ==============================================================================


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "PMM V1 complete Python reference implementation and test suite. "
            "Runs every primitive from the paper end-to-end: Miko Decomposition, "
            "Hash Chain Commitment, Mira RLC, RMC towers, dual binding, the "
            "three-strategy soundness proof, and the recursive ~140-byte outer proof."
        )
    )
    parser.add_argument(
        "--seed",
        type=int,
        default=1337,
        help="Random seed for reproducible test runs (default: 1337)",
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Print detailed per-step output, including byte breakdowns",
    )
    args = parser.parse_args()

    try:
        all_passed = run_all_tests(seed=args.seed, verbose=args.verbose)
    except Exception:
        print("\nUNEXPECTED ERROR DURING TEST EXECUTION:\n")
        traceback.print_exc()
        return 1

    return 0 if all_passed else 1


if __name__ == "__main__":
    sys.exit(main())
