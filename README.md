# PMM V1 — Reference Implementation & Verification Suite

This repository contains a single-file Python reference implementation of
**PMM V1** — *Miko Decomposition, Hash Chain Commitment, and Mira RLC: Three
Deterministic Primitives for Post-Quantum Polynomial Proofs over Binary
Fields* — together with an automated test suite that exercises every
primitive described in the paper, end to end, from proving through
verification.

If you are reviewing the paper and want to check that the constructions
described in it actually work as claimed, this is the fastest way to do
that. No setup, no dependencies, one command.

---

## What this is

`pmm_v1.py` is **one file**. It contains:

1. Binary field arithmetic over $\mathbb{F}_{2^{256}}$
2. Polynomial arithmetic over that field
3. Vanishing polynomial construction (Artin–Schreier iteration)
4. Miko Decomposition (the core factorization primitive)
5. Hash Chain Commitment (the Merkle-free binding scheme)
6. Mira RLC (cross-binding, RMC tower batching, multi-proof aggregation)
7. Recursive Miko Commitment (RMC) towers
8. The dual binding security architecture
9. The three exhaustive soundness attack strategies from the paper
10. Native recursive composition, producing the constant **~140-byte**
    outer proof

Every one of these is implemented *and* tested in the same file. Running it
mechanically checks every theorem, lemma, and construction claimed in the
paper against its own specification, on your machine, right now.

This is **not** a performance benchmark. The paper's hardware-accelerated
Rust implementation is what production proving speed claims are based on.
This file makes no speed claims — its only job is to demonstrate, in plain,
readable Python, that the mathematics is internally consistent and that
every defense mechanism described in the paper actually catches the attack
it claims to catch.

---

## Requirements

- Python 3.8 or later
- **No third-party packages.** Every import used is part of the Python
  standard library (`hashlib`, `struct`, `random`, `argparse`, `sys`,
  `traceback`, `dataclasses`, `typing`).

You do not need to `pip install` anything. You do not need a virtual
environment, though using one is fine if you prefer.

---

## How to run it

Clone the repository and run the file directly:

```bash
git clone https://github.com/atlasw231-maker/PMM-PAPER
cd PMM-PAPER
python3 pmm_v1.py
```

That's it. This runs the complete test suite with default settings and
prints a section-by-section report, ending in a summary.

### Command-line options

```bash
python3 pmm_v1.py --help
```

```
usage: pmm_v1.py [-h] [--seed SEED] [--verbose]

options:
  -h, --help   show this help message and exit
  --seed SEED  Random seed for reproducible test runs (default: 1337)
  --verbose    Print detailed per-step output, including byte breakdowns
```

**`--seed N`** — re-run with a different random seed. The test suite uses
randomly generated witnesses, bases, and perturbations throughout; running
with several different seeds is a good way to convince yourself the result
isn't an artifact of one particular set of random values.

```bash
python3 pmm_v1.py --seed 42
python3 pmm_v1.py --seed 99999
```

**`--verbose`** — print additional detail, including the exact byte-by-byte
breakdown of the outer proof and the per-level degree bound checks.

```bash
python3 pmm_v1.py --verbose
```

### Expected output

A successful run ends with:

```
==============================================================================
  TEST SUMMARY
==============================================================================
  Total checks: 57
  Passed:       57
  Failed:       0

==============================================================================
  ALL TESTS PASSED
==============================================================================
```

The process exit code is `0` on success and `1` if any check fails, so this
also works cleanly in CI:

```bash
python3 pmm_v1.py && echo "verification passed"
```

---

## What gets tested, and where to find it in the paper

The test suite runs in twelve sections, in the same order as the paper.
Each section header in the output names the paper's corresponding theorem,
lemma, or section number, so you can read the code and the paper side by
side.

| # | Section | Paper reference |
|---|---|---|
| 1 | Field arithmetic over $\mathbb{F}_{2^{256}}$ | Section 2.1 |
| 2 | Polynomial arithmetic | — |
| 3 | Vanishing polynomials | Theorem 3.1 |
| 4 | Miko Decomposition | Definition 3.2, Theorem 3.3, Theorem 3.4 |
| 5 | Hash Chain Commitment | Definition 4.1, Lemma 4.2, Lemma 4.3 |
| 6 | Mira RLC cross-binding | Lemma 5.1 |
| 7 | Full proof generation and verification | Section 7.3 |
| 8 | RMC towers | Section 6 |
| 9 | Dual binding security | Theorem 6.1, Corollary 6.2 |
| 10 | The three exhaustive soundness strategies | Theorem 7.1 |
| 11 | Multi-proof aggregation | Section 5.4 |
| 12 | Recursive composition — the 140-byte proof | Section 8 |

### A few specific checks worth knowing about

**Theorem 3.3 (Uniqueness).** The suite decomposes the same polynomial
twice and confirms the results are bit-identical, then separately confirms
that decomposing the all-zero polynomial yields the all-zero quotient
sequence — this second fact is the structural reason the recursive outer
proof can stay constant size (see Section 12 below).

**Theorem 6.1 (Dual Binding).** The suite builds a real RMC tower, then
perturbs a single coefficient in a random leaf twenty times, checking each
time whether the cryptographic path (commitment changes), the algebraic
path (the Miko identity differs at random challenge points), or both,
catch the perturbation. You should see a 100% catch rate on the
cryptographic path and a near-100% catch rate on the algebraic path
(bounded by the Schwartz–Zippel probability, which is astronomically close
to 1 at this field size) — and every single perturbation caught by at
least one of the two independent paths.

**Theorem 7.1 (the three attack strategies).** Each of the three
strategies described in the paper is exercised directly:

- *Strategy 1*: an honest decomposition of a genuinely nonzero residual,
  checking that the verifier correctly rejects it.
- *Strategy 2*: fifty trials of substituting a fake quotient coefficient
  and checking that both the Miko identity check and the Mira
  cross-binding check independently catch the substitution.
- *Strategy 3*: the "zero-residual attack," where a prover claims an
  all-zero quotient sequence to make the algebraic identity hold
  trivially — and confirming this is rejected *deterministically* (not
  probabilistically) by the public-point consistency check, exactly as
  the paper describes.

**Section 8 (the ~140-byte proof).** This is the most important section
to look at if you're verifying the paper's headline size claim. The suite
builds an outer recursive proof for both a *valid* and an *invalid* inner
proof, and checks:

1. When the inner proof is valid, the outer circuit's residual is
   identically zero.
2. By Theorem 3.3 applied to the zero polynomial, every outer quotient is
   forced to be zero — this is verified directly, not assumed.
3. The resulting outer proof, built from `com2`, `binding2`, the
   Mira-folded (zero) quotient confirmation, `r_final2`, and a small
   metadata footer, is exactly **140 bytes**.
4. The honest outer verifier accepts this proof.
5. When the inner proof is *invalid*, the residual is nonzero, the
   quotients are *not* all zero, and the same verifier correctly
   *rejects* the resulting (still 140-byte-shaped, but invalid) proof.

Run with `--verbose` to see the exact byte breakdown:

```
Outer proof byte breakdown (valid-inner case):
  com2:              32 bytes
  binding2:          32 bytes
  quotients_folded:  32 bytes
  r_final2:          32 bytes
  metadata:          12 bytes
  TOTAL:             140 bytes
```

---

## Reading the code

The file is organized into fourteen numbered sections, each with a comment
block at the top explaining what it implements and which part of the paper
it corresponds to. If you want to read the implementation rather than just
run the tests, read top to bottom — the sections build on each other in the
same order the paper introduces the corresponding ideas:

```
SECTION 1  — Field arithmetic
SECTION 2  — Polynomial arithmetic
SECTION 3  — Vanishing polynomials (Artin–Schreier)
SECTION 4  — Miko Decomposition
SECTION 5  — Hash Chain Commitment
SECTION 6  — Mira RLC
SECTION 7  — Recursive Miko Commitment (RMC) towers
SECTION 8  — Full proof: generation and verification
SECTION 9  — Recursive composition / the 140-byte outer proof
SECTION 10 — Dual binding security exercises
SECTION 11 — Multi-proof aggregation
SECTION 12 — Test framework
SECTION 13 — The full test suite (run_all_tests)
SECTION 14 — Entry point
```

Every function has a docstring referencing the specific definition, lemma,
or theorem it implements.

---

## What this does *not* claim

- **No performance claims.** This is pure Python with a schoolbook
  carryless-multiplication field implementation. It is not fast, and it is
  not meant to be. The paper's performance numbers come from a separate,
  hardware-accelerated Rust implementation.
- **Not a substitute for cryptographic peer review.** This suite confirms
  that the constructions are *internally consistent* — that the algebra
  works, that the claimed defenses catch the attacks they claim to catch,
  and that the proof size claim is real. It is not a substitute for formal
  cryptanalysis by independent reviewers, which any new construction
  should receive before being relied upon in production.
- **Reference implementation, not production code.** This file is written
  for clarity and direct correspondence with the paper, not for
  constant-time execution or resistance to side-channel attacks.

---

## Questions or issues

If a check fails on your machine, please open an issue with:

- The exact command you ran
- The full output
- Your Python version (`python3 --version`)

A failing check on a freshly cloned copy of this repository, with no
modifications, would itself be a significant and important finding — please
report it.

---

## License

See the repository's `LICENSE` file. The contents of `pmm_v1.py` are
provided as a reference implementation for review and verification
purposes.
