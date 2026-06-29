# Miko Decomposition, Hash Chain Commitment, and Mira RLC  
## Three Deterministic Primitives for Post-Quantum Polynomial Proofs over Binary Fields

**Miko Angelo De La Paz**  
`delapazmikoangelo@gmail.com`

June 2026

---

## Abstract

We present three deterministic primitives for transparent, post‑quantum zero‑knowledge proofs over $\mathbb{F}_{2^{256}}$.

1. **Miko Decomposition** uniquely factorises any polynomial $R(X)$ of degree $< n = 2^k$ into $k$ quotient polynomials with exponentially decreasing degrees; its correctness is checked via the Miko identity using only two challenge points, achieving $(n/2^{256})^2$ soundness.
2. **Hash Chain Commitment** replaces Merkle trees with sequential SHA‑256 hashing while deliberately leaving the residual polynomial un‑committed; binding comes algebraically from the Miko identity and Mira cross‑binding, and a Phase 3 commitment lock enables native recursion with no adaptive‑attack window.
3. **Mira** (Multi‑Instance Recursive Aggregation) uses random linear combinations to compress evaluations, cross‑bind public and challenge points, and verify recursive Miko towers in $O(1)$ time per tower.

The resulting dual‑binding architecture (algebraic via Schwartz‑Zippel, cryptographic via SHA‑256) ensures that even if SHA‑256 is broken, algebraic security survives. Together, the primitives yield PMM, a post‑quantum ZK proof system with $\sim 140$‑byte constant‑size on‑chain proofs, no trusted setup, and native recursive composition.

---

## 1. Introduction

Zero‑knowledge proof systems require three fundamental operations: verifying that a committed polynomial has bounded degree, binding the prover to that polynomial before challenges are revealed, and compressing verification checks to minimise proof size. Existing approaches use probabilistic queries with tree‑based commitments, or algebraic constructions over prime fields requiring trusted setup.

This paper introduces three primitives that perform these operations **deterministically over binary fields, without trusted setup, and with hash‑independent algebraic security**.

### 1.1 Our Contribution

- **Miko Decomposition (Section 3):** Deterministic polynomial factorisation with exponentially decreasing degree bounds. Replaces probabilistic degree testing (FRI) with algebraic verification via the Miko identity. Requires 2 challenge points vs. FRI’s 30–50. Soundness: $(n/2^{256})^2$.
- **Hash Chain Commitment (Section 4):** Sequential SHA‑256 binding where the residual polynomial is not committed – binding is algebraic via Miko identity and Mira cross‑binding. The Phase 3 commitment lock (Lemma 4.3) prevents adaptive attacks in recursive composition. Hash‑independent security: if SHA‑256 breaks, algebraic binding survives.
- **Mira (Multi‑Instance Recursive Aggregation) (Section 5):** RLC meta‑protocol for evaluation compression and cross‑binding. Compresses $s$ challenge evaluations per quotient into one field element. Compresses $m$ RMC internal node checks into $O(1)$ verification. Enables constant‑size proof aggregation across multiple proofs.

### 1.2 First Application: PMM

These primitives compose into **PMM** (Polynomial Miko‑Mira), a transparent post‑quantum ZK proof system demonstrating native recursion (Section 8). PMM serves as the reference application, not the sole use case. The primitives are general – any ZK system over characteristic 2 can adopt them independently.

### 1.3 The Dual Binding Security Architecture

|   |   |
|---|---|
| **First Layer: Algebraic – Miko Identity Check** | Schwartz‑Zippel over $\mathbb{F}_{2^{256}}$<br>Soundness: $(n/2^{256})^2$ |
| $\downarrow$ |   |
| **Second Layer: Cryptographic – SHA‑256 Hash Chain** | Preimage resistance<br>Binding: $2^{-256}$ |
| $\downarrow$ |   |
| **Adversary Must Break BOTH** | Combined probability: $\min((n/2^{256})^2, 2^{-256})$<br>*Algebraic layer survives hash failure* |

### 1.4 Comparison to Prior Approaches

| Property | FRI (STARKs) | Merkle Trees | Miko Decomposition | Hash Chain + RMC |
|---|---|---|---|---|
| Degree testing | Probabilistic, 30–50 queries | N/A | Deterministic, 2 challenges | N/A |
| Commitment structure | Requires Merkle trees | Generic hash tree | N/A | Sequential chain + recursive Miko |
| Algebraic meaning | None (proximity only) | None (opaque hashes) | Miko identity at every level | Miko identity at every RMC node |
| Hash‑independent? | No | No | Yes | Yes (dual binding) |
| Selective opening | Required (query positions) | Core purpose | Not needed | Not needed |
| Verification cost | $O(\text{queries}\cdot\log n)$ | $O(\log n)$ per path | $O(n)$ total | $O(1)$ per tower |
| Proof size | 50–200 KB | $O(\log n)$ per path | $\sim 400$ B (inner) | $\sim 140$ B (outer) |

---

## 2. Preliminaries

### 2.1 The Binary Field $\mathbb{F}_{2^{256}}$

Elements are 256‑bit polynomials over $\mathbb{F}_2$ modulo the irreducible pentanomial:
$$p(X) = X^{256} + X^{10} + X^5 + X^2 + 1$$

- Addition is XOR (single cycle).
- Multiplication is carryless with Barrett reduction, hardware‑accelerated via PCLMULQDQ (x86‑64) and PMULL (ARM64).
- Squaring is the Frobenius endomorphism: $(a+b)^2 = a^2 + b^2$ (free bit‑spreading).
- Inversion uses Itoh‑Tsujii with $\sim 15$-step addition chain.

**No discrete logarithm:** The additive group has exponent $2$ ($a+a=0$ for all $a$). The multiplicative group $\mathbb{F}_{2^{256}}^\times$ is cyclic of order $2^{256}-1$ but is never used for cryptographic hardness.

### 2.2 The Schwartz‑Zippel Lemma

**Lemma (Schwartz‑Zippel).** For any non‑zero polynomial $f(X)$ of degree $d$ over field $\mathbb{F}$ and uniformly random $z \in \mathbb{F}$:
$$\Pr[f(z) = 0] \leq \frac{d}{|\mathbb{F}|}$$
This bound is information‑theoretic – no quantum algorithm can increase it.

For $s$ independent challenges chosen after the polynomial is fixed via Fiat‑Shamir commitment:
$$\Pr[\forall i: f(z_i) = 0 \mid f \neq 0] \leq \left(\frac{d}{|\mathbb{F}|}\right)^s$$

#### Parameter‑Dependent Soundness Error for $s=2$

| Circuit Size $n$ | Soundness $(n/2^{256})^2$ |
|---|---|
| $2^{10} = 1,024$ | $2^{-492}$ |
| $2^{13} = 8,192$ | $2^{-486}$ |
| $2^{15} = 32,768$ | $2^{-482}$ |
| $2^{17} = 131,072$ | $2^{-478}$ |
| $2^{20} = 1,048,576$ | $2^{-472}$ |

### 2.3 Additive Subspaces and Linearized Polynomials

An additive subspace of size $2^k$ over $\mathbb{F}_2$:
$$D = \mathrm{span}_{\mathbb{F}_2}\{\beta_0,\ldots,\beta_{k-1}\}$$

A linearized polynomial has the form:
$$L(X) = \sum_{i=0}^k c_i X^{2^i}$$

Frobenius linearity (characteristic 2 only):
$$L(a+b) = L(a) + L(b)$$
because $(a+b)^{2^i} = a^{2^i} + b^{2^i}$.

---

## 3. Miko Decomposition

### 3.1 Vanishing Polynomials over Binary Fields

**Theorem (Linearized Vanishing Polynomial).**  
Let $S = \mathrm{span}_{\mathbb{F}_2}\{\beta_0,\ldots,\beta_{k-1}\}$ be an additive subspace of $\mathbb{F}_{2^{256}}$ of size $2^k$. The vanishing polynomial
$$V_S(X) = \prod_{s \in S} (X + s)$$
is a linearized polynomial with exactly $k+1$ non‑zero terms. It is constructed via the Artin‑Schreier iteration:
$$V_0(X) = X$$
$$V_{i+1}(X) = V_i(X)^2 + \lambda_i V_i(X) \quad \text{where } \lambda_i = V_i(\beta_i)$$
After $k$ iterations, $V_k(X) = V_S(X)$. Evaluation at any point costs $O(k) = O(\log n)$ field operations.

### 3.2 The Miko Decomposition Algorithm

**Definition (Miko Decomposition).**  
Given $R(X) \in \mathbb{F}_{2^{256}}[X]$ of degree $< n = 2^k$ and an $\mathbb{F}_2$ basis $\{\beta_0,\ldots,\beta_{k-1}\}$, the Miko decomposition produces a sequence $(Q_0,\ldots,Q_{k-1}, r_{\text{final}})$ satisfying the Miko identities:
$$R_0(X) = R(X)$$
$$R_j(X) = R_{j+1}(X) + V_j(X) \cdot Q_j(X) \quad (j = 0,\ldots,k-1)$$
$$R_k = r_{\text{final}} \text{ (constant)}$$
where $V_j(X)$ is the vanishing polynomial of $\mathrm{span}_{\mathbb{F}_2}\{\beta_{j+1},\ldots,\beta_{k-1}\}$.

**Theorem (Uniqueness).**  
For any $R(X)$ of degree $< n$ and any $\mathbb{F}_2$-linearly independent basis, there exists exactly one sequence $(Q_0,\ldots,Q_{k-1}, r_{\text{final}})$ satisfying the Miko identities.

**Theorem (Exponential Degree Decrease).**
$$\deg(Q_j) < \frac{n}{2^{j+1}} = 2^{k-j-1}$$
$$\deg(R_j) < \frac{n}{2^j} = 2^{k-j}$$

#### Degree Bounds by Level

| Level $j$ | $n$   | $\deg(R_j)$ | $\deg(Q_j)$ |
|-----------|-------|-------------|-------------|
| 0         | $2^k$ | $< 2^k$     | $< 2^{k-1}$ |
| 1         | $2^k$ | $< 2^{k-1}$ | $< 2^{k-2}$ |
| 2         | $2^k$ | $< 2^{k-2}$ | $< 2^{k-3}$ |
| $\vdots$  | $\vdots$ | $\vdots$  | $\vdots$    |
| $k-1$     | $2^k$ | $< 2$       | $< 1$       |
| $k$       | $2^k$ | $< 1$       | —           |

### 3.3 Miko Identity as the Algebraic First Defence

**Lemma (Miko Identity Check Soundness).**  
If the prover uses fake quotients $Q_j' \neq Q_j$, the verifier’s Miko identity check at $s$ independent challenge points fails with probability at least
$$1 - \left(\frac{n}{2^{256}}\right)^s.$$

---

## 4. Hash Chain Commitment

### 4.1 Construction

**Definition (Hash Chain Commitment).**  
Given quotients $Q_0,\ldots,Q_{k-1}$ and remainder $r_{\text{final}}$:
$$h_k = \text{SHA‑256}(\text{"final"} \mid r_{\text{final\_bytes}})$$
$$h_j = \text{SHA‑256}(h_{j+1} \mid \text{"level\_"} \mid j \mid Q_{j\_\text{bytes}}) \quad (j = k-1,\ldots,0)$$
$$\mathrm{com} = h_0 \text{ (32 bytes)}$$

**Lemma (Hash Chain Binding).**  
To change any $Q_j$ after publishing $\mathrm{com}$, an adversary must find a SHA‑256 preimage. Success probability $\leq 2^{-256}$.

### 4.2 The Residual Polynomial Is Intentionally Not Committed

$R(X)$ is excluded from the hash chain. Binding between the committed $Q_j$ and $R$ derives algebraically from the Miko identity check (Lemma 3.3) and Mira cross‑binding (Lemma 5.1).

### 4.3 The Phase 3 Commitment Lock

**Lemma (Phase 3 Commitment Lock).**  
Once the prover publishes $\mathrm{com}$ in Phase 3 of the proving protocol, no PPT adversary can modify any $Q_j$ without changing $\mathrm{com}$, and consequently the Fiat‑Shamir challenges $z_i = \text{SHA‑256}(\mathrm{com} \mid i)$ and Mira parameters derived from $\mathrm{com}$.

---

## 5. Mira: Multi‑Instance Recursive Aggregation

### 5.1 Cross‑Binding: Linking Public and Challenge Points

The cross‑binding equation prevents the prover from using different $Q_j$ values at public points vs. challenge points. For $t = k+1$ public points $\omega_0,\ldots,\omega_{t-1}$:

$$\mathrm{binding} = A_{\text{combined}} + \gamma_1 \cdot C_{\text{combined}} + \gamma_2 \cdot r_{\text{final}}$$

where

$$A_{\text{combined}} = \sum_{i=0}^{t-1} \beta^{\,i} \cdot \sum_{j=0}^{k-1} V_j(\omega_i) \cdot Q_j(\omega_i)$$
$$C_{\text{combined}} = \sum_{j=0}^{k-1} V_j(z) \cdot Q_j(z)$$
$$\gamma_1 = \text{SHA‑256}(\mathrm{com} \mid z \mid v \mid 0),\quad
\gamma_2 = \text{SHA‑256}(\mathrm{com} \mid z \mid v \mid 1)$$

**Lemma (Mira Cross‑Binding Security).**  
If the prover uses fake $Q_j' \neq Q_j$ that differ from the committed quotients at either public points or the challenge point, the probability that the cross‑binding equation holds is $\leq 1/|\mathbb{F}| = 2^{-256}$.

### 5.2 Zero‑Residual Attack Defence

**Attack:** Prover claims all $Q_j' = 0$, $r_{\text{final}}' = 0$. Miko identity holds trivially ($0=0$). Cross‑binding becomes $0 = 0$.

**Defence – deterministic rejection:** The hash chain opening at public points $\omega_i$ reveals $Q_j'(\omega_i) = 0$ for all $j,i$. This forces $A_{\text{combined}} = 0$. The verifier independently computes the expected A‑matrix evaluations from the circuit’s public inputs $w_{\text{pub}}$:

$$A_{\text{expected}} = \sum_{i=0}^{t-1} \beta^{\,i} \cdot (A[i] \cdot w_{\text{pub}})$$

For any real circuit with non‑zero public inputs, $A_{\text{expected}} \neq 0$. The verifier checks $A_{\text{combined}} = A_{\text{expected}}$. Since $0 \neq A_{\text{expected}}$, deterministic rejection occurs.

### 5.3 Mira RLC for RMC Tower Batch Verification

For recursive Miko commitment towers, Mira compresses $m$ internal node identity checks into a single equation per challenge point:

$$Q_{\text{batched}} = \sum_{j=0}^{m-1} \alpha^{\,j} \cdot Q_{\text{node}_j}(z)$$

where $\alpha = \text{SHA‑256}(\mathrm{com} \mid \text{"rmc\_batch"})$.

**Lemma (Mira RMC Batch Verification Soundness).**  
If any of the $m$ internal RMC nodes has an incorrect evaluation, the batched check fails with probability at least
$$1 - \frac{m}{|\mathbb{F}|}.$$

---

## 6. RMC Towers: Recursive Miko Commitment

### 6.1 The Shallow Quotient Problem

For a circuit with $n = 5{,}000$ constraints ($k = 13$), shallow Miko levels produce quotients with degree up to 2,500. Transmitting all coefficients requires $\sim 80$ KB.

### 6.2 Recursive Miko Decomposition

RMC towers recursively apply Miko decomposition until all pieces have degree $< 76$ (the base polynomial threshold). The resulting binary tree encodes the Miko decomposition structure.

Miko identity at every internal node:
$$Q_{\text{parent}}(z) = Q_{\text{left}}(z) + V(z) \cdot Q_{\text{right}}(z)$$

### 6.3 Dual Binding Theorem

**Theorem (RMC Tower Dual Binding).**  
Let $B = (B_1,\ldots,B_m)$ be the base polynomials of an RMC tower with root commitment $c$, each of degree $< d$. An adversary providing fake base polynomials $B' \neq B$ such that
1. $\mathrm{com}(B') = \mathrm{com}(B)$ (same root commitment)
2. the Miko identity holds at $s$ independent random challenge points

succeeds with probability at most
$$\min\!\left(2^{-256}, \left(\frac{d}{2^{256}}\right)^s\right).$$

### 6.4 Corollary: Hash‑Independent Security

Even if SHA‑256 is completely broken (instant collisions found), the algebraic layer (Miko identity check) remains secure. This distinguishes RMC towers from Merkle trees, whose security collapses entirely if the hash function breaks.

---

## 7. Complete Security Analysis

### 7.1 The Prover’s Only Degree of Freedom

The prover selects a witness $w$. From $w$, everything follows deterministically:
1. $R(X) = \sum_{i=0}^{n-1} r_i X^i$ where $r_i = (A[i] \cdot w) \otimes (B[i] \cdot w) \oplus (C[i] \cdot w)$
2. Miko decomposition: $R \rightarrow (Q_0,\ldots,Q_{k-1}, r_{\text{final}})$ unique (Theorem 3.3)
3. Hash chain: $\mathrm{com} = \text{SHA‑256‑chain}(Q_j, r_{\text{final}})$
4. Fiat‑Shamir challenges: $z_i = \text{SHA‑256}(\mathrm{com} \mid i)$, $\beta, \gamma_1, \gamma_2, \delta = \text{SHA‑256}(\mathrm{com} \mid \ldots)$
5. Evaluations: $Q_j(z_i)$, $R(z_i)$ – deterministic from the committed $Q_j$

### 7.2 Complete Soundness

**Theorem (Complete Soundness).**  
Let $C$ be an unsatisfiable circuit with $n \leq 2^{17}$ constraints over $\mathbb{F}_{2^{256}}$. For any PPT adversary $A$ making $q$ random oracle queries:
$$\Pr[\text{Verifier}^H(C, A^H(C)) = \text{ACCEPT}] \leq \frac{t}{2^{256}} + \frac{m}{2^{256}} + O\!\left(\frac{q^2}{2^{256}}\right)$$
where $t = k+1$ and $m$ is the number of Mira‑batched RMC nodes. For practical parameters this yields $\sim 2^{-250}$ security, exceeding the NIST 128‑bit requirement by 122 bits.

### 7.3 Three Attack Strategies

#### Strategy 1: Real $R \neq 0$ from Invalid Witness
Prover selects $w$ such that $R \neq 0$. Verifier checks $R(z_0) = R(z_1) = 0$. By Schwartz‑Zippel:
$$\Pr[R(z_0)=0 \wedge R(z_1)=0] \leq \left(\frac{n}{2^{256}}\right)^2$$

#### Strategy 2: Fake $Q_j' \neq Q_j$
Prover substitutes fake quotients in the hash chain. Miko identity check catches this with probability $\geq 1 - (n/2^{256})^2$. Even if bypassed, Mira cross‑binding catches the forgery with probability $\geq 1 - 2^{-256}$.

#### Strategy 3: Zero Residual Attack
Prover sets all $Q_j' = 0$, $r_{\text{final}}' = 0$. Miko identity holds trivially. Public‑point consistency check catches this deterministically: $A_{\text{combined}} = 0 \neq A_{\text{expected}}$.

### 7.4 Witness Grinding Bound
Prover can try $T$ different witnesses. Each trial succeeds with probability $\leq (n/2^{256})^2$. By the union bound:
$$\Pr[\text{any success}] \leq T \cdot \left(\frac{n}{2^{256}}\right)^2$$
$T$ is bounded by the number of ROM queries $q$, contributing the $O(q^2/2^{256})$ term.

---

## 8. First Application: PMM with Recursive Composition

The three primitives compose into PMM, demonstrating native recursion: PMM proves PMM verification over the same field with no additional cryptography.

### Recursive Proof Architecture

| Inner Proof $\pi_1$ | Outer Proof $\pi_2$ | On‑Chain Verifier |
|---|---|---|
| Full verification of original circuit | Verifier circuit ($\sim 5,000$ constraints) | One |
| Variable size ($\sim 400$–500 bytes) | Constant $\sim 140$ bytes | $\sim 140$ bytes |
| Off‑chain | On‑chain | Post‑quantum |

### Outer Proof Size Breakdown

| Component | Size |
|---|---|
| $\mathrm{com}_2$ | 32 bytes |
| $\mathrm{binding}_2$ | 32 bytes |
| `all_quotients_folded` (Mira over all 13 levels) | 32 bytes |
| $\mathrm{remainder}_2$ | 32 bytes |
| Counts/overhead | $\sim 12$ bytes |
| **Total** | $\sim 140$ bytes (constant) |

### Recursive Soundness Preservation

**Theorem.** If the primitives are sound for the verifier circuit, then PMM with recursive composition is sound for any circuit. Each recursion layer adds $s=2$ independent challenge points with fresh Fiat‑Shamir randomness. After $\ell$ layers:
$$\epsilon_\ell \leq \left(\frac{n}{2^{256}}\right)^{2^{\ell+1}}$$

*Proof sketch.* The outer proof $\pi_2$ verifies $\pi_1$’s hash chain, Miko identity, and Mira cross‑binding. If $\pi_1$ is invalid, the verifier rejects, the outer circuit’s residual $R_2 \neq 0$, and $\pi_2$ cannot be generated. The challenge sets for different layers are independently distributed in the Random Oracle Model, hence soundness errors multiply.

---

## 9. Post‑Quantum Security

**Theorem.** All three primitives are secure against quantum adversaries. Shor’s algorithm provides no advantage. Grover’s algorithm provides at most a quadratic speedup on SHA‑256 preimage search.

*Proof (exhaustive component analysis):*

| Component | Operation | Quantum Vulnerability |
|---|---|---|
| Field arithmetic | XOR, carryless multiply over $\mathbb{F}_{2^{256}}$ | None – No DLOG in char 2 |
| Miko decomposition | Polynomial division | None – Division, not exponentiation |
| Hash chain | SHA‑256($h_{j+1} \mid Q_j$) | Grover only: $2^{256} \to 2^{128}$ |
| Schwartz‑Zippel | $\Pr[f(z)=0] \leq d/2^{256}$ | None – Information‑theoretic |
| Fiat‑Shamir | $z_i = \text{SHA‑256}(\mathrm{com} \mid i)$ | QROM‑secure via Unruh (2015) |
| Mira RLC | $\sum \alpha^j \cdot v_j$ | None – Linear combination |
| RMC towers | SHA‑256 + Miko identity | None beyond hash chain |

---

## 10. Performance Characteristics

### Prover Complexity

| Phase | Complexity |
|---|---|
| Residual Computation | $O(n)$ |
| Miko Decomposition | $O(n \log^2 n)$ |
| RMC Tower Construction | $O(n \log n)$ |
| Hash Chain Commitment | $O(n \log n)$ |
| Evaluation at Challenge Points | $O(s \cdot n)$ |
| **Total** | $O(n \cdot (s + \log n)) \approx O(n \log n)$ |

### Verifier Complexity

| Step | Complexity |
|---|---|
| Proof Parsing | $O(k)$ |
| Hash Chain Reconstruction | $O(n)$ |
| Challenge Derivation | $O(s)$ |
| Miko Identity Verification | $O(s \cdot (k^2 + n))$ |
| RMC Tower Traversal | $O(k \log k)$ |
| **Total** | $O(s \cdot n + s \cdot k^2)$ |

### Proof Size

| Proof | Size |
|---|---|
| Inner Proof $\pi_1$ | $\sim 400$–$500$ bytes (variable by circuit) |
| Outer Proof $\pi_2$ | $\sim 140$ bytes (constant) |

The outer proof size is constant, independent of original circuit size.

---

## 11. Conclusion

We have introduced three post‑quantum transparent primitives over binary fields: **Miko Decomposition** (deterministic low‑degree testing via a 2‑challenge Miko identity), **Hash Chain Commitment** (Merkle‑free binding with algebraic residual binding and a Phase‑3 lock for native recursion), and **Mira** (RLC‑based aggregation for cross‑binding, batch tower verification, and constant‑size proofs). The dual‑layer security – algebraic Schwartz‑Zippel plus SHA‑256 – guarantees hash‑independent soundness. When composed into PMM, the primitives deliver $\sim 140$‑byte on‑chain proofs with native recursion, no trusted setup, and post‑quantum security in the random oracle model.

---

## References

1. Schwartz, J. T. & Zippel, R. *Probabilistic polynomial testing and applications to matrix identities.* J. ACM, 27(4), 701–717, 1980.
2. Fiat, A. & Shamir, A. *How to prove yourself: Practical solutions to identification and signature problems.* CRYPTO 1987.
3. Unruh, D. *Revocable quantum timed‑release encryption.* J. Cryptology, 29(4), 955–1009, 2015.
4. Ben‑Sasson, E., Bentov, I., Horesh, Y., & Riabzev, M. *Scalable, transparent, and post‑quantum secure computational integrity.* EUROCRYPT 2018.
5. Groth, J. *On the size of pairing‑based non‑interactive arguments.* EUROCRYPT 2016.
6. Gabizon, A., Williamson, Z. J., & Ciobotaru, O. *PLONK: Permutations over Lagrange‑bases for Oecumenical Noninteractive arguments of Knowledge.* ePrint 2019/953.
7. Lidl, R. & Niederreiter, H. *Finite Fields* (2nd ed.). Cambridge University Press, 1997.
8. NIST SP 800‑38D. *Recommendation for Block Cipher Modes of Operation: GCM and GMAC.*
