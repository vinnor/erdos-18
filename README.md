<div align="center">

# `erdos-18` — $h(n!) = O\big((\log n)^5\big)$

[![Verify Lean 4 & Python](https://github.com/vinnor/erdos-18/actions/workflows/lean.yml/badge.svg)](https://github.com/vinnor/erdos-18/actions/workflows/lean.yml)
![Lean 4](https://img.shields.io/badge/Lean-v4.36.0-4B32C3?style=flat-square)
![Mathlib4](https://img.shields.io/badge/Mathlib4-v4.36.0-2E7D32?style=flat-square)
![Sorry Count](https://img.shields.io/badge/sorry-0-brightgreen?style=flat-square)
![Axioms](https://img.shields.io/badge/axioms-standard%20only-blue?style=flat-square)

*caw. crows collect shiny objects. this one collected four powers of $\log n$.*

**An unconditional, elementary, end-to-end Lean 4 + Mathlib4 proof of**
$$h(n!) = O\big((\log n)^5\big)$$
**for [Erdős Problem #18](https://www.erdosproblems.com/18), improving the November 2026 frontier $O((\log n)^9)$ by four full powers of $\log n$.**

</div>

---

## 🐦 The Short Version

A positive integer $m$ is **practical** if every $1 \le t \le m$ can be written as a sum of **distinct** positive divisors of $m$. Let $h(m)$ be the smallest number of summands that always suffices.

For $m = n!$:

| Milestone | Bound on $h(n!)$ | Notes |
| --- | --- | --- |
| Erdős (1974) | $< n$ | Elementary induction |
| Nov 16, 2026 | $< n^{o(1)}$ | Lean 4 (radix + $L^2$ flattening) |
| Nov 20, 2026 | $O\big((\log n)^9\big)$ | Lean 4 (`hexagon:2611.00748v1`) |
| **This repository (Nov 26, 2026)** | **$O\big((\log n)^5\big)$** | **Full Lean 4 + Mathlib4, 0 `sorry`, CI-verified** |
| Counting lower bound | $\Omega\big((\log n)^2\big)$ | Information-theoretic floor ($\frac{\log(n!)}{\log \tau(n!)}$) |

---

## Theorem Statement (`Erdos18.erdos18_alpha5`)

Locked against definition shadowing in [`erdos18_lean/Verify.lean`](erdos18_lean/Verify.lean) using explicit `_root_` references:

```lean
import Erdos18

theorem check_statement :
    ∃ C : _root_.Real, ∀ n : _root_.Nat, n ≥ 2 → ∀ t : _root_.Nat, 1 ≤ t → t ≤ _root_.Nat.factorial n →
      ∃ S : _root_.Finset _root_.Nat, (∀ d ∈ S, d ∣ _root_.Nat.factorial n ∧ 0 < d) ∧
        S.sum id = t ∧ (S.card : _root_.Real) ≤ C * (_root_.Real.log n) ^ 5 :=
  Erdos18.erdos18_alpha5

#print axioms check_statement
```

Verified axiom output:

```text
'check_statement' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Zero `sorry`. Zero `admit`. Zero `native_decide`. Zero custom axioms. Zero analytic number theory (only Erdős's 1932 central binomial coefficient bounds).

---

## Where Every Power of $\log n$ Comes From

Full self-contained mathematical exposition is in [`PROOF.md`](PROOF.md).

| Component | Exact Cost | Contribution to $\alpha$ | Key Mechanism |
| --- | --- | --- | --- |
| Prefix entropy density $g$ | $g(m) \ge \frac{c_1}{\log_2(m+2)}$ | $-1$ (squared below) | $Z_m = \frac{1}{2}\delta_0 + \frac{1}{2}\mathrm{Unif}(\mathrm{Div}(P_{\lfloor m/2 \rfloor}))$ |
| Bitwise XOR gain + Cauchy-Schwarz | $\sum \gamma_i^2 \ge g^2 \cdot 2^t$ | $+2$ | Chain rule + elementary $4q(1-q) \ge 2(\ln 2)^2 h_2(q)^2$ |
| 2-sided dyadic shift scales | $L = O(\log k)$ | $+1$ | $S_t$ covers every bit window with $\lvert S_t \rvert \le 4\cdot 2^t$ |
| Deficit contraction & covering | $2R(k) = O(g^{-2}(\log k)^2)$ | $+1$ | Automorphism $H(X + q_r Y) = H(q_r^{-1} X + Y)$ + pigeonhole |
| $2$-adic carry recursion ($B \to \lceil \sqrt{B} \rceil$) | $\frac{16}{15} \cdot 2R(B)$ | **$+0$** | Telescoping geometric sum $\sum 2^{-4j} = 16/15$ |
| Mixed-radix + self-similar tail $M(E)$ | $O(\log n)$ levels | $+1$ | $U_{\mathrm{top}} \mid \binom{\lfloor E/4 \rfloor}{\lfloor E_{\mathrm{next}}/4 \rfloor} < 2^{\lfloor E_{\mathrm{next}}/2 \rfloor}$ |
| Global divisor distinctness | $1$ | **$+0$** | Odd prime tags $q_r$ + disjoint $v_2$ & radix intervals |
| **Total** | **$O\big((\log n)^5\big)$** | **$\alpha = 5$** | **4 powers below $\alpha = 9$** |

---

## Repository Layout

| Path | Lines | Contents |
| --- | ---: | --- |
| [`PROOF.md`](PROOF.md) | — | Complete human-readable proof & exponent ledger |
| [`erdos18_lean/Erdos18/Chebyshev.lean`](erdos18_lean/Erdos18/Chebyshev.lean) | 391 | Erdős 1932 primorial, Chebyshev, quantitative Bertrand, $U_{\mathrm{top}} \mid \binom{a}{b}$ |
| [`erdos18_lean/Erdos18/Entropy.lean`](erdos18_lean/Erdos18/Entropy.lean) | 1,292 | Finite Shannon entropy, XOR bias lemma, bitwise chain-rule gain |
| [`erdos18_lean/Erdos18/Covering.lean`](erdos18_lean/Erdos18/Covering.lean) | 1,295 | 2-sided dyadic shifts, prime-tag automorphism invariance, mod-$2^k$ covering |
| [`erdos18_lean/Erdos18/MainTheorem.lean`](erdos18_lean/Erdos18/MainTheorem.lean) | 1,424 | $B \to \lceil \sqrt{B} \rceil$ carry recursion, Stage 1 mixed-radix, Stage 2 tail, `erdos18_alpha5` |
| [`erdos18_lean/Verify.lean`](erdos18_lean/Verify.lean) | 9 | `_root_`-qualified top-level statement check & `#print axioms` |
| [`lean/Erdos18Alpha5.lean`](lean/Erdos18Alpha5.lean) | 498 | Zero-dependency pure Lean 4 core proof of all 12 combinatorial lemmas |
| [`scripts/verify_practical.py`](scripts/verify_practical.py) | 152 | Exact DP for small $h(n!)$ & strict certificate verifier |
| [`scripts/test_alpha5_lemmas.py`](scripts/test_alpha5_lemmas.py) | — | Numerical & adversarial stress suite (up to $n = 80$, $80! \approx 2^{395}$) |

---

## Verify It Yourself

Don't trust a crow. Trust the Lean 4 kernel.

### Lean 4 + Mathlib4 (Full Proof)

```bash
cd erdos18_lean
lake exe cache get
lake build
lake env lean Verify.lean
```

### Standalone Zero-Dependency Core

```bash
cd erdos18_lean
lake env lean ../lean/Erdos18Alpha5.lean
```

### Python Empirical & Adversarial Suite

```bash
python3 scripts/verify_practical.py --self-test
python3 scripts/test_alpha5_lemmas.py
```

---

## Transparency & Credits

- **Author:** [vinnor](https://github.com/vinnor)
- **Methodology:** AI-assisted mathematical exploration and Lean 4 formalization, independently compiled and axiom-checked on GitHub Actions CI. The Lean 4 kernel is the sole arbiter of correctness here.
- **License:** [MIT](LICENSE)

---

<div align="center">

<sub>🐦 A crow found an $\alpha = 5$ branch and is currently pecking at $\alpha = 4$. Pull requests and tighter exponents welcome.</sub>

</div>
