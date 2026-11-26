<div align="center">

# `erdos-18` — $h(n!) = O\!\left((\log n)^3 (\log\log n)^2\right)$

[![Verify Lean 4 & Python](https://github.com/vinnor/erdos-18/actions/workflows/lean.yml/badge.svg)](https://github.com/vinnor/erdos-18/actions/workflows/lean.yml)
![Lean 4](https://img.shields.io/badge/Lean-v4.36.0-4B32C3?style=flat-square)
![Mathlib4](https://img.shields.io/badge/Mathlib4-v4.36.0-2E7D32?style=flat-square)
![Sorry Count](https://img.shields.io/badge/sorry-0-brightgreen?style=flat-square)
![Axioms](https://img.shields.io/badge/axioms-standard%20only-blue?style=flat-square)

*caw. crows collect shiny objects. this one collected ~six powers of $\log n$.*

**Unconditional, elementary, end-to-end Lean 4 + Mathlib4 proofs of**
$$h(n!) = O\!\left((\log n)^3 \big(\log\log(n+16)\big)^2\right) \qquad\text{and}\qquad h(n!) = O\big((\log n)^4\big)$$
**for [Erdős Problem #18](https://www.erdosproblems.com/18), improving the November 2026 frontier $O((\log n)^9)$ by ~6 powers of $\log n$ — sitting just one power of $\log n$ (plus $(\log\log n)^2$) above the information-theoretic floor $\Omega((\log n)^2)$.**

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
| This repo — Milestone 1 | $O\big((\log n)^5\big)$ | `Erdos18.erdos18_alpha5` (Lean 4, 0 `sorry`) |
| This repo — Corollary | $O\big((\log n)^4\big)$ | `Erdos18.erdos18_alpha4` (Lean 4, 0 `sorry`) |
| **This repo — Headline (Nov 26, 2026)** | **$O\!\left((\log n)^3 (\log\log(n+16))^2\right)$** | **`Erdos18.erdos18_alpha3_loglog2` (Lean 4 + Mathlib4, 0 `sorry`, CI-verified)** |
| Counting lower bound | $\Omega\big((\log n)^2\big)$ | Information-theoretic floor ($\frac{\log(n!)}{\log \tau(n!)}$) |

---

## Theorem Statements (`erdos18_lean/Verify.lean`)

All three bounds are locked against definition shadowing in [`erdos18_lean/Verify.lean`](erdos18_lean/Verify.lean) using explicit `_root_` references:

```lean
import Erdos18

theorem check_alpha5 :
    ∃ C : _root_.Real, ∀ n : _root_.Nat, n ≥ 2 → ∀ t : _root_.Nat, 1 ≤ t → t ≤ _root_.Nat.factorial n →
      ∃ S : _root_.Finset _root_.Nat, (∀ d ∈ S, d ∣ _root_.Nat.factorial n ∧ 0 < d) ∧
        S.sum id = t ∧ (S.card : _root_.Real) ≤ C * (_root_.Real.log n) ^ 5 :=
  Erdos18.erdos18_alpha5

theorem check_alpha4 :
    ∃ C : _root_.Real, ∀ n : _root_.Nat, n ≥ 2 → ∀ t : _root_.Nat, 1 ≤ t → t ≤ _root_.Nat.factorial n →
      ∃ S : _root_.Finset _root_.Nat, (∀ d ∈ S, d ∣ _root_.Nat.factorial n ∧ 0 < d) ∧
        S.sum id = t ∧ (S.card : _root_.Real) ≤ C * (_root_.Real.log n) ^ 4 :=
  Erdos18.erdos18_alpha4

theorem check_alpha3_loglog2 :
    ∃ C : _root_.Real, ∀ n : _root_.Nat, n ≥ 2 → ∀ t : _root_.Nat, 1 ≤ t → t ≤ _root_.Nat.factorial n →
      ∃ S : _root_.Finset _root_.Nat, (∀ d ∈ S, d ∣ _root_.Nat.factorial n ∧ 0 < d) ∧
        S.sum id = t ∧
        (S.card : _root_.Real) ≤
          C * (_root_.Real.log n) ^ 3 * (_root_.Real.log (_root_.Real.log ((n : _root_.Real) + 16))) ^ 2 :=
  Erdos18.erdos18_alpha3_loglog2

#print axioms check_alpha5
#print axioms check_alpha4
#print axioms check_alpha3_loglog2
```

Verified axiom output:

```text
'check_alpha5' depends on axioms: [propext, Classical.choice, Quot.sound]
'check_alpha4' depends on axioms: [propext, Classical.choice, Quot.sound]
'check_alpha3_loglog2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Zero `sorry`. Zero `admit`. Zero `native_decide`. Zero custom axioms. Zero analytic number theory (only Erdős's 1932 central binomial coefficient bounds).

---

## Where Every Factor Comes From

Full self-contained mathematical exposition is in [`PROOF.md`](PROOF.md).

| Component | Exact Cost | Contribution | Key Mechanism |
| --- | --- | --- | --- |
| Convex entropy–variance bound $f_4$ | $4q(1-q) \ge (\ln 2)\, f_4(h_2(q))$ | Shaves $\log n \to \log\log n$ | Sharp $f_4(u) = \frac{u}{\ln(4/u)}$ replaces Cauchy-Schwarz $g^2$ |
| Full-pool $s$-prime subsets + weighted dyadic shifts | $\Sigma^*(k) = O\big(\log k \cdot (\log\log k)^2\big)$ | $+1$ (+ $(\log\log)^2$) | 4-regime log-harmonic bound over $P_{\lfloor (k+1)/4 \rfloor}$ |
| Deficit contraction & mod-$2^k$ covering | $2R^*(k) = O\big((\log k)^2 (\log\log k)^2\big)$ | $+1$ (from $\ln(2k)$) | Odd prime-tag automorphism $H(X+q_r Y) = H(q_r^{-1}X+Y)$ + pigeonhole |
| $2$-adic carry recursion ($B \to \lceil \sqrt{B} \rceil$) | $\frac{16}{7} C^*_R F^*(B) + B_0$ | **$+0$** | Telescoping geometric sum $\sum (3/4)^{2j} = 16/7$ |
| Mixed-radix Stage 1 + self-similar tail Stage 2 | $O(\log n)$ levels | $+1$ | Canonical $\frac{\log(n!)}{n}$ factor; $U_{\mathrm{top}} \mid \binom{\lfloor E/4 \rfloor}{\lfloor E_{\mathrm{next}}/4 \rfloor}$ |
| Global divisor distinctness | $1$ | **$+0$** | Prime tags $q_r$ + disjoint $v_2$ & mixed-radix intervals |
| **Total** | **$O\!\left((\log n)^3 (\log\log(n+16))^2\right)$** | **$\alpha = 3$ (+ $(\log\log)^2$)** | **~6 powers below $\alpha = 9$** |

---

## Repository Layout (7,841 Lines of Lean 4 + Mathlib4)

| Path | Lines | Contents |
| --- | ---: | --- |
| [`PROOF.md`](PROOF.md) | — | Complete self-contained human-readable proof |
| [`erdos18_lean/Erdos18/Chebyshev.lean`](erdos18_lean/Erdos18/Chebyshev.lean) | 391 | Erdős 1932 primorial, Chebyshev, quantitative Bertrand, $U_{\mathrm{top}} \mid \binom{a}{b}$ |
| [`erdos18_lean/Erdos18/Entropy.lean`](erdos18_lean/Erdos18/Entropy.lean) | 1,292 | Base Shannon entropy & bitwise chain-rule gain |
| [`erdos18_lean/Erdos18/Covering.lean`](erdos18_lean/Erdos18/Covering.lean) | 1,295 | Base $O((\log k)^4)$ covering, 2-sided dyadic shift sets, pigeonhole sumset cover |
| [`erdos18_lean/Erdos18/MainTheorem.lean`](erdos18_lean/Erdos18/MainTheorem.lean) | 1,424 | `erdos18_alpha5` + reusable carry/Stage 1–2 machinery |
| [`erdos18_lean/Erdos18/Alpha3Entropy.lean`](erdos18_lean/Erdos18/Alpha3Entropy.lean) | 537 | Convex `f4nat` / `psiNat` sharp entropy–variance & bitwise gain (Lemmas 1'–2') |
| [`erdos18_lean/Erdos18/Alpha3Covering.lean`](erdos18_lean/Erdos18/Alpha3Covering.lean) | 2,048 | Full-pool $s$-prime subsets, 4-regime `SigmaStar_le`, weighted covering `mod_two_pow_covering_alpha3` |
| [`erdos18_lean/Erdos18/Alpha3Main.lean`](erdos18_lean/Erdos18/Alpha3Main.lean) | 822 | Telescoping carry & tail recursion, `erdos18_alpha3_loglog2`, `erdos18_alpha4` |
| [`erdos18_lean/Verify.lean`](erdos18_lean/Verify.lean) | 25 | `_root_`-locked statement check & `#print axioms` for all 3 bounds |
| [`lean/Erdos18Alpha5.lean`](lean/Erdos18Alpha5.lean) | 498 | Standalone zero-dependency pure Lean 4 combinatorial core |
| [`scripts/verify_practical.py`](scripts/verify_practical.py) | 152 | Exact DP for small $h(n!)$ & strict certificate verifier |
| [`scripts/test_alpha3_lemmas.py`](scripts/test_alpha3_lemmas.py) | — | Numerical & end-to-end verification suite up to $n = 100$ ($100! \approx 2^{525}$) |
| [`scripts/stress_alpha3.py`](scripts/stress_alpha3.py) | — | High-precision 80-digit & adversarial stress tests (up to $k = 2^{1000}$) |

---

## Verify It Yourself

Don't trust a crow. Trust the Lean 4 kernel.

### Lean 4 + Mathlib4 (All 3 Theorems)

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

### Python Verification & Adversarial Stress Suite

```bash
python3 scripts/verify_practical.py --self-test
python3 scripts/test_alpha5_lemmas.py
python3 scripts/test_alpha3_lemmas.py
python3 scripts/stress_alpha3.py
```

---

## Transparency & Credits

- **Author:** [vinnor](https://github.com/vinnor)
- **Methodology:** AI-assisted mathematical research and Lean 4 formalization, independently compiled and axiom-checked on GitHub Actions CI. The Lean 4 kernel is the sole arbiter of correctness here.
- **License:** [MIT](LICENSE)

---

<div align="center">

<sub>🐦 Started at $\alpha = 9$. Landed at $\alpha = 3 \cdot (\log\log)^2$. One more power of $\log n$ left to the floor.</sub>

</div>
