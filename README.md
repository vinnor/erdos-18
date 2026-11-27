<div align="center">

# `erdos-18` — $h(n!) = O\!\left((\log n)^3 \log\log n\right)$

[![Verify Lean 4 & Python](https://github.com/vinnor/erdos-18/actions/workflows/lean.yml/badge.svg)](https://github.com/vinnor/erdos-18/actions/workflows/lean.yml)
![Lean 4](https://img.shields.io/badge/Lean-v4.36.0-4B32C3?style=flat-square)
![Mathlib4](https://img.shields.io/badge/Mathlib4-v4.36.0-2E7D32?style=flat-square)
![Sorry Count](https://img.shields.io/badge/sorry-0-brightgreen?style=flat-square)
![Axioms](https://img.shields.io/badge/axioms-standard%20only-blue?style=flat-square)

*caw. crows collect shiny objects. this one collected ~6 powers of $\log n$ and threw away 2-adic carries.*

**Unconditional, elementary, carry-free Lean 4 + Mathlib4 proof of**
$$h(n!) = O\!\left((\log n)^3 \log\log(n+16)\right)$$
**for [Erdős Problem #18](https://www.erdosproblems.com/18), improving the November 2026 frontier $O((\log n)^9)$ by nearly six powers of $\log n$ — sitting just $\log n \cdot \log\log n$ above the information-theoretic floor $\Omega((\log n)^2)$ and settling all three parts (a), (b), and (c) of Erdős #18 in one theorem.**

</div>

---

## 🐦‍⬛ The Short Version

A positive integer $m$ is **practical** if every $1 \le t \le m$ can be written as a sum of **distinct** positive divisors of $m$. Let $h(m)$ be the smallest number of summands that always suffices.

For $m = n!$:

| Milestone | Bound on $h(n!)$ | Notes |
| --- | --- | --- |
| Erdős (1974) | $< n$ | Elementary induction |
| Tenenbaum–Yokota / Yokota (1990/1995) | $O\big(n / (\log n)^{1/2 - \varepsilon}\big)$ | Decreasing greedy |
| Hughes (Sep 2026, `arXiv:2609.10902`) | $(2\log 2 + o(1))\, n / \log n$ | Reciprocal divisor gaps |
| `conjectures.io` (Sep 2026) | $< n^{o(1)}$ | Lean 4 (radix + $L^2$ flattening) |
| Howe–Huffman–Kohlmeyer–Kruer (Nov 20, 2026) | $O\big((\log n)^9\big)$ | Lean 4 (`hexagon:2611.00748v1`) |
| This repo — Milestone 1 | $O\big((\log n)^5\big)$ | `Erdos18.erdos18_alpha5` (Lean 4, 0 `sorry`) |
| This repo — Milestone 2 | $O\big((\log n)^4\big)$ | `Erdos18.erdos18_alpha4` (Lean 4, 0 `sorry`) |
| This repo — Milestone 3 | $O\!\left((\log n)^3 (\log\log(n+16))^2\right)$ | `Erdos18.erdos18_alpha3_loglog2` (Lean 4, 0 `sorry`) |
| **This repo — Headline (Nov 27, 2026)** | **$O\!\left((\log n)^3 \log\log(n+16)\right)$** | **`Erdos18.erdos18_alpha3_loglog1` (Lean 4 + Mathlib4, 0 `sorry`, CI-verified)** |
| Counting lower bound | $\Omega\big((\log n)^2\big)$ | Information-theoretic floor ($\frac{\log(n!)}{\log \tau(n!)}$) |

Since $n!$ is practical and $\log\log(n!) = \log n + O(\log\log n)$, `erdos18_alpha3_loglog1` immediately implies all three questions of Erdős Problem #18:
- **18(a):** $h(m) < (\log\log m)^{O(1)}$ for infinitely many practical $m$ (namely $m = n!$, with exponent $4$),
- **18(b):** $h(n!) < n^{o(1)}$,
- **18(c):** $h(n!) < (\log n)^{O(1)}$ (specifically $O((\log n)^3 \log\log(n+16))$).

---

## Theorem Statements (`erdos18_lean/Verify.lean`)

All four bounds are locked against definition shadowing in [`erdos18_lean/Verify.lean`](erdos18_lean/Verify.lean) using explicit `_root_` references:

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

theorem check_alpha3_loglog1 :
    ∃ C : _root_.Real, ∀ n : _root_.Nat, n ≥ 2 → ∀ t : _root_.Nat, 1 ≤ t → t ≤ _root_.Nat.factorial n →
      ∃ S : _root_.Finset _root_.Nat, (∀ d ∈ S, d ∣ _root_.Nat.factorial n ∧ 0 < d) ∧
        S.sum id = t ∧
        (S.card : _root_.Real) ≤
          C * (_root_.Real.log n) ^ 3 * _root_.Real.log (_root_.Real.log ((n : _root_.Real) + 16)) :=
  Erdos18.erdos18_alpha3_loglog1

#print axioms check_alpha5
#print axioms check_alpha4
#print axioms check_alpha3_loglog2
#print axioms check_alpha3_loglog1
```

Verified axiom output:

```text
'check_alpha5' depends on axioms: [propext, Classical.choice, Quot.sound]
'check_alpha4' depends on axioms: [propext, Classical.choice, Quot.sound]
'check_alpha3_loglog2' depends on axioms: [propext, Classical.choice, Quot.sound]
'check_alpha3_loglog1' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Zero `sorry`. Zero `admit`. Zero `native_decide`. Zero custom axioms. Zero analytic number theory, zero Dirichlet characters, zero Pólya–Vinogradov — only Erdős's 1932 central binomial coefficient bounds and `Finset` pigeonhole.

---

## Where Every Factor Comes From

Full self-contained mathematical exposition is in [`PROOF.md`](PROOF.md) and [`paper/erdos18.tex`](paper/erdos18.tex).

| Component | Exact Cost | Contribution | Key Mechanism |
| --- | --- | --- | --- |
| Pointwise KL contraction & $\mathbb{F}_q$ dilation | Linear in $H_{\mathrm{nat}}(V)$ ($c_1 = \frac{1}{484}$) | **Kills `f4` $\log\log n$** | Leaves $\mathbb{Z}/2^k\mathbb{Z}$ for carry-free $\prod_{q \in Q'} \mathbb{F}_q$ |
| 2-factor smooth pigeonhole dilator | $\mathbb{P}(c_1 c_2 \equiv x \pmod q) \ge \frac{1/40}{q-1}$ | **$+0$** | Elementary `Finset` pigeonhole on $0.28m$-smooth $[1, 0.56m]$ (zero character sums) |
| Greedy CRT coordinate matching | $\sum_{r=1}^{N/2} \frac{1}{r\ln(N/r)} = \ln\ln N + O(1)$ | $+1$ (+ $\log\log n$) | Injective $r$-prime subsets across 16-subinterval Bertrand prime band |
| Contraction tail & mod-$M'$ covering | $2R(m) = O\big((\log m)^2 \log\log m\big)$ | $+1$ (from $\ln(2m)$) | Disjoint tag primes $Q_{\mathrm{tag}}$ + pigeonhole sumset cover |
| Exact digit quotient tail | $O(\log m)$ binary terms | **$+0$** | Greedy $M' \le \lfloor r/(2m^5)\rfloor$; mod-$M'$ cover sum $< m^5 M' \implies$ direct binary quotient |
| Mixed-radix Stage 1 + 11-prime Stage 2 | $O(\log n)$ levels | $+1$ | Canonical $\frac{\log(n!)}{m}$ factor + $m \to m/2$ recursion |
| **Total** | **$O\!\left((\log n)^3 \log\log(n+16)\right)$** | **$\alpha = 3 \cdot \log\log$** | **~6 powers + one $\log\log n$ below $\alpha = 9$** |

---

## Repository Layout (13,586 Lines of Lean 4 + Mathlib4)

| Path | Lines | Contents |
| --- | ---: | --- |
| [`PROOF.md`](PROOF.md) | — | Complete self-contained human-readable proof |
| [`paper/erdos18.tex`](paper/erdos18.tex) | — | Publication-ready AMS LaTeX manuscript |
| [`erdos18_lean/Erdos18/PrimeFieldEntropy.lean`](erdos18_lean/Erdos18/PrimeFieldEntropy.lean) | 1,097 | Pointwise KL contraction ($c_1 = 1/484$) & universal $\mathbb{F}_q$ dilation entropy gain |
| [`erdos18_lean/Erdos18/PrimeFieldDilation.lean`](erdos18_lean/Erdos18/PrimeFieldDilation.lean) | 417 | Elementary 2-factor smooth pigeonhole dilator (`smoothSet`, $\ge \frac{1/40}{q-1}$, zero character sums) |
| [`erdos18_lean/Erdos18/PrimeFieldCovering.lean`](erdos18_lean/Erdos18/PrimeFieldCovering.lean) | 3,155 | Carry-free CRT chain rule, 16-subinterval prime band, adaptive dilation contraction & mod-$M'$ covering |
| [`erdos18_lean/Erdos18/PrimeFieldMain.lean`](erdos18_lean/Erdos18/PrimeFieldMain.lean) | 1,063 | 11-prime strip Stage 2 ($m \to m/2$), Stage 1 mixed-radix, **`erdos18_alpha3_loglog1`** |
| [`erdos18_lean/Erdos18/Alpha3Entropy.lean`](erdos18_lean/Erdos18/Alpha3Entropy.lean) | 537 | Convex `f4nat` sharp entropy–variance & bitwise gain (Milestone 3) |
| [`erdos18_lean/Erdos18/Alpha3Covering.lean`](erdos18_lean/Erdos18/Alpha3Covering.lean) | 2,048 | Full-pool $s$-prime subsets & weighted dyadic covering (Milestone 3) |
| [`erdos18_lean/Erdos18/Alpha3Main.lean`](erdos18_lean/Erdos18/Alpha3Main.lean) | 822 | `erdos18_alpha3_loglog2` & `erdos18_alpha4` (Milestones 2–3) |
| [`erdos18_lean/Erdos18/Chebyshev.lean`](erdos18_lean/Erdos18/Chebyshev.lean) | 391 | Erdős 1932 primorial, Chebyshev, quantitative Bertrand, $U_{\mathrm{top}} \mid \binom{a}{b}$ |
| [`erdos18_lean/Erdos18/Entropy.lean`](erdos18_lean/Erdos18/Entropy.lean) | 1,292 | Base Shannon entropy & bitwise chain-rule gain |
| [`erdos18_lean/Erdos18/Covering.lean`](erdos18_lean/Erdos18/Covering.lean) | 1,295 | Base $O((\log k)^4)$ covering |
| [`erdos18_lean/Erdos18/MainTheorem.lean`](erdos18_lean/Erdos18/MainTheorem.lean) | 1,424 | `erdos18_alpha5` + reusable mixed-radix Stage 1 machinery |
| [`erdos18_lean/Verify.lean`](erdos18_lean/Verify.lean) | 34 | `_root_`-locked statement check & `#print axioms` for all 4 bounds |
| [`lean/Erdos18Alpha5.lean`](lean/Erdos18Alpha5.lean) | 498 | Standalone zero-dependency pure Lean 4 combinatorial core |
| [`scripts/verify_practical.py`](scripts/verify_practical.py) | 153 | Exact DP for small $h(n!)$ & strict certificate verifier |
| [`scripts/test_primefield.py`](scripts/test_primefield.py) | 459 | Numerical & end-to-end verification suite for the prime-field proof (2-factor smooth pigeonhole + 80/80 PASS) |
| [`scripts/test_alpha5_lemmas.py`](scripts/test_alpha5_lemmas.py) | — | Numerical & end-to-end verification suite for Milestone 1 |
| [`scripts/test_alpha3_lemmas.py`](scripts/test_alpha3_lemmas.py) | — | Numerical & end-to-end verification suite for Milestone 3 |
| [`scripts/stress_alpha3.py`](scripts/stress_alpha3.py) | — | High-precision 80-digit & adversarial stress tests (up to $k = 2^{1000}$) |

---

## Verify It Yourself

Don't trust a crow. Trust the Lean 4 kernel.

### Lean 4 + Mathlib4 (All 4 Theorems)

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
python3 scripts/test_primefield.py
```

---

## Transparency & Credits

- **Author:** [vinnor](https://github.com/vinnor)
- **Methodology:** Human-directed, AI-assisted mathematical research and Lean 4 formalization, independently compiled and axiom-checked on GitHub Actions CI. The Lean 4 kernel is the sole arbiter of correctness here.
- **License:** [MIT](LICENSE)

---

<div align="center">

<sub>🐦‍⬛ Started at $\alpha = 9$. Landed at $\alpha = 3 \cdot \log\log$. Zero carries, zero character sums, 13,586 lines of Lean 4.</sub>

</div>
