# Elementary Proof of $h(n!) = O((\log n)^3 (\log\log(n+16))^2)$ (Erdős Problem #18)

This document presents the complete, self-contained elementary proof formalized end-to-end in Lean 4 + Mathlib4 under `erdos18_lean/` (`Erdos18.erdos18_alpha3_loglog2` and its corollary `Erdos18.erdos18_alpha4`).

## 1. Definitions & Main Theorems

- A positive integer $m$ is **practical** if every integer $1 \le t \le m$ is a sum of distinct positive divisors of $m$.
- For a practical integer $m$, $h(m)$ is the least integer such that every $1 \le t \le m$ is a sum of at most $h(m)$ distinct positive divisors of $m$.

**Theorem (`Erdos18.erdos18_alpha3_loglog2`).** There exists an absolute constant $C > 0$ such that for every integer $n \ge 2$ and every integer $1 \le t \le n!$, there exists a finite set $S$ of positive divisors of $n!$ with $\sum_{d \in S} d = t$ and
$$|S| \le C (\ln n)^3 \big(\ln\ln(n + 16)\big)^2.$$

**Corollary (`Erdos18.erdos18_alpha4`).** Since $(\ln\ln(n+16))^2 \le 20 \ln n$ for all $n \ge 2$, $h(n!) = O((\ln n)^4)$ unconditionally.

Let $E = v_2(n!) = n - s_2(n)$, $P_y := \prod_{3 \le p \le y} p$ (odd primorial, with $P_y = 1$ for $y < 3$), and $\pi_{\mathrm{odd}}(y) := |\{p \text{ prime} : 3 \le p \le y\}|$.

## 2. Elementary Prime-Number Inputs (`Erdos18/Chebyshev.lean`)

Zero analytic number theory is used beyond four elementary facts from Erdős (1932) via central binomial coefficients $\binom{2m}{m}$:

1. **Primorial upper bound (`oddPrimorial_lt_two_pow`):** $\prod_{p \le y} p \le 4^y$ for all $y \ge 1$, so omitting $p = 2$, $P_{\lfloor m/2 \rfloor} < 2^m$ for all $m \ge 1$.
2. **Chebyshev lower bounds (`prime_counting_lower`, `prefix_entropy_rate_lower`):** Explicit absolute constants $c_0 \in (0, 1/2]$ and $c_1 \in (0, 1]$ satisfy $\pi_{\mathrm{odd}}(y) \ge c_0 \frac{y}{\log_2 y}$ for $y \ge 3$ and $1 + \frac{1}{2}\pi_{\mathrm{odd}}(\lfloor m/2 \rfloor) \ge \frac{c_1 m}{\log_2(m+2)}$ for all $m \ge 1$.
3. **Quantitative Bertrand (`bertrand_quantitative`):** $\pi_{\mathrm{odd}}(2y) - \pi_{\mathrm{odd}}(y) \ge c_B \frac{y}{\ln y}$ for all $y \ge y_0$, guaranteeing $\pi_{\mathrm{odd}}(\lfloor k/2 \rfloor) - \pi_{\mathrm{odd}}(\lfloor (k+1)/4 \rfloor) \ge 2R^*(k)$ for sufficiently large $k$ and $\pi_{\mathrm{odd}}(\lfloor E/4 \rfloor) - \pi_{\mathrm{odd}}(\lfloor (k+1)/4 \rfloor) \ge 2R^*(k)$ for $k = \lfloor 0.45 E \rfloor$ and sufficiently large $E$.
4. **Stage 2 binomial divisibility (`uTop_dvd_choose`):** For $E \ge 84$, $k = \lfloor 0.45 E \rfloor$, $E_{\mathrm{next}} = E - k$, $a = \lfloor E/4 \rfloor$, and $b = \lfloor E_{\mathrm{next}}/4 \rfloor$: $2b > a$ and $U_{\mathrm{top}} := \prod_{b < p \le a} p \mid \binom{a}{b} < 2^a \le 2^{0.25 E} < 2^{\lfloor E_{\mathrm{next}}/2 \rfloor}$.

## 3. Sharp Convex Entropy–Variance & Bitwise Gain (`Erdos18/Alpha3Entropy.lean`)

### Lemma 1' (`convexOn_f4nat`, `binEntropy_f4nat_le`, `binEntropy_xor_gain_f4nat`)

Define $f_4 : [0, 1] \to [0, \infty)$ by $f_4(0) := 0$ and $f_4(u) := \frac{u}{\ln(4/u)}$ for $u \in (0, 1]$, with $\psi(u) := 1/f_4(u) = \frac{\ln(4/u)}{u}$.

1. $f_4$ is continuous, strictly increasing, and strictly convex on $[0, 1]$ ($f_4'(u) = \frac{L+1}{L^2} > 0$, $f_4''(u) = \frac{L+2}{u L^3} > 0$ where $L = \ln(4/u) \ge \ln 4$).
2. For all $q \in [0, 1]$ with $\beta = |1 - 2q|$:
   $$1 - \beta^2 = 4q(1-q) \ge (\ln 2)\, f_4\big(h_2(q)\big).$$
   *Proof:* By symmetry assume $q \in (0, 1/2]$. From $4q(1-q) \ge 2(\ln 2)^2 h_2(q)^2$, $h_2(q) \le \frac{\sqrt{2q}}{\ln 2}$, so $\frac{4}{h_2(q)} \ge \sqrt{\frac{8(\ln 2)^2}{q}} > \sqrt{\frac{e}{q}}$ and $\ln(4/h_2(q)) > \frac{1}{2}\ln(e/q)$. Meanwhile $(\ln 2) h_2(q) = q\ln(1/q) + (1-q)\ln(1 + \frac{q}{1-q}) \le q\ln(e/q)$. Dividing gives $(\ln 2) f_4(h_2(q)) < 2q \le 4q(1-q)$.
3. For all $p, q \in [0, 1]$ with $\alpha = |1 - 2p|$, $\beta = |1 - 2q|$:
   $$h_2\!\left(\frac{1-\alpha\beta}{2}\right) - h_2\!\left(\frac{1-\alpha}{2}\right) \ge (1-\beta^2)\left(1 - h_2\!\left(\frac{1-\alpha}{2}\right)\right).$$

### Lemma 2' (`Hnat_conv_sub_ge_bitwise_f4nat`)

For independent random variables $X, Z$ on $\mathbb{Z}/2^k\mathbb{Z}$, with $\gamma_j(Z) := H(z_j \mid Z_{<j})$ and $\delta_j(X) := 1 - H(x_j \mid X_{<j})$:
$$H(X + Z) - H(X) \ge (\ln 2) \sum_{j=0}^{k-1} f_4\big(\gamma_j(Z)\big)\, \delta_j(X).$$

*Proof:* Follow the bitwise chain rule and bijection $(U_{<j}, Z_{<j}) \leftrightarrow (X_{<j}, Z_{<j})$ to obtain $H(X+Z) - H(X) \ge \sum_{j=0}^{k-1} \mathbb{E}_b[4q_b(1-q_b)]\,\delta_j(X)$, apply Lemma 1'(2) pointwise, and apply Jensen's inequality for convex $f_4$ on $[0, 1]$. $\square$

## 4. Full-Pool $s$-Prime Subsets & Weighted Dyadic Covering (`Erdos18/Alpha3Covering.lean`)

### Lemma 3A* (`SigmaStar_le`)

Let $k \ge 2$, $L := \lfloor \log_2(\lfloor (k+1)/2 \rfloor) \rfloor + 1$, and $x := \lfloor (k+1)/4 \rfloor$. For each $t \in \{0, \dots, L-1\}$, let $m := 2^t$ and choose $\mathcal{D}_{k,t}$ of maximum cardinality among four sets of positive odd divisors of $P_x$ below $2^m$:
- $\mathcal{D}^{(0)}_{k,t} := \{1\}$,
- $\mathcal{D}^{(A)}_{k,t} := \{p \text{ odd prime} : 3 \le p \le \min(2^m - 1, x)\}$,
- $\mathcal{D}^{(B)}_{k,t} := \left\{\prod_{p \in A} p : A \subseteq \{3 \le p \le x \text{ prime}\},\; |A| = s\right\}$ where $s := \max\{s' \ge 0 : x^{s'} < 2^m\}$ (when $1 \le s \le \pi_{\mathrm{odd}}(x)$),
- $\mathcal{D}^{(C)}_{k,t} := \mathrm{Div}(P_{\lfloor m/2 \rfloor})$.

Set $Z_{k,t} := \frac{1}{2}\delta_0 + \frac{1}{2}\mathrm{Unif}(\mathcal{D}_{k,t})$ and $g_{k,t} := \frac{1 + \frac{1}{2}\log_2|\mathcal{D}_{k,t}|}{2^t} \in [\frac{1}{m}, 1]$. Partitioning $\{0, \dots, L-1\}$ into four regimes:
- **Regime 0 ($m < M_0$):** $O(1)$ terms, bounded by $O(\Phi(k))$.
- **Regime 1 ($M_0 \le m \le 2\log_2 x$):** Candidate A gives $g_{k,t} \ge 1/8$ across $O(\log\log x)$ terms.
- **Regime 2 ($2\log_2 x < m \le \frac{c_0}{2} x$):** Candidate B + $\binom{N}{s} \ge (N/s)^s$ gives $g_{k,t} \ge \frac{u}{4\log_2 x}$ with $u = t_2 - t + 1 \in \{1, \dots, \lfloor \log_2 x \rfloor\}$, summing via $\sum_{u=1}^U \frac{1}{u} \le 1 + \ln U$ to $O(\log_2 x \cdot (\ln\log_2 x)^2)$.
- **Regime 3 ($m > \frac{c_0}{2} x$):** $O(1)$ terms, each with Candidate C density $g_{k,t} \ge c_1/\log_2(k+2)$.

Hence there exists an explicit constant $C^*_\Sigma > 0$ such that for all $k \ge 2$,
$$\Sigma^*(k) := \sum_{t=0}^{L-1} \psi(g_{k,t}) \le C^*_\Sigma\, \log_2(k+2)\,\big(\ln\ln(k+16)\big)^2.$$

### Lemma 3B* (`mod_two_pow_covering_alpha3`)

Define $Y = 2^s Z_{k,t}$ by sampling $t$ with weight $w_t := \psi(g_{k,t}) / \Sigma^*(k)$ and $s \sim \mathrm{Unif}(S_t)$ where $S_t := \{0, \dots, \min(2^{t+1}-1, k-2^t)\} \cup \{\max(0, k - 3\cdot 2^t + 1), \dots, k-2^t\}$ ($|S_t| \le 4\cdot 2^t$). By concavity, Lemma 2', and Jensen on $f_4$, every bit $0 \le j < k$ receives weight
$$W_j \ge (\ln 2)\frac{w_{t^*}}{4}\, f_4(g_{k,t^*}) = \frac{\ln 2}{4\,\Sigma^*(k)} =: \eta^*,$$
giving uniform contraction $H(X + q_r Y) - H(X) = H(q_r^{-1} X + Y) - H(q_r^{-1} X) \ge \eta^*(k - H(X))$ for any odd tag prime $q_r$. With $R^*(k) := \lceil \frac{4\,\Sigma^*(k)\ln(2k)}{\ln 2} \rceil = O((\log k)^2 (\log\log k)^2)$ and $2R^*(k)$ distinct odd tag primes $q_r \in (\lfloor (k+1)/4 \rfloor, Q_{\max}]$, two independent halves satisfy $|\mathrm{supp}(S_R)| > 2^{k-1}$ and cover $\mathbb{Z}/2^k\mathbb{Z}$ by pigeonhole in at most $2R^*(k)$ strictly distinct positive divisors of $2^k P_{Q_{\max}}$ with $v_2 < k$ and value $< Q_{\max} \cdot 2^k$. $\square$

## 5. Carry Recursion & Global Reduction (`Erdos18/Alpha3Main.lean`)

### Lemma 4* (`lemma4_carry_recursion_alpha3`)

For all $E \ge 2$ and $r \in [1, 2^{\lfloor E/2 \rfloor})$ with $B = \lfloor \log_2 r \rfloor + 1$, $r$ is a sum of at most $O((\log(B+2))^2 (\log\log(B+16))^2)$ strictly distinct positive divisors of $2^E P_{\lfloor E/4 \rfloor}$. Using $k = B - \lceil \sqrt{B} \rceil$ and $Q_{\max} = \lfloor k/2 \rfloor$, the step shrinks $B \to \lceil \sqrt{B} \rceil$ while preserving $v_2$-disjointness; since $F^*(\lceil \sqrt{B} \rceil) \le \frac{9}{16} F^*(B)$ for $B \ge 16$, strong induction telescopes with constant $\frac{16}{7}$.

### Stages 1–2 & Main Theorems (`erdos18_alpha3_loglog2`, `erdos18_alpha4`)

Factor $n!/M(E) = D_1 \cdots D_L$ greedily with $D_j \le 2^{\lfloor E/2 \rfloor}$ and $L = O(\log n)$ (`Stage 1`), representing each mixed-radix digit via Lemma 4* in disjoint intervals $[D_1\cdots D_j, D_1\cdots D_{j+1})$. Represent the top quotient $r_L < M(E)$ via self-similar tail recursion $M(E) \to M(\lceil 0.55 E \rceil)$ (`Stage 2`), separating Group 1 ($v_2 < k$, Lemma 3B*), Group 2 ($v_2 \ge k$ and $< 2^k U_{\mathrm{top}}$, Lemma 4*), and Group 3 ($\ge 2^k U_{\mathrm{top}}$, induction). Both stages sum to
$$h(n!) = O\!\left((\log n)^3 \big(\log\log(n+16)\big)^2\right),$$
and consequently $h(n!) = O((\log n)^4)$. $\square$
