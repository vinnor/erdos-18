# Elementary Carry-Free Proof of $h(n!) = O((\log n)^3 \log\log(n+16))$ (Erdős Problem #18)

This document presents the complete, self-contained elementary proof formalized end-to-end in Lean 4 + Mathlib4 under `erdos18_lean/` (`Erdos18.erdos18_alpha3_loglog1`, together with the earlier 2-adic milestones `erdos18_alpha3_loglog2`, `erdos18_alpha4`, and `erdos18_alpha5`).

## 1. Definitions & Main Theorem

- A positive integer $m$ is **practical** if every integer $1 \le t \le m$ is a sum of distinct positive divisors of $m$.
- For a practical integer $m$, $h(m)$ is the least integer such that every $1 \le t \le m$ is a sum of at most $h(m)$ distinct positive divisors of $m$.

**Theorem (`Erdos18.erdos18_alpha3_loglog1`).** There exists an absolute constant $C > 0$ such that for every integer $n \ge 2$ and every integer $1 \le t \le n!$, there exists a finite set $S$ of positive divisors of $n!$ with $\sum_{d \in S} d = t$ and
$$|S| \le C (\ln n)^3 \ln\ln(n + 16).$$

**Immediate Corollaries.** Since $n!$ is practical and $\ln\ln(n!) = \ln n + O(\ln\ln n)$, the single theorem above simultaneously resolves all three parts of Erdős Problem #18:
- **18(a):** $h(m) < (\ln\ln m)^4$ for infinitely many practical integers $m = n!$;
- **18(b):** $h(n!) < n^{o(1)}$;
- **18(c):** $h(n!) = O((\ln n)^3 \ln\ln(n + 16)) = O((\ln n)^4)$.

Throughout, all entropies are measured in nats: $H_{\mathrm{nat}}(X) := -\sum_x p(x)\ln p(x)$ and $\Delta_q^{\mathrm{nat}}(U) := \ln q - H_{\mathrm{nat}}(U) = D_{\mathrm{KL}}^{\mathrm{nat}}(p \,\|\, u_q)$ on $\mathbb{F}_q = \mathbb{Z}/q\mathbb{Z}$.

## 2. Why Leave $\mathbb{Z}/2^k\mathbb{Z}$ for $\prod_{q \in Q'} \mathbb{F}_q$?

In 2-adic covering modulo $2^k$ (our earlier Milestone 3, `Alpha3Covering.lean`), binary carries force a bitwise chain rule with convex variance envelope $f_4(u) = u/\ln(4/u)$, incurring an unavoidable $\ln(4/g) = \Theta(\log\log n)$ penalty on top of the $\Theta(\log n \cdot \log\log n)$ scale-selection integral — locking 2-adic entropy bounds at $O((\log n)^3 (\log\log n)^2)$.

Working instead modulo a squarefree product of large primes $M' = \prod_{q \in Q'} q$ via CRT $\mathbb{Z}/M'\mathbb{Z} \cong \prod_{q \in Q'} \mathbb{F}_q$ has two decisive advantages:
1. **Zero carries across coordinates:** Every prime factor $q \in Q'$ acts as an independent prime field $\mathbb{F}_q$ with no nontrivial proper subgroups or nested ideals.
2. **Linear entropy gain via multiplicative dilation:** Averaging $U + cV$ over $c \in \mathbb{F}_q^*$ gives entropy gain **linear** in $H_{\mathrm{nat}}(V)$ (eliminating $f_4$'s $\ln(4/g)$ loss unconditionally), and the random multiplier $c \in \mathbb{F}_q^*$ is supplied by an elementary **2-factor smooth Finset pigeonhole** product $c_1 c_2 \mid m!$ with zero character sums or Pólya–Vinogradov.

## 3. Pointwise KL Contraction & Universal $\mathbb{F}_q$ Dilation (`Erdos18/PrimeFieldEntropy.lean`)

### Lemma 1 (`pointwise_kl_contraction_le`)

Let $q \ge 3$ be an integer, $p$ a probability distribution on $\mathbb{Z}/q\mathbb{Z}$, and $r \in (0, 1/2]$. Define
$$T_r(p)(x) := r\,p(x) + (1 - r)\frac{1 - p(x)}{q - 1}.$$
Then with absolute constant $c_1 := \frac{1}{484}$,
$$D_{\mathrm{KL}}^{\mathrm{nat}}\big(p \,\|\, T_r(p)\big) \;\ge\; \frac{1}{484} \cdot \frac{\min(\ln(1/r),\, \ln q)}{\ln q} \cdot \Delta_q^{\mathrm{nat}}(p).$$

*Proof.* Put $\theta := \frac{qr - 1}{q - 1}$ and $u_x := q p(x)$, so $q T_r(p)(x) = 1 + \theta(u_x - 1)$.
- If $r \le 1/q$, then $\theta \le 0$ and $\ln(1 + z) \le z$ plus Cauchy–Schwarz ($q\sum p(x)^2 \ge 1$) yield $D_{\mathrm{KL}}^{\mathrm{nat}}(p \,\|\, T_r(p)) \ge \Delta_q^{\mathrm{nat}}(p)$.
- If $r \in (1/q, 1/2]$, then $\theta \in (0, 1/2)$, $\theta < r$, and setting $B(u) := u\ln u - (u-1)$ and $g_\theta(u) := u\ln\frac{u}{\theta u + 1 - \theta} - (1-\theta)(u-1)$ gives $\Delta_q^{\mathrm{nat}}(p) = \frac{1}{q}\sum_x B(u_x)$ and $D_{\mathrm{KL}}^{\mathrm{nat}}(p \,\|\, T_r(p)) = \frac{1}{q}\sum_x g_\theta(u_x)$. On $u \in [0, 10/\theta]$, $g_\theta''(u) = \frac{(1-\theta)^2}{u(\theta u + 1 - \theta)^2} \ge \frac{1}{484} B''(u)$ integrates twice from $u = 1$; on $u \in (10/\theta, q]$, direct comparison yields $g_\theta(u) > 0.14\,u\ln(1/r) \ge \frac{1}{484}\frac{\ln(1/r)}{\ln q} B(u)$. $\square$

### Lemma 2 (`fq_uniform_dilation_entropy_gain`, `fq_general_dilation_entropy_gain`)

For every prime $q \ge 3$ and independent random variables $U, V$ on $\mathbb{F}_q$,
$$\frac{1}{q - 1} \sum_{c \in \mathbb{F}_q^*} \big(H_{\mathrm{nat}}(U + cV) - H_{\mathrm{nat}}(U)\big) \;\ge\; \frac{1}{2420\ln q}\left(H_{\mathrm{nat}}(V) - \frac{5\ln q}{q}\right)\Delta_q^{\mathrm{nat}}(U).$$
More generally, for any probability weights $W$ on $\mathbb{F}_q^*$ satisfying $W(c) \ge c_{\mathrm{dil}} / (q - 1)$ for all $c \in \mathbb{F}_q^*$, the weighted average gain is at least $c_{\mathrm{dil}}$ times the right-hand side.

*Proof.* Express $H_{\mathrm{nat}}(U + cV) - H_{\mathrm{nat}}(U)$ via the exact Jensen-gap identity for $-t\ln t$, apply convexity of $t \mapsto a\ln\frac{a}{ra + (1-r)t}$ over $c \in \mathbb{F}_q^*$ (using $\mathbb{E}_{c \in \mathbb{F}_q^*}[p(x' + c(y-z))] = \frac{1 - p(x')}{q - 1}$ for $z \neq y$) to get $\ge \sum_y r(y) D_{\mathrm{KL}}^{\mathrm{nat}}(p \,\|\, T_{r(y)}(p))$, and apply Lemma 1 (handling $r_{\max} \le 1/2$ directly and $r_{\max} > 1/2$ by dropping $y_{\max}$ and using $H_{\mathrm{nat}}(V) < 2.5 S_{\neq}$). $\square$

## 4. Elementary 2-Factor Smooth Pigeonhole Dilator (`Erdos18/PrimeFieldDilation.lean`)

### Lemma 3 (`two_factor_smooth_dilator_prob`, `two_factor_smooth_entropy_gain`)

Define the $0.28 m$-smooth set
$$A(m) := \left\{1 \le a \le \lfloor 14m/25 \rfloor : P^+(a) \le \lfloor 7m/25 \rfloor\right\}.$$
1. **Exact divisibility:** For every $m \ge 16$ and $c_1, c_2 \in A(m)$, $c_1 c_2 < m^2$ and $c_1 c_2 \mid m!$ (each prime $p \in (\sqrt{m}, 0.28m]$ appears at most twice in $c_1 c_2$, while $v_p(m!) \ge \lfloor 1/0.28 \rfloor = 3$).
2. **Chebyshev cardinality (`smoothSet_card_ge`):** Since $2(\lfloor 7m/25 \rfloor + 1) > \lfloor 14m/25 \rfloor$, the only excluded elements of $[1, \lfloor 14m/25 \rfloor]$ are primes in $(7m/25, 14m/25]$. Erdős's 1932 primorial bound $\prod_{p \le y} p \le 4^y$ yields $|A(m)| \ge \frac{44}{45}\lfloor 14m/25 \rfloor > \frac{q-1}{2}$ for all $m \ge 4 \cdot 4^{45}$ and prime $q \in (14m/25, m]$.
3. **Finset pigeonhole on $\mathbb{F}_q^*$:** Since $A(m) \hookrightarrow \mathbb{F}_q^*$ is injective, for every $x \in \mathbb{F}_q^*$, $|A(m) \cap x A(m)^{-1}| \ge 2|A(m)| - (q - 1) \ge q/20$, giving
   $$\mathbb{P}_{c_1, c_2 \sim \mathrm{Unif}(A(m))}\big(c_1 c_2 \equiv x \pmod q\big) \;\ge\; \frac{1/40}{q - 1}.$$

Combining Lemmas 2 and 3 yields universal prime-field dilation entropy gain with $c_{\mathrm{dil}} = 1/40$, using zero character sums and zero analytic number theory. $\square$

## 5. Carry-Free CRT Covering & Stage 1–2 Assembly (`PrimeFieldCovering.lean`, `PrimeFieldMain.lean`)

### Lemma 4 (`adaptive_dilation_contraction`)

Using a 16-subinterval quantitative Bertrand band (`exists_prime_band`, from `Chebyshev.lean`), separate three pairwise disjoint prime sets inside $[1, m]$: a base prime pool $P_{\mathrm{pool}}$ (for $r$-prime squarefree divisor blocks $Z_r$), tag primes $Q_{\mathrm{tag}}$, and target strip primes $Q_{\mathrm{strip}}$ with $M_{\mathrm{strip}} := \prod_{q \in Q_{\mathrm{strip}}} q$ and core divisor $M_{\mathrm{core}}(m) \mid m!$. For any distribution $X$ on $\mathbb{Z}/M'\mathbb{Z}$ ($M' = \prod_{q \in Q'} q$, $Q' \subseteq Q_{\mathrm{strip}}$):
1. Order $Q'$ by decreasing conditional coordinate deficit via the CRT chain rule (`crt_list_dilation_entropy_gain`).
2. Select the subset size $r \in \{1, \dots, \lfloor N/2 \rfloor\}$ adaptively by greedy top-$r$ matching; injectivity of $r$-prime products below $(q_{\min})^r$ supplies entropy $H_{\mathrm{nat}}(Z_r) \ge \ln\binom{N}{r} \ge r\ln(N/r)$, and the harmonic sum
   $$\sum_{r=1}^{\lfloor N/2 \rfloor} \frac{1}{r\ln(N/r)} = \ln\ln N + O(1)$$
   forces a single-step contraction rate
   $$\eta \;\ge\; \frac{1}{193600\, \ln m\, (\ln\ln(m + 16) + 4)}$$
   for the random divisor $Y = p_{\mathrm{tag}} c_1 c_2 Z_r \mid M_{\mathrm{core}}(m)$.

### Lemma 5 & Main Theorem (`mod_Mprime_covering`, `stage2_tail_recursion_primefield`, `erdos18_alpha3_loglog1`)

1. **Mod-$M'$ Covering:** Iterating Lemma 4 across $R(m) = O((\ln m)^2 \ln\ln(m+16))$ independent draws tagged by distinct primes in $Q_{\mathrm{tag}}$ drives the entropy deficit below $\ln 2$, forcing support $> M'/2$. Pairing two disjoint tag halves covers all of $\mathbb{Z}/M'\mathbb{Z}$ by pigeonhole in $2R(m)$ strictly distinct divisors of $M_{\mathrm{core}}(m)$, each $< m^3 M'$ and not divisible by $M'$.
2. **Carry-Free Exact Digit Representation (`exact_digit_rep_primefield`):** For any $r < M_{\mathrm{strip}}/m^5$, subtracting the mod-$M'$ cover leaves a nonnegative quotient $< 2m^6$ divisible by $M'$, represented directly in $O(\log m)$ binary powers $2^b M'$ — **completely eliminating the $\sqrt{B}$ carry recursion**.
3. **Stage 1 & Stage 2 (11-Prime Strip):** Mixed-radix Stage 1 factors $n!/M_{\mathrm{core}}(n)$ into $O(\log n)$ digits $< M_{\mathrm{strip}}/n^5$. Stage 2 reduces $x < M_{\mathrm{core}}(m)$ recursively from $m \to m/2$ across three exhaustive branches: Branch A ($x < M_{\mathrm{strip}}/m^5$, Lemma 5b), Branch B ($M_{\mathrm{strip}}/m^5 \le x < m^5 M_{\mathrm{strip}}$, stripping 11 primes from $Q_{\mathrm{strip}}$ so the binary quotient is $< m^{16} < 2^{m/4}$ and returning immediately), and Branch C ($x \ge m^5 M_{\mathrm{strip}}$, splitting $v_{M'}$-disjoint groups and recursing on $M_{\mathrm{core}}(m/2)$). Summing both stages yields
   $$h(n!) = O\!\left((\ln n)^3 \ln\ln(n + 16)\right). \quad\square$$

## 6. Why $O((\log n)^3 \log\log n)$ Is a Natural Barrier

Two exact factors remain above the information-theoretic floor $\Omega((\log n)^2)$: (i) the injective harmonic $\log\log n$ factor $\sum_{r \le N/2} \frac{1}{r\ln(N/r)}$ from prime-product coordinate matching, and (ii) the $\Theta(\log n)$ contraction tail $\ln(2m)$. Improving beyond $O((\log n)^3 \log\log n)$ reduces across 2-adic, prime-field, and Archimedean completions either to super-polynomial modular non-collapse / equidistribution lying strictly beyond GRH+RH, or to genuinely non-Fourier multi-term additive energy bounds for divisor sumsets.
