# Elementary Proof of $h(n!) = O((\log n)^5)$ (Erdős Problem #18)

This document presents the complete, self-contained elementary proof formalized end-to-end in Lean 4 + Mathlib4 under `erdos18_lean/` (`Erdos18.erdos18_alpha5`).

## 1. Definitions & Main Theorem

- A positive integer $m$ is **practical** if every integer $1 \le t \le m$ is a sum of distinct positive divisors of $m$.
- For a practical integer $m$, $h(m)$ is the least integer such that every $1 \le t \le m$ is a sum of at most $h(m)$ distinct positive divisors of $m$.

**Theorem (`Erdos18.erdos18_alpha5`).** There exists an absolute constant $C > 0$ such that for every integer $n \ge 2$ and every integer $1 \le t \le n!$, there exists a finite set $S$ of positive divisors of $n!$ with $\sum_{d \in S} d = t$ and $|S| \le C (\ln n)^5$.

Let $E = v_2(n!) = n - s_2(n)$, $P_m = \prod_{3 \le p \le m} p$ (odd primorial, with $P_m = 1$ for $m < 3$), and $\pi_{\mathrm{odd}}(x) = |\{p \text{ prime} : 3 \le p \le x\}|$.

## 2. Elementary Prime-Number Inputs (`Erdos18/Chebyshev.lean`)

The proof uses zero analytic number theory, relying solely on four elementary facts from Erdős (1932) via central binomial coefficients $\binom{2m}{m}$:

1. **Primorial upper bound (`oddPrimorial_lt_two_pow`):** $\prod_{p \le x} p \le 4^x$ for all $x \ge 1$. Omitting $p = 2$, $Q_m := P_{\lfloor m/2 \rfloor} \le \frac{1}{2} \cdot 4^{\lfloor m/2 \rfloor} < 2^m$ for all $m \ge 1$.
2. **Chebyshev lower bound (`prime_counting_lower`, `prefix_entropy_rate_lower`):** $\pi(x) \ge c_0 \frac{x}{\ln x}$ for all $x \ge 2$, yielding $1 + \frac{1}{2}\pi_{\mathrm{odd}}(\lfloor m/2 \rfloor) \ge \frac{c_1 m}{\log_2(m+2)}$ for all $m \ge 1$ with an explicit constant $c_1 > 0$.
3. **Quantitative Bertrand bound (`bertrand_quantitative`):** $\pi_{\mathrm{odd}}(2x) - \pi_{\mathrm{odd}}(x) \ge c_{\mathrm{B}} \frac{x}{\ln x}$ for all $x \ge x_0$, guaranteeing $\pi_{\mathrm{odd}}(\lfloor k/2 \rfloor) - \pi_{\mathrm{odd}}(\lfloor (k+1)/4 \rfloor) \ge 2 R(k) = O((\log k)^4)$ for all sufficiently large $k$, and $\pi_{\mathrm{odd}}(\lfloor E/4 \rfloor) - \pi_{\mathrm{odd}}(\lfloor (k+1)/4 \rfloor) \ge 2 R(k)$ for $k = \lfloor 0.45 E \rfloor$ and sufficiently large $E$.
4. **Stage 2 binomial divisibility (`uTop_dvd_choose`):** For $a = \lfloor E/4 \rfloor$ and $b = \lfloor E_{\mathrm{next}}/4 \rfloor$ with $E_{\mathrm{next}} = E - \lfloor 0.45 E \rfloor$: whenever $2b > a$ (which holds for all $E \ge 84$), every prime $p \in (b, a]$ divides $a!$ and neither $b!$ nor $(a-b)!$, so
   $$U_{\mathrm{top}} := \prod_{b < p \le a} p \;\Big|\; \binom{a}{b} < 2^a \le 2^{0.25 E} < 2^{\lfloor E_{\mathrm{next}}/2 \rfloor}.$$

## 3. Binary Entropy & Bitwise Chain-Rule Gain (`Erdos18/Entropy.lean`)

### Lemma 1 (`binEntropy_sq_le`, `binEntropy_xor_gain`)

For all $q \in [0, 1]$ with $\beta = |1 - 2q|$ and all $p \in [0, 1]$ with $\alpha = |1 - 2p|$:

1. $1 - \beta^2 = 4q(1-q) \ge 2(\ln 2)^2 h_2(q)^2$.
   *Proof:* For $x \ge 1$, $\ln x \le \frac{x-1}{\sqrt{x}}$. Hence for $q \in (0,1)$, $(\ln 2) h_2(q) = q \ln(1/q) + (1-q)\ln(1/(1-q)) \le \sqrt{q(1-q)}(\sqrt{1-q} + \sqrt{q}) \le \sqrt{2 q(1-q)}$. Squaring yields $4q(1-q) \ge 2(\ln 2)^2 h_2(q)^2$.
2. $h_2\!\left(\frac{1-\alpha\beta}{2}\right) - h_2\!\left(\frac{1-\alpha}{2}\right) \ge (1-\beta^2)\left(1 - h_2\!\left(\frac{1-\alpha}{2}\right)\right)$.
   *Proof:* Expand $1 - h_2\!\left(\frac{1-u}{2}\right) = \frac{1}{\ln 2}\sum_{m=1}^\infty \frac{u^{2m}}{2m(2m-1)}$ and apply $1 - \beta^{2m} \ge 1 - \beta^2$ term-by-term.

### Lemma 2 (`Hnat_conv_sub_ge_bitwise`)

For independent random variables $X, Z$ on $\mathbb{Z}/2^k\mathbb{Z}$, writing $U = X + Z \pmod{2^k}$, $\gamma_j(Z) := H(z_j \mid Z_{<j})$, and $\delta_j(X) := 1 - H(x_j \mid X_{<j})$:

$$H(X + Z) - H(X) \ge 2(\ln 2)^2 \sum_{j=0}^{k-1} \gamma_j(Z)^2 \, \delta_j(X).$$

*Proof:* By the chain rule, $H(U) - H(X) = \sum_{j=0}^{k-1} (H(u_j \mid U_{<j}) - H(x_j \mid X_{<j}))$. Conditioning reduces entropy and $(U_{<j}, Z_{<j}) \leftrightarrow (X_{<j}, Z_{<j})$ is a bijection, so $H(u_j \mid U_{<j}) \ge H(u_j \mid X_{<j}, Z_{<j})$. Conditioned on $(X_{<j}=a, Z_{<j}=b)$, the carry $c_j(a,b)$ is deterministic and $x_j \perp z_j$, so $u_j = x_j \oplus z_j \oplus c_j(a,b)$ has bias $\alpha_a \beta_b$. Applying Lemma 1, taking expectations over independent $(a,b)$, and applying Jensen $\mathbb{E}[h_2(q_b)^2] \ge \gamma_j(Z)^2$ gives the result.

## 4. Parametric Mod-$2^k$ Covering (`Erdos18/Covering.lean`)

### Lemma 3 (`mod_two_pow_covering`)

Let $k \ge 2$, $L = \lfloor \log_2(\lfloor (k+1)/2 \rfloor) \rfloor + 1$, and for each $0 \le t < L$ let $Q_{2^t} = P_{\lfloor 2^t/2 \rfloor} < 2^{2^t}$. Define $Z_{2^t} = \frac{1}{2}\delta_0 + \frac{1}{2}\mathrm{Unif}(\mathrm{Div}(Q_{2^t}))$, and define $Y = 2^s Z_{2^t}$ with $t \sim \mathrm{Unif}(\{0, \dots, L-1\})$ and $s \sim \mathrm{Unif}(S_t)$, where

$$S_t := \{0, \dots, \min(2^{t+1}-1, k-2^t)\} \cup \{\max(0, k - 3\cdot 2^t + 1), \dots, k-2^t\}.$$

Let $g := \frac{c_1}{\log_2(k+2)}$ and $R(k) := \left\lceil \frac{4 L \ln(2k)}{2(\ln 2)^2 g^2} \right\rceil = O((\log k)^4)$. For any integer $Q_{\max} \ge 3$ satisfying $\pi_{\mathrm{odd}}(Q_{\max}) - \pi_{\mathrm{odd}}(\lfloor (k+1)/4 \rfloor) \ge 2 R(k)$, every residue $a \in \mathbb{Z}/2^k\mathbb{Z}$ is congruent modulo $2^k$ to a sum of at most $2 R(k)$ strictly distinct positive divisors of $2^k P_{Q_{\max}}$, each with $v_2 < k$ and value $< Q_{\max} \cdot 2^k$.

*Proof outline:*
1. For all $0 \le t < L$ and $s \in S_t$, $Y = 2^s Z_{2^t} < 2^k$, $|S_t| \le 4 \cdot 2^t$, and every prime factor of $Q_{2^t}$ is $\le \lfloor (k+1)/4 \rfloor$.
2. Since $0 \notin \mathrm{Div}(Q_{2^t})$ and all $2^{\pi_{\mathrm{odd}}(\lfloor 2^t/2 \rfloor)}$ divisors are $< 2^{2^t}$, $H(Z_{2^t} \bmod 2^{2^t}) = 1 + \frac{1}{2}\pi_{\mathrm{odd}}(\lfloor 2^t/2 \rfloor) \ge g \cdot 2^t$.
3. For each bit $0 \le j < k$, taking $t^* = \lfloor \log_2 \min(j+1, k-j) \rfloor$, every $s \in [j - 2^{t^*} + 1, j]$ lies in $S_{t^*}$ with probability $\ge \frac{1}{4 L \cdot 2^{t^*}}$. By concavity, Lemma 2, and Cauchy-Schwarz, $H(X + Y) - H(X) \ge \frac{2(\ln 2)^2 g^2}{4L}(k - H(X))$.
4. Pick $2R(k)$ distinct odd tag primes $q_1, \dots, q_{2R(k)} \in (\lfloor (k+1)/4 \rfloor, Q_{\max}]$. Since multiplication by odd $q_r$ is an automorphism of $\mathbb{Z}/2^k\mathbb{Z}$, $H(X + q_r Y) - H(X) = H(q_r^{-1} X + Y) - H(q_r^{-1} X) \ge \frac{2(\ln 2)^2 g^2}{4L}(k - H(X))$.
5. After $R(k)$ copies, $k - H(S_R) < 1 \implies |\mathrm{supp}(S_R)| > 2^{k-1}$. Splitting into two independent halves $S_R, S'_R$ with disjoint prime tags gives $\mathrm{supp}(S_R) + \mathrm{supp}(S'_R) = \mathbb{Z}/2^k\mathbb{Z}$ by pigeonhole. Omitting zero terms yields $\le 2R(k)$ pairwise distinct divisors (each uniquely tagged by $q_r$).

## 5. Carry Recursion & Global Reduction (`Erdos18/MainTheorem.lean`)

### Lemma 4 (`lemma4_carry_recursion`, Zero-Loss $B \to \lceil \sqrt{B} \rceil$)

For all $E \ge 2$ and $r \in [1, 2^{\lfloor E/2 \rfloor})$ with $B = \lfloor \log_2 r \rfloor + 1$, $r$ is a sum of at most $O((\log(B+2))^4)$ distinct positive divisors of $2^E P_{\lfloor E/4 \rfloor}$.

*Proof:* For $B \le B_0$, expand $r$ in binary ($O(1)$ powers of $2$). For $B > B_0$, set $k = B - \lceil \sqrt{B} \rceil$ and $Q_{\max} = \lfloor k/2 \rfloor$. Lemma 3 gives $\le 2R(k)$ distinct divisors with $v_2 < k$ whose sum $S \equiv r \pmod{2^k}$ satisfies $S < 2R(k)\lfloor k/2 \rfloor 2^k \le 2^{B-1} \le r$. Then $r' = (r - S)/2^k < 2^{\lceil \sqrt{B} \rceil}$ satisfies $r' < 2^{\lfloor (E-k)/2 \rfloor}$; recurse on $(r', E - k)$ and multiply returned divisors by $2^k$ (preserving $v_2$ disjointness). Total terms telescope as $\sum_{j \ge 0} 2R(B^{2^{-j}}) = O((\log B)^4)$.

### Main Theorem (`erdos18_alpha5`)

For $t = n!$, take $\{n!\}$; for $n < 64$, $n!$ is practical so $h(n!) \le 64! = O(1)$. For $n \ge 64$ and $1 \le t < n!$:

- **Stage 1 (`greedy_factorize`, `mixed_radix_stage1`):** Write $M(E) = 2^E P_{\lfloor E/4 \rfloor}$ and factor $U = n!/M(E) = D_1 \cdots D_L$ greedily with $D_j \le 2^{\lfloor E/2 \rfloor}$ and $L = O(\log n)$. Expand $t$ in mixed radix $(D_1, \dots, D_L)$: each digit $r_j < D_{j+1} \le 2^{\lfloor E/2 \rfloor}$ uses $O((\log n)^4)$ distinct divisors of $M(E)$ via Lemma 4, multiplied by $D_1 \cdots D_j$ (pairwise disjoint intervals). Total Stage 1 cost: $O((\log n)^5)$.
- **Stage 2 (`stage2_tail_recursion`):** For the top quotient $r_L < M(E)$, recurse $M(E) \to M(E_{\mathrm{next}})$ with $k = \lfloor 0.45 E \rfloor$ and $E_{\mathrm{next}} = E - k$. For $E > E_0$ and $x \ge 2^{\lfloor E/2 \rfloor}$:
  - **Group 1** ($v_2 < k$): Lemma 3 produces $S_1 \equiv x \pmod{2^k}$ with $S_1 < 2^{\lfloor E/2 \rfloor} \le x$ in $O((\log E)^4)$ terms.
  - Let $x_1 = (x - S_1)/2^k = q_1 U_{\mathrm{top}} + r_1$ with $r_1 < U_{\mathrm{top}} < 2^{\lfloor E_{\mathrm{next}}/2 \rfloor}$ and $q_1 < M(E_{\mathrm{next}})$.
  - **Group 2** ($v_2 \ge k$, in $[2^k, 2^k U_{\mathrm{top}})$): represent $r_1$ via Lemma 4 in $O((\log E)^4)$ terms, multiplied by $2^k$.
  - **Group 3** ($v_2 \ge k$, $\ge 2^k U_{\mathrm{top}}$): recurse on $q_1$ in $M(E_{\mathrm{next}})$, multiplied by $2^k U_{\mathrm{top}}$.
  - The three groups are pairwise disjoint and $T_{\mathrm{tail}}(E) \le O((\log E)^4) + T_{\mathrm{tail}}(\lceil 0.55 E \rceil) = O((\log E)^5)$.

Combining Stage 1 and Stage 2 gives $h(n!) = O((\log n)^5)$ unconditionally for all $n \ge 2$. $\square$
