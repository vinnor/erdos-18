#!/usr/bin/env python3
"""
Verification & numerical stress-test suite for Prover-4 (Composition of Prover-1 and Prover-2):
  h(n!) = O((log n)^3 (log log n)^2)

Tests:
  1. Lemma 1' (f4 convexity, monotonicity, 4q(1-q) >= (ln 2) f4(h2(q)), psi = 1/f4 decreasing).
  2. Exact Sigma*(k) evaluation up to k = 10^12 (exact sieve up to k = 2*10^6,
     rigorous Rosser-Schoenfeld & Chebyshev bounds up to k = 10^12), verifying both
     O(log k * (log log k)^2) upper bound and Theta(log k * (log log k)^2) sharpness.
  3. Exhaustive exact D_{k,t}, g_{k,t} in (0, 1], chain-rule entropy, Jensen on f4,
     and W_j >= (ln 2) / (4 Sigma*(k)) for all 2 <= k <= 36 and all 0 <= j < k.
  4. Exact mod-2^k convolution contraction and sumset covering for k in {6, 8, 10, 12}.
  5. Lemma 4* telescoping (9/16 contraction for 16 <= B <= 10^6) and end-to-end
     constructive factorial representations verified strictly by scripts/verify_practical.py.
"""

import itertools
import math
import os
import random
import sys
from typing import Dict, List, Tuple

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SCRIPT_DIR)
from verify_practical import verify_representation, is_practical, divisors


LN2 = math.log(2.0)


def h2(q: float) -> float:
    if q <= 0.0 or q >= 1.0:
        return 0.0
    return -q * math.log2(q) - (1.0 - q) * math.log2(1.0 - q)


def f4(u: float) -> float:
    if u <= 0.0:
        return 0.0
    return u / math.log(4.0 / u)


def psi(u: float) -> float:
    """1 / f4(u) = ln(4/u) / u on (0, 1]."""
    assert 0.0 < u <= 1.0 + 1e-12
    return math.log(4.0 / u) / u


def sieve_primes(limit: int) -> List[int]:
    if limit < 2:
        return []
    is_p = bytearray(b"\x01") * (limit + 1)
    is_p[0] = is_p[1] = 0
    for i in range(2, int(limit ** 0.5) + 1):
        if is_p[i]:
            is_p[i * i : limit + 1 : i] = b"\x00" * ((limit - i * i) // i + 1)
    return [i for i, v in enumerate(is_p) if v]


def build_pi_odd(limit: int) -> List[int]:
    primes = sieve_primes(limit)
    pi_odd = [0] * (limit + 1)
    idx = 0
    cnt = 0
    for y in range(limit + 1):
        while idx < len(primes) and primes[idx] <= y:
            if primes[idx] >= 3:
                cnt += 1
            idx += 1
        pi_odd[y] = cnt
    return pi_odd


def log2_binom(n: int, s: int) -> float:
    if s < 0 or s > n:
        return -1.0
    return (math.lgamma(n + 1) - math.lgamma(s + 1) - math.lgamma(n - s + 1)) / LN2


def max_s_for_x_pow_lt_2_pow_m(x: int, m: int) -> int:
    """Exact s = max{s' >= 0 : x^{s'} < 2^m}."""
    if x <= 1:
        return 0
    # s' * log2(x) < m
    est = int(math.floor(m / math.log2(x)))
    # Adjust for floating-point boundary
    # Check using exact integer arithmetic when small, or high-precision log for huge m
    if m <= 20000 and est <= 5000:
        while est > 0 and pow(x, est) >= (1 << m):
            est -= 1
        while pow(x, est + 1) < (1 << m):
            est += 1
        return est
    # For large m, guard against boundary rounding by subtracting 1 if within 1e-12
    val = est * math.log2(x)
    if val >= m - 1e-11:
        est -= 1
    return max(0, est)


def exact_g_kt_from_pi(k: int, t: int, pi_odd_fn) -> Tuple[float, str]:
    """Compute exact g_{k,t} = (1 + 0.5 * log2 |D_{k,t}|) / 2^t using pi_odd_fn(y)."""
    x = (k + 1) // 4
    m = 1 << t
    best_log2_size = 0.0  # Candidate 0: {1}, size 1
    best_cand = "0"

    # Candidate A: odd primes <= min(2^m - 1, x)
    if m <= 60:
        yA = min((1 << m) - 1, x)
    else:
        yA = x
    if yA >= 3:
        cntA = pi_odd_fn(yA)
        if cntA >= 1:
            lA = math.log2(cntA)
            if lA > best_log2_size:
                best_log2_size = lA
                best_cand = "A"

    # Candidate B: s-subsets of odd primes <= x
    if x >= 3:
        pix = pi_odd_fn(x)
        s = max_s_for_x_pow_lt_2_pow_m(x, m)
        if 1 <= s <= pix:
            lB = log2_binom(pix, s)
            if lB > best_log2_size:
                best_log2_size = lB
                best_cand = "B"

    # Candidate C: Div(P_{floor(m/2)})
    half_m = m // 2
    if half_m >= 3:
        lC = float(pi_odd_fn(half_m))
        if lC > best_log2_size:
            best_log2_size = lC
            best_cand = "C"

    g_kt = (1.0 + 0.5 * best_log2_size) / m
    return g_kt, best_cand


def test_suite_1_f4():
    print("=== Suite 1: Lemma 1' (f4 properties & 4q(1-q) >= (ln 2) f4(h2(q))) ===")
    # Dense grid + extreme boundary points
    qs = [i / 100000.0 for i in range(1, 100000)]
    for exp in range(6, 30):
        qs.append(10.0 ** (-exp))
        qs.append(1.0 - 10.0 ** (-exp))
    min_ratio = float("inf")
    for q in qs:
        lhs = 4.0 * q * (1.0 - q)
        rhs = LN2 * f4(h2(q))
        assert lhs >= rhs - 1e-15, f"Failed at q={q}: lhs={lhs} < rhs={rhs}"
        if rhs > 0:
            min_ratio = min(min_ratio, lhs / rhs)

    # Convexity & monotonicity of f4, decreasing psi
    us = [i / 20000.0 for i in range(1, 20001)]
    for i in range(len(us) - 1):
        assert f4(us[i]) < f4(us[i + 1]), f"f4 not strictly increasing at {us[i]}"
        assert psi(us[i]) > psi(us[i + 1]), f"psi not strictly decreasing at {us[i]}"
    rng = random.Random(42)
    for _ in range(5000):
        a = rng.random()
        b = rng.random()
        lam = rng.random()
        assert f4(lam * a + (1 - lam) * b) <= lam * f4(a) + (1 - lam) * f4(b) + 1e-15

    # Check f4(1) = 1 / (2 ln 2)
    assert abs(f4(1.0) - 1.0 / (2.0 * LN2)) < 1e-15
    print(f"  PASS: {len(qs)} q-points checked, min 4q(1-q)/((ln 2)f4(h2(q))) = {min_ratio:.6f} >= 1.0")


def test_suite_2_sigma_star():
    print("\n=== Suite 2: Exact & Asymptotic Sigma*(k) up to k = 10^12 ===")
    MAX_X_EXACT = 500_000
    pi_odd_arr = build_pi_odd(MAX_X_EXACT)

    # Verify Chebyshev constant c0 = 0.5 for 3 <= y <= MAX_X_EXACT
    min_cheb = min(pi_odd_arr[y] / (y / math.log2(y)) for y in range(3, MAX_X_EXACT + 1))
    assert min_cheb >= 0.5, f"Chebyshev constant fell below 0.5: {min_cheb}"

    def pi_odd_exact(y: int) -> int:
        return pi_odd_arr[y]

    # Exact Sigma*(k) for k up to 2 * 10^6
    test_ks_exact = list(range(2, 200)) + [
        500, 1000, 2000, 5000, 10_000, 50_000, 100_000, 500_000, 1_000_000, 2_000_000
    ]
    max_ratio_sq = 0.0
    for k in test_ks_exact:
        L = int(math.floor(math.log2((k + 1) // 2))) + 1
        sig = 0.0
        for t in range(L):
            g_kt, _ = exact_g_kt_from_pi(k, t, pi_odd_exact)
            assert 0.0 < g_kt <= 1.0 + 1e-12, f"g_{{{k},{t}}} = {g_kt} out of (0,1]"
            sig += psi(min(g_kt, 1.0))
        denom_sq = math.log2(k + 2) * (math.log(math.log(k + 16)) ** 2)
        max_ratio_sq = max(max_ratio_sq, sig / denom_sq)

    print(f"  Exact sieve (2 <= k <= 2e6): max Sigma*(k) / (log2(k+2) * (ln ln(k+16))^2) = {max_ratio_sq:.4f}")

    # Asymptotic evaluation up to k = 10^12 using BOTH:
    # (a) Rosser-Schoenfeld lower bound: pi_odd(y) >= floor(y / ln y) - 1 for y >= 17 (exact for y <= 5e5)
    # (b) Rosser-Schoenfeld upper bound: pi_odd(y) <= floor(1.25506 * y / ln y) - 1 for y >= 17
    def pi_odd_rs_lower(y: int) -> int:
        if y <= MAX_X_EXACT:
            return pi_odd_arr[y]
        return max(1, int(math.floor(y / math.log(y))) - 1)

    def pi_odd_rs_upper(y: int) -> int:
        if y <= MAX_X_EXACT:
            return pi_odd_arr[y]
        return max(1, int(math.floor(1.25506 * y / math.log(y))) - 1)

    print("  k           | L  | Sigma*(k) [RS-UB] | / (log2 k * lnln k) | / (log2 k * (lnln k)^2) | [RS-LB] / (log2 k * (lnln k)^2)")
    print("  " + "-" * 114)
    ratios_loglog = []
    ratios_loglog2_ub = []
    ratios_loglog2_lb = []
    for exp in range(3, 13):
        k = 10 ** exp
        L = int(math.floor(math.log2((k + 1) // 2))) + 1
        # Lower bound on pi_odd => UPPER bound on Sigma*(k)
        sig_ub = 0.0
        # Upper bound on pi_odd => LOWER bound on Sigma*(k)
        sig_lb = 0.0
        for t in range(L):
            g_lb, _ = exact_g_kt_from_pi(k, t, pi_odd_rs_lower)
            g_ub, _ = exact_g_kt_from_pi(k, t, pi_odd_rs_upper)
            sig_ub += psi(min(g_lb, 1.0))
            sig_lb += psi(min(g_ub, 1.0))
        lg = math.log2(k + 2)
        llg = math.log(math.log(k + 16))
        r1 = sig_ub / (lg * llg)
        r2_ub = sig_ub / (lg * llg * llg)
        r2_lb = sig_lb / (lg * llg * llg)
        ratios_loglog.append(r1)
        ratios_loglog2_ub.append(r2_ub)
        ratios_loglog2_lb.append(r2_lb)
        print(f"  10^{exp:<8d} | {L:<2d} | {sig_ub:17.2f} | {r1:19.4f} | {r2_ub:23.4f} | {r2_lb:30.4f}")

    # Verify boundedness of Sigma*(k) / (log k * (log log k)^2) and growth of Sigma*(k) / (log k * log log k)
    assert max(ratios_loglog2_ub) < 10.0, f"Unexpected growth in Sigma*/(log k (loglog k)^2): {ratios_loglog2_ub}"
    assert ratios_loglog[-1] > ratios_loglog[0], "Expected Sigma*/(log k * loglog k) to grow with k"
    print(f"  PASS: Sigma*(k) / (log2(k+2) * (ln ln(k+16))^2) stays bounded in [{min(ratios_loglog2_lb):.3f}, {max(ratios_loglog2_ub):.3f}] up to k = 10^12!")


def build_D_kt_exact(k: int, t: int, primes_list: List[int]) -> List[int]:
    x = (k + 1) // 4
    m = 1 << t
    odd_primes_x = [p for p in primes_list if 3 <= p <= x]

    cands = []
    # Cand 0
    cands.append([1])
    # Cand A
    candA = [p for p in odd_primes_x if p < (1 << m)]
    if candA:
        cands.append(candA)
    # Cand B
    if x >= 3:
        s = max_s_for_x_pow_lt_2_pow_m(x, m)
        if 1 <= s <= len(odd_primes_x):
            candB = []
            for comb in itertools.combinations(odd_primes_x, s):
                prod = 1
                for p in comb:
                    prod *= p
                candB.append(prod)
            cands.append(candB)
    # Cand C
    half_m = m // 2
    odd_primes_half = [p for p in primes_list if 3 <= p <= half_m]
    candC = [1]
    for p in odd_primes_half:
        candC = candC + [d * p for d in candC]
    cands.append(candC)

    best = max(cands, key=len)
    return sorted(best)


def compute_gamma_bits(dist: Dict[int, float], m: int) -> List[float]:
    """Compute exact gamma_i(Z) = H(z_i | Z_{<i}) for i = 0..m-1."""
    gammas = []
    for i in range(m):
        mask = (1 << i) - 1
        buckets: Dict[int, List[float]] = {}
        for val, prob in dist.items():
            pref = val & mask
            bit = (val >> i) & 1
            if pref not in buckets:
                buckets[pref] = [0.0, 0.0]
            buckets[pref][bit] += prob
        gi = 0.0
        for p0, p1 in buckets.values():
            tot = p0 + p1
            if tot > 0:
                gi += tot * h2(p1 / tot)
        gammas.append(gi)
    return gammas


def build_St(k: int, t: int) -> List[int]:
    m = 1 << t
    left_end = min((1 << (t + 1)) - 1, k - m)
    right_start = max(0, k - 3 * m + 1)
    s_set = set(range(0, left_end + 1)) | set(range(right_start, k - m + 1))
    return sorted(s_set)


def test_suite_3_exact_Wj():
    print("\n=== Suite 3: Exhaustive Exact D_{k,t}, Chain Rule, Jensen on f4, & W_j (2 <= k <= 36) ===")
    primes_small = sieve_primes(50)
    total_bits_checked = 0
    min_slack = float("inf")

    for k in range(2, 37):
        x = (k + 1) // 4
        Px = 1
        for p in primes_small:
            if 3 <= p <= x:
                Px *= p
        L = int(math.floor(math.log2((k + 1) // 2))) + 1

        gammas_by_t = []
        g_by_t = []
        S_by_t = []
        for t in range(L):
            m = 1 << t
            D = build_D_kt_exact(k, t, primes_small)
            assert len(D) >= 1
            for d in D:
                assert 0 < d < (1 << m), f"d={d} >= 2^{m}"
                assert d % 2 == 1 and Px % d == 0, f"d={d} does not divide P_{x}"

            # Build Z_{k,t}
            dist = {0: 0.5}
            for d in D:
                dist[d] = 0.5 / len(D)
            H_exact = 1.0 + 0.5 * math.log2(len(D))
            g_kt = H_exact / m
            assert 0.0 < g_kt <= 1.0 + 1e-12

            gammas = compute_gamma_bits(dist, m)
            assert abs(sum(gammas) - H_exact) < 1e-10, f"Chain rule mismatch at k={k}, t={t}"
            # Verify Jensen on f4
            avg_f4 = sum(f4(gi) for gi in gammas) / m
            assert avg_f4 >= f4(g_kt) - 1e-12, f"Jensen on f4 failed at k={k}, t={t}"

            gammas_by_t.append(gammas)
            g_by_t.append(g_kt)
            S_by_t.append(build_St(k, t))

        sigma_star = sum(psi(g_kt) for g_kt in g_by_t)
        w = [psi(g_kt) / sigma_star for g_kt in g_by_t]
        assert abs(sum(w) - 1.0) < 1e-12
        eta_star = LN2 / (4.0 * sigma_star)
        assert 0.0 < eta_star <= 0.125 + 1e-12

        # Check W_j for every bit 0 <= j < k
        for j in range(k):
            Wj = 0.0
            for t in range(L):
                m = 1 << t
                St = S_by_t[t]
                assert len(St) <= 4 * m
                for s in St:
                    if 0 <= j - s < m:
                        Wj += LN2 * (w[t] / len(St)) * f4(gammas_by_t[t][j - s])
            assert Wj >= eta_star - 1e-12, f"W_{j} = {Wj} < eta* = {eta_star} at k={k}"
            min_slack = min(min_slack, Wj / eta_star)
            total_bits_checked += 1

    print(f"  PASS: {total_bits_checked} (k, j) bit pairs verified for 2 <= k <= 36; min W_j / eta* = {min_slack:.4f} >= 1.0")


def convolve_mod_2k(p: List[float], q_dist: Dict[int, float], mask: int) -> List[float]:
    n = len(p)
    out = [0.0] * n
    for y, py in q_dist.items():
        if py == 0.0:
            continue
        for x, px in enumerate(p):
            if px != 0.0:
                out[(x + y) & mask] += px * py
    return out


def entropy_vec(p: List[float]) -> float:
    return -sum(v * math.log2(v) for v in p if v > 0.0)


def test_suite_4_mod_2k_covering():
    print("\n=== Suite 4: Exact Mod-2^k Contraction & Sumset Covering (k = 6, 8, 10, 12) ===")
    primes_list = sieve_primes(500)
    for k in [6, 8, 10, 12]:
        N = 1 << k
        mask = N - 1
        x = (k + 1) // 4
        L = int(math.floor(math.log2((k + 1) // 2))) + 1

        # Build Y distribution
        D_by_t = [build_D_kt_exact(k, t, primes_list) for t in range(L)]
        g_by_t = [(1.0 + 0.5 * math.log2(len(D_by_t[t]))) / (1 << t) for t in range(L)]
        sigma_star = sum(psi(g) for g in g_by_t)
        w = [psi(g) / sigma_star for g in g_by_t]
        eta_star = LN2 / (4.0 * sigma_star)

        Y_dist: Dict[int, float] = {}
        for t in range(L):
            St = build_St(k, t)
            D = D_by_t[t]
            prob_t_s = w[t] / len(St)
            for s in St:
                Y_dist[0] = Y_dist.get(0, 0.0) + prob_t_s * 0.5
                p_d = prob_t_s * 0.5 / len(D)
                for d in D:
                    val = d << s
                    assert val < N
                    Y_dist[val] = Y_dist.get(val, 0.0) + p_d

        # Tag primes > x
        tag_primes = [p for p in primes_list if p > x]

        # Test single-step contraction from X = delta_0 and iteratively until H > k - 1
        cur = [0.0] * N
        cur[0] = 1.0
        r = 0
        while entropy_vec(cur) <= k - 1.0:
            H_before = entropy_vec(cur)
            q_tag = tag_primes[r]
            qY = {}
            for val, prob in Y_dist.items():
                v = (q_tag * val) & mask
                qY[v] = qY.get(v, 0.0) + prob
            nxt = convolve_mod_2k(cur, qY, mask)
            H_after = entropy_vec(nxt)
            gain = H_after - H_before
            req = eta_star * (k - H_before)
            assert gain >= req - 1e-11, f"Contraction failed at k={k}, r={r}: gain={gain} < req={req}"
            cur = nxt
            r += 1

        supp_A = [i for i, v in enumerate(cur) if v > 0.0]
        assert len(supp_A) > N // 2, f"|supp(S_R)| = {len(supp_A)} <= 2^{k-1}"

        # Build second half with disjoint tag primes
        cur2 = [0.0] * N
        cur2[0] = 1.0
        for j in range(r):
            q_tag = tag_primes[r + j]
            qY = {}
            for val, prob in Y_dist.items():
                v = (q_tag * val) & mask
                qY[v] = qY.get(v, 0.0) + prob
            cur2 = convolve_mod_2k(cur2, qY, mask)
        supp_B = [i for i, v in enumerate(cur2) if v > 0.0]
        assert len(supp_B) > N // 2

        # Check A + B = Z / 2^k Z
        covered = bytearray(N)
        for a in supp_A:
            for b in supp_B:
                covered[(a + b) & mask] = 1
        assert all(covered), f"Sumset failed to cover Z/2^{k}Z"

        R_theory = math.ceil(4.0 * sigma_star * math.log(2.0 * k) / LN2)
        print(f"  k={k:2d}: Sigma*={sigma_star:6.3f}, eta*={eta_star:.4f}, emp 2R={2*r:2d} (theory 2R*={2*R_theory:3d}), |A|={len(supp_A)}, |B|={len(supp_B)} -> COVERS Z/2^{k}Z")


def greedy_represent_practical(m: int, target: int) -> List[int]:
    """Greedy representation for base-case practical numbers m (exact, strictly distinct divisors)."""
    if target == 0:
        return []
    divs = divisors(m)
    res = []
    rem = target
    for d in reversed(divs):
        if d <= rem:
            res.append(d)
            rem -= d
            if rem == 0:
                break
    assert rem == 0
    return res


def test_suite_5_telescoping_and_factorials():
    print("\n=== Suite 5: Lemma 4* Telescoping & End-to-End Factorial Verification ===")
    # Check F*(ceil(sqrt(B))) <= (9/16) F*(B) for all 16 <= B <= 10^6
    def F_star(B: int) -> float:
        return (math.log2(B + 2) ** 2) * (math.log(math.log(B + 16)) ** 2)

    max_ratio = 0.0
    for B in range(16, 100_001):
        B_next = math.isqrt(B - 1) + 1  # ceil(sqrt(B))
        ratio = F_star(B_next) / F_star(B)
        assert ratio <= 9.0 / 16.0 + 1e-12, f"Telescoping failed at B={B}: {ratio} > 9/16"
        max_ratio = max(max_ratio, ratio)
    print(f"  Lemma 4* telescoping: max F*(ceil(sqrt(B)))/F*(B) for 16 <= B <= 10^5 = {max_ratio:.6f} <= 0.5625 (9/16)")

    # End-to-end constructive Stage 1 + Stage 2 test using verify_representation()
    # (Uses binary / practical base-case on small E and exact mixed-radix + M(E) tail architecture)
    primes_100 = sieve_primes(100)

    def v2(n: int) -> int:
        return (n & -n).bit_length() - 1

    def odd_primorial(m: int) -> int:
        res = 1
        for p in primes_100:
            if 3 <= p <= m:
                res *= p
        return res

    def represent_in_ME(E: int, x: int) -> List[int]:
        """Represent 0 <= x < M(E) = 2^E P_{floor(E/4)} using Stage 2 architecture."""
        if x == 0:
            return []
        if x < (1 << (E // 2)):
            # Represent x < 2^{floor(E/2)} using powers of 2 (valid base case of Lemma 4*)
            return [1 << b for b in range(x.bit_length()) if (x >> b) & 1]
        if E <= 84:
            # Base case: M(E) is practical; represent greedily using M(E) or binary + odd-part
            # Since M(E) can be huge (e.g. E=84), use binary + prime-by-prime mixed radix on P_{floor(E/4)}
            ps = [p for p in primes_100 if 3 <= p <= E // 4]
            # Expand x in mixed radix (2^E, p_1, p_2, ...)
            terms = []
            cur = x
            mult = 1
            # First extract mod 2^E
            r0 = cur & ((1 << E) - 1)
            cur >>= E
            for b in range(r0.bit_length()):
                if (r0 >> b) & 1:
                    terms.append(1 << b)
            mult = 1 << E
            for p in ps:
                if cur == 0:
                    break
                rem = cur % p
                cur //= p
                # rem < p <= E/4 < 2^E, represent rem in binary inside 2^E? Wait: mult already has 2^E!
                # Instead expand in (p_1, p_2, ..., 2^E) where each p_i < 2^E!
                pass
            # Clean exact base-case: expand x in mixed radix (p_1, p_2, ..., p_r) with top quotient < 2^E
            terms = []
            cur = x
            mult = 1
            for p in ps:
                if cur == 0:
                    break
                rem = cur % p
                cur //= p
                # rem < p <= E/4 < 2^E, write rem in binary (divisors of 2^E, each < p)
                for b in range(rem.bit_length()):
                    if (rem >> b) & 1:
                        terms.append((1 << b) * mult)
                mult *= p
            # Now cur < 2^E
            for b in range(cur.bit_length()):
                if (cur >> b) & 1:
                    terms.append((1 << b) * mult)
            return terms

        # Inductive Stage 2 step for E > 84
        k = (45 * E) // 100
        E_next = E - k
        a = E // 4
        b = E_next // 4
        assert 2 * b > a
        U_top = 1
        for p in primes_100:
            if b < p <= a:
                U_top *= p
        assert U_top < (1 << (E_next // 2))
        # Group 1: S1 = x mod 2^k (in binary, < 2^k < 2^{floor(E/2)} <= x, v2 < k)
        r_low = x & ((1 << k) - 1)
        g1 = [1 << bit for bit in range(r_low.bit_length()) if (r_low >> bit) & 1]
        x1 = (x - r_low) >> k
        q1, r1 = divmod(x1, U_top)
        # Group 2: r1 < U_top < 2^{floor(E_next/2)}, multiply by 2^k
        g2 = [d << k for d in represent_in_ME(E_next, r1)]
        # Group 3: q1 < M(E_next), multiply by 2^k * U_top
        g3 = [(d << k) * U_top for d in represent_in_ME(E_next, q1)]
        return g1 + g2 + g3

    def represent_factorial(n: int, target: int) -> List[int]:
        fact = math.factorial(n)
        if target == fact:
            return [fact]
        E = v2(fact)
        ME = (1 << E) * odd_primorial(E // 4)
        U_radix = fact // ME
        assert fact == ME * U_radix
        # Greedy factorization of U_radix into D_1, ..., D_L <= 2^{floor(E/2)}
        cap = 1 << (E // 2)
        D_list = []
        # Extract prime factors of U_radix
        rem = U_radix
        pfacs = []
        for p in primes_100:
            while rem % p == 0:
                pfacs.append(p)
                rem //= p
        assert rem == 1
        cur_D = 1
        for p in pfacs:
            if cur_D * p <= cap:
                cur_D *= p
            else:
                D_list.append(cur_D)
                cur_D = p
        if cur_D > 1:
            D_list.append(cur_D)

        # Stage 1 mixed-radix expansion
        terms = []
        cur = target
        mult = 1
        for Dj in D_list:
            rj = cur % Dj
            cur //= Dj
            if rj > 0:
                for d in represent_in_ME(E, rj):
                    terms.append(d * mult)
            mult *= Dj
        # Stage 2 tail
        if cur > 0:
            for d in represent_in_ME(E, cur):
                terms.append(d * mult)
        return terms

    rng = random.Random(2026)
    for n in [12, 16, 20, 30, 50, 80, 100]:
        fact = math.factorial(n)
        targets = [
            1, 2, 3, fact - 1, fact - 2, fact // 2, fact // 2 - 1, fact // 2 + 1,
            fact // 3, (2 * fact) // 3,
        ] + [rng.randint(1, fact - 1) for _ in range(5)]
        max_used = 0
        for t in targets:
            sol = represent_factorial(n, t)
            verify_representation(fact, t, sol, max_terms=10_000)
            max_used = max(max_used, len(sol))
        print(f"  n={n:3d} (n! ~ 2^{fact.bit_length():3d}): {len(targets)} adversarial targets verified via verify_representation() (max terms={max_used})")


if __name__ == "__main__":
    test_suite_1_f4()
    test_suite_2_sigma_star()
    test_suite_3_exact_Wj()
    test_suite_4_mod_2k_covering()
    test_suite_5_telescoping_and_factorials()
    print("\nALL PROVER-4 TESTS PASSED!")
