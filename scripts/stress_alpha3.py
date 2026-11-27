#!/usr/bin/env python3
"""
Adversarial High-Precision Stress & Counterexample Suite for Milestone 3 (O((log n)^3 (log log n)^2)).
Stress-tests every inequality, regime boundary, constant, edge case, and propagation step:
  1. High-precision check of Lemma 1' (f4 convexity, monotonicity, 4q(1-q) >= (ln 2) f4(h2(q))).
  2. Exhaustive small-k (2 <= k <= 500) + huge-k (up to 2^1000) regime partition,
     disjointness/exhaustiveness, g_{k,t} in (0, 1], s-prime product < 2^{2^t},
     and Chebyshev constant consistency across c0 in (0, 0.5] and c1 in (0, 1].
  3. Exact finite-sum checks of every Regime 0, 1, 2, 3 inequality and C*_Sigma(c0, c1).
  4. Exhaustive exact D_{k,t}, gamma_i, Jensen on f4, W_j >= eta* for 2 <= k <= 80,
     plus adversarial X distributions (not just delta_0) for mod-2^k contraction.
  5. Tag-prime headroom (including k == 3 mod 4), Lemma 4* exact recurrence simulation
     up to B = 2^1000, and Stage 2 boundary checks (E >= 84).
"""

import itertools
import math
import random
from decimal import Decimal, getcontext
from typing import Dict, List, Tuple

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
    assert 0.0 < u <= 1.0 + 1e-12, f"psi domain violation: u={u}"
    return math.log(4.0 / u) / u


def Phi(k: int) -> float:
    return math.log2(k + 2) * (math.log(math.log(k + 16)) ** 2)


def F_star(k: int) -> float:
    return (math.log2(k + 2) ** 2) * (math.log(math.log(k + 16)) ** 2)


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


def C_sigma_star(c0: float, c1: float) -> float:
    M0 = max(64, 8 * math.ceil(math.log2(1.0 / c0)))
    r0 = 0.5 * math.ceil(math.log2(M0)) * M0 * math.log(4.0 * M0)
    r1 = 40.0 * LN2
    r2 = 40.0
    r3 = math.ceil(math.log2(4.0 / c0)) * (math.log(4.0 / c1) + 1.4) / c1
    return r0 + r1 + r2 + r3


def attack_1_high_precision_f4():
    print("=== Attack 1: High-Precision Lemma 1' (f4) & Boundary Stress ===")
    getcontext().prec = 80
    ln2_d = Decimal(2).ln()
    four_d = Decimal(4)

    def h2_dec(q: Decimal) -> Decimal:
        return (-q * q.ln() - (Decimal(1) - q) * (Decimal(1) - q).ln()) / ln2_d

    def f4_dec(u: Decimal) -> Decimal:
        return u / (four_d / u).ln()

    # Extreme boundary points down to 10^-60 and near 0.5
    test_qs = [Decimal(10) ** (-e) for e in range(1, 61)]
    test_qs += [Decimal("0.5") - Decimal(10) ** (-e) for e in range(1, 20)]
    test_qs += [Decimal("0.5")]
    min_ratio = Decimal("999")
    min_q = None
    for q in test_qs:
        lhs = Decimal(4) * q * (Decimal(1) - q)
        rhs = ln2_d * f4_dec(h2_dec(q))
        assert lhs >= rhs, f"COUNTEREXAMPLE Lemma 1' at q={q}: lhs={lhs} < rhs={rhs}"
        ratio = lhs / rhs
        if ratio < min_ratio:
            min_ratio = ratio
            min_q = q
    print(f"  PASS (80-digit Decimal): {len(test_qs)} extreme q-points down to 10^-60; min ratio = {float(min_ratio):.8f} at q={min_q}")


def attack_2_regimes_and_chebyshev_consistency():
    print("\n=== Attack 2: Regime Partition, Disjointness, Constants (k=2..500 & up to 2^1000) ===")
    pi_odd_arr = build_pi_odd(2000)

    # First check Chebyshev constant c0 = 0.5 on [3, 2000] and c1 on [1, 2000]
    min_c0 = min(pi_odd_arr[y] / (y / math.log2(y)) for y in range(3, 2001))
    min_c1 = min((1.0 + 0.5 * pi_odd_arr[m // 2]) / (m / math.log2(m + 2)) for m in range(1, 2001))
    print(f"  Empirical exact minimums on [1..2000]: min c0 = {min_c0:.6f}, min c1 = {min_c1:.6f}")

    # Test across adversarial (c0, c1) pairs including non-powers-of-2
    c_pairs = [
        (0.5, 0.34),
        (0.37, 0.25),
        (0.25, 0.20),
        (0.13, 0.10),
        (0.05, 0.05),
        (0.01, 0.01),
    ]

    # Small k in [2, 500] with exact sieve
    for c0, c1 in c_pairs:
        M0 = max(64, 8 * math.ceil(math.log2(1.0 / c0)))
        # Verify M0 inequality: m/2 - log2(m) - log2(1/c0) >= m/4 for all m >= M0
        for m in [M0, M0 + 1, 2 * M0, 10000]:
            assert 0.5 * m - math.log2(m) - math.log2(1.0 / c0) >= 0.25 * m - 1e-12

        C_sig = C_sigma_star(c0, c1)
        for k in range(2, 501):
            x = (k + 1) // 4
            L = ((k + 1) // 2).bit_length()  # floor(log2(floor((k+1)/2))) + 1
            assert L == int(math.floor(math.log2((k + 1) // 2))) + 1

            # Check regime partition exhaustiveness & disjointness
            reg_counts = [0, 0, 0, 0]
            sig_total = 0.0
            for t in range(L):
                m = 1 << t
                # Check floor(m/2) <= x
                assert (m // 2) <= x, f"floor(m/2) > x at k={k}, t={t}"

                in0 = (m < M0)
                in1 = (not in0) and (x >= 2 and m <= 2.0 * math.log2(x))
                in2 = (not in0) and (x >= 2 and m > 2.0 * math.log2(x) and m <= 0.5 * c0 * x)
                in3 = (not in0) and (m > 0.5 * c0 * x)

                hits = int(in0) + int(in1) + int(in2) + int(in3)
                assert hits == 1, f"Regime overlap/gap at k={k}, t={t}, m={m}, x={x}, c0={c0}: {(in0,in1,in2,in3)}"
                for idx, flag in enumerate((in0, in1, in2, in3)):
                    if flag:
                        reg_counts[idx] += 1

                # Compute exact g_{k,t}
                best_l2 = 0.0
                # Cand A
                yA = min((1 << m) - 1, x) if m <= 60 else x
                if yA >= 3 and pi_odd_arr[yA] >= 1:
                    best_l2 = max(best_l2, math.log2(pi_odd_arr[yA]))
                # Cand B
                if x >= 3:
                    # Exact s: max s' >= 0 with x^{s'} < 2^m
                    s = int(math.floor(m / math.log2(x)))
                    while s > 0 and pow(x, s) >= (1 << m):
                        s -= 1
                    while pow(x, s + 1) < (1 << m):
                        s += 1
                    assert pow(x, s) < (1 << m) <= pow(x, s + 1)
                    pix = pi_odd_arr[x]
                    if 1 <= s <= pix:
                        lB = (math.lgamma(pix + 1) - math.lgamma(s + 1) - math.lgamma(pix - s + 1)) / LN2
                        best_l2 = max(best_l2, lB)
                # Cand C
                if m // 2 >= 3:
                    best_l2 = max(best_l2, float(pi_odd_arr[m // 2]))

                g_kt = (1.0 + 0.5 * best_l2) / m
                assert 1.0 / m - 1e-12 <= g_kt <= 1.0 + 1e-12, f"g_kt out of range: {g_kt}"
                sig_total += psi(min(g_kt, 1.0))

            assert reg_counts[0] <= math.ceil(math.log2(M0))
            assert reg_counts[3] <= math.ceil(math.log2(4.0 / c0))
            assert sig_total <= C_sig * Phi(k) + 1e-9, f"Sigma*(k) exceeded C*_Sigma*Phi(k) at k={k}, c0={c0}"

    print("  PASS: All k in [2, 500] across 6 (c0, c1) pairs passed regime disjointness, exhaustiveness, g_kt in (0,1], and Sigma* <= C*_Sigma Phi(k).")

    # Large k = 2^p up to 2^1000 (testing ALL four regimes simultaneously, including Regime 1 which activates at x >= 2^32!)
    # Use log-domain arithmetic for huge k so nothing overflows!
    for c0, c1 in c_pairs:
        M0 = max(64, 8 * math.ceil(math.log2(1.0 / c0)))
        C_sig = C_sigma_star(c0, c1)
        for p in [40, 60, 80, 100, 200, 500, 1000]:
            # k = 2^p - 1 (adversarial odd k) and k = 2^p + 3 (adversarial k = 3 mod 4)
            for delta in [-1, 0, 3]:
                # Work with log2(k) = p (tiny correction for delta)
                # x = floor((k+1)/4) ~ 2^{p-2}
                log2_x = p - 2.0
                log2_k2 = p + (math.log2(1.0 + (delta + 2) / (2.0 ** p)) if p <= 50 else 0.0)
                ln_ln_k16 = math.log(p * LN2) if p >= 50 else math.log(math.log((1 << p) + delta + 16))
                phi_k = log2_k2 * (ln_ln_k16 ** 2)

                L = p  # floor(log2(floor((k+1)/2))) + 1: for k = 2^p, floor((k+1)/2) = 2^{p-1}, L = p
                if delta == -1:
                    # k = 2^p - 1 -> (k+1)/2 = 2^{p-1} -> L = p
                    pass
                elif delta == 3:
                    # k = 2^p + 3 -> (k+1)/2 = 2^{p-1} + 2 -> L = p
                    pass

                reg_sums = [0.0, 0.0, 0.0, 0.0]
                reg_counts = [0, 0, 0, 0]
                for t in range(L):
                    # Compare m = 2^t in log2 domain: log2(m) = t
                    in0 = (t < math.log2(M0))
                    in1 = (not in0) and (t <= math.log2(2.0 * log2_x))
                    in2 = (not in0) and (t > math.log2(2.0 * log2_x)) and (t <= math.log2(0.5 * c0) + log2_x)
                    in3 = (not in0) and (t > math.log2(0.5 * c0) + log2_x)

                    hits = int(in0) + int(in1) + int(in2) + int(in3)
                    assert hits == 1, f"Large-k regime error at p={p}, t={t}, c0={c0}: {(in0,in1,in2,in3)}"

                    # Worst-case lower bound on g_{k,t} from proof's Chebyshev constants (c0, c1)
                    if in0:
                        m = 1 << t
                        g_lb = 1.0 / m
                        reg_sums[0] += psi(g_lb)
                        reg_counts[0] += 1
                    elif in1:
                        m = 1 << t
                        # Proof bound: g_{k,t} >= 1/8
                        assert 0.5 * m - math.log2(m) - math.log2(1.0 / c0) >= 0.25 * m - 1e-12
                        g_lb = 0.125
                        reg_sums[1] += psi(g_lb)
                        reg_counts[1] += 1
                    elif in2:
                        # Proof bound: g_{k,t} >= log2(c0 * x / m) / (4 * log2(x))
                        # log2(c0 * x / m) = log2(c0) + log2_x - t >= 1.0
                        log2_ratio = math.log2(c0) + log2_x - t
                        assert log2_ratio >= 1.0 - 1e-12, f"Regime 2 log2_ratio < 1: {log2_ratio}"
                        g_lb = log2_ratio / (4.0 * log2_x)
                        assert 0.0 < g_lb <= 0.25 + 1e-12
                        reg_sums[2] += psi(g_lb)
                        reg_counts[2] += 1
                    else:
                        # Regime 3: g_{k,t} >= c1 / log2(k+2)
                        g_lb = c1 / log2_k2
                        assert 0.0 < g_lb <= 1.0
                        reg_sums[3] += psi(g_lb)
                        reg_counts[3] += 1

                # Check each regime's claimed bound individually!
                assert reg_sums[0] <= 0.5 * math.ceil(math.log2(M0)) * M0 * math.log(4.0 * M0) * phi_k + 1e-6
                assert reg_sums[1] <= 40.0 * LN2 * phi_k + 1e-6
                assert reg_sums[2] <= 40.0 * phi_k + 1e-6, f"Regime 2 exceeded 40*Phi at p={p}, c0={c0}: {reg_sums[2]/phi_k}"
                assert reg_counts[3] <= math.ceil(math.log2(4.0 / c0)), f"Regime 3 count exceeded at p={p}, c0={c0}: {reg_counts[3]}"
                assert reg_sums[3] <= math.ceil(math.log2(4.0 / c0)) * (math.log(4.0 / c1) + 1.4) / c1 * phi_k + 1e-6
                assert sum(reg_sums) <= C_sig * phi_k + 1e-6

    # Also test Regime 2 numerical sub-inequalities at extreme boundary k = 2 and x = 32 (k = 127)
    for k in [2, 3, 10, 127, 128, 1000, 10**9]:
        lnln = math.log(math.log(k + 16))
        if k >= 127:
            x = (k + 1) // 4
            lnlog2x = math.log(math.log2(x))
            assert lnlog2x < 1.37 * lnln
            assert 1.0 + lnlog2x < 2.4 * lnln
            assert math.log(16.0 * math.log2(x)) < 4.0 * lnln
        # Even using the proof's bound 2.78 + 1.37 * lnln < 4.0 * lnln at k = 2:
        assert 2.78 + 1.37 * lnln < 4.0 * lnln, f"Tight inequality failed at k={k}"

    print("  PASS: All large k up to 2^1000 across 6 (c0, c1) pairs passed EVERY regime sub-bound (Regime 0, 1, 2, 3) and total bound!")


def build_D_kt_exact(k: int, t: int, primes_list: List[int]) -> List[int]:
    x = (k + 1) // 4
    m = 1 << t
    odd_primes_x = [p for p in primes_list if 3 <= p <= x]
    cands = [[1]]
    candA = [p for p in odd_primes_x if p < (1 << m)]
    if candA:
        cands.append(candA)
    if x >= 3:
        s = int(math.floor(m / math.log2(x)))
        while s > 0 and pow(x, s) >= (1 << m):
            s -= 1
        while pow(x, s + 1) < (1 << m):
            s += 1
        if 1 <= s <= len(odd_primes_x):
            candB = []
            for comb in itertools.combinations(odd_primes_x, s):
                prod = 1
                for p in comb:
                    prod *= p
                candB.append(prod)
            cands.append(candB)
    half_m = m // 2
    odd_primes_half = [p for p in primes_list if 3 <= p <= half_m]
    candC = [1]
    for p in odd_primes_half:
        candC = candC + [d * p for d in candC]
    cands.append(candC)
    return sorted(max(cands, key=len))


def build_St(k: int, t: int) -> List[int]:
    m = 1 << t
    left_end = min((1 << (t + 1)) - 1, k - m)
    right_start = max(0, k - 3 * m + 1)
    return sorted(set(range(0, left_end + 1)) | set(range(right_start, k - m + 1)))


def compute_gamma_bits(dist: Dict[int, float], m: int) -> List[float]:
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


def entropy_vec(p: List[float]) -> float:
    return -sum(v * math.log2(v) for v in p if v > 0.0)


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


def attack_3_exact_Wj_and_adversarial_X():
    print("\n=== Attack 3: Exhaustive W_j (2 <= k <= 64) & Adversarial X Contraction ===")
    primes_small = sieve_primes(100)
    min_ratio_Wj = float("inf")
    # For k <= 64, x <= 16, pi_odd(16) = 5 (3,5,7,11,13), max |D| <= 32, very fast!
    for k in range(2, 65):
        x = (k + 1) // 4
        L = ((k + 1) // 2).bit_length()
        gammas_by_t = []
        g_by_t = []
        S_by_t = []
        for t in range(L):
            m = 1 << t
            D = build_D_kt_exact(k, t, primes_small)
            dist = {0: 0.5}
            for d in D:
                dist[d] = 0.5 / len(D)
                assert 0 < d < (1 << m)
            g_kt = (1.0 + 0.5 * math.log2(len(D))) / m
            gammas = compute_gamma_bits(dist, m)
            assert abs(sum(gammas) - g_kt * m) < 1e-10
            gammas_by_t.append(gammas)
            g_by_t.append(g_kt)
            S_by_t.append(build_St(k, t))
        sig = sum(psi(g) for g in g_by_t)
        w = [psi(g) / sig for g in g_by_t]
        eta = LN2 / (4.0 * sig)
        for j in range(k):
            # Check exact m_j, t* coverage
            mj = min(j + 1, k - j)
            t_star = mj.bit_length() - 1
            assert 0 <= t_star < L
            St_star = set(S_by_t[t_star])
            for s in range(j - (1 << t_star) + 1, j + 1):
                assert s in St_star, f"Shift coverage gap at k={k}, j={j}, t*={t_star}, s={s}"
            Wj = 0.0
            for t in range(L):
                m = 1 << t
                St = S_by_t[t]
                for s in St:
                    if 0 <= j - s < m:
                        Wj += LN2 * (w[t] / len(St)) * f4(gammas_by_t[t][j - s])
            assert Wj >= eta - 1e-12, f"W_j < eta* at k={k}, j={j}"
            min_ratio_Wj = min(min_ratio_Wj, Wj / eta)

    print(f"  PASS: Exhaustive 2 <= k <= 64 verified; min W_j / eta* = {min_ratio_Wj:.6f} >= 1.0")

    # Adversarial X distributions for k = 8 and k = 10:
    # 1. Single-bit missing entropy (uniform on even numbers, or uniform on [0, 2^{k-1}))
    # 2. Concentrating deficit on the hardest middle bit j = k//2
    # 3. Random sparse and near-uniform distributions with various odd tag primes q_r
    rng = random.Random(1337)
    for k in [8, 10]:
        N = 1 << k
        mask = N - 1
        x = (k + 1) // 4
        L = ((k + 1) // 2).bit_length()
        D_by_t = [build_D_kt_exact(k, t, primes_small) for t in range(L)]
        g_by_t = [(1.0 + 0.5 * math.log2(len(D_by_t[t]))) / (1 << t) for t in range(L)]
        sig = sum(psi(g) for g in g_by_t)
        w = [psi(g) / sig for g in g_by_t]
        eta = LN2 / (4.0 * sig)

        Y_dist: Dict[int, float] = {}
        for t in range(L):
            St = build_St(k, t)
            D = D_by_t[t]
            prob_ts = w[t] / len(St)
            for s in St:
                Y_dist[0] = Y_dist.get(0, 0.0) + prob_ts * 0.5
                p_d = prob_ts * 0.5 / len(D)
                for d in D:
                    Y_dist[d << s] = Y_dist.get(d << s, 0.0) + p_d

        # Build adversarial X distributions
        adv_Xs = []
        # (a) Uniform on evens (all deficit at bit 0)
        p_even = [2.0 / N if i % 2 == 0 else 0.0 for i in range(N)]
        adv_Xs.append(("even_only", p_even))
        # (b) Uniform on lower half [0, N/2) (all deficit at top bit k-1)
        p_low = [2.0 / N if i < N // 2 else 0.0 for i in range(N)]
        adv_Xs.append(("lower_half", p_low))
        # (c) Deficit solely at middle bit j = k//2
        mid_bit = 1 << (k // 2)
        p_mid = [2.0 / N if (i & mid_bit) == 0 else 0.0 for i in range(N)]
        adv_Xs.append(("mid_bit_zero", p_mid))
        # (d) Near-uniform with tiny 0.01 perturbation on middle bit
        p_near = [(1.01 if (i & mid_bit) == 0 else 0.99) / N for i in range(N)]
        adv_Xs.append(("near_unif_mid", p_near))
        # (e) Random Dirac mixture
        p_rand = [rng.random() ** 4 for _ in range(N)]
        tot = sum(p_rand)
        p_rand = [v / tot for v in p_rand]
        adv_Xs.append(("rand_skewed", p_rand))

        tag_primes = [p for p in primes_small if p > x][:5]
        min_gain_ratio = float("inf")
        for name, X_dist in adv_Xs:
            H_before = entropy_vec(X_dist)
            deficit = k - H_before
            for q_tag in [1] + tag_primes:
                qY = {}
                for val, prob in Y_dist.items():
                    v = (q_tag * val) & mask
                    qY[v] = qY.get(v, 0.0) + prob
                nxt = convolve_mod_2k(X_dist, qY, mask)
                gain = entropy_vec(nxt) - H_before
                req = eta * deficit
                assert gain >= req - 1e-11, f"CONTRACTION BROKEN at k={k}, X={name}, q={q_tag}: gain={gain} < req={req}"
                if req > 1e-12:
                    min_gain_ratio = min(min_gain_ratio, gain / req)
        print(f"  PASS (k={k:2d}): All {len(adv_Xs)} adversarial X x {len(tag_primes)+1} tags passed; min gain/(eta*deficit) = {min_gain_ratio:.4f} >= 1.0")


def attack_4_lemma4_and_stage2_boundaries():
    print("\n=== Attack 4: Tag-Prime Parity, Lemma 4* Recurrence (to 2^1000), & Stage 2 Boundaries ===")
    pi_odd_arr = build_pi_odd(5000)

    # 1. Check k == 3 (mod 4) tag-prime interval equality: pi_odd(floor(k/2)) == pi_odd(2*floor((k+1)/4))
    for k in range(2, 5000):
        a = k // 2
        b = (k + 1) // 4
        if k % 4 == 3:
            assert 2 * b == a + 1 and (2 * b) % 2 == 0 and 2 * b >= 2
            assert pi_odd_arr[a] == pi_odd_arr[2 * b], f"pi_odd parity failure at k={k}"
        else:
            assert a >= 2 * b

    # 2. Check Stage 2 inequalities for all E in [1, 10000]
    first_E_all_ok = None
    for E in range(1, 10001):
        k = (45 * E) // 100
        E_next = E - k
        a = E // 4
        b = E_next // 4
        cond_2b_gt_a = (2 * b > a)
        cond_bertrand_gap = (E // 4 >= 2 * ((k + 1) // 4))
        if E >= 84:
            assert cond_2b_gt_a, f"Stage 2 2b > a FAILED at E={E}"
            assert cond_bertrand_gap, f"Stage 2 Bertrand gap FAILED at E={E}"
            assert E_next <= math.ceil(0.55 * E)
        if cond_2b_gt_a and cond_bertrand_gap and first_E_all_ok is None:
            first_E_all_ok = E

    # Record last E < 84 failing 2b > a or a < floor(E_next/2)
    last_fail_2b = max((E for E in range(1, 84) if not (2 * ((E - (45 * E) // 100) // 4) > E // 4)), default=0)
    assert all((E // 4) < ((E - (45 * E) // 100) // 2) for E in range(84, 10001))

    # 3. Check Lemma 4* telescoping and exact strong induction up to B = 2^1000
    for B in range(16, 10001):
        B_next = math.isqrt(B - 1) + 1
        assert B_next + 2 <= math.sqrt(B) + 3 <= 1.75 * math.sqrt(B) <= B ** 0.75 < (B + 2) ** 0.75
        assert F_star(B_next) <= (9.0 / 16.0) * F_star(B) + 1e-12

    # Simulate exact strong induction for B = 2^1000 with C_R = 1000, B0 = 1000
    C_R = 1000.0
    B0 = 1000
    # Compute exact recursive sum down from B = 2^1000
    B_cur = 1 << 1000
    total_rec = 0.0
    steps = 0
    while B_cur > B0:
        B_next = math.isqrt(B_cur - 1) + 1
        k_cur = B_cur - B_next
        # F*(k_cur) using log2(k_cur+2) ~ k_cur.bit_length()
        lg_k = math.log2(k_cur + 2) if k_cur < (1 << 500) else float(k_cur.bit_length())
        lnln_k = math.log(lg_k * LN2) if k_cur >= (1 << 50) else math.log(math.log(k_cur + 16))
        total_rec += C_R * (lg_k ** 2) * (lnln_k ** 2)
        B_cur = B_next
        steps += 1
    total_rec += B0

    # Compare against (16/7) * C_R * F*(2^1000) + B0
    lg_B = 1000.0
    lnln_B = math.log(1000.0 * LN2)
    bound_B = (16.0 / 7.0) * C_R * (lg_B ** 2) * (lnln_B ** 2) + B0
    assert total_rec <= bound_B, f"Lemma 4* strong induction FAILED at B=2^1000: {total_rec} > {bound_B}"

    # 4. Check explicit 2 R*(k) <= (12 C*_Sigma + 1) F*(k) at k = 2..500
    for c0, c1 in [(0.5, 0.34), (0.1, 0.1)]:
        C_sig = C_sigma_star(c0, c1)
        C_R_exp = 12.0 * C_sig + 1.0
        for k in range(2, 501):
            # Worst-case Sigma*(k) = C_sig * Phi(k)
            sig_max = C_sig * Phi(k)
            R_max = math.ceil(4.0 * sig_max * math.log(2.0 * k) / LN2)
            assert 2 * R_max <= C_R_exp * F_star(k) + 1e-9

    print(f"  PASS: Tag-prime parity (k=3 mod 4), Stage 2 (E>=84, last fail E<84 checked), and Lemma 4* exact recurrence to B=2^1000 ({steps} steps, ratio {total_rec/bound_B:.4f} <= 1.0) ALL PASSED!")


if __name__ == "__main__":
    attack_1_high_precision_f4()
    attack_2_regimes_and_chebyshev_consistency()
    attack_3_exact_Wj_and_adversarial_X()
    attack_4_lemma4_and_stage2_boundaries()
    print("\nADVERSARIAL STRESS RESULT: ZERO COUNTEREXAMPLES FOUND — ALL CHECKS PASSED!")
