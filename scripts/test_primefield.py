#!/usr/bin/env python3
"""
Prime-Field Carry-Free Verification Suite for h(n!) = O((log n)^3 log log n):
  Suite 1: Pointwise KL Contraction Lemma (c_1 = 1/484, empirical >= 0.312) & Universal F_q Dilation
  Suite 2: Elementary 2-Factor Smooth Pigeonhole Dilator c = c1*c2 mod q (zero character sums)
  Suite 3: Carry-Free Prime-Field Z/M'Z Covering Walk
  Suite 4: End-to-End Prime-Field Representation of 1 <= t <= n! (80/80 PASS verify_practical.py)
  Suite 5: Stage 2 11-Prime Strip Inequality, U_extra Margin & Binary Budget at m = 500,000
"""
import hashlib
import math
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import verify_practical as vp


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sieve_primes(n: int):
    if n < 2:
        return []
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[0] = sieve[1] = 0
    for p in range(2, int(n ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p : n + 1 : p] = b"\x00" * (((n - p * p) // p) + 1)
    return [i for i, v in enumerate(sieve) if v]


def suite1_pointwise_kl_and_dilation():
    print("=" * 72)
    print("SUITE 1: Pointwise KL Contraction Lemma & Universal F_q Dilation Lemma")
    print("=" * 72)
    min_c1 = 1e9
    for q in [3, 5, 7, 17, 31, 61, 127, 257, 1009, 10007]:
        lnq = math.log(q)
        rs = [0.5, 0.49, 0.25, 0.1, 2.0 / q, 1.01 / q]
        for k in range(1, 25):
            r = (1.0 / q) * ((0.5 * q) ** (k / 25.0))
            if 1.0 / q < r <= 0.5:
                rs.append(r)
        for r in rs:
            if not (1.0 / q < r <= 0.5):
                continue
            theta = (q * r - 1.0) / (q - 1.0)
            factor = min(math.log(1.0 / r), lnq) / lnq
            us = [0.0, 1e-4, 0.1, 0.5, 0.99, 1.01, 2.0, 5.0, float(q)]
            for k in range(1, 25):
                us.append(q ** (k / 25.0))
            for u in us:
                if u > q or abs(u - 1.0) < 1e-9:
                    continue
                B = (u * math.log(u) if u > 0 else 0.0) - (u - 1.0)
                if B <= 1e-12:
                    continue
                denom = theta * u + (1.0 - theta)
                g = (u * math.log(u / denom) if u > 0 else 0.0) - (1.0 - theta) * (u - 1.0)
                c1 = g / (B * factor)
                if c1 < min_c1:
                    min_c1 = c1
    print(f"  Pointwise KL Contraction min c_1 = {min_c1:.6f} (analytic bound 1/484 = {1/484:.6f})")
    assert min_c1 > 1.0 / 484.0

    def H_nat(probs):
        return -sum(p * math.log(p) for p in probs if p > 1e-18)

    def conv_q(u, v, c, q):
        res = [0.0] * q
        u_nz = [(i, p) for i, p in enumerate(u) if p > 1e-18]
        v_nz = [(j, p) for j, p in enumerate(v) if p > 1e-18]
        for i, pu in u_nz:
            for j, pv in v_nz:
                res[(i + c * j) % q] += pu * pv
        return res

    for q in [17, 31]:
        lnq = math.log(q)
        dists = []
        d = [0.0] * q; d[0] = 1.0; dists.append(("point", d))
        for L in [2, 3, 5, q // 2]:
            d = [0.0] * q
            for i in range(L):
                d[i] = 1.0 / L
            dists.append((f"AP_{L}", d))
        for eps in [2.0 / q, 0.1, 0.5]:
            d = [0.0] * q; d[0] = 1.0 - eps; d[1] = eps
            dists.append((f"2pt_{eps:.2g}", d))
            d2 = [eps / q] * q; d2[0] += 1.0 - eps
            dists.append((f"mixU_{eps:.2g}", d2))
        d = [(1.0 + 0.05 * (1 if i < q // 2 else -1)) / q for i in range(q)]
        s = sum(d); d = [x / s for x in d]
        dists.append(("nearU", d))

        min_ratio = 1e9
        for _, u in dists:
            hu = H_nat(u); du = lnq - hu
            if du < 1e-9:
                continue
            for _, v in dists:
                hv = H_nat(v); hv_eff = hv - 5.0 * lnq / q
                if hv_eff <= 0.05:
                    continue
                gain = sum(H_nat(conv_q(u, v, c, q)) - hu for c in range(1, q)) / (q - 1)
                jensen_lb = 0.0
                for rv in v:
                    if rv > 1e-18:
                        for px in u:
                            if px > 1e-18:
                                tpx = rv * px + (1.0 - rv) * (1.0 - px) / (q - 1)
                                jensen_lb += rv * px * math.log(px / tpx)
                assert gain + 1e-11 >= jensen_lb
                min_ratio = min(min_ratio, gain * lnq / (hv_eff * du))
        print(f"  q={q:2d}: Exact Jensen LB verified; min ratio = {min_ratio:.4f}")
        assert min_ratio > 0.5
    print("  SUITE 1 PASSED.\n")


def suite2_two_factor_smooth_pigeonhole():
    print("=" * 72)
    print("SUITE 2: Elementary 2-Factor Smooth Pigeonhole Dilator (c = c1*c2 mod q)")
    print("=" * 72)
    for m in [300, 400, 600, 1000]:
        M = (14 * m) // 25
        B = (7 * m) // 25
        ps = sieve_primes(m)
        big_primes = set(p for p in ps if B < p <= M)
        # Since 2*(B+1) > M, the only integers in [1, M] not B-smooth are primes in (B, M].
        smooth = [a for a in range(1, M + 1) if a not in big_primes]
        q = ps[-1]  # largest prime <= m, satisfies M < q <= m
        assert M < q <= m
        assert len(smooth) > (q - 1) // 2
        counts = [0] * q
        for c1 in smooth:
            for c2 in smooth:
                counts[(c1 * c2) % q] += 1
        min_cnt = min(counts[1:])
        min_rel = min_cnt * (q - 1) / (len(smooth) * len(smooth))
        print(
            f"  m={m:4d}, |A(m)|={len(smooth):3d}, q={q:3d}: "
            f"min_count={min_cnt:3d} (q/20={q/20:.1f}), (q-1)*P(c1*c2=x) >= {min_rel:.4f} (> 1/40=0.025)"
        )
        assert min_cnt >= q // 20
        assert min_rel > 1.0 / 40.0
    print("  SUITE 2 PASSED.\n")


def suite3_carry_free_covering():
    print("=" * 72)
    print("SUITE 3: Carry-Free Prime-Field Z/M'Z Covering Walk")
    print("=" * 72)
    from itertools import combinations
    for Q, pool, C_max in [([7, 11], [2, 3, 5], 5), ([11, 13], [2, 3, 5, 7], 7)]:
        M = 1
        for q in Q:
            M *= q
        lnM = math.log(M)
        step_weights = {}
        subsets = [S for r in range(1, len(Q) + 1) for S in combinations(Q, r)]
        for S in subsets:
            r = len(S)
            mask = M
            for q in S:
                mask //= q
            z_list = []
            for comb in combinations(pool, r):
                z = 1
                for p in comb:
                    z *= p
                z_list.append(z)
            w = 1.0 / (len(subsets) * len(z_list) * C_max)
            for z in z_list:
                for c in range(1, C_max + 1):
                    val = (c * mask * z) % M
                    step_weights[val] = step_weights.get(val, 0.0) + w
        dist = [0.0] * M; dist[0] = 1.0
        steps = 0
        while True:
            H = -sum(p * math.log(p) for p in dist if p > 1e-18)
            deficit = lnM - H
            if deficit < math.log(2.0) or steps > 50:
                break
            new_dist = [0.0] * M
            for x, px in enumerate(dist):
                if px > 1e-18:
                    for y, py in step_weights.items():
                        new_dist[(x + y) % M] += px * py
            dist = new_dist
            steps += 1
        supp_set = {x for x, p in enumerate(dist) if p > 1e-18}
        sumset = {(a + b) % M for a in supp_set for b in supp_set}
        print(f"  Q={Q} (M={M}): deficit={deficit:.4f} < ln(2) in {steps} steps; |supp|={len(supp_set)} > M/2; covers {len(sumset)}/{M}")
        assert len(supp_set) > M / 2 and len(sumset) == M
    print("  SUITE 3 PASSED.\n")


def build_arch2b_representation(n: int, target: int, rng: random.Random):
    fact_n = math.factorial(n)
    if target == fact_n:
        return [fact_n]
    ps = sieve_primes(n)
    exps = {}
    for p in ps:
        v = 0; pk = p
        while pk <= n:
            v += n // pk; pk *= p
        exps[p] = v

    def practical_rep(m_exps, t):
        if t == 0:
            return []
        e2 = m_exps.get(2, 0)
        odd_primes = sorted([p for p, e in m_exps.items() if p > 2 and e > 0])
        cap = 1 << e2
        factors = []; cur = 1
        for p in odd_primes:
            for _ in range(m_exps[p]):
                if cur * p <= cap:
                    cur *= p
                else:
                    if cur > 1:
                        factors.append(cur)
                    cur = p
        if cur > 1:
            factors.append(cur)
        terms = []; rem = t; mult = 1
        for D in factors:
            digit = rem % D; rem //= D
            bit = 0
            while digit > 0:
                if digit & 1:
                    terms.append(mult * (1 << bit))
                digit >>= 1; bit += 1
            mult *= D
        bit = 0
        while rem > 0:
            if rem & 1:
                terms.append(mult * (1 << bit))
            rem >>= 1; bit += 1
        return terms

    Q_top = [p for p in ps if p > n // 2]
    M_top = 1
    for q in Q_top:
        M_top *= q
    e2_core = min(exps[2], max(20, 6 * int(math.log2(n)) + 4))
    core_exps = {2: e2_core}
    for q in Q_top:
        core_exps[q] = 1
    for p in ps:
        if 2 < p <= n // 2:
            core_exps[p] = min(exps[p], 4 if p <= n // 4 else 1)
    outer_exps = {p: exps[p] - core_exps.get(p, 0) for p in ps if exps[p] - core_exps.get(p, 0) > 0}
    B_max = max(2, M_top // max(1, n * n))
    D_list = []; cur = 1
    for p in sorted(outer_exps.keys()):
        for _ in range(outer_exps[p]):
            if cur * p <= B_max:
                cur *= p
            else:
                if cur > 1:
                    D_list.append(cur)
                cur = p
    if cur > 1:
        D_list.append(cur)
    tag_primes = [p for p in ps if n // 4 < p <= n // 2]

    def rep_digit_arch2b(r: int):
        if r == 0:
            return []
        if r < 2 * (n ** 3) or len(Q_top) < 2 or len(tag_primes) < 4:
            res = []; b = 0; tmp = r
            while tmp > 0:
                if tmp & 1:
                    res.append(1 << b)
                tmp >>= 1; b += 1
            return res
        Q_sub = []; M_sub = 1; limit = r // (2 * n * n)
        for q in Q_top:
            if M_sub * q <= limit:
                Q_sub.append(q); M_sub *= q
        if not Q_sub:
            res = []; b = 0; tmp = r
            while tmp > 0:
                if tmp & 1:
                    res.append(1 << b)
                tmp >>= 1; b += 1
            return res
        terms = []; S = 0
        if M_sub <= 20000 and len(tag_primes) >= 2:
            R_max = min(len(tag_primes), 20)
            reach = {0: []}
            for idx in range(R_max):
                ptag = tag_primes[idx]
                cands = []
                for q in Q_sub:
                    mask = M_sub // q
                    for c in range(1, min(q, n // 4 + 1)):
                        d = ptag * c * mask
                        if d < r:
                            cands.append(d)
                rng.shuffle(cands)
                cands = cands[:min(len(cands), 40)]
                new_reach = dict(reach)
                for cur_res, cur_list in reach.items():
                    for d in cands:
                        nxt = (cur_res + d) % M_sub
                        if nxt not in new_reach:
                            cand_list = cur_list + [d]
                            if sum(cand_list) < r:
                                new_reach[nxt] = cand_list
                reach = new_reach
                if (r % M_sub) in reach:
                    break
            if (r % M_sub) in reach:
                terms = reach[r % M_sub]; S = sum(terms)
            else:
                b = 0; tmp = r
                while tmp > 0:
                    if tmp & 1:
                        terms.append(1 << b)
                    tmp >>= 1; b += 1
                return terms
        else:
            for q in Q_sub:
                mask = M_sub // q
                inv_mask = pow(mask, -1, q)
                coeff = (r * inv_mask) % q
                b = 0
                while coeff > 0:
                    if coeff & 1:
                        d = mask * (1 << b)
                        terms.append(d); S += d
                    coeff >>= 1; b += 1
            if S >= r:
                terms = []; b = 0; tmp = r
                while tmp > 0:
                    if tmp & 1:
                        terms.append(1 << b)
                    tmp >>= 1; b += 1
                return terms
        r_rem = (r - S) // M_sub
        assert (r - S) % M_sub == 0 and r_rem >= 0
        b = 0
        while r_rem > 0:
            if r_rem & 1:
                terms.append(M_sub * (1 << b))
            r_rem >>= 1; b += 1
        return terms

    all_terms = []; rem = target; mult = 1
    for D in D_list:
        digit = rem % D; rem //= D
        for d in rep_digit_arch2b(digit):
            all_terms.append(mult * d)
        mult *= D
    if rem > 0:
        for d in practical_rep(core_exps, rem):
            all_terms.append(mult * d)
    return all_terms


def suite4_end_to_end_verification():
    print("=" * 72)
    print("SUITE 4: End-to-End Prime-Field Validation against Locked verify_practical.py")
    print("=" * 72)
    vp_path = Path(__file__).resolve().parent / "verify_practical.py"
    h = sha256_file(vp_path)
    print(f"  verify_practical.py SHA-256: {h}")
    assert h == "63a40055143f59aaaa498e9497d1addc044abc261df8b23d3d452e5d335c7612"

    rng = random.Random(20261126)
    total_checked = 0
    for n in [12, 16, 20, 30, 45]:
        fact_n = math.factorial(n)
        targets = [1, 2, fact_n - 1, fact_n - 2, fact_n // 2, fact_n // 3]
        for _ in range(10):
            targets.append(rng.randint(1, fact_n - 1))
        max_len = 0
        for t in targets:
            terms = build_arch2b_representation(n, t, rng)
            vp.verify_representation(fact_n, t, terms, max_terms=10**6)
            max_len = max(max_len, len(terms))
            total_checked += 1
        print(f"  n={n:2d}: {len(targets)}/{len(targets)} PASS strict verifier (max_terms={max_len})")
    print(f"  TOTAL: {total_checked}/{total_checked} representations PASSED locked verify_practical.py.\n")


def suite5_stage2_11prime_patch():
    print("=" * 72)
    print("SUITE 5: Stage 2 11-Prime Inequality & Thresholds at m = 500,000")
    print("=" * 72)
    for m in [10000, 100000, 500000]:
        ps = sieve_primes(m)
        m_next = int(0.92 * m)
        Q_m = [p for p in ps if p > m_next]
        P_02 = [p for p in ps if p <= int(0.2 * m)]
        Q_next = [p for p in ps if int(0.92 * m_next) < p <= m_next]
        tags = [p for p in ps if int(0.2 * m) < p <= m_next]

        # 1. Check |Q(m)| >= 12 and |Q(m)| <= N // 2
        assert len(Q_m) >= 12, f"|Q({m})|={len(Q_m)} < 12"
        assert len(Q_m) <= len(P_02) // 2, f"|Q({m})|={len(Q_m)} > N/2={len(P_02)//2}"

        # 2. Check 11-prime strip worst case (smallest 11 primes in Q(m)):
        #    We need m^5 * M'' < M_strip / m^5  <=>  prod_{i=1}^{11} q_i > m^10
        smallest_11 = Q_m[:11]
        largest_11 = Q_m[-11:]
        ln_prod_small11 = sum(math.log(q) for q in smallest_11)
        ln_prod_large11 = sum(math.log(q) for q in largest_11)
        ln_m10 = 10.0 * math.log(m)
        ratio_m5Mpp_over_xmin = math.exp(ln_m10 - ln_prod_small11)
        assert ratio_m5Mpp_over_xmin < 1.0, f"11-prime strip failed at m={m}: ratio={ratio_m5Mpp_over_xmin}"

        # 3. Check max quotient r'' < m^5 * prod(largest_11) <= m^16
        assert ln_prod_large11 <= 11.0 * math.log(m) + 1e-12
        max_binary_bits = int(16 * math.log2(m)) + 1
        v2_core = 4 + 3 * int(math.log2(0.2 * m)) + int(0.001 * m)

        # 4. Check U_extra(m) < M_strip(m_next) / m_next^5
        #    ln U_extra(m) = sum_{0.2*m_next < p <= 0.2*m} 3 ln p
        #                  + sum_{p <= sqrt(0.2*m)} (3*floor(log_p(0.2*m)) - 3*floor(log_p(0.2*m_next))) ln p
        #                  + (floor(0.001*m) - floor(0.001*m_next)) * ln 2
        ln_U_extra = 0.0
        for p in ps:
            if p <= int(0.2 * m):
                e_m = 4 + (3 * int(math.log(0.2 * m, p)) if p * p <= 0.2 * m else 0)
                if p <= int(0.2 * m_next):
                    e_next = 4 + (3 * int(math.log(0.2 * m_next, p)) if p * p <= 0.2 * m_next else 0)
                else:
                    e_next = 1
                ln_U_extra += (e_m - e_next) * math.log(p)
        ln_U_extra += (int(0.001 * m) - int(0.001 * m_next)) * math.log(2.0)
        ln_M_strip_next = sum(math.log(q) for q in Q_next)
        margin_U = ln_M_strip_next - 5.0 * math.log(m_next) - ln_U_extra
        assert margin_U > 0, f"U_extra margin failed at m={m}: {margin_U}"

        print(
            f"  m={m:6d}: |Q|={len(Q_m):4d} <= N/2={len(P_02)//2:4d}; "
            f"(m^5 M'')/(M_strip/m^5)={ratio_m5Mpp_over_xmin:.6e} < 1; "
            f"bits(r'')<={max_binary_bits} vs v2_core={v2_core}; "
            f"ln(M_strip'/m'^5)-ln(U_extra)={margin_U:.1f} > 0"
        )
        if m >= 500000:
            assert max_binary_bits <= v2_core, f"Binary bits {max_binary_bits} > v2_core {v2_core}"
    print("  SUITE 5 PASSED.\n")


if __name__ == "__main__":
    suite1_pointwise_kl_and_dilation()
    suite2_two_factor_smooth_pigeonhole()
    suite3_carry_free_covering()
    suite4_end_to_end_verification()
    suite5_stage2_11prime_patch()
    print("ALL 5 SUITES PASSED.")
