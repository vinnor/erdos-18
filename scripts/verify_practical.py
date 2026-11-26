#!/usr/bin/env python3
"""
Exact verification & empirical sandbox for Erdős Problem #18 (practical numbers & h(n!)).
No external dependencies. Never relax assertions in this file.
"""

import argparse
import math
import random
from typing import Iterable, List, Tuple


def prime_factorization(n: int) -> List[Tuple[int, int]]:
    factors = []
    d = 2
    temp = n
    while d * d <= temp:
        if temp % d == 0:
            e = 0
            while temp % d == 0:
                temp //= d
                e += 1
            factors.append((d, e))
        d += 1 if d == 2 else 2
    if temp > 1:
        factors.append((temp, 1))
    return factors


def is_practical(n: int) -> bool:
    """Stewart-Sierpinski characterization of practical numbers."""
    if n < 1:
        return False
    if n == 1:
        return True
    facs = prime_factorization(n)
    if facs[0][0] != 2:
        return False
    sigma_prefix = (2 ** (facs[0][1] + 1)) - 1
    for p, e in facs[1:]:
        if p > sigma_prefix + 1:
            return False
        sigma_prefix *= (p ** (e + 1) - 1) // (p - 1)
    return True


def divisors(n: int) -> List[int]:
    divs = [1]
    for p, e in prime_factorization(n):
        new_divs = []
        pe = 1
        for _ in range(e + 1):
            for d in divs:
                new_divs.append(d * pe)
            pe *= p
        divs = new_divs
    divs.sort()
    return divs


def exact_h(n: int) -> Tuple[int, int]:
    """
    Returns (h(n), witness_k) where witness_k in [1, n-1] requires h(n) distinct divisors.
    Exact DP; practical for n up to ~50,000.
    """
    if n <= 1:
        return (0, 0)
    assert is_practical(n), f"{n} is not practical!"
    divs = [d for d in divisors(n) if d < n]
    INF = 10**9
    dp = [INF] * n
    dp[0] = 0
    for d in divs:
        for s in range(n - 1, d - 1, -1):
            cand = dp[s - d] + 1
            if cand < dp[s]:
                dp[s] = cand
    worst_h = -1
    witness = -1
    for k in range(1, n):
        assert dp[k] < INF, f"Unrepresentable target {k} for practical n={n}"
        if dp[k] > worst_h:
            worst_h = dp[k]
            witness = k
    return worst_h, witness


def verify_representation(m: int, target: int, summands: Iterable[int], max_terms: int) -> None:
    """Strict certificate checker for any constructive algorithm on large m (e.g., n!)."""
    terms = list(summands)
    assert 1 <= target <= m, f"Target {target} out of range [1, {m}]"
    assert len(terms) <= max_terms, f"Used {len(terms)} > {max_terms} terms"
    assert len(set(terms)) == len(terms), "Duplicate divisors used! Distinctness violated."
    for d in terms:
        assert isinstance(d, int) and d > 0, f"Invalid divisor {d}"
        assert m % d == 0, f"{d} does not divide {m}!"
    assert sum(terms) == target, f"Sum mismatch: {sum(terms)} != {target}"


def factorial_tau(n: int) -> int:
    """Exact number of divisors tau(n!)."""
    tau = 1
    for p in range(2, n + 1):
        # check prime
        is_p = True
        d = 2
        while d * d <= p:
            if p % d == 0:
                is_p = False
                break
            d += 1
        if is_p:
            v = 0
            pk = p
            while pk <= n:
                v += n // pk
                pk *= p
            tau *= (v + 1)
    return tau


def counting_lower_bound(n: int) -> float:
    """Exact information-theoretic lower bound log(n!) / log(tau(n!) + 1)."""
    log_fact = math.lgamma(n + 1)
    log_tau = math.log(factorial_tau(n) + 1)
    return log_fact / log_tau


def self_test() -> None:
    # Verified Erdős benchmarks: h(2!)=1, h(3!)=2, h(4!)=3
    assert exact_h(2)[0] == 1
    assert exact_h(6)[0] == 2
    assert exact_h(24)[0] == 3
    verify_representation(24, 23, [12, 8, 3], max_terms=3)
    print("SELF-TEST PASSED: h(2!)=1, h(3!)=2, h(4!)=3.")
    for n in range(2, 8):
        fact = math.factorial(n)
        h_val, wit = exact_h(fact)
        lb = counting_lower_bound(n)
        print(f"n={n}, n!={fact:6d}, tau={factorial_tau(n):3d}, exact h(n!)={h_val} (witness={wit}), counting_LB={lb:.2f}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--n", type=int, help="Compute exact h(n!) for small n (recommended n <= 8)")
    args = parser.parse_args()
    if args.self_test:
        self_test()
    elif args.n is not None:
        fact = math.factorial(args.n)
        h_val, wit = exact_h(fact)
        print(f"n={args.n}, n!={fact}, exact h(n!)={h_val}, witness={wit}, LB={counting_lower_bound(args.n):.2f}")