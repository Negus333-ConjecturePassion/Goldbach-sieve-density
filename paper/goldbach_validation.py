"""
Goldbach Sieve-Density Framework -- Computational Validation Script
Reproduces Section 4.2 (table) and Section 4.3 (graph) of
Goldbach_Sieve_Density_Framework_vE.

Compares three estimators of the Goldbach representation count R(n):
  1. True R(n): exact brute-force count
  2. Cramer Naive: independence-model estimate (no singular series correction)
  3. Hardy-Littlewood: naive estimate corrected by the singular series S(n)

Note: all three loops start at p=3, so the p=2 representation
(n = 2 + (n-2), valid whenever n-2 is prime) is knowingly and consistently
omitted from all three columns. This affects all estimators equally and does
not bias the comparison between them.
"""

import math
import matplotlib.pyplot as plt


def is_prime(n: int) -> bool:
    """Standard deterministic primality test for small to medium integers."""
    if n < 2:
        return False
    if n in (2, 3):
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0:
            return False
        i += 6
    return True


def true_goldbach_count(n: int) -> int:
    """Exact count of prime pairs (p, n-p) with 3 <= p <= n/2."""
    count = 0
    for p in range(3, n // 2 + 1):
        if is_prime(p) and is_prime(n - p):
            count += 1
    return count


def odd_prime_factors(n: int) -> list:
    """
    Actual distinct odd prime factors of n (fully factored, not truncated
    to a fixed scan limit). Strips factors of 2 first -- the original bug
    in this script omitted that step, leaving leftover powers of 2 in the
    factor list.
    """
    m = n
    while m % 2 == 0:
        m //= 2
    factors = []
    d = 3
    while d * d <= m:
        if m % d == 0:
            factors.append(d)
            while m % d == 0:
                m //= d
        d += 2
    if m > 1:
        factors.append(m)
    return factors


def singular_series(n: int) -> float:
    """
    Hardy-Littlewood singular series:
        S(n) = 2 * C2 * prod_{p | n, p odd} (p-1)/(p-2)
    where C2 is the twin-prime constant.
    """
    c2 = 0.6601618158468619
    prod = 1.0
    for p in odd_prime_factors(n):
        prod *= (p - 1) / (p - 2)
    return 2 * c2 * prod


def cramer_naive_estimate(n: int) -> float:
    """Naive independence-model estimate: sum_{x=3}^{n/2} 1/(ln(x) ln(n-x))."""
    total = 0.0
    for x in range(3, n // 2 + 1):
        total += 1.0 / (math.log(x) * math.log(n - x))
    return total


def hardy_littlewood_estimate(n: int) -> float:
    """Singular-series-corrected estimate: S(n) * cramer_naive_estimate(n)."""
    return singular_series(n) * cramer_naive_estimate(n)


def print_validation_table():
    """Reproduces the Section 4.2 table."""
    test_values = [1000, 10000, 50000, 100000, 9996, 100002, 100170]

    header = (f"{'N':<10} | {'odd prime factors':<20} | {'True R(N)':<10} | "
              f"{'Cramer Naive':<14} | {'Hardy-Littlewood':<18} | "
              f"{'HL/True':<8} | {'Naive/True':<10}")
    print(header)
    print("-" * len(header))

    for N in test_values:
        actual = true_goldbach_count(N)
        naive = cramer_naive_estimate(N)
        hl = hardy_littlewood_estimate(N)
        hl_ratio = hl / actual if actual else float('nan')
        naive_ratio = naive / actual if actual else float('nan')
        factors = odd_prime_factors(N)
        print(f"{N:<10} | {str(factors):<20} | {actual:<10} | "
              f"{naive:<14.4f} | {hl:<18.4f} | {hl_ratio:<8.4f} | "
              f"{naive_ratio:<10.4f}")


def plot_validation_graph(output_path="goldbach_validation_plot.png",
                           step=100, n_min=100, n_max=100000):
    """Reproduces the Section 4.3 graph."""
    n_values = list(range(n_min, n_max + step, step))
    hl_ratios, naive_ratios = [], []

    for n in n_values:
        actual = true_goldbach_count(n)
        naive = cramer_naive_estimate(n)
        hl = hardy_littlewood_estimate(n)
        if actual > 0:
            hl_ratios.append(hl / actual)
            naive_ratios.append(naive / actual)

    fig, ax = plt.subplots(figsize=(12, 7))
    ax.plot(n_values, hl_ratios, 'o-', linewidth=2.5, markersize=5,
            label='Hardy-Littlewood / True R(N)', color='#2E86AB', alpha=0.85)
    ax.plot(n_values, naive_ratios, 's-', linewidth=2.5, markersize=5,
            label='Cramer Naive / True R(N)', color='#A23B72', alpha=0.85)
    ax.axhline(y=1.0, color='gray', linestyle='--', linewidth=1.5,
               alpha=0.6, label='Perfect estimate (ratio = 1)')
    ax.set_xlabel('N (even number)', fontsize=12, fontweight='bold')
    ax.set_ylabel('Estimator / True R(N)', fontsize=12, fontweight='bold')
    ax.set_title('Goldbach: Hardy-Littlewood vs. Cramer Naive Estimates\n'
                 '(Singular Series Correction)', fontsize=13,
                 fontweight='bold', pad=20)
    ax.grid(True, alpha=0.3, linestyle=':', linewidth=0.8)
    ax.legend(fontsize=11, loc='upper right')
    ax.set_ylim(0.15, 1.45)
    ax.set_xlim(0, n_max + 2000)

    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    print(f"\nPlot saved to: {output_path}")
    print(f"HL/True range: [{min(hl_ratios):.4f}, {max(hl_ratios):.4f}]")
    print(f"Naive/True range: [{min(naive_ratios):.4f}, {max(naive_ratios):.4f}]")


if __name__ == "__main__":
    print_validation_table()
    plot_validation_graph()
