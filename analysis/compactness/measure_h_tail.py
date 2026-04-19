#!/usr/bin/env python3
"""
Sprint 4d reformulé — Étape 1 : mesure empirique de la queue de Δh.

Objectif : déterminer si Δh := h(3n+1) - h(n) admet une queue
intégrable (Lyapunov stochastique) ou une queue lourde (no-go).

Protocole :
  1. Pour bit_length b ∈ {10, 20, 30, 40, 50}, échantillonner 10^6
     entiers impairs uniformément dans [2^(b-1), 2^b).
  2. Calculer la fonction de survie empirique S_b(t) := P(Δh > t).
  3. Fit exponentiel : log S_b(t) vs t → slope = -α.
  4. Fit polynomial : log S_b(t) vs log(t) → slope = -p.
  5. MGF : M_b(α) := E[exp(α · Δh)] pour α ∈ {0.1 .. 2.0}.
  6. Gate SUCCESS / MIXED / FAIL selon stabilité de M_b(α).

Règles : seed=42, atomic writes, sortie JSON + PNG.
"""

import json
import math
import os
import random
import sys
from collections import Counter

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


# =====================================================================
# Définition de h (référence ProjetCollatz.Compactness.h)
# =====================================================================
def h(n: int) -> int:
    """Plus long run de '0' dans bin(n)[2:].rstrip('0'). h(0) = 0."""
    if n == 0:
        return 0
    s = bin(n)[2:].rstrip("0")
    if not s:
        return 0
    max_run = 0
    current = 0
    for c in s:
        if c == '0':
            current += 1
            if current > max_run:
                max_run = current
        else:
            current = 0
    return max_run


# =====================================================================
# Utilitaires
# =====================================================================
def sanity_check():
    """Vérifie h() contre les valeurs Lean de référence."""
    reference = [(0, 0), (1, 0), (5, 1), (9, 2), (17, 3), (27, 1),
                 (73, 2), (267, 4), (1025, 9)]
    for (n, expected) in reference:
        got = h(n)
        assert got == expected, f"h({n}) = {got} ≠ {expected}"
    print("Sanity check: PASS (h matches Lean reference)\n")


def atomic_write_json(path: str, data: dict) -> None:
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        json.dump(data, f, indent=2)
    os.replace(tmp, path)


def sample_deltas(bit_length: int, N: int, seed_offset: int) -> list[int]:
    """N impairs aléatoires dans [2^(b-1), 2^b). Retourne liste des Δh."""
    rng = random.Random(42 + seed_offset)
    lo = 2 ** (bit_length - 1)
    hi = 2 ** bit_length
    deltas = []
    for _ in range(N):
        n = rng.randrange(lo, hi)
        if n % 2 == 0:
            n += 1
            if n >= hi:
                n -= 2
        deltas.append(h(3 * n + 1) - h(n))
    return deltas


def survival(deltas: list[int], t_max: int) -> list[tuple[int, float]]:
    """Retourne [(t, P(Δh > t)) for t in 0..t_max]."""
    N = len(deltas)
    # histogramme via Counter
    c = Counter(deltas)
    # survival : P(Δh > t) = sum_{d > t} count[d] / N
    sorted_keys = sorted(c.keys(), reverse=True)
    cumul = 0
    tail = {}
    # Compute cumul from max down to min
    for k in sorted_keys:
        cumul += c[k]
        tail[k] = cumul / N
    # P(Δh > t) = tail[t+1] if (t+1) is a key, else interpolate
    out = []
    all_keys_sorted_asc = sorted(c.keys())
    for t in range(0, t_max + 1):
        # count strictly greater than t
        cnt = sum(c[k] for k in c if k > t)
        out.append((t, cnt / N))
    return out


def linear_fit(x: list[float], y: list[float]) -> tuple[float, float, float]:
    """(slope, intercept, R²). None if not enough points."""
    n = len(x)
    if n < 2:
        return 0.0, 0.0, 0.0
    mean_x = sum(x) / n
    mean_y = sum(y) / n
    num = sum((x[i] - mean_x) * (y[i] - mean_y) for i in range(n))
    den = sum((xi - mean_x) ** 2 for xi in x)
    if den == 0:
        return 0.0, 0.0, 0.0
    slope = num / den
    intercept = mean_y - slope * mean_x
    ss_res = sum((y[i] - (slope * x[i] + intercept)) ** 2 for i in range(n))
    ss_tot = sum((yi - mean_y) ** 2 for yi in y)
    r2 = 1 - ss_res / ss_tot if ss_tot > 0 else 0.0
    return slope, intercept, r2


def mgf_estimate(deltas: list[int], alpha: float) -> float:
    """E[exp(α·Δh)] estimé."""
    # Attention : pour α grand et Δh grand, exp peut overflow
    try:
        return sum(math.exp(alpha * d) for d in deltas) / len(deltas)
    except OverflowError:
        return float('inf')


# =====================================================================
# Main analysis
# =====================================================================
def main():
    sanity_check()

    bit_lengths = [10, 20, 30, 40, 50]
    N = 10 ** 6
    alphas = [0.1, 0.2, 0.3, 0.5, 0.7, 1.0, 1.5, 2.0]

    results = {}
    all_deltas = {}

    for idx, b in enumerate(bit_lengths):
        print(f"[{idx+1}/{len(bit_lengths)}] bit_length = {b}, sampling {N} odd integers...")
        deltas = sample_deltas(b, N, seed_offset=b)
        all_deltas[b] = deltas

        # Basic stats
        max_d = max(deltas)
        min_d = min(deltas)
        mean_d = sum(deltas) / len(deltas)
        var_d = sum((d - mean_d) ** 2 for d in deltas) / len(deltas)
        std_d = math.sqrt(var_d)
        print(f"  max Δh = {max_d}, min = {min_d}, mean = {mean_d:+.4f}, std = {std_d:.3f}")

        # Survival
        t_max = b
        surv = survival(deltas, t_max)
        # Print a few key values
        print(f"  P(Δh > 0) = {next(p for t, p in surv if t == 0):.4f}")
        for t_show in [0, 2, 5, 10, b // 2, min(b - 1, t_max)]:
            p = next((p for t, p in surv if t == t_show), None)
            if p is not None:
                print(f"  P(Δh > {t_show:3}) = {p:.6f}")

        # Exponential fit : log S vs t (only t with S > 0)
        ts_exp = [t for t, p in surv if p > 0]
        log_S = [math.log(p) for t, p in surv if p > 0]
        slope_exp, intcp_exp, r2_exp = linear_fit(ts_exp, log_S)
        alpha_exp = -slope_exp
        print(f"  Exp fit : log S(t) ~ {slope_exp:+.4f} t + {intcp_exp:+.2f}  "
              f"(α = {alpha_exp:.4f}, R² = {r2_exp:.4f})")

        # Polynomial fit : log S vs log t (t >= 1)
        ts_pol = [math.log(t) for t, p in surv if p > 0 and t >= 1]
        log_S_pol = [math.log(p) for t, p in surv if p > 0 and t >= 1]
        slope_pol, intcp_pol, r2_pol = linear_fit(ts_pol, log_S_pol)
        p_decay = -slope_pol
        print(f"  Poly fit: log S(t) ~ {slope_pol:+.4f} log(t) + {intcp_pol:+.2f}  "
              f"(p = {p_decay:.4f}, R² = {r2_pol:.4f})")

        # MGF estimates
        mgf = {}
        for alpha in alphas:
            M = mgf_estimate(deltas, alpha)
            mgf[f"{alpha}"] = M
            print(f"  M({alpha:.2f}) = {M:.4e}")

        # Histogram for plotting
        hist_counter = Counter(deltas)

        results[str(b)] = {
            "N": N,
            "max_delta": max_d,
            "min_delta": min_d,
            "mean_delta": mean_d,
            "std_delta": std_d,
            "survival": [[t, p] for t, p in surv],
            "exp_fit": {"slope": slope_exp, "intercept": intcp_exp,
                        "alpha": alpha_exp, "r2": r2_exp},
            "poly_fit": {"slope": slope_pol, "intercept": intcp_pol,
                         "p_decay": p_decay, "r2": r2_pol},
            "mgf": mgf,
            "histogram": {str(k): v for k, v in sorted(hist_counter.items())},
        }
        print()

    # =================================================================
    # Gate decision
    # =================================================================
    print("=" * 70)
    print("=== GATE ANALYSIS ===")
    print("=" * 70)

    # Check 1: α stable across bit_lengths?
    alphas_fit = [results[str(b)]["exp_fit"]["alpha"] for b in bit_lengths]
    alpha_mean = sum(alphas_fit) / len(alphas_fit)
    alpha_std = math.sqrt(sum((a - alpha_mean) ** 2 for a in alphas_fit) / len(alphas_fit))
    alpha_stable = alpha_std < 0.2 * alpha_mean if alpha_mean > 0 else False
    print(f"\nExponential decay rate α across bit_lengths:")
    for b, a in zip(bit_lengths, alphas_fit):
        print(f"  bl = {b:3}: α = {a:.4f}")
    print(f"  mean α = {alpha_mean:.4f}, std = {alpha_std:.4f}, "
          f"stable = {alpha_stable}")

    # Check 2: MGF at α=0.5 stable?
    mgf_05 = [float(results[str(b)]["mgf"]["0.5"]) for b in bit_lengths]
    mgf_05_finite = all(math.isfinite(m) and m < 1e10 for m in mgf_05)
    mgf_05_bounded = all(m < 10 for m in mgf_05) if mgf_05_finite else False
    print(f"\nMGF at α = 0.5 across bit_lengths:")
    for b, m in zip(bit_lengths, mgf_05):
        print(f"  bl = {b:3}: M(0.5) = {m:.4e}")
    print(f"  all finite = {mgf_05_finite}, all < 10 = {mgf_05_bounded}")

    # Check 3: Polynomial fit R² better than exp fit?
    r2_exp_all = [results[str(b)]["exp_fit"]["r2"] for b in bit_lengths]
    r2_pol_all = [results[str(b)]["poly_fit"]["r2"] for b in bit_lengths]
    print(f"\nFit quality (R²):")
    print(f"  Exponential R²: {[f'{r:.4f}' for r in r2_exp_all]}")
    print(f"  Polynomial R² : {[f'{r:.4f}' for r in r2_pol_all]}")

    # Gate decision
    gate = "UNKNOWN"
    rationale = ""
    if alpha_stable and mgf_05_bounded:
        gate = "SUCCESS_EXPONENTIAL"
        rationale = (f"Queue exponentielle confirmée : α ≈ {alpha_mean:.3f} stable "
                     f"à travers bit_lengths, MGF(0.5) borné < 10.")
    elif mgf_05_finite and not mgf_05_bounded:
        # MGF croît avec bit_length → queue heavy
        gate = "MIXED"
        rationale = (f"MGF(0.5) fini mais croît avec bit_length "
                     f"(de {mgf_05[0]:.2e} à {mgf_05[-1]:.2e}).")
    elif not mgf_05_finite:
        gate = "FAIL"
        rationale = "MGF(0.5) diverge — queue trop lourde."
    else:
        # α non stable mais MGF borné
        gate = "SUCCESS_WITH_CAVEATS"
        rationale = (f"α varie ({alpha_mean:.3f} ± {alpha_std:.3f}) mais "
                     f"MGF(0.5) borné. Possible lognormal ou ajustement affiné nécessaire.")

    print(f"\n>>> GATE : {gate}")
    print(f">>> {rationale}")

    results["_gate"] = {
        "verdict": gate,
        "rationale": rationale,
        "alpha_mean": alpha_mean,
        "alpha_std": alpha_std,
        "alpha_stable": alpha_stable,
        "mgf_0.5_finite": mgf_05_finite,
        "mgf_0.5_bounded": mgf_05_bounded,
    }

    # =================================================================
    # Save JSON
    # =================================================================
    out_json = "analysis/compactness/measure_h_tail_results.json"
    atomic_write_json(out_json, results)
    print(f"\nResults saved to {out_json}")

    # =================================================================
    # Plot 1 : Survival functions (log-y)
    # =================================================================
    fig, ax = plt.subplots(figsize=(10, 6))
    colors = plt.cm.viridis(np.linspace(0, 0.8, len(bit_lengths)))
    for b, color in zip(bit_lengths, colors):
        surv = results[str(b)]["survival"]
        ts = [t for t, _ in surv]
        ps = [p if p > 0 else 1e-7 for _, p in surv]
        ax.semilogy(ts, ps, marker='o', markersize=3, linewidth=1,
                    color=color, label=f'bit_length = {b}')
    ax.set_xlabel('t')
    ax.set_ylabel('P(Δh > t)   [log scale]')
    ax.set_title('Survival function of Δh = h(3n+1) - h(n), N=10⁶ per bl')
    ax.legend()
    ax.grid(True, alpha=0.3, which='both')
    out_png1 = "analysis/compactness/survival_linear_y_log.png"
    plt.savefig(out_png1, dpi=100, bbox_inches='tight')
    plt.close()
    print(f"Plot saved to {out_png1}")

    # =================================================================
    # Plot 2 : Log-log survival (pour détecter polynomial)
    # =================================================================
    fig, ax = plt.subplots(figsize=(10, 6))
    for b, color in zip(bit_lengths, colors):
        surv = results[str(b)]["survival"]
        ts = [t for t, p in surv if p > 0 and t >= 1]
        ps = [p for t, p in surv if p > 0 and t >= 1]
        ax.loglog(ts, ps, marker='o', markersize=3, linewidth=1,
                  color=color, label=f'bit_length = {b}')
    ax.set_xlabel('t   [log scale]')
    ax.set_ylabel('P(Δh > t)   [log scale]')
    ax.set_title('Log-log survival function')
    ax.legend()
    ax.grid(True, alpha=0.3, which='both')
    out_png2 = "analysis/compactness/survival_log_log.png"
    plt.savefig(out_png2, dpi=100, bbox_inches='tight')
    plt.close()
    print(f"Plot saved to {out_png2}")

    # =================================================================
    # Plot 3 : Histogram of Δh (linear)
    # =================================================================
    fig, ax = plt.subplots(figsize=(10, 6))
    for b, color in zip(bit_lengths, colors):
        hist = results[str(b)]["histogram"]
        ds = sorted(int(k) for k in hist.keys())
        counts = [hist[str(d)] / N for d in ds]
        ax.plot(ds, counts, marker='o', markersize=3, linewidth=1,
                color=color, label=f'bit_length = {b}')
    ax.set_xlabel('Δh')
    ax.set_ylabel('P(Δh = d)')
    ax.set_title('Empirical PMF of Δh')
    ax.legend()
    ax.grid(True, alpha=0.3)
    out_png3 = "analysis/compactness/pmf_delta_h.png"
    plt.savefig(out_png3, dpi=100, bbox_inches='tight')
    plt.close()
    print(f"Plot saved to {out_png3}")

    print(f"\n=== Étape 1 terminée. Gate = {gate} ===")
    sys.exit(0)


if __name__ == "__main__":
    main()
