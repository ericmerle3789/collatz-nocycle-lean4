#!/usr/bin/env python3
"""
Sprint 4d étape 1.5 — Matrice de transition Syracuse sur ZMod(2^k).

Objectif : identifier si α_empirique ≈ 0.686 (étape 1) s'explique
spectralement par |λ₂| de la chaîne de Markov sur les résidus
impairs mod 2^k, via α_spectral = -log |λ₂|.

Approche : construction empirique (sampling) de la matrice de
transition M[i, j] = P(T(n) ≡ j | n ≡ i mod 2^k), puis
diagonalisation et comparaison.

Contraintes : seed=42, atomic writes, pas de réseau, runtime < 45 min.
"""

import json
import math
import os
import random

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt


# =====================================================================
# Dynamique Syracuse
# =====================================================================
def v2(n: int) -> int:
    """2-adic valuation of n (with v2(0) = 0 by convention)."""
    if n == 0:
        return 0
    v = 0
    while n & 1 == 0:
        n >>= 1
        v += 1
    return v


def syracuse_next(n: int) -> int:
    """T(n) = (3n+1) / 2^{v₂(3n+1)}. For odd n, always yields an odd result."""
    m = 3 * n + 1
    return m >> v2(m)


def odd_residues(k: int) -> list[int]:
    """Liste des résidus impairs dans [1, 2^k)."""
    return [i for i in range(1, 2 ** k, 2)]


# =====================================================================
# Construction matrice par sampling
# =====================================================================
def build_transition_matrix(k: int, samples_per_residue: int,
                            sample_window_L: int = 10,
                            seed: int = 42) -> tuple[np.ndarray, list[int]]:
    """
    M[i, j] = P(T(n) mod 2^k = residues[j] | n mod 2^k = residues[i]).

    Pour chaque résidu i, on échantillonne `samples_per_residue` valeurs
    n dans [1, 2^(k+L)) avec n ≡ i mod 2^k, puis on compte les j = T(n) mod 2^k.
    """
    residues = odd_residues(k)
    m = len(residues)  # 2^(k-1)
    idx = {r: i for i, r in enumerate(residues)}

    M = np.zeros((m, m), dtype=np.float64)
    rng = random.Random(seed + k)

    upper = 2 ** (k + sample_window_L)
    stride = 2 ** k

    for i, r in enumerate(residues):
        # Sample n = r + j*2^k pour j random dans [0, 2^L)
        max_j = (upper - r) // stride
        for _ in range(samples_per_residue):
            j_rand = rng.randrange(0, max_j)
            n = r + j_rand * stride
            if n % 2 == 0:
                continue  # should not happen since r is odd
            t_n = syracuse_next(n)
            t_res = t_n % (2 ** k)
            if t_res % 2 == 0:
                # shouldn't happen: syracuse_next of odd is odd
                continue
            j_col = idx[t_res]
            M[i, j_col] += 1

    # Normalize each row to sum to 1 (estimated probabilities)
    row_sums = M.sum(axis=1, keepdims=True)
    # Guard against zero rows
    row_sums[row_sums == 0] = 1
    M = M / row_sums

    return M, residues


def check_stochastic(M: np.ndarray, tol: float = 1e-9) -> tuple[bool, float]:
    """Vérifie que M est stochastique à tolérance près."""
    row_sums = M.sum(axis=1)
    max_dev = float(np.max(np.abs(row_sums - 1.0)))
    return max_dev < tol, max_dev


# =====================================================================
# Analyse spectrale
# =====================================================================
def analyze_spectrum(M: np.ndarray) -> dict:
    """Eigenvalues triées par |·| décroissant ; spectral gap ; alpha."""
    eigvals = np.linalg.eigvals(M)
    # Tri par module décroissant
    order = np.argsort(-np.abs(eigvals))
    eigvals_sorted = eigvals[order]
    modules = np.abs(eigvals_sorted)

    lambda1 = complex(eigvals_sorted[0])
    lambda2 = complex(eigvals_sorted[1]) if len(eigvals_sorted) > 1 else complex(0.0)

    spectral_gap = 1.0 - abs(lambda2)
    alpha_spectral = -math.log(abs(lambda2)) if abs(lambda2) > 1e-12 else float('inf')

    # Pre-calcul : périodicité via arg(lambda_i) pour |lambda_i| = 1
    unit_eigvals = [complex(e) for e in eigvals_sorted if abs(abs(e) - 1.0) < 1e-6]
    n_unit = len(unit_eigvals)

    return {
        "n_eigvals": int(M.shape[0]),
        "lambda1": [lambda1.real, lambda1.imag],
        "lambda2": [lambda2.real, lambda2.imag],
        "abs_lambda1": float(abs(lambda1)),
        "abs_lambda2": float(abs(lambda2)),
        "spectral_gap": float(spectral_gap),
        "alpha_spectral": alpha_spectral,
        "top5_modules": [float(m) for m in modules[:5]],
        "n_unit_eigvals": n_unit,  # should be 1 for aperiodic irreducible
        "is_aperiodic_irreducible": n_unit == 1,
    }


# =====================================================================
# Main
# =====================================================================
def atomic_write_json(path: str, data: dict) -> None:
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        json.dump(data, f, indent=2)
    os.replace(tmp, path)


def main():
    ks = [4, 5, 6, 7]
    samples_per_residue = 100_000
    alpha_empirical = 0.686

    results = {"alpha_empirical": alpha_empirical, "per_k": {}}

    for k in ks:
        print(f"\n[k = {k}] {len(odd_residues(k))} odd residues, "
              f"sampling {samples_per_residue} per residue...")
        M, residues = build_transition_matrix(k, samples_per_residue)
        ok, dev = check_stochastic(M)
        print(f"  Stochastic check: max |rowsum - 1| = {dev:.2e}  ({'OK' if ok else 'FAIL'})")

        spec = analyze_spectrum(M)
        print(f"  |λ₁| = {spec['abs_lambda1']:.6f}  (doit être 1)")
        print(f"  |λ₂| = {spec['abs_lambda2']:.6f}")
        print(f"  spectral gap = {spec['spectral_gap']:.4f}")
        print(f"  α_spectral = -log|λ₂| = {spec['alpha_spectral']:.4f}")
        print(f"  α_empirical (étape 1)  = {alpha_empirical:.4f}")
        deviation = abs(spec['alpha_spectral'] - alpha_empirical)
        print(f"  |α_spectral - α_empirical| = {deviation:.4f}")
        print(f"  top 5 |λ| : {[f'{m:.4f}' for m in spec['top5_modules']]}")
        print(f"  aperiodic + irreducible : {spec['is_aperiodic_irreducible']}")

        results["per_k"][str(k)] = {
            "matrix_size": len(residues),
            "stochastic_dev": dev,
            "alpha_spectral": spec['alpha_spectral'],
            "alpha_empirical": alpha_empirical,
            "alpha_deviation": deviation,
            "abs_lambda2": spec['abs_lambda2'],
            "spectral_gap": spec['spectral_gap'],
            "top5_modules": spec['top5_modules'],
            "is_aperiodic_irreducible": spec['is_aperiodic_irreducible'],
            "match_empirical": deviation <= 0.05,
        }

    # =================================================================
    # Stabilité de |λ₂| avec k
    # =================================================================
    print("\n" + "=" * 70)
    print("=== Stabilité de |λ₂| avec k ===")
    print("=" * 70)
    lambdas_by_k = [(k, results["per_k"][str(k)]["abs_lambda2"],
                     results["per_k"][str(k)]["alpha_spectral"])
                    for k in ks]
    for (k, lam, alp) in lambdas_by_k:
        print(f"  k = {k}: |λ₂| = {lam:.4f}, α_spectral = {alp:.4f}")

    # Mesure de stabilité
    alphas = [alp for (_, _, alp) in lambdas_by_k]
    alpha_mean = sum(alphas) / len(alphas)
    alpha_std = math.sqrt(sum((a - alpha_mean) ** 2 for a in alphas) / len(alphas))
    print(f"  mean α_spectral = {alpha_mean:.4f}, std = {alpha_std:.4f}")

    results["stability"] = {
        "alpha_spectral_mean": alpha_mean,
        "alpha_spectral_std": alpha_std,
        "stable": alpha_std < 0.05,
    }

    # =================================================================
    # Verdict
    # =================================================================
    last_k = ks[-1]
    last_result = results["per_k"][str(last_k)]
    match_empirical_last = last_result["match_empirical"]
    stable = results["stability"]["stable"]
    aperiodic_all = all(results["per_k"][str(k)]["is_aperiodic_irreducible"]
                        for k in ks)

    print("\n" + "=" * 70)
    print("=== VERDICT ===")
    print("=" * 70)
    print(f"stable (std < 0.05)                : {stable}")
    print(f"aperiodic+irreducible (tous k)     : {aperiodic_all}")
    print(f"|α_spectral(k={last_k}) - α_emp| ≤ 0.05 : {match_empirical_last}")

    if stable and aperiodic_all and match_empirical_last:
        verdict = "GO_OPTION_B_PRIME"
        rationale = (f"α_spectral stable (std={alpha_std:.3f}) et "
                     f"proche de α_empirique ({last_result['alpha_spectral']:.3f} "
                     f"vs {alpha_empirical:.3f}). L'opérateur de transfert "
                     f"explique la décroissance empirique.")
    elif not stable:
        verdict = "PIVOT_OPTION_B"
        rationale = (f"α_spectral non stable avec k "
                     f"(std={alpha_std:.3f} ≥ 0.05). Le modèle markovien "
                     f"mod 2^k ne capture pas uniformément la structure.")
    elif not match_empirical_last:
        deviation_last = last_result["alpha_deviation"]
        verdict = "INCONCLUSIVE"
        rationale = (f"α_spectral stable mais décalé de α_empirique "
                     f"({last_result['alpha_spectral']:.3f} vs {alpha_empirical:.3f}, "
                     f"|Δ|={deviation_last:.3f}). Coïncidence partielle.")
    else:
        verdict = "INCONCLUSIVE"
        rationale = "Cas non trivial, voir résultats détaillés."

    print(f"\nVERDICT : {verdict}")
    print(f"  {rationale}")
    results["verdict"] = {"code": verdict, "rationale": rationale}

    # =================================================================
    # Sauvegardes
    # =================================================================
    out_json = "analysis/compactness/transfer_spectrum_results.json"
    atomic_write_json(out_json, results)
    print(f"\nJSON saved to {out_json}")

    # Plot 1 : |λ₂| vs k
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))
    ks_arr = ks
    lam2_arr = [results["per_k"][str(k)]["abs_lambda2"] for k in ks]
    alpha_s_arr = [results["per_k"][str(k)]["alpha_spectral"] for k in ks]

    ax1.plot(ks_arr, lam2_arr, marker='o', markersize=10, linewidth=2,
             color='tab:blue', label='|λ₂(k)|')
    ax1.axhline(y=math.exp(-alpha_empirical), color='red', linestyle='--',
                label=f'exp(-α_emp) = {math.exp(-alpha_empirical):.4f}')
    ax1.set_xlabel('k')
    ax1.set_ylabel('|λ₂|')
    ax1.set_title('Deuxième valeur propre vs k')
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    ax2.plot(ks_arr, alpha_s_arr, marker='s', markersize=10, linewidth=2,
             color='tab:green', label='α_spectral = -log|λ₂|')
    ax2.axhline(y=alpha_empirical, color='red', linestyle='--',
                label=f'α_empirique = {alpha_empirical:.4f}')
    ax2.axhline(y=math.log(2), color='gray', linestyle=':',
                label=f'log(2) = {math.log(2):.4f}')
    ax2.set_xlabel('k')
    ax2.set_ylabel('α')
    ax2.set_title('α_spectral vs α_empirique')
    ax2.legend()
    ax2.grid(True, alpha=0.3)

    out_png = "analysis/compactness/spectrum_vs_k.png"
    plt.tight_layout()
    plt.savefig(out_png, dpi=100, bbox_inches='tight')
    plt.close()
    print(f"PNG saved to {out_png}")

    print(f"\n=== Étape 1.5 terminée. Verdict = {verdict} ===")


if __name__ == "__main__":
    main()
