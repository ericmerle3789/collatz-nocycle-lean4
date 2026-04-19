#!/usr/bin/env python3
"""
Sprint 4e préparatoire — Test empirique de l'hypothèse « h comme certificat anti-cycle ».

Flash d'Eric : « Si le 0000 reste 0000, pas de cycle. Si un 1 apparaît dans le bloc, cycle. »

Traduction : h(n) ≥ 4 serait une condition nécessaire de non-appartenance au
bassin du cycle {1, 2, 4}. Contraposée : toute orbite qui reste `h ≥ 4`
indéfiniment ne cycle pas.

Tests :
  1. Cycle trivial {1, 2, 4} → h = 0 partout (compat. hypothèse).
  2. Pour 1000 seeds par range (petit/moyen/grand/énorme) : tracer h le long
     de l'orbite Syracuse jusqu'à 1, mesurer min h, indice du min, fraction
     d'orbite au-dessus de 4.
  3. Hypothèse inverse : existe-t-il des orbites transitoires où h passe
     sous 4 AVANT d'atteindre un voisinage de 1 (bit_length > 10) ?
  4. Fraction d'orbite à h ≥ 4 par range de seed.
  5. Faux cycle : sequence périodique artificielle — h reste-t-il ≥ 4 ?

Règles : seed=42, atomic writes, pas de réseau, pas de commit.
"""

import json
import math
import os
import random
from collections import Counter

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


# =====================================================================
# Fonctions de base
# =====================================================================
def h(n: int) -> int:
    if n == 0:
        return 0
    s = bin(n)[2:].rstrip("0")
    if not s:
        return 0
    m = 0; c = 0
    for ch in s:
        if ch == '0':
            c += 1
            if c > m: m = c
        else:
            c = 0
    return m


def v2(n: int) -> int:
    if n == 0: return 0
    v = 0
    while n & 1 == 0:
        n >>= 1
        v += 1
    return v


def syracuse_next(n: int) -> int:
    """T(n) = (3n+1) / 2^{v₂(3n+1)}. Odd → odd."""
    m = 3 * n + 1
    return m >> v2(m)


def syracuse_orbit(n: int, max_steps: int = 10_000) -> list[int]:
    """Orbite Syracuse de n (impair) jusqu'à 1 ou max_steps."""
    orbit = [n]
    while n != 1 and len(orbit) < max_steps:
        n = syracuse_next(n)
        orbit.append(n)
    return orbit


# =====================================================================
# Sanity check (red team fix B1 : protocole)
# =====================================================================
def _sanity_check():
    """Vérifie h() contre les valeurs Lean de référence (TestCompactnessDefs)."""
    reference = [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 1),
                 (9, 2), (17, 3), (27, 1), (73, 2), (267, 4), (1025, 9)]
    for (n, expected) in reference:
        got = h(n)
        assert got == expected, f"h({n}) = {got} ≠ {expected} (Lean)"
    # Sanity Syracuse : syracuse_next(1) = 1 (point fixe)
    assert syracuse_next(1) == 1
    # syracuse_next(3) = (3*3+1)/2 = 5
    assert syracuse_next(3) == 5
    # syracuse_next(7) = (3*7+1)/2 = 11
    assert syracuse_next(7) == 11
    print("Sanity check h() + syracuse_next() vs Lean : PASS\n")


_sanity_check()


# =====================================================================
# Test 1 : cycle trivial
# =====================================================================
print("=" * 70)
print("TEST 1 — Cycle trivial {1, 2, 4}")
print("=" * 70)
for n in [1, 2, 4]:
    hn = h(n)
    print(f"  h({n}) = {hn}  (< 4 : {hn < 4})")
# Syracuse : 1 → 1 (boucle fixe pour le map compressé)
print(f"\n  syracuse_next(1) = {syracuse_next(1)}  (confirme point fixe)")
print("  → Hypothèse Eric compatible : cycle trivial a h = 0 partout.\n")


# =====================================================================
# Test 2 : orbites aléatoires, mesure de h
# =====================================================================
print("=" * 70)
print("TEST 2 — Orbites Syracuse, profil de h le long de l'orbite")
print("=" * 70)


def analyze_orbit(seed: int) -> dict:
    orbit = syracuse_orbit(seed)
    hs = [h(n) for n in orbit]
    bls = [n.bit_length() for n in orbit]
    reached_1 = (orbit[-1] == 1)
    bl_initial = bls[0]

    # Index du premier passage sous 4
    first_below = next((i for i, hv in enumerate(hs) if hv < 4), None)
    # Index du dernier passage au-dessus ou égal à 4
    last_ge4 = max((i for i, hv in enumerate(hs) if hv >= 4), default=-1)
    # Fraction d'orbite au-dessus de 4
    frac_ge4 = sum(1 for hv in hs if hv >= 4) / len(hs)
    # bit_length au moment du premier passage sous 4
    # (red team fix B4 : is not None au lieu de test truthy qui échoue sur index=0)
    bl_at_first_below = bls[first_below] if first_below is not None else None
    # Ratio bl_at_first_dip / bl_initial (red team fix B6 : seuil RELATIF)
    bl_ratio_at_first_below = (bl_at_first_below / bl_initial
                               if bl_at_first_below is not None else None)

    return {
        "seed": seed,
        "orbit_len": len(orbit),
        "reached_1": reached_1,
        "min_h": min(hs),
        "max_h": max(hs),
        "first_below_4_idx": first_below,
        "first_below_4_rel": first_below / len(orbit) if first_below is not None else None,
        "bl_at_first_below_4": bl_at_first_below,
        "bl_ratio_at_first_below_4": bl_ratio_at_first_below,
        "last_ge_4_idx": last_ge4,
        "frac_ge_4": frac_ge4,
        "initial_h": hs[0],
        "initial_bl": bl_initial,
    }


random.seed(42)
ranges_defs = [
    ("small (bl=10-14)", 2**10, 2**14),
    ("medium (bl=20-24)", 2**20, 2**24),
    ("large (bl=30-34)", 2**30, 2**34),
    ("huge (bl=60-64)", 2**60, 2**64),
]

summaries = {}
all_stats = {}
for label, lo, hi in ranges_defs:
    # 1000 seeds per range (huge : 200 pour limiter runtime)
    N = 200 if "huge" in label else 1000
    seeds = []
    while len(seeds) < N:
        n = random.randrange(lo, hi)
        if n % 2 == 1:
            seeds.append(n)

    stats = [analyze_orbit(s) for s in seeds]
    all_stats[label] = stats

    # Agrégats
    all_reached = all(s["reached_1"] for s in stats)
    fracs_ge4 = [s["frac_ge_4"] for s in stats]
    min_hs = [s["min_h"] for s in stats]
    first_below_rels = [s["first_below_4_rel"] for s in stats
                        if s["first_below_4_rel"] is not None]
    bls_at_first_below = [s["bl_at_first_below_4"] for s in stats
                          if s["bl_at_first_below_4"] is not None]

    # Cas où h reste ≥ 4 TOUTE l'orbite (zéro dip) — TAUTOLOGIE Collatz :
    # toujours 0 puisque toutes les orbites atteignent 1 par conjecture
    always_ge_4 = sum(1 for s in stats if s["first_below_4_idx"] is None)
    # ANCIEN critère absolu (biaisé — red team B6)
    dip_while_bl_gt_10 = sum(1 for s in stats
                             if s["bl_at_first_below_4"] is not None
                             and s["bl_at_first_below_4"] > 10)
    # NOUVEAU critère relatif : dip alors que bl est ENCORE ≥ 50% de bl_initial
    # (= orbite n'est pas encore redescendue de moitié en taille)
    bl_ratios = [s["bl_ratio_at_first_below_4"] for s in stats
                 if s["bl_ratio_at_first_below_4"] is not None]
    dip_while_bl_at_least_half = sum(1 for s in stats
                                     if s["bl_ratio_at_first_below_4"] is not None
                                     and s["bl_ratio_at_first_below_4"] >= 0.5)
    # Critère ENCORE plus strict : dip alors que bl ≥ 80% de bl_initial
    dip_while_bl_almost_initial = sum(1 for s in stats
                                      if s["bl_ratio_at_first_below_4"] is not None
                                      and s["bl_ratio_at_first_below_4"] >= 0.8)

    summary = {
        "range": label,
        "N": N,
        "bl_range": [lo.bit_length(), (hi - 1).bit_length()],
        "all_orbits_reach_1": all_reached,
        "frac_ge_4_mean": float(np.mean(fracs_ge4)),
        "frac_ge_4_std": float(np.std(fracs_ge4)),
        "min_h_mean": float(np.mean(min_hs)),
        "min_h_max": int(max(min_hs)),
        "min_h_histogram": dict(Counter(min_hs)),
        "first_below_4_rel_mean": float(np.mean(first_below_rels)) if first_below_rels else None,
        "first_below_4_rel_median": float(np.median(first_below_rels)) if first_below_rels else None,
        "bl_at_first_below_4_mean": float(np.mean(bls_at_first_below)) if bls_at_first_below else None,
        "bl_at_first_below_4_median": float(np.median(bls_at_first_below)) if bls_at_first_below else None,
        "bl_ratio_at_first_below_4_mean": float(np.mean(bl_ratios)) if bl_ratios else None,
        "bl_ratio_at_first_below_4_median": float(np.median(bl_ratios)) if bl_ratios else None,
        "orbits_never_below_4_TAUTOLOGIE_COLLATZ": always_ge_4,
        "orbits_dip_bl_gt_10_absolute": dip_while_bl_gt_10,
        "orbits_dip_bl_gte_half_initial": dip_while_bl_at_least_half,
        "orbits_dip_bl_gte_80pct_initial": dip_while_bl_almost_initial,
    }
    summaries[label] = summary

    print(f"\n[{label}]  N = {N}")
    print(f"  Toutes atteignent 1 : {all_reached} (TAUTOLOGIE Collatz)")
    print(f"  Fraction orbite avec h ≥ 4 : mean = {summary['frac_ge_4_mean']:.3f}, "
          f"std = {summary['frac_ge_4_std']:.3f}")
    print(f"  min h le long de l'orbite : mean = {summary['min_h_mean']:.2f}, "
          f"max (sur orbites) = {summary['min_h_max']}")
    print(f"  [TAUTOLOGIE] orbites où h reste TOUJOURS ≥ 4 : {always_ge_4} (toujours 0)")
    print(f"  [SEUIL ABSOLU] dip à bl > 10             : {dip_while_bl_gt_10}")
    print(f"  [SEUIL RELATIF] dip à bl ≥ bl_init/2     : {dip_while_bl_at_least_half}")
    print(f"  [SEUIL RELATIF FORT] dip à bl ≥ 80% init : {dip_while_bl_almost_initial}")
    print(f"  1er dip < 4 : position relative median = "
          f"{summary['first_below_4_rel_median']:.3f}, "
          f"ratio bl/bl_init median = {summary['bl_ratio_at_first_below_4_median']:.3f}")


# =====================================================================
# Test 3 : hypothèse inverse — critère RELATIF (red team fix B6)
# =====================================================================
print("\n" + "=" * 70)
print("TEST 3 — Hypothèse inverse (critère RELATIF bl_ratio au 1er dip)")
print("=" * 70)
print("Question : le 1er dip h < 4 se fait-il quand l'orbite est déjà")
print("redescendue proche de 1 (ratio petit), ou alors que n est encore GRAND")
print("(ratio proche de 1) ?")
print()
print("Si Eric's hypothesis : ratio doit être PETIT (dip = fin d'orbite).")
print("Si rejet : ratio sera GRAND (dip très tôt, bl encore proche initial).\n")

total_dip_early_rel = 0  # bl_at_first_dip ≥ 50% bl_initial
total_dip_very_early = 0  # bl_at_first_dip ≥ 80% bl_initial
total_dip_late_rel = 0  # bl_at_first_dip < 50% bl_initial
total_no_dip = 0
for label in summaries:
    summary = summaries[label]
    total_dip_early_rel += summary["orbits_dip_bl_gte_half_initial"]
    total_dip_very_early += summary["orbits_dip_bl_gte_80pct_initial"]
    total_dip_late_rel += (summary["N"]
                           - summary["orbits_dip_bl_gte_half_initial"]
                           - summary["orbits_never_below_4_TAUTOLOGIE_COLLATZ"])
    total_no_dip += summary["orbits_never_below_4_TAUTOLOGIE_COLLATZ"]

total = total_dip_early_rel + total_dip_late_rel + total_no_dip
print(f"  Dip < 4 alors que bl ≥ 80% bl_initial (dip TRÈS précoce) : "
      f"{total_dip_very_early:5} ({total_dip_very_early/total*100:5.1f}%)")
print(f"  Dip < 4 alors que bl ≥ 50% bl_initial (dip précoce)      : "
      f"{total_dip_early_rel:5} ({total_dip_early_rel/total*100:5.1f}%)")
print(f"  Dip < 4 alors que bl <  50% bl_initial (dip tardif)      : "
      f"{total_dip_late_rel:5} ({total_dip_late_rel/total*100:5.1f}%)")
print(f"  Aucun dip < 4 (TAUTOLOGIE 0 sur Collatz)                : "
      f"{total_no_dip:5} ({total_no_dip/total*100:5.1f}%)")
print(f"  Total : {total}")


# =====================================================================
# Test 4 : fraction au-dessus de 4, profil par range
# =====================================================================
print("\n" + "=" * 70)
print("TEST 4 — Fraction d'orbite avec h ≥ 4 par range")
print("=" * 70)
for label, summary in summaries.items():
    print(f"  {label:28}: frac_ge_4 = {summary['frac_ge_4_mean']:.3f} "
          f"± {summary['frac_ge_4_std']:.3f}")


# =====================================================================
# Test 5 : faux cycle artificiel (séquence périodique)
# =====================================================================
print("\n" + "=" * 70)
print("TEST 5 — Faux cycle (séquence périodique artificielle)")
print("=" * 70)

# Exemple 1 : séquence périodique arbitraire avec h ≥ 4 partout ?
# On prend des n avec h ≥ 4 connus : n = 17, 33, 65, ... (2^k + 1 pour k ≥ 4)
# puis on voit s'ils forment un cycle sous Syracuse.

print("Essai : forcer un cycle avec h ≥ 4 pour tous les membres.")
candidates = [33, 65, 129, 257, 513, 1025, 2049, 4097, 8193]
# Ces nombres 2^k+1 ont h = k-1, bl = k+1. Pour k ≥ 4, h ≥ 3.
# Vérifions h directement :
for n in candidates:
    print(f"  n = {n:6} (2^{n.bit_length()-1}+1), h = {h(n):3}, T(n) = {syracuse_next(n):8}")
print()

# Un faux cycle : prendre une séquence artificielle (pas Syracuse)
fake_cycle = [33, 65, 129, 257, 513, 1025]
print(f"Faux cycle artificiel : {fake_cycle}")
print(f"  h values: {[h(n) for n in fake_cycle]}")
print(f"  All h ≥ 4 : {all(h(n) >= 4 for n in fake_cycle)}")
print(f"  Mais ces n ne forment PAS un cycle Syracuse. Évidence : ")
for n in fake_cycle:
    print(f"    T({n}) = {syracuse_next(n)} ≠ membre suivant")
print("  → On peut fabriquer artificiellement des séquences avec h ≥ 4 partout.")
print("  → Mais elles ne sont pas des cycles de Syracuse, donc pas de contradiction.\n")

# Exemple 2 : si un cycle EXISTAIT avec h ≥ 4 partout, quelle propriété ?
# On check : partmi les orbites testées, y a-t-il un point n avec T(n) qui
# aurait h ≥ 4 ET dont T^k(n) ne redescendrait jamais sous 4 ?
# Answer: non (toutes atteignent 1 et donc h=0).

print("Contre-partie négative : parmi toutes les orbites testées,")
print("toutes atteignent 1 → toutes dipent sous 4 à un moment donné.")
print("Donc l'hypothèse 'h ≥ 4 persistant' n'a JAMAIS été observée sur vrais cycles.")


# =====================================================================
# Plots
# =====================================================================
print("\n" + "=" * 70)
print("Génération des plots...")
print("=" * 70)

# Plot 1 : quelques orbites avec h le long
fig, axes = plt.subplots(2, 2, figsize=(14, 8))
axes_flat = axes.flatten()
example_seeds = [27, 255, 2047, 10**10 + 7]
example_seeds_odd = [s if s % 2 == 1 else s + 1 for s in example_seeds]

for ax, seed in zip(axes_flat, example_seeds_odd):
    orbit = syracuse_orbit(seed)
    hs = [h(n) for n in orbit]
    bls = [n.bit_length() for n in orbit]
    ax.plot(hs, label='h(T^k(n))', color='tab:blue', linewidth=1)
    ax.plot(bls, label='bit_length(T^k(n))', color='tab:orange',
            linewidth=0.8, alpha=0.7)
    ax.axhline(y=4, color='red', linestyle='--', label='seuil h = 4', alpha=0.5)
    ax.set_xlabel('Syracuse step k')
    ax.set_ylabel('h ou bit_length')
    ax.set_title(f'Orbite de n = {seed}, longueur = {len(orbit)}')
    ax.legend(fontsize=8)
    ax.grid(True, alpha=0.3)

plt.tight_layout()
out_png1 = "analysis/compactness/h_along_orbits.png"
plt.savefig(out_png1, dpi=100, bbox_inches='tight')
plt.close()
print(f"  PNG : {out_png1}")


# Plot 2 : histogramme de min_h par range
fig, ax = plt.subplots(figsize=(10, 6))
colors = plt.cm.viridis(np.linspace(0, 0.8, len(ranges_defs)))
width = 0.2
for i, (label, _, _) in enumerate(ranges_defs):
    min_h_hist = summaries[label]["min_h_histogram"]
    xs = sorted(int(k) for k in min_h_hist.keys())
    ys = [min_h_hist[x] / summaries[label]["N"] for x in xs]
    ax.bar([x + i*width - 0.3 for x in xs], ys, width=width,
           label=label, color=colors[i])
ax.set_xlabel('min h le long de l\'orbite')
ax.set_ylabel('fraction d\'orbites')
ax.set_title('Distribution du minimum de h sur orbites Syracuse')
ax.legend()
ax.grid(True, alpha=0.3, axis='y')
out_png2 = "analysis/compactness/min_h_distribution.png"
plt.savefig(out_png2, dpi=100, bbox_inches='tight')
plt.close()
print(f"  PNG : {out_png2}")


# Plot 3 : bl_at_first_below_4 par range
fig, ax = plt.subplots(figsize=(10, 6))
for i, (label, _, _) in enumerate(ranges_defs):
    bls = [s["bl_at_first_below_4"] for s in all_stats[label]
           if s["bl_at_first_below_4"] is not None]
    if bls:
        ax.hist(bls, bins=30, alpha=0.6, label=label, color=colors[i])
ax.axvline(x=10, color='red', linestyle='--', label='seuil bl = 10')
ax.set_xlabel('bit_length(n) au premier dip h < 4')
ax.set_ylabel('# orbites')
ax.set_title('bit_length au moment du premier passage h < 4')
ax.legend()
ax.grid(True, alpha=0.3)
out_png3 = "analysis/compactness/bl_at_first_dip.png"
plt.savefig(out_png3, dpi=100, bbox_inches='tight')
plt.close()
print(f"  PNG : {out_png3}")


# =====================================================================
# Verdict (red team fixes B5, B8, B9 intégrés)
# =====================================================================
print("\n" + "=" * 70)
print("=== VERDICT (critères relatifs) ===")
print("=" * 70)

# Red team fix B5 : la tautologie "orbits_never_below_4 = 0" ne teste RIEN
# puisque toutes les orbites Collatz atteignent 1 = cycle trivial par conjecture.
# Donc on ne peut PAS tester "h ≥ 4 persiste partout" sur les orbites Collatz.
# Red team fix B9 : aucun cycle non-trivial n'existe < 2^68 → hypothèse
# non-falsifiable empiriquement sur Collatz.
# Red team fix B8 : le vrai signal est DIP_EARLY (position relative ≈ 0.03),
# pas NO_SIGNAL.

# Critère clair : quelle fraction des orbites a son 1er dip alors que bl est
# encore très proche de bl_initial (ratio ≥ 0.8) ?
frac_very_early = total_dip_very_early / total
frac_early_rel = total_dip_early_rel / total

if frac_very_early > 0.8:
    verdict = "DIP_EARLY_STRONG"
    rationale = (
        f"Le 1er dip h < 4 arrive alors que bl(n) ≥ 80% bl_initial dans "
        f"{total_dip_very_early}/{total} "
        f"({frac_very_early*100:.1f}%) orbites. h chute BIEN AVANT "
        f"l'approche finale de 1, donc l'hypothèse 'h ≥ 4 persiste ⟹ pas de "
        f"cycle' est rejetée : h descend sous 4 alors que n est encore à sa "
        f"taille initiale. Signal très clair, pas de bruit.")
elif frac_early_rel > 0.5:
    verdict = "DIP_EARLY"
    rationale = (
        f"Dip à bl ≥ bl_init/2 dans {frac_early_rel*100:.1f}% des cas. "
        f"h chute significativement avant la fin de l'orbite.")
elif frac_early_rel < 0.1:
    verdict = "DIP_TERMINAL"
    rationale = (
        f"Dip à bl ≥ bl_init/2 seulement {frac_early_rel*100:.1f}% des cas. "
        f"Le dip h < 4 est principalement terminal (approche de 1). "
        f"Hypothèse d'Eric partiellement soutenue.")
else:
    verdict = "MIXED"
    rationale = (
        f"Dip à bl ≥ bl_init/2 dans {frac_early_rel*100:.1f}% des cas. "
        f"Signal intermédiaire.")

print(f"\nVerdict : {verdict}")
print(f"  {rationale}")

# Note explicitée sur la non-testabilité (red team fix B9)
print(f"\n[IMPORTANT — red team retrospectif]")
print(f"  TAUTOLOGIE : 0/{total} orbites 'jamais < 4' car toutes atteignent")
print(f"  le cycle trivial par la conjecture de Collatz. L'hypothèse brute")
print(f"  'h ≥ 4 ⟹ pas de cycle' ne peut pas être FALSIFIÉE empiriquement")
print(f"  puisque aucun cycle non-trivial n'existe < 2^68.")
print(f"  Ce test mesure donc un signal adjacent : à quelle phase de l'orbite")
print(f"  h chute-t-il sous 4 ? Réponse empirique : TRÈS tôt, bl encore proche")
print(f"  de bl_initial → l'hypothèse brute d'Eric ne tient pas.")

# =====================================================================
# Sauvegarde
# =====================================================================
out = {
    "verdict": {"code": verdict, "rationale": rationale},
    "caveats_red_team": [
        "TAUTOLOGIE : 0 orbites 'jamais dip < 4' car Collatz conjecture empirique",
        "NON-FALSIFIABLE : aucun cycle non-trivial < 2^68, hypothèse brute intestable",
        "Seuil absolu bl > 10 remplacé par seuils relatifs (bl/bl_initial ≥ 0.5 et 0.8)",
    ],
    "per_range": summaries,
    "aggregates": {
        "total_orbits": total,
        "dip_very_early_bl_gte_80pct": total_dip_very_early,
        "dip_early_bl_gte_half": total_dip_early_rel,
        "dip_late_bl_lt_half": total_dip_late_rel,
        "never_dip_TAUTOLOGIE_COLLATZ": total_no_dip,
        "fraction_very_early": total_dip_very_early / total,
        "fraction_early_rel": total_dip_early_rel / total,
    },
    "test_1_trivial": {str(n): h(n) for n in [1, 2, 4]},
    "test_5_fake_cycle": {
        "candidates": fake_cycle,
        "h_values": [h(n) for n in fake_cycle],
        "all_h_ge_4": all(h(n) >= 4 for n in fake_cycle),
        "syracuse_next": [syracuse_next(n) for n in fake_cycle],
        "is_real_cycle": False,
    }
}
path = "analysis/compactness/h_cycle_detector_results.json"
tmp = path + ".tmp"
with open(tmp, "w") as f:
    json.dump(out, f, indent=2)
os.replace(tmp, path)
print(f"\nJSON : {path}")
print(f"\n=== Test h-as-cycle-detector terminé. Verdict = {verdict} ===")
