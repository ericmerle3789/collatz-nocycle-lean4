# RAPPORT TRANSFER OPERATOR — Sprint 4d étape 1.5
**Branche** : `claude/binary-compactness`
**Date** : 2026-04-19
**Durée réelle** : 12 s de compute + ~25 min de préparation/analyse

---

## 🎯 Verdict : **PIVOT_OPTION_B**

- L'opérateur de transfert `P(T(n) ≡ j | n ≡ i mod 2^k)` sur les résidus
  impairs NE capture PAS la décroissance empirique α ≈ 0.686 de Δh.
- La chaîne de Markov mod 2^k mélange **beaucoup plus vite** que la queue de Δh :
  `|λ₂(k=7)| = 0.19` vs la valeur attendue `exp(-0.686) = 0.50`.
- Consigne : revenir à **Option B (mesure de comptage)** pour l'étape 2 Lean.

---

## 📊 Résultats chiffrés

| k | # états | \|λ₂\| | α_spectral = -log\|λ₂\| | α_empirique (étape 1) | Écart |
|---|--------:|-------:|------------------------:|----------------------:|------:|
| 4 |      8  | 0.0939 |            **2.3651**   |                0.686  | 1.68  |
| 5 |     16  | 0.1248 |            **2.0811**   |                0.686  | 1.40  |
| 6 |     32  | 0.2145 |            **1.5394**   |                0.686  | 0.85  |
| 7 |     64  | 0.1949 |            **1.6354**   |                0.686  | 0.95  |

- **mean α_spectral = 1.905, std = 0.335** — **non stable** (critère std < 0.05 violé).
- Tendance : α_spectral décroît avec k (2.37 → 1.54) puis remonte (1.64), suggérant
  un plateau autour de **~1.6–2.0** pour k large.
- La valeur attendue `exp(-0.686) ≈ 0.504` n'apparaît **nulle part** dans les
  top-5 modules (maximum observé : 0.2145).

## 🔬 Diagnostic technique

**Toutes les matrices sont stochastiques correctement** :
- `max |rowsum - 1| < 2·10⁻¹⁶` pour k ∈ {5, 6, 7} (exact pour k=4).
- `λ₁ = 1` exactement, `|λ₁| = 1` exactement, unique valeur propre unité.
- **Apériodique + irréductible** pour tous les k testés.

**Top 5 valeurs propres (k=7)** :
- `1.0000` (λ₁ stationnaire)
- `0.1949` (double, probablement pair conjugué ou structure ZMod symétrique)
- `0.1886` (double)
- **Aucun eigenvalue ≈ 0.5** : le trou spectral est **trop grand** pour expliquer
  une queue en `0.504^t`.

## 🔴 Interprétation mathématique

Le mismatch α_spectral ≈ 1.9 vs α_empirique ≈ 0.69 signifie :

1. **La chaîne mod 2^k oublie très vite** sa position initiale (après ~1 étape
   de Syracuse, la distribution des résidus est quasi-uniforme).
2. Mais **Δh ne dépend pas que du résidu** : elle dépend de la structure binaire
   **globale** de `n` et `3n+1`, qui s'étend bien au-delà de `mod 2^k`.
3. **α_empirique ≈ log(2) ≈ 0.693** n'est donc **pas** un effet du trou spectral
   de la chaîne sur les résidus. Origine plus probable :
   - **Distribution géométrique de `v₂(3n+1)`** : `P(v₂ = j) = 2^{-j}` pour j ≥ 1,
     qui injecte directement un facteur `log(2)` dans toute analyse de queue.
   - **Carry propagation** dans la multiplication `3 · n` sur représentation
     binaire : les longs blocs de zéros dans `3n+1` exigent des coïncidences
     binaires de probabilité géométriquement décroissante.
4. L'**opérateur de transfert sur des objets plus riches** (e.g., cylindres
   `ZTwo`, distributions de paires `(résidu, valuation)`) pourrait recapturer
   `α ≈ 0.686`, mais pas la chaîne brute mod 2^k.

## ➡️ Conséquences pour le Sprint 4d étape 2

- **Confirmer Option B (mesure de comptage)** comme cible primaire pour Lean.
- **Abandonner Option B'** (Ruelle transfer operator sur mod 2^k) dans sa forme
  naïve : le bénéfice théorique attendu (α_spectral = α_empirique) n'existe pas.
- **Option B'** reste *potentiellement* viable sur un espace plus fin (cylindres
  2-adiques avec valuation), mais ce serait du travail Sprint 4e/4f.
- **Option D** (analyse spectrale Walsh-Hadamard / Fourier 2-adique) est
  également mise en suspens faute d'indication spectrale simple.

## 📂 Artefacts produits

- [analysis/compactness/transfer_operator_spectrum.py](analysis/compactness/transfer_operator_spectrum.py) — 260 lignes, seed=42
- [analysis/compactness/transfer_spectrum_results.json](analysis/compactness/transfer_spectrum_results.json) — résultats complets
- [analysis/compactness/spectrum_vs_k.png](analysis/compactness/spectrum_vs_k.png) — mismatch visuel

## ✅ Sanity checks passés

1. **Stochasticité exacte** de M pour tous k (sum rows = 1 à erreur flottante près).
2. **Syracuse odd-to-odd** : T(n) toujours impair pour n impair, cohérent.
3. **Seed déterministe** (42 + k) → reproductible.
4. **100 000 samples par résidu** : écart-type des entrées matrice < 1/sqrt(100000) ≈ 0.003,
   donc |λ₂| à 10⁻³ près. L'écart α_spectral vs α_empirique (> 0.8) est bien
   au-delà du bruit d'échantillonnage.

## 🌟 Synthèse en une phrase

> **L'opérateur de transfert sur ZMod(2^k) montre un trou spectral bien plus
> grand que ce qu'impliquerait α_empirique ≈ 0.686, donc cette abstraction ne
> capture pas le mécanisme de décroissance de la queue de Δh ; PIVOT vers
> Option B (mesure de comptage) est la recommandation.**
