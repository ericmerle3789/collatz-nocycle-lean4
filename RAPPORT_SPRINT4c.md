# RAPPORT SPRINT 4c — CompactnessSyracuseLink.lean (bridge h ↔ Syracuse)
**Branche** : `claude/binary-compactness`
**Date** : 2026-04-19
**Référence** : `NOTE_2ADIC_REFRAMING_v3.md` §2.3, §4.2
**Suite de** : RAPPORT_SPRINT4b.md

---

## 🎯 Verdict global : **GOLD**

- `lake build ProjetCollatz.CompactnessSyracuseLink` → EXIT 0 (7889 jobs)
- `lake env lean test/TestCompactnessSyracuseLink.lean` → EXIT 0
- **0 sorry, 0 axiome**
- **5 théorèmes prouvés**
- 12 `example` passent (`native_decide` + application directe)
- 2 passes red team : plan GREEN, code YELLOW → GREEN après 2 fixes documentaires

---

## 📋 Protocole suivi

1. **Red team plan** (agent parallèle, AVANT écriture) → verdict PROCEED.
   - 4 théorèmes viables identifiés + 1 corollaire.
   - Théorème optionnel `h_3n_plus_one_bound` jugé hors budget (nécessite
     analyse fine de la représentation binaire de 3n+1). Écarté.
2. **Écriture** de `CompactnessSyracuseLink.lean` + `TestCompactnessSyracuseLink.lean`.
3. **3 itérations fix** lors de l'écriture :
   - `rw [hm']` → motive issue (pollution RHS). Fix : `set m := ...` + `conv_lhs`.
   - `(Nat.div_mul_cancel hdvd).symm` orientation opposée à celle attendue.
     Fix : laisser l'orientation naturelle `m * 2^(v2Nat n)`.
   - Test `27 * 16` non-syntaxique pour `IsCompact_mul_pow2`.
     Fix : `27 * 2^4` explicite.
4. **Build GOLD** : 0 sorry, 0 axiome.
5. **Red team code final** (agent parallèle, APRÈS écriture) → verdict YELLOW.
   - Issue 1 : header docstring indiquait "4 théorèmes" au lieu de 5.
   - Issue 2 : double commentaire lignes 60-61 redondant (pouvait être fusionné).
6. **2 fixes documentaires appliqués** :
   - Header : "4 théorèmes" → "5 théorèmes prouvés" + ajout de
     `IsCompact_syracuseNext_iff` à la liste du contenu.
   - Commentaire : fusion du double commentaire en un bloc explicatif unifié.
7. **Build + tests re-vérifiés** EXIT 0 → **GREEN final**.

---

## 📂 Livrables

### `ProjetCollatz/CompactnessSyracuseLink.lean` (92 lignes)

Structure :

1. **§1 `h` invariante par multiplication par puissance de 2 (lignes 39-47)**
   - `h_mul_pow2 (n k : ℕ) : h (n * 2^k) = h n`
   - Preuve par induction sur `k`, cas succ via `pow_succ` + `mul_comm` +
     lemme clé `h_two_mul` (Sprint 4b).

2. **§2 `h` invariante par division par la partie paire (lignes 49-62)**
   - `h_div_pow2_v2Nat (n : ℕ) : h n = h (n / 2^(v2Nat n))`
   - Cas `n = 0` trivial (`simp`).
   - Cas `n ≠ 0` : `pow2_v2Nat_dvd` (SyracuseDefs) + `Nat.div_mul_cancel` +
     `conv_lhs` pour éviter la pollution du RHS.

3. **§3 IsCompact préservé (lignes 64-70)**
   - `IsCompact_mul_pow2 (k m n : ℕ) : IsCompact k (n * 2^m) ↔ IsCompact k n`
   - Corollaire direct de `h_mul_pow2` via `unfold + rw`.

4. **§4 Bridge Syracuse (lignes 72-91)** — **cœur du Sprint 4c**
   - `h_syracuseNext (n : ℕ) : h (syracuseNext n) = h (3 * n + 1)`
     - Preuve : `syracuseNext n = (3n+1) / 2^(v2_3n1 n)` par définition.
       `v2_3n1 = v2Nat ∘ (3·+1)`. Appliquer `h_div_pow2_v2Nat` à `3n+1`
       renvoie exactement `h ((3n+1) / 2^(v2Nat (3n+1))) = h (3n+1)`.
   - `IsCompact_syracuseNext_iff (k n : ℕ) : IsCompact k (syracuseNext n) ↔ IsCompact k (3 * n + 1)`
     - Corollaire de `h_syracuseNext`.

### `test/TestCompactnessSyracuseLink.lean` (58 lignes)

12 `example` :
- **h_mul_pow2** : `h (12 * 4) = h 12`, `h (5 * 8) = h 5`, `h 80 = h 5`,
  `h (3 * 16) = h 3`, `h 48 = 0` (native_decide sur 48 = 110000₂).
- **h_div_pow2_v2Nat** : `h 72 = h (72 / 2^(v2Nat 72))` (72 = 9·8).
- **IsCompact_mul_pow2** : application à `27 * 8` et `27 * 2^4`.
- **h_syracuseNext** : appliqué à 3, 5, 7, 9 (canonical Syracuse iterates).
- **IsCompact_syracuseNext_iff** : forme générique.

---

## 📊 Résumé chiffré

| Métrique | Valeur |
|----------|-------:|
| Lignes CompactnessSyracuseLink.lean | 92 |
| Lignes TestCompactnessSyracuseLink.lean | 58 |
| Sorry | **0** |
| Axiomes | **0** |
| Théorèmes prouvés | **5** |
| Tests `example` | 12 |
| `lake build` exit | 0 |
| Warnings build (hors Sprint 4c) | 0 sur ce fichier |

---

## 🔍 Red teams effectués

### Red team plan (avant écriture) — PROCEED
- Validation de la réduction `h_syracuseNext` à `h_div_pow2_v2Nat (3n+1)`.
- Recommandation : écarter `h_3n_plus_one_bound` (hors budget).
- Recommandation : `conv_lhs` plutôt que `rw` direct sur `n` pour éviter
  la pollution de `v2Nat n`.

### Red team code (après écriture) — YELLOW
- Check 1 (correction `h_mul_pow2`) : PASS.
- Check 2 (correction `h_div_pow2_v2Nat`) : PASS, pattern `set + conv_lhs` validé.
- Check 3 (correction `h_syracuseNext`) : PASS.
- Check 4 (cohérence docstring) : FAIL — "4 théorèmes" au lieu de 5.
- Check 5 (lisibilité preuve Théorème 2) : WARNING — double commentaire redondant.
- Check 6 (tests couvrent les branches) : PASS.
- Check 7 (imports minimaux) : PASS.
- Verdict : **YELLOW, 2 corrections documentaires mineures**.

### Fixes YELLOW → GREEN
1. Header `## Contenu` : ajout de `IsCompact_syracuseNext_iff` et correction
   du compte total 4 → 5.
2. Commentaire lignes 55-57 fusionné en un bloc unifié décrivant le but
   `h n = h m` et la stratégie `conv_lhs + hn_eq`.
3. Build + tests re-vérifiés EXIT 0 → **GREEN final**.

---

## 🔬 Points mathématiques vérifiés

1. **Correction de `h_mul_pow2`** : induction sur `k`, cas base `k = 0`
   donne `h (n * 1) = h n` via `simp`. Cas succ utilise
   `n * 2^(k+1) = 2 * (n * 2^k)` et applique `h_two_mul` (Sprint 4b).
2. **Correction de `h_div_pow2_v2Nat`** : la partie paire de `n` est
   `2^(v2Nat n)` par définition (Sprint existant `pow2_v2Nat_dvd`).
   Diviser par cette puissance donne le noyau impair `m`, et
   `h n = h (m * 2^(v2Nat n)) = h m` par `h_mul_pow2`.
3. **Bridge `h_syracuseNext`** : `syracuseNext n = (3n+1) / 2^(v2_3n1 n)`
   par définition. Comme `v2_3n1 n = v2Nat (3n+1)`, `syracuseNext n`
   n'est autre que le noyau impair de `3n+1`. Par `h_div_pow2_v2Nat`,
   `h (3n+1) = h (noyau impair de 3n+1) = h (syracuseNext n)`.
4. **Conséquence pour Sprint 4d** : l'analyse du drift `Δh(n) := h(T(n)) - h(n)`
   (où `T = syracuseNext`) se réduit à l'analyse de `h(3n+1) - h(n)`.
   Les divisions par 2 ne bruitent plus l'analyse, ce qui ouvre la voie
   au théorème no-go T3 (`NOTE_2ADIC_REFRAMING_v3.md` §2.3).

---

## 🔴 Limites et angles morts

1. **Pas de lemme `h_3n_plus_one_bound`** : l'étape suivante naturelle
   (`h(3n+1) ≤ h(n) + c` ou contre-exemple rigoureux) est hors scope
   Sprint 4c. Nécessite analyse combinatoire de la représentation
   binaire de `3n+1` — à traiter en Sprint 4d avec les valeurs
   problématiques `r = 9 mod 16` identifiées empiriquement (Sprint 2c).

2. **Bridge avec `PadicInt.valuation`** : Sprint 4c relie `h` à `v2Nat`
   mais pas encore à `PadicInt.valuation` du Sprint 4a. Pont à faire
   en Sprint 4d pour unifier la dynamique 2-adique et la compacité.

3. **`native_decide` dans les tests** : convention héritée de Sprint 4b,
   robuste mais dépend du compilateur Lean.

4. **Warnings build préexistants** : `ProjetCollatz/SyracuseDefs.lean`
   conserve 3 warnings linter (`simpa`, `simp` args inutilisés) non liés
   à Sprint 4c. Hors scope.

---

## ➡️ Prochaines étapes (Sprint 4d)

### Sprint 4d (ambitieux, cible T3 no-go)
- Lemme `h_3n_plus_one_bound` : encadrement de `h(3n+1)` en fonction de `h(n)`
  et de la structure de `n mod 16` (ou plus fin).
- Théorème no-go T3 (`NOTE_2ADIC_REFRAMING_v3.md` §2.3) : sous l'hypothèse
  Collatz, le drift moyen `E[Δh]` sous `syracuseNext` ne peut pas contredire
  la convergence (équivalent formel de la conjecture dans le langage compact).
- Pont `h ↔ PadicInt.valuation` pour boucler la formalisation 4a/4b/4c.

### Sprint 4a-quater (option, fermeture complète)
- Rappel : `cylinder_measure` reste axiomatisé en Sprint 4a-ter, avec plan
  de preuve détaillé en 6 étapes (4-8h Lean estimé). Indépendant de 4c.

---

## 📦 Commits proposés

3 commits séparés (feat + test + docs) :

```
feat(compactness): bridge h and Syracuse dynamics (CompactnessSyracuseLink)

- Implements NOTE_2ADIC_REFRAMING_v3.md §2.3 interface layer
- theorem h_mul_pow2 : h invariant under multiplication by 2^k
- theorem h_div_pow2_v2Nat : h equals h of odd kernel
- theorem IsCompact_mul_pow2 : compactness invariant under doubling
- theorem h_syracuseNext : h(syracuseNext n) = h(3n+1) [key bridge]
- theorem IsCompact_syracuseNext_iff : corollary of h_syracuseNext
- 0 sorry, 0 axiom (GOLD)
- lake build EXIT 0 (7889 jobs)
- Red team: plan PROCEED → code YELLOW → fixed → GREEN

test(compactness): 12 examples for h_mul_pow2, h_syracuseNext, IsCompact

Covers concrete h values (12·4, 5·8, 80, 48, 3·16), h_div_pow2_v2Nat on 72,
IsCompact preservation on 27·8 / 27·2^4, and Syracuse bridge on canonical
iterates (3, 5, 7, 9).

docs(sprint4c): GOLD verdict report (bridge h ↔ Syracuse dynamics)
```

---

## 🌟 Synthèse en une phrase

> **Sprint 4c GOLD livré : 92 lignes Lean 4 établissant le bridge
> `h ∘ syracuseNext = h ∘ (3·+1)` via 5 théorèmes prouvés (0 sorry, 0 axiome),
> 12 tests PASS, 2 passes red team GREEN après 2 fixes documentaires,
> réduisant l'analyse du drift compact Syracuse au drift de la carte
> `n ↦ 3n+1` — étape de plomberie indispensable avant le théorème no-go
> T3 du Sprint 4d.**
