# RAPPORT SPRINT 4b — CompactnessDefs.lean (h, IsCompact, C)
**Branche** : `claude/binary-compactness`
**Date** : 2026-04-19
**Référence** : `NOTE_2ADIC_REFRAMING_v3.md` §2.1, §4.2

---

## 🎯 Verdict global : **GOLD**

- `lake build ProjetCollatz.CompactnessDefs` → EXIT 0, 0 warning
- `lake env lean test/TestCompactnessDefs.lean` → EXIT 0
- **0 sorry, 0 axiome**
- **6 théorèmes prouvés**
- 15 tests `native_decide` passent

---

## 📋 Protocole suivi

1. **Exploration Mathlib** : `Nat.bits`, `Nat.zero_bits`, `Nat.one_bits`,
   `Nat.bit0_bits`, `List.dropWhile_cons_of_pos`.
2. **Red team plan** (agent parallèle, AVANT écriture) → verdict PROCEED avec 4
   corrections identifiées (utiliser `Nat.bit0_bits` direct, `simp` au lieu
   de `rfl`, `native_decide` pour les tests, import minimal).
3. **Écriture** + 2 itérations fix (`Set.mem_setOf_eq` inconnu, `omega` fail
   sur unfold implicite → utiliser `show` + `have` explicites).
4. **Build GOLD** : 0 sorry, 0 axiome, 119 jobs compilés.
5. **Tests** : 15 examples `native_decide` sur valeurs concrètes (incl. 27,
   73, 267, 1025 des rapports Sprints 1-3).
6. **Red team code final** (agent parallèle, APRÈS écriture) → verdict GREEN,
   1 observation mineure (import superflu `Mathlib.Data.List.TakeWhile`).
7. **Fix import** : supprimé avec commentaire d'explication. Build + tests
   toujours EXIT 0.

---

## 📂 Livrables

### `ProjetCollatz/CompactnessDefs.lean` (117 lignes)

Structure :

1. **§1 Fonction `h` et dérivées (lignes 45-77)**
   - `private def maxFalseRunAux` — scan left-to-right avec accumulateur
     et meilleur run trouvé.
   - `def List.maxFalseRun : List Bool → ℕ` — wrapper public.
   - `def h : ℕ → ℕ` — longueur du plus grand bloc interne de zéros.
   - `def IsCompact (k n : ℕ) : Prop := h n < k`.
   - `def C (k : ℕ) : Set ℕ := { n | IsCompact k n }`.

2. **§2 Lemmes structurels (lignes 79-117)**
   - `@[simp] h_zero : h 0 = 0` — prouvé via `Nat.zero_bits` + `rfl`.
   - `@[simp] h_one : h 1 = 0` — prouvé via `Nat.one_bits` + `rfl`.
   - `one_is_compact {k} (hk : 1 ≤ k) : IsCompact k 1` — via `simp` + `omega`.
   - `@[simp] h_two_mul (n) : h (2 * n) = h n` — **lemme clé** via
     `Nat.bit0_bits` + `List.dropWhile_cons_of_pos`.
   - `double_preserves_compact (k n) (hn : IsCompact k n) : IsCompact k (2 * n)`
     — corollaire direct de `h_two_mul`.
   - `C_monotone (k : ℕ) : C k ⊆ C (k + 1)` — trivial par `omega`.

### `test/TestCompactnessDefs.lean` (53 lignes)

15 `example` avec `native_decide` :
- **h sur valeurs concrètes** : 0, 1, 2, 3, 4, 5, 9, 17, 27, 73, 267, 1025.
- **IsCompact** : `IsCompact 4 27` (True), `¬ IsCompact 4 267` (False).
- **Application `double_preserves_compact`** : 27 compact ⟹ 54 compact.
- **Application `C_monotone`** : `n ∈ C 3 → n ∈ C 4`.

---

## 📊 Résumé chiffré

| Métrique | Valeur |
|----------|-------:|
| Lignes CompactnessDefs.lean | 117 |
| Lignes TestCompactnessDefs.lean | 53 |
| Sorry | **0** |
| Axiomes | **0** |
| Théorèmes prouvés | **6** |
| Tests `native_decide` | 15 |
| `lake build` exit | 0 |
| Warnings build | 0 |

---

## 🔍 Red teams effectués

### Red team plan (avant écriture) — PROCEED
- Validation de l'algorithme `maxFalseRunAux` sur 5 cas tests.
- Sémantique de `dropWhile (!·)` alignée avec Python `rstrip("0")` MSB.
- Risque identifié : `rfl` terminal après `rw [Nat.bit0_bits]` (résolu via `simp`).
- Recommandation `Nat.bit0_bits` plutôt que `Nat.bits_append_bit` manuel (appliquée).
- Recommandation `native_decide` pour les tests (appliquée).

### Red team code (après écriture) — GREEN
- 11 checks tous PASS (algorithme, sémantique h, tests, preuves, simp-loop,
  namespace, conventions, imports).
- 1 observation mineure : `Mathlib.Data.List.TakeWhile` superflu
  (`dropWhile_cons_of_pos` vient du core Lean). **Fix appliqué**.
- Verdict : **GREEN, prêt pour commit**.

---

## 🔬 Points mathématiques vérifiés

1. **Correction de `maxFalseRunAux`** : scan left-to-right avec invariant
   `(acc, best)`. Le `max acc best` final capture un éventuel run de queue
   (non exercé pour `h`, car `(bits n).dropWhile (!·)` se termine par `true`).
2. **Sémantique `dropWhile (!·)` = `rstrip("0")` MSB** : vérifié sur 9, 12, 17,
   27, 73, 267, 1025.
3. **Preuve `h_two_mul`** : `Nat.bit0_bits` donne `bits (2n) = false :: bits n`,
   puis `dropWhile_cons_of_pos` (`!false = true`) élimine le `false` de tête,
   réduisant à `(bits n).dropWhile (!·)`. Donc `h(2n) = h(n)`. Algèbre intacte.
4. **Cas limites** :
   - `n = 0` : `2*0 = 0`, `h 0 = h 0` trivialement.
   - `n = 1` : `h 1 = 0`, donc `IsCompact k 1 ↔ k > 0`.
   - `n = 2` : `h 2 = h (2*1) = h 1 = 0` (par `h_two_mul`).

---

## 🔴 Limites et angles morts

1. **Pas de lemme `h_odd_mul`** : `h (2*n + 1) = ?` non formalisé (complexe,
   hors scope Sprint 4b). Sprint 4c ou 4d futur.

2. **Convention nom `h`** : court mais risqué en cas d'`open`. Noté dans le red
   team, non bloquant.

3. **Pas d'interface avec `SyracuseDefs.v2Nat`** : Sprint 4b définit `h` mais
   n'établit pas de pont avec la machinerie existante du projet. Point à
   traiter au Sprint 4c (ex : `Compactness.h_of_syr_step`).

4. **`native_decide` dans les tests** : dépend du compilateur Lean. Robuste
   mais le `decide` pur (kernel) serait plus formel. Acceptable pour Sprint 4b.

---

## ➡️ Prochaines étapes (Sprint 4c / 4d)

### Sprint 4c (suggestion)
- Lemmes supplémentaires sur `h` : `h_two_add_one` ou `h_bit_true`.
- Interface avec `SyracuseDefs.v2Nat` : `h n = v2_somewhere(n)` ?
- Connexion avec Sprint 4a : `C_4 ∩ [1, N]` comme union finie de cylindres
  2-adiques (via `ProjetCollatz.PAdic.cylinder`).

### Sprint 4d (ambitieux)
- Formaliser le T3 no-go (§2.3 de la note v3) avec `CompactnessDefs`.
- Interface entre `h` et `PadicInt.valuation` (bridge lemme mentionné en
  Sprint 4a red team).

---

## 📦 Commits proposés

```
feat(compactness): add h, IsCompact, C definitions with trivial lemmas

- Implements NOTE_2ADIC_REFRAMING_v3.md §2.1, §4.2
- def h : ℕ → ℕ (longest internal zero block in binary rep)
- def IsCompact (k n : ℕ) : Prop := h n < k
- def C (k : ℕ) : Set ℕ := { n | IsCompact k n }
- 6 proved theorems: h_zero, h_one, one_is_compact, h_two_mul,
  double_preserves_compact, C_monotone
- 0 sorry, 0 axiom (GOLD)
- lake build EXIT 0, 0 warnings
- Red team: 2 passes GREEN (plan + code)

test(compactness): 15 native_decide tests for h on concrete values

Covers h values for 0, 1, 2, 3, 4, 5, 9, 17, 27, 73, 267, 1025
and applications of IsCompact, double_preserves_compact, C_monotone.

docs(sprint4b): GOLD verdict report
```

3 commits séparés (feat, test, docs).

---

## 🌟 Synthèse en une phrase

> **Sprint 4b GOLD livré en ~1.5h : 117 lignes Lean 4 définissant `h`,
> `IsCompact`, `C` + 6 théorèmes prouvés (0 sorry, 0 axiome), 15 tests
> `native_decide` PASS, 2 passes red team GREEN, prêt pour commit.**
