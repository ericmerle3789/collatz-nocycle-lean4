import ProjetCollatz.SyracuseDefs
import ProjetCollatz.CollatzCore
import ProjetCollatz.CollatzOddInst

/-!
# HardLowerBoundPaper.lean

But : fournir un « Lean paper » (mini-article) qui expose, de façon *lisible* et *audit-able*,
les briques **générales** (∀ trajectoires) utilisées ensuite par les bridges (Rule4b / Branch).

Philosophie :
- Ici : uniquement du **béton** (aucun axiome empirique).
- Les hypothèses data-level (SEL, Rule4b) restent confinées dans `ProjetCollatz/Hypotheses.lean`.

Analogie :
- `SyracuseDefs.lean` = l'atelier (plein de machines/outils)
- ce fichier = le manuel « papier » qui explique quelles pièces s'emboîtent et quelles vis serrer,
  dans un ordre logique, sans dépendre d'une liste finie de cas.

Ce fichier commence volontairement *petit* : on verrouille d'abord les interfaces et le plan.
On ajoutera ensuite (1 théorème à la fois) les lemmes de bornes « durs » dès qu'ils sont exprimés
avec les bons objets (`Nrec`, `steps_up_to`, somme des `a_i`, etc.).
-/


namespace ProjetCollatz

open scoped BigOperators

noncomputable section

/-!
## 1) Rappels : briques Syracuse (béton)

Tout ce qui suit est déjà prouvé dans `SyracuseDefs.lean`. On le ré-expose ici
pour que l'« article » ait une lecture linéaire.
-/

-- Valuation 2-adique (convention `v2Nat 0 = 0`).
#check v2Nat
#check pow2_v2Nat_dvd
#check pow2_dvd_le_v2Nat_pos

-- Macro-pas Syracuse odd→odd.
#check syracuseNext
#check syracuseNext_spec
#check syracuseNext_odd

-- Suites et reconstruction `Nrec`.
#check nSeq
#check aSeq
#check x0_of_start
#check NrecSyr
#check steps_up_to_NrecSyr

/-!
## 2) Objet « paper » : l'interface du lemme dur

Le lemme dur qu'on vise (bientôt) a la forme suivante (schéma) :

1) À partir d'une trajectoire reconstruite `Nrec n0 a`, on obtient une inégalité générale
   qui dépend de `K` et de `∑_{i < K} a_i`.

2) Donc si on dispose d'une hypothèse *structurelle* sur la somme des `a_i`
   (ex : `∑ a_i ≤ c*K`), on dérive un lower bound exponentiel.

Ce fichier sert à :
- formaliser proprement la **forme** de ces énoncés,
- isoler les dépendances (CollatzCore / CollatzOddInst),
- éviter que les bridges soient un mélange de « data » et de « papier ».

⚠️ Autocritique (rigueur) :
- On n'implémente pas ici un énoncé qui dépendrait d'un nom de lemme inexistant.
- Prochaine étape (action unique) : greper/identifier dans `CollatzOddInst.lean`
  le lemma exact déjà disponible (ou écrire l'induction si nécessaire), puis l'insérer ici.
-/

/-!
## 3) Premiers corollaires déjà utilisables (sans nouvelles preuves)

Même sans le « lemme dur » final, on peut déjà figer des corollaires *structurels*
qui sont de vrais résultats généraux :

- `steps_up_to_NrecSyr` donne un témoin `steps_up_to` pour la trajectoire reconstruite
  associée à un `start_n`. C'est une brique standard de plomberie pour brancher ensuite
  les lemmes de bornes qui vivent dans `CollatzCore`.
-/

theorem steps_up_to_NrecSyr_paper (start_n : ℕ) (K : ℕ) :
    _root_.CollatzCore.steps_up_to (fun k => NrecSyr start_n k) (aSeq start_n) K := by
  simpa using (steps_up_to_NrecSyr start_n K)


/-
## 4) Somme partielle des valuations `a_i`

C'est le premier objet "paper" concret qui manquait :
- on veut parler de `S(K) = ∑_{i < K} a_i`
- puis exprimer des hypothèses du type `S(K) ≤ c*K`.

Ici on définit la somme finie avec `Finset.range K`.
C'est **général** (∀ suites `a : ℕ → ℕ`) et ne dépend d'aucun oracle.
-/

/-- Somme partielle `S(K) = ∑_{i < K} a i` (sur `ℕ`). -/
def aSum (a : ℕ → ℕ) (K : ℕ) : ℕ :=
  Finset.sum (Finset.range K) (fun i => a i)

/-- Version spécialisée à la suite des valuations `aSeq start_n`. -/
def aSumSeq (start_n : ℕ) (K : ℕ) : ℕ := aSum (aSeq start_n) K

/-- Déroulage : `S(K+1) = S(K) + a K`. -/
theorem aSum_succ (a : ℕ → ℕ) (K : ℕ) :
    aSum a (K + 1) = aSum a K + a K := by
  -- `∑ i < K+1, a i = (∑ i < K, a i) + a K`
  simpa [aSum, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using (Finset.sum_range_succ (fun i => a i) K)

/-- Déroulage spécialisé : `aSumSeq start_n (K+1) = aSumSeq start_n K + aSeq start_n K`. -/

theorem aSumSeq_succ (start_n : ℕ) (K : ℕ) :
    aSumSeq start_n (K + 1) = aSumSeq start_n K + aSeq start_n K := by
  simpa [aSumSeq] using (aSum_succ (a := aSeq start_n) K)


/-
## 5) Le « lemme dur » (ré-export) : bornes générales sur `Nrec`

Ici, on ne prouve rien de nouveau : on **ré-exporte** (format “paper”) les lemmes déjà
présents dans `CollatzOddInst.lean`, en les ré-écrivant avec nos notations `aSum`.

C'est le point de bascule vers la généralisation :
- ces énoncés valent pour **toute** suite `a : ℕ → ℕ` et tout `n0 : ℚ`.
- les oracles (SEL/Rule4b) ne servent qu'à fournir ensuite une hypothèse de type "mean".
-/

/-- Version paper : application directe du noyau dur à `Nrec`, avec `aSum`. -/
theorem hard_lower_bound_inst_paper (n0 : ℚ) (a : ℕ → ℕ) (K : ℕ) :
    _root_.CollatzOddInst.Nrec n0 a K ≥
      _root_.CollatzOddInst.Nrec n0 a 0 * (3 : ℚ)^K /
        ((2 : ℚ) ^ (aSum a K)) := by
  -- `aSum a K` est définitionnellement `Finset.sum (Finset.range K) (fun i => a i)`
  simpa [aSum] using (_root_.CollatzOddInst.hard_lower_bound_inst n0 a K)

/-- Version paper : borne exponentielle si la moyenne des `a_i` est bornée. -/
theorem hard_lower_bound_mean_inst_paper (n0 : ℚ) (a : ℕ → ℕ) (K t : ℕ)
    (hn0 : 0 ≤ n0)
    (hmean : Finset.sum (Finset.range K) (fun i => (a i : ℚ)) ≤ (t : ℚ) * (K : ℚ)) :
    _root_.CollatzOddInst.Nrec n0 a K ≥
      _root_.CollatzOddInst.Nrec n0 a 0 * ((3 : ℚ) / ((2 : ℚ) ^ t)) ^ K := by
  -- `∑ i ∈ range K, (a i : ℚ)` est notation pour `Finset.sum (range K) ...`
  have hmean' : (∑ i ∈ Finset.range K, (a i : ℚ)) ≤ (t : ℚ) * (K : ℚ) := by
    simpa using hmean
  simpa using (_root_.CollatzOddInst.hard_lower_bound_mean_inst (n0 := n0) (a := a) (K := K) (t := t) hn0 hmean')

/-!
## 6) Hypothèse "paper" : borne moyenne (interface universelle)

On fige ici la forme exacte de la **clé** que devront fournir les bridges (Rule4b/Branch)
ou, plus tard, un invariant/argument général.

- `MeanBound a K t` est une hypothèse purement *formelle* (aucune donnée, aucun oracle).
- Le paper prouve : `MeanBound` ⇒ borne exponentielle (via le noyau dur).

C'est la séparation robuste :
- Le paper (béton) : "si on me donne MeanBound, je conclus".
- Les bridges (bois) : "voici pourquoi MeanBound est vraie dans tel contexte".
-/

/-- Hypothèse paper : somme (en ℚ) des `a_i` sur `range K` bornée par `t*K`. -/
def MeanBound (a : ℕ → ℕ) (K t : ℕ) : Prop :=
  Finset.sum (Finset.range K) (fun i => (a i : ℚ)) ≤ (t : ℚ) * (K : ℚ)

/-- Corollaire paper : `MeanBound` implique la borne exponentielle sur `Nrec`. -/
theorem hard_lower_bound_of_MeanBound (n0 : ℚ) (a : ℕ → ℕ) (K t : ℕ)
    (hn0 : 0 ≤ n0)
    (hMB : MeanBound a K t) :
    _root_.CollatzOddInst.Nrec n0 a K ≥
      _root_.CollatzOddInst.Nrec n0 a 0 * ((3 : ℚ) / ((2 : ℚ) ^ t)) ^ K := by
  -- Pure délégation à `hard_lower_bound_mean_inst_paper`.
  simpa [MeanBound] using
    (hard_lower_bound_mean_inst_paper (n0 := n0) (a := a) (K := K) (t := t) hn0 hMB)

/-- Spécialisation Syracuse (odd→odd) : `MeanBound` sur `aSeq` ⇒ borne exponentielle sur `NrecSyr`. -/
theorem syracuse_hard_lower_bound_of_MeanBound (start_n K t : ℕ)
    (hn0 : 0 ≤ x0_of_start start_n)
    (hMB : MeanBound (aSeq start_n) K t) :
    NrecSyr start_n K ≥ NrecSyr start_n 0 * ((3 : ℚ) / ((2 : ℚ) ^ t)) ^ K := by
  simpa [NrecSyr] using
    (hard_lower_bound_of_MeanBound (n0 := x0_of_start start_n) (a := aSeq start_n)
      (K := K) (t := t) hn0 hMB)

/-
### Spécialisation Syracuse (odd→odd)

On instancie `n0` et `a` avec les objets Syracuse factorisés :
- `n0 = x0_of_start start_n`
- `a = aSeq start_n`
- trajectoire reconstruite `NrecSyr start_n`.
-/

theorem syracuse_hard_lower_bound_inst (start_n K : ℕ) :
    NrecSyr start_n K ≥
      NrecSyr start_n 0 * (3 : ℚ)^K /
        ((2 : ℚ) ^ (aSumSeq start_n K)) := by
  simpa [NrecSyr, aSumSeq, aSum] using
    (hard_lower_bound_inst_paper (n0 := x0_of_start start_n) (a := aSeq start_n) (K := K))

end

end ProjetCollatz
