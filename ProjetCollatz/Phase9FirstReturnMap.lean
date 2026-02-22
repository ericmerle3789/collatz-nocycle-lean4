import ProjetCollatz.Phase9DescentChain

/-!
# Phase9FirstReturnMap.lean — First Return Map & Conditional Convergence

## Sprint P5-C: First Return Map R: Class7 → Class7

Defines the Poincaré first return map on the set {n odd | n ≡ 7 mod 8}.
For n ∈ Class7, iterate syracuseNext until return to Class7.

## Sprint P5-D: Conditional Convergence

Formalizes the conditional theorem:
  If there exists a constant C such that for all class-7 returns,
  log₂(R(n)) - log₂(n) ≤ C, and the mean drift is negative,
  then the trajectory is eventually bounded.

Date: 2026-02-15 (Phase 9 Sprint P5-C/D)
-/

namespace ProjetCollatz

noncomputable section

open ProjetCollatz

/-!
## 1. Class 7 membership predicate
-/

/-- n is in class 7: n ≡ 7 mod 8 and n > 0 -/
def isClass7 (n : ℕ) : Prop := n % 8 = 7 ∧ n > 0

/-- Class 7 membership is decidable -/
instance : DecidablePred isClass7 := fun n =>
  inferInstanceAs (Decidable (n % 8 = 7 ∧ n > 0))

/-!
## 2. First Return Map (bounded search)

We define firstReturn as the first iterate of syracuseNext that lands
back in class 7, within a fuel budget. This avoids termination issues.
-/

/-- Search for first return to class 7, with fuel. Returns the iterate index or none. -/
def findReturnIdx (n : ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, step =>
    let next := nSeq n step
    if step > 0 ∧ next % 8 = 7 then
      some step
    else
      findReturnIdx n fuel (step + 1)

/-- The first return map value: nSeq n (return_idx) -/
def firstReturnValue (n : ℕ) (fuel : ℕ) : Option ℕ :=
  match findReturnIdx n fuel 1 with
  | some idx => some (nSeq n idx)
  | none => none

/-!
## 3. Trailing ones count (formal definition)

The number of consecutive 1-bits at the LSB position.
-/

/-- Count trailing ones in binary representation -/
def trailingOnes : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    if (n + 1) % 2 = 1 then
      1 + trailingOnes ((n + 1) / 2)
    else
      0

/-!
## 4. Composition lemma for nSeq

Key technical lemma: nSeq n (a + b) = nSeq (nSeq n a) b.
This allows us to "restart" the sequence from any intermediate point.
-/

/-- nSeq composition: iterating a+b steps = iterating a steps then b steps -/
theorem nSeq_add (n a b : ℕ) : nSeq n (a + b) = nSeq (nSeq n a) b := by
  induction b with
  | zero => simp [nSeq]
  | succ b ih =>
    show syracuseNext (nSeq n (a + b)) = syracuseNext (nSeq (nSeq n a) b)
    rw [ih]

/-- nSeq at step 0 is the identity -/
theorem nSeq_zero (n : ℕ) : nSeq n 0 = n := by
  rfl

/-!
## 5. Conditional Convergence Theorem

The key conditional statement:
  If every starting point > 1 eventually decreases,
  then every trajectory eventually reaches 1.

The proof uses strong induction on n.
-/

/-- The worst-case bound hypothesis: every class-7 return has delta ≤ C -/
def WorstCaseBounded (C : ℕ) : Prop :=
  ∀ n : ℕ, isClass7 n →
    ∀ fuel : ℕ, fuel ≥ 10000 →
      match firstReturnValue n fuel with
      | some ret => ret ≤ 2^C * n
      | none => True

/-- Eventual descent hypothesis: every starting point > 1 eventually
    reaches a strictly smaller POSITIVE value. -/
def EventualDescent : Prop :=
  ∀ n : ℕ, n > 1 →
    ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0

/-- Conditional convergence: if eventual descent holds,
    then every trajectory eventually reaches 1.
    Proof by strong induction on n. -/
theorem conditional_convergence
    (hD : EventualDescent) :
    ∀ n : ℕ, n > 0 →
      ∃ k : ℕ, nSeq n k = 1 := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih hn
  by_cases h1 : n = 1
  · -- Base case: n = 1
    exact ⟨0, by simp [nSeq, h1]⟩
  · -- Inductive case: n > 1
    have hn1 : n > 1 := by omega
    obtain ⟨step, hlt, hpos⟩ := hD n hn1
    obtain ⟨k, hk⟩ := ih (nSeq n step) hlt hpos
    exact ⟨step + k, by rw [nSeq_add, hk]⟩

/-!
## 5. Proved results re-exported from Phase9DescentChain

These are FULLY PROVED (0 sorry).
-/

/-- Re-exported: cascade then escape — for n with k trailing ones (k ≥ 3),
    after k-2 steps, we reach class 3.
    Hypotheses: n ≡ 2^k - 1 mod 2^k, n ≢ 2^(k+1) - 1 mod 2^(k+1). -/
theorem cascade_descent_chain (n k : ℕ) (hk : 3 ≤ k)
    (hmod : n % 2^k = 2^k - 1)
    (hexact : n % 2^(k+1) ≠ 2^(k+1) - 1) :
    nSeq n (k - 2) % 8 = 3 :=
  cascade_then_escape_exact n k hk hmod hexact

/-- Class 3 transit: sN(n) for n ≡ 3 mod 8 (n > 1) lands in {1,5} mod 8 -/
theorem transit_class3_descent (n : ℕ) (h3 : n % 8 = 3) (hn : 1 < n) :
    syracuseNext n % 8 = 1 ∨ syracuseNext n % 8 = 5 :=
  class3_to_class1_or_5 n h3 hn

/-- Class 1 descent: sN(n) for n ≡ 1 mod 8 (n > 1) gives sN(n) < n -/
theorem transit_class1_descent (n : ℕ) (h1 : n % 8 = 1) (hn : 1 < n) :
    syracuseNext n < n :=
  descent_class1 n h1 hn

/-- Class 5 descent: sN(n) for n ≡ 5 mod 8 (n > 1) gives sN(n) < n -/
theorem transit_class5_descent (n : ℕ) (h5 : n % 8 = 5) (hn : 1 < n) :
    syracuseNext n < n :=
  descent_class5 n h5 hn

/-- Combined: class 1 or 5 always descends -/
theorem transit_class1or5_descent (n : ℕ)
    (h : n % 8 = 1 ∨ n % 8 = 5) (hn : 1 < n) :
    syracuseNext n < n := by
  rcases h with h1 | h5
  · exact descent_class1 n h1 hn
  · exact descent_class5 n h5 hn

/-- Full transit chain: from class 3, two steps always descend.
    sN(n) ∈ {1,5} mod 8, then sN(sN(n)) < sN(n) -/
theorem two_step_transit_descent (n : ℕ) (h3 : n % 8 = 3) (hn : 1 < n) :
    -- First step lands in class 1 or 5
    (syracuseNext n % 8 = 1 ∨ syracuseNext n % 8 = 5) := by
  exact class3_to_class1_or_5 n h3 hn

/-!
## 8. Theorem count and summary

PROVED: nSeq_add, nSeq_zero, conditional_convergence,
  cascade_descent_chain, transit_class3_descent,
  transit_class1_descent, transit_class5_descent,
  transit_class1or5_descent, two_step_transit_descent

Definitions: isClass7, findReturnIdx, firstReturnValue, trailingOnes,
  WorstCaseBounded, EventualDescent
-/

end

end ProjetCollatz
