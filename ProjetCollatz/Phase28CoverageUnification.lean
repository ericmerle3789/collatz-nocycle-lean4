import ProjetCollatz.Phase27DriftLemma

/-!
# Phase28CoverageUnification.lean — Coverage Unification Theorem

## Purpose

Unify the 25+ individual descent theorems from Phase 9 into a single
coverage density statement:

  **For at least 448 out of 512 odd residues mod 1024, descent is provable.**

This gives a Haar measure lower bound: μ(Descent set in Z₂) ≥ 448/512 ≈ 0.875.

## Strategy

Rather than a 448-way case split (impractical), we use a layered approach:
1. Classes 1 and 5 mod 8: cover 256/512 = 50% (2 theorems)
2. Class 3 mod 16: covers 64 additional residues (1 theorem)
3. Refined sub-cases: cover 99 more (22 theorems)
4. Near-perfect 6-step chains: cover 9 more (9 theorems, Cycle 107)

The Coverage Unification Theorem states that descent is provable for
all odd n > 1 whose residue mod 1024 falls in the covered set.

## Date: 2026-02-17 (Cycle 102), updated 2026-02-18 (Cycle 107)
-/

namespace ProjetCollatz

noncomputable section

open ProjetCollatz

/-!
## Part 1: EventualDescent Predicate

We use the same predicate from Phase9: ∃ step, nSeq n step < n ∧ nSeq n step > 0.
-/

/-- The eventual descent predicate for a starting value n. -/
def EventualDescentAt (n : ℕ) : Prop :=
  ∃ step : ℕ, nSeq n step < n ∧ nSeq n step > 0

/-!
## Part 2: Layer 1 — Classes 1 and 5 mod 8

These two classes cover exactly 256 out of 512 odd residues mod 1024.
Every odd n ≡ 1 mod 8 or n ≡ 5 mod 8 descends in exactly 1 step.
-/

/-- Layer 1a: Descent for all odd n ≡ 1 mod 8. -/
theorem coverage_layer1a (n : ℕ) (h : n % 8 = 1) (hn : n > 1) :
    EventualDescentAt n :=
  eventual_descent_class1 n h hn

/-- Layer 1b: Descent for all odd n ≡ 5 mod 8. -/
theorem coverage_layer1b (n : ℕ) (h : n % 8 = 5) (hn : n > 1) :
    EventualDescentAt n :=
  eventual_descent_class5 n h hn

/-!
## Part 3: Layer 2 — Class 3 mod 16

All odd n ≡ 3 mod 16 descend in 2 steps (salmon trap → abyss).
This covers 64 additional residues mod 1024.
-/

/-- Layer 2: Descent for all odd n ≡ 3 mod 16. -/
theorem coverage_layer2 (n : ℕ) (h : n % 16 = 3) (hn : n > 1) :
    EventualDescentAt n :=
  eventual_descent_mod16_eq3 n h hn

/-!
## Part 4: Layer 3 — Sub-cases of class 11 mod 16 and class 7 mod 8

These refined descent chains cover 99 additional odd residues mod 1024.
The structure is:
- mod 64 = 11 → 3-step descent (covers residues from class 3, sub-case 11 mod 16)
- mod 128 = 59 → 4-step descent
- mod 256 = 43, 7, 39, 79, 95, 135, 175, 199 → variable-step descents
- mod 512 = 79, 199, 335, 455 → longer chains
- mod 1024 = 287, 815, 975 → deep chains
- mod 32 = 23 → covers sub-case of class 7
- mod 128 = 7, 15 → covers more of class 7
-/

-- Layer 3: Examples of individual descent proofs available.
-- Rather than duplicating all 22 proofs, we state the unified coverage
-- theorem that asserts: for any of the covered modular classes,
-- descent holds. This is proved by case-splitting on n % 1024
-- at each layer.

/-- The main unified descent theorem for the first two layers.
    Covers all odd n > 1 with n % 8 ∈ {1, 5} or n % 16 = 3.

    This accounts for 320/512 = 62.5% of odd residues. -/
theorem coverage_layers_1_2 (n : ℕ) (hn : n > 1) (_hodd : n % 2 = 1)
    (h : n % 8 = 1 ∨ n % 8 = 5 ∨ n % 16 = 3) :
    EventualDescentAt n := by
  rcases h with h1 | h5 | h3
  · exact coverage_layer1a n h1 hn
  · exact coverage_layer1b n h5 hn
  · exact coverage_layer2 n h3 hn

/-- Key coverage count for layers 1-2:
    Among odd residues mod 1024, exactly 320 satisfy
    (r % 8 = 1 ∨ r % 8 = 5 ∨ r % 16 = 3). -/
theorem coverage_count_layers_1_2 :
    (Finset.filter (fun r =>
      r % 8 = 1 ∨ r % 8 = 5 ∨ r % 16 = 3)
      (Finset.filter (fun r => r % 2 = 1) (Finset.range 1024))).card = 320 := by
  native_decide

/-!
## Part 5: Layer 3 Unified — Class 3 sub-cases (mod 64, 128, 256)

For n ≡ 11 mod 16 (part of class 3 mod 8), we have sub-theorems
covering additional residues. We unify them progressively.
-/

/-- Layer 3a: n ≡ 11 mod 64 (3-step descent chain) -/
theorem coverage_layer3a (n : ℕ) (h : n % 64 = 11) (hn : n > 1) :
    EventualDescentAt n :=
  eventual_descent_mod64_eq11 n h hn

/-- Layer 3b: n ≡ 59 mod 128 (4-step descent chain) -/
theorem coverage_layer3b (n : ℕ) (h : n % 128 = 59) (hn : n > 1) :
    EventualDescentAt n :=
  eventual_descent_mod128_eq59 n h hn

/-- Layer 3c: n ≡ 43 mod 256 (descent chain from Phase 9) -/
theorem coverage_layer3c (n : ℕ) (h : n % 256 = 43) (hn : n > 1) :
    EventualDescentAt n :=
  eventual_descent_mod256_eq43 n h hn

/-!
## Part 6: Layer 4 — Class 7 sub-cases (mod 32, 128, 256, 512, 1024)
-/

/-- Layer 4a: n ≡ 23 mod 32 -/
theorem coverage_layer4a (n : ℕ) (h : n % 32 = 23) (hn : n > 1) :
    EventualDescentAt n :=
  eventual_descent_mod32_eq23 n h hn

/-- Layer 4b: n ≡ 7 mod 128 -/
theorem coverage_layer4b (n : ℕ) (h : n % 128 = 7) (hn : n > 1) :
    EventualDescentAt n :=
  eventual_descent_mod128_eq7 n h hn

/-- Layer 4c: n ≡ 15 mod 128 -/
theorem coverage_layer4c (n : ℕ) (h : n % 128 = 15) (hn : n > 1) :
    EventualDescentAt n :=
  eventual_descent_mod128_eq15 n h hn

/-!
## Part 7: Coverage Density — The Main Statement

We state the key density result: at least 419/512 of odd residues
mod 1024 are in the provable descent set.

This is formalized via the Finset count.
-/

/-- The set of odd residues mod 1024 for which descent is provable.
    A residue r is covered if it satisfies one of the modular descent conditions. -/
def isDescentCovered (r : ℕ) : Bool :=
  r % 8 = 1
  ∨ r % 8 = 5
  ∨ r % 16 = 3
  ∨ r % 64 = 11
  ∨ r % 128 = 59
  ∨ r % 64 = 43       -- upgraded from r % 256 = 43 (Cycle 105)
  ∨ r % 32 = 23
  ∨ r % 256 = 7
  ∨ r % 256 = 135
  ∨ r % 128 = 7
  ∨ r % 128 = 15
  ∨ r % 256 = 39
  ∨ r % 256 = 95
  ∨ r % 256 = 175
  ∨ r % 512 = 79
  ∨ r % 512 = 335
  ∨ r % 256 = 79
  ∨ r % 512 = 199
  ∨ r % 512 = 455
  ∨ r % 256 = 199
  ∨ r % 1024 = 287
  ∨ r % 1024 = 815
  ∨ r % 1024 = 975
  ∨ r % 256 = 123     -- Cycle 105, 5-step descent
  ∨ r % 256 = 219     -- Cycle 106, 5-step descent (v₂=[1,2,1,1,≥3])
  -- Cycle 107: 9 near-perfect 6-step descent chains (ratio 729/1024)
  ∨ r % 1024 = 347
  ∨ r % 1024 = 507
  ∨ r % 1024 = 923
  ∨ r % 1024 = 423
  ∨ r % 1024 = 583
  ∨ r % 1024 = 735
  ∨ r % 1024 = 367
  ∨ r % 1024 = 999
  ∨ r % 1024 = 575

/-- The covered residues as a Finset. -/
def coveredResidues1024 : Finset ℕ :=
  Finset.filter (fun r => isDescentCovered r = true)
    (Finset.filter (fun r => r % 2 = 1) (Finset.range 1024))

/-- **Coverage Density Theorem**: At least 448 out of 512 odd residues
    mod 1024 have provable descent.

    This establishes: μ_Haar(Descent set ∩ Z₂*) ≥ 448/512 = 0.875

    As recommended by Gemini Deep Think, this is a lower bound on the
    Haar measure of the descent set in the 2-adic integers. -/
theorem coverage_density_448_of_512 :
    coveredResidues1024.card ≥ 448 := by
  native_decide

/-- Backwards compatibility alias for Phase29/30 references. -/
theorem coverage_density_439_of_512 :
    coveredResidues1024.card ≥ 439 := by
  have h := coverage_density_448_of_512
  omega

/-!
## Part 8: Descent Holds for All Covered Residues

This is the unification theorem: for any odd n > 1 whose residue
mod 1024 is in the covered set, eventual descent is provable.
-/

/-- **Coverage Unification Theorem** (partial — layers 1-2):
    Every odd n > 1 with (n % 8 = 1 ∨ n % 8 = 5 ∨ n % 16 = 3) descends. -/
theorem coverage_unified_layers12 (n : ℕ) (hn : n > 1) (hodd : n % 2 = 1)
    (h : n % 8 = 1 ∨ n % 8 = 5 ∨ n % 16 = 3) :
    EventualDescentAt n :=
  coverage_layers_1_2 n hn hodd h

/-- **Combined coverage for layers 1-5 (all 34 theorems)**:
    Descent provable for all n > 1 whose residue mod 1024 belongs
    to any of the 34 certified modular classes. -/
theorem coverage_all_layers (n : ℕ) (hn : n > 1)
    (h : n % 8 = 1 ∨ n % 8 = 5 ∨ n % 16 = 3 ∨ n % 64 = 11
       ∨ n % 128 = 59 ∨ n % 64 = 43 ∨ n % 32 = 23
       ∨ n % 256 = 7 ∨ n % 256 = 135 ∨ n % 128 = 7 ∨ n % 128 = 15
       ∨ n % 256 = 39 ∨ n % 256 = 95 ∨ n % 256 = 175
       ∨ n % 512 = 79 ∨ n % 512 = 335 ∨ n % 256 = 79
       ∨ n % 512 = 199 ∨ n % 512 = 455 ∨ n % 256 = 199
       ∨ n % 1024 = 287 ∨ n % 1024 = 815 ∨ n % 1024 = 975
       ∨ n % 256 = 123 ∨ n % 256 = 219
       -- Cycle 107: 9 near-perfect 6-step chains
       ∨ n % 1024 = 347 ∨ n % 1024 = 507 ∨ n % 1024 = 923
       ∨ n % 1024 = 423 ∨ n % 1024 = 583 ∨ n % 1024 = 735
       ∨ n % 1024 = 367 ∨ n % 1024 = 999 ∨ n % 1024 = 575) :
    EventualDescentAt n := by
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · exact eventual_descent_class1 n h hn
  · exact eventual_descent_class5 n h hn
  · exact eventual_descent_mod16_eq3 n h hn
  · exact eventual_descent_mod64_eq11 n h hn
  · exact eventual_descent_mod128_eq59 n h hn
  · exact eventual_descent_mod64_eq43 n h hn
  · exact eventual_descent_mod32_eq23 n h hn
  · exact eventual_descent_mod256_eq7 n h hn
  · exact eventual_descent_mod256_eq135 n h hn
  · exact eventual_descent_mod128_eq7 n h hn
  · exact eventual_descent_mod128_eq15 n h hn
  · exact eventual_descent_mod256_eq39 n h hn
  · exact eventual_descent_mod256_eq95 n h hn
  · exact eventual_descent_mod256_eq175 n h hn
  · exact eventual_descent_mod512_eq79 n h hn
  · exact eventual_descent_mod512_eq335 n h hn
  · exact eventual_descent_mod256_eq79 n h hn
  · exact eventual_descent_mod512_eq199 n h hn
  · exact eventual_descent_mod512_eq455 n h hn
  · exact eventual_descent_mod256_eq199 n h hn
  · exact eventual_descent_mod1024_eq287 n h hn
  · exact eventual_descent_mod1024_eq815 n h hn
  · exact eventual_descent_mod1024_eq975 n h hn
  · exact eventual_descent_mod256_eq123 n h hn
  · exact eventual_descent_mod256_eq219 n h hn
  -- Cycle 107: 9 near-perfect 6-step chains
  · exact eventual_descent_mod1024_eq347 n h hn
  · exact eventual_descent_mod1024_eq507 n h hn
  · exact eventual_descent_mod1024_eq923 n h hn
  · exact eventual_descent_mod1024_eq423 n h hn
  · exact eventual_descent_mod1024_eq583 n h hn
  · exact eventual_descent_mod1024_eq735 n h hn
  · exact eventual_descent_mod1024_eq367 n h hn
  · exact eventual_descent_mod1024_eq999 n h hn
  · exact eventual_descent_mod1024_eq575 n h hn

/-!
## Part 9: Summary

### PROVED:

1. **coverage_layers_1_2**: Descent for 320/512 odd residues (62.5%)
2. **coverage_count_layers_1_2**: Verified by native_decide
3. **coverage_density_448_of_512**: coveredResidues1024.card ≥ 448 (by native_decide)
4. **Individual layers 3-5**: Wrappers for Phase 9 descent theorems

### ARCHITECTURE:

The coverage is organized in 5 layers:
- Layer 1: mod 8 = 1, 5 (256 residues, 50%)
- Layer 2: mod 16 = 3 (64 residues, 12.5%)
- Layer 3: mod 64, 128, 256 sub-cases of class 3 (variable)
- Layer 4: mod 32, 128, 256, 512, 1024 sub-cases of class 7 (variable)
- Layer 5: 9 near-perfect mod 1024 residues (Cycle 107, 6-step chains)

### NOTE ON EXHAUSTIVE UNIFICATION:

A complete unification theorem mapping every covered residue mod 1024
to its specific descent proof would require a decision procedure.
The individual descent theorems are the CERTIFICATES.
The density count (≥ 448) is the MEASUREMENT.

Together they establish: "For a set of odd integers with 2-adic density
at least 448/512, formal descent certificates exist in Lean 4."
-/

end

end ProjetCollatz
