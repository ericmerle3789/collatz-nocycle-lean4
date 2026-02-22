import ProjetCollatz.Phase30GlobalDescent

/-!
# Phase33ConditionalCollatz.lean — Conditional Collatz Theorem

## Purpose

Prove the **conditional Collatz theorem**: IF every odd n > 1 eventually
descends under the Syracuse odd-to-odd map, THEN every n > 0 eventually
reaches 1 under the standard Collatz iteration.

This is a pure logical theorem — provable independently of the Collatz
conjecture itself. It reduces the full conjecture to the descent property
that our certificate system verifies computationally.

## Architecture

1. Define the standard Collatz map: n ↦ n/2 (even), n ↦ 3n+1 (odd)
2. Define `collatz_iter` (iteration) and `reaches_one`
3. Prove `nSeq_odd`: Syracuse preserves oddness (key missing lemma)
4. Prove `conditional_collatz_syracuse`: 0 sorry, pure induction
5. Prove the bridge: Syracuse steps ↔ standard Collatz steps
6. Prove `conditional_collatz`: full form, 0 sorry

## Date: 2026-02-18 (Cycle 110)
-/

namespace ProjetCollatz

/-!
## Part 1: Standard Collatz definitions
-/

/-- The standard Collatz function: n/2 if even, 3n+1 if odd. -/
def collatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Iteration of the standard Collatz function. -/
def collatz_iter : ℕ → ℕ → ℕ
  | n, 0 => n
  | n, k + 1 => collatz (collatz_iter n k)

/-- A natural number reaches 1 if some iterate equals 1. -/
def reaches_one (n : ℕ) : Prop :=
  ∃ k : ℕ, collatz_iter n k = 1

/-!
## Part 2: Basic Collatz properties
-/

/-- Collatz of 1 = 4. -/
theorem collatz_one : collatz 1 = 4 := by
  simp [collatz]

/-- Collatz of an even number > 0 is strictly less. -/
theorem collatz_even_lt (n : ℕ) (hn : n > 0) (heven : n % 2 = 0) :
    collatz n < n := by
  simp [collatz, heven]
  omega

/-- Collatz of an even number is n/2. -/
theorem collatz_even (n : ℕ) (heven : n % 2 = 0) :
    collatz n = n / 2 := by
  simp [collatz, heven]

/-- Collatz of an odd number is 3n+1. -/
theorem collatz_odd (n : ℕ) (hodd : n % 2 = 1) :
    collatz n = 3 * n + 1 := by
  simp [collatz, hodd]

/-- Iteration composes: collatz_iter n (a + b) = collatz_iter (collatz_iter n a) b. -/
theorem collatz_iter_add (n a b : ℕ) :
    collatz_iter n (a + b) = collatz_iter (collatz_iter n a) b := by
  induction b with
  | zero => simp [collatz_iter]
  | succ b ih =>
    show collatz (collatz_iter n (a + b)) = collatz (collatz_iter (collatz_iter n a) b)
    rw [ih]

/-- If some iterate is 1, then the number reaches 1. -/
theorem reaches_one_of_iter (n : ℕ) (k : ℕ) (h : collatz_iter n k = 1) :
    reaches_one n :=
  ⟨k, h⟩

/-- If n reaches m via k Collatz steps, and m reaches 1, then n reaches 1. -/
theorem reaches_one_of_reaches (n m : ℕ) (k : ℕ)
    (hiter : collatz_iter n k = m) (hm : reaches_one m) :
    reaches_one n := by
  obtain ⟨j, hj⟩ := hm
  exact ⟨k + j, by rw [collatz_iter_add, hiter, hj]⟩

/-!
## Part 3: Even numbers reduce
-/

/-- An even number reaches 1 if n/2 reaches 1. -/
theorem reaches_one_even (n : ℕ) (_hn : n > 0) (heven : n % 2 = 0)
    (h_half : reaches_one (n / 2)) :
    reaches_one n := by
  obtain ⟨k, hk⟩ := h_half
  refine ⟨1 + k, ?_⟩
  rw [collatz_iter_add]
  -- collatz_iter (collatz_iter n 1) k = 1
  -- collatz_iter n 1 = collatz n = n/2
  have h1 : collatz_iter n 1 = collatz n := rfl
  rw [h1, collatz_even n heven, hk]

/-!
## Part 4: Syracuse preserves oddness (key lemma)
-/

/-- nSeq preserves oddness: if n is odd, then nSeq n k is odd for all k. -/
theorem nSeq_odd (n : ℕ) (k : ℕ) (hodd : n % 2 = 1) :
    nSeq n k % 2 = 1 := by
  induction k with
  | zero => simp [nSeq]; exact hodd
  | succ k _ =>
    simp only [nSeq]
    exact syracuseNext_odd (nSeq n k)

/-!
## Part 5: Conditional Collatz Theorem (Syracuse form)

**Main result #1**: If every odd n > 1 eventually descends under Syracuse,
then every odd n > 0 eventually reaches 1 under Syracuse iteration.

This is **pure logic** — 0 sorry, 0 axioms, 0 bridges needed.
-/

/-- **Conditional Collatz Theorem (Syracuse form)**:
    If every odd n > 1 eventually descends under Syracuse,
    then every odd n > 0 eventually reaches 1 under Syracuse. -/
theorem conditional_collatz_syracuse
    (h_desc : ∀ n : ℕ, n > 1 → n % 2 = 1 → Descends n) :
    ∀ n : ℕ, n > 0 → n % 2 = 1 → ∃ k : ℕ, nSeq n k = 1 := by
  intro n hn hodd
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h1 : n = 1
    · exact ⟨0, by simp [nSeq, h1]⟩
    · have hn1 : n > 1 := by omega
      obtain ⟨m, hm_pos, hm_lt⟩ := h_desc n hn1 hodd
      have h_nseq_odd : nSeq n m % 2 = 1 := nSeq_odd n m hodd
      have h_nseq_pos : nSeq n m > 0 := nSeq_pos n (by omega) m
      obtain ⟨k, hk⟩ := ih (nSeq n m) hm_lt h_nseq_pos h_nseq_odd
      exact ⟨m + k, by rw [nSeq_add, hk]⟩

/-!
## Part 6: Bridge — Repeated halving lemma

To connect Syracuse to standard Collatz, we need: starting from even m
divisible by 2^k, k halvings via Collatz give m/2^k.
-/

/-- One halving step: collatz_iter (2*m) 1 = m (for any m ≥ 0). -/
theorem collatz_iter_one_even (m : ℕ) :
    collatz_iter (2 * m) 1 = m := by
  simp [collatz_iter, collatz]

/-- Repeated halving: collatz_iter (m * 2^k) k = m when m is odd.
    This is the core bridge between Syracuse and Collatz.
    Proof: peel off one factor of 2 per step via collatz. -/
theorem collatz_iter_halving (m k : ℕ) (_hodd : m % 2 = 1) :
    collatz_iter (m * 2 ^ k) k = m := by
  induction k with
  | zero => simp [collatz_iter]
  | succ k ih =>
    -- collatz_iter (m * 2^(k+1)) (k+1)
    -- = collatz (collatz_iter (m * 2^(k+1)) k)
    -- We use: collatz_iter x (1 + k) = collatz_iter (collatz x) k
    -- and collatz (m * 2^(k+1)) = m * 2^k (one halving)
    rw [show k + 1 = 1 + k from by omega, collatz_iter_add]
    -- Now: collatz_iter (collatz_iter (m * 2 ^ (1 + k)) 1) k = m
    simp only [collatz_iter]
    -- Goal: collatz_iter (collatz (m * 2 ^ (1 + k))) k = m
    -- m * 2^(1+k) is even, so collatz halves it to m * 2^k
    have heven : (m * 2 ^ (1 + k)) % 2 = 0 := by
      have h2k : 2 ^ (1 + k) = 2 * 2 ^ k := by ring
      rw [h2k, show m * (2 * 2 ^ k) = 2 * (m * 2 ^ k) from by ring]
      simp [Nat.mul_mod_right]
    rw [collatz_even (m * 2 ^ (1 + k)) heven]
    -- m * 2^(1+k) / 2 = m * 2^k
    have hdiv : m * 2 ^ (1 + k) / 2 = m * 2 ^ k := by
      rw [show 2 ^ (1 + k) = 2 * 2 ^ k from by ring]
      rw [show m * (2 * 2 ^ k) = 2 * (m * 2 ^ k) from by ring]
      exact Nat.mul_div_cancel_left (m * 2 ^ k) (by omega : 0 < 2)
    rw [hdiv]
    exact ih

/-- syracuseNext(n) is reachable from odd n via standard Collatz steps. -/
theorem syracuseNext_reachable (n : ℕ) (hodd : n % 2 = 1) :
    ∃ s : ℕ, s > 0 ∧ collatz_iter n s = syracuseNext n := by
  refine ⟨1 + v2_3n1 n, by omega, ?_⟩
  rw [collatz_iter_add]
  -- Goal: collatz_iter (collatz_iter n 1) (v2_3n1 n) = syracuseNext n
  -- collatz_iter n 1 = collatz n = 3*n+1 (since n is odd)
  have h1 : collatz_iter n 1 = collatz n := rfl
  rw [h1, collatz_odd n hodd]
  -- Goal: collatz_iter (3*n+1) (v₂(3n+1)) = syracuseNext n
  -- Use spec: 3*n+1 = syracuseNext n * 2^(v₂(3n+1))
  have hspec := syracuseNext_spec n
  rw [show 3 * n + 1 = syracuseNext n * 2 ^ v2_3n1 n from hspec.symm]
  exact collatz_iter_halving (syracuseNext n) (v2_3n1 n) (syracuseNext_odd n)

/-- nSeq n m is reachable from n via standard Collatz iteration. -/
theorem nSeq_reachable (n : ℕ) (hodd : n % 2 = 1) (m : ℕ) :
    ∃ s : ℕ, collatz_iter n s = nSeq n m := by
  induction m with
  | zero => exact ⟨0, by simp [collatz_iter, nSeq]⟩
  | succ m ihm =>
    obtain ⟨s₁, hs₁⟩ := ihm
    have h_succ : nSeq n (m + 1) = syracuseNext (nSeq n m) := by simp [nSeq]
    have h_odd_m : nSeq n m % 2 = 1 := nSeq_odd n m hodd
    obtain ⟨s₂, _, hs₂⟩ := syracuseNext_reachable (nSeq n m) h_odd_m
    exact ⟨s₁ + s₂, by rw [collatz_iter_add, hs₁, hs₂, h_succ]⟩

/-!
## Part 7: Conditional Collatz Theorem (full form)
-/

/-- **Conditional Collatz Theorem (full form)**:
    If every odd n > 1 eventually descends under Syracuse,
    then every n > 0 eventually reaches 1 under standard Collatz. -/
theorem conditional_collatz
    (h_desc : ∀ n : ℕ, n > 1 → n % 2 = 1 → Descends n) :
    ∀ n : ℕ, n > 0 → reaches_one n := by
  intro n hn
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h1 : n = 1
    · exact ⟨0, by simp [collatz_iter, h1]⟩
    · have hn1 : n > 1 := by omega
      by_cases heven : n % 2 = 0
      · have h_half_lt : n / 2 < n := by omega
        have h_half_pos : n / 2 > 0 := by omega
        exact reaches_one_even n (by omega) heven (ih (n / 2) h_half_lt h_half_pos)
      · have hodd : n % 2 = 1 := by omega
        obtain ⟨m, _, hm_lt⟩ := h_desc n hn1 hodd
        have h_nseq_pos : nSeq n m > 0 := nSeq_pos n (by omega) m
        obtain ⟨s, hs⟩ := nSeq_reachable n hodd m
        exact reaches_one_of_reaches n (nSeq n m) s hs (ih (nSeq n m) hm_lt h_nseq_pos)

/-!
## Part 8: Interpretation

Our certificate system (Phase28 + Phase29 + Phase30) provides `Descends n`
for all odd n > 1 (via algebraic theorems and stability certificates).

`conditional_collatz` shows this descent property is **exactly the missing
piece** for Collatz: provide it for all n, and the conjecture follows
by pure logic.

The logical chain:
1. Phase28/29: ∀ residue r mod 2^k, certified descent
2. Phase30: ∀ odd n > 1, Descends n (global coverage)
3. Phase33: Descends ∀ ⟹ reaches_one ∀ (this file)
-/

end ProjetCollatz
