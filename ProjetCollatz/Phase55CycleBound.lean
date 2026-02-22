import ProjetCollatz.Phase52SteinerEquation

/-!
# Phase55CycleBound.lean — Algebraic Cycle Bounds via Product Inequality

## Purpose

Prove structural algebraic results about hypothetical Collatz cycles,
establishing the **per-step product inequality** and the **IsCycleMin** structure.

These results formalize the mathematical argument that bounds cycle elements:
- For a cycle with minimum element n and k odd steps,
  (3·nSeq_j + 1)·n ≤ (3·n + 1)·nSeq_j for each step j (since n ≤ nSeq_j).
- Taking the product: 2^S · n^k ≤ (3n+1)^k.
- Combined with Baker: n ≤ O(k^μ) where μ depends on the Baker exponent used.

## Mathematical Gap (Documented)

The full derivation of B4 (n < 2^71 for ALL cycle elements) requires:
1. An upper bound on k (number of odd steps in a cycle), OR
2. A Baker exponent strong enough that k^μ/3 < 2^71 for ALL k ≥ 92.

Neither condition achieves B4 for ALL k directly. The resolution (Phase 56–58):
Product Bound gives n ≤ (k⁷+k)/3, and k ≤ 982 → n < 2^71. The best known:
- Baker μ=6 (our B1): n ≤ k^7/3, works for k ≤ 962 only
- Rhin μ=5.125: n ≤ k^6.125/3, works for k ≤ ~5200 only
- No known Baker exponent gives universal B4 without bounding k from above

Therefore, B4 remains as an explicit hypothesis in `ExternalCycleHypothesesFull`.
This is mathematically honest: the theorem chain is:
  ExternalCycleHypotheses (B1+B2+B3) + B4 → no_nontrivial_cycle_full → False

## Key Results

| Theorem | Status | Content |
|---------|--------|---------|
| `per_step_ineq` | proven | (3m+1)n ≤ (3n+1)m when n ≤ m |
| `IsCycleMin` | structure | Cycle with minimum element property |
| `cycle_all_odd` | proven | nSeq n j is odd for all j |
| `corrSum_add_eq` | proven | corrSum + 3^k·n = n·2^S |
| `n_le_corrSum` | proven | n ≤ corrSum (gap ≥ 1) |
| `baker_bounds_n_via_corrSum` | proven | Baker + corrSum → n·3^k ≤ corrSum·k^6 |

## References

- Steiner (1977), Congressus Numerantium XX
- Baker (1966), Mathematika; Rhin (1987)
- Simons & de Weger (2005), Acta Arithmetica 117.1
- Hercher (2023), arXiv:2201.00406

## Date: 2026-02-21 (Phase 55)
-/

namespace ProjetCollatz

noncomputable section

/-!
## Part A: Per-Step Product Inequality

The key algebraic fact: if n ≤ m (n is the cycle minimum, m = nSeq_j),
then (3m+1)·n ≤ (3n+1)·m. This is equivalent to n ≤ m.

Over rationals: (3m+1)/m = 3+1/m ≤ 3+1/n = (3n+1)/n when n ≤ m.

The product of these inequalities over all k cycle steps gives:
  ∏((3·nSeq_j+1)·n) ≤ ∏((3n+1)·nSeq_j)
  ⟹ [∏(3·nSeq_j+1)]·n^k ≤ (3n+1)^k·[∏ nSeq_j]
  ⟹ 2^S · [∏ nSeq_j] · n^k ≤ (3n+1)^k · [∏ nSeq_j]  (using cycle identity)
  ⟹ 2^S · n^k ≤ (3n+1)^k
-/

/-- **Per-step key inequality**: (3·m+1)·n ≤ (3·n+1)·m when n ≤ m.

Expanding: 3·m·n + n ≤ 3·n·m + m, which simplifies to n ≤ m. -/
theorem per_step_ineq (n m : ℕ) (h : n ≤ m) :
    (3 * m + 1) * n ≤ (3 * n + 1) * m := by
  nlinarith

/-- Variant with explicit ordering for Finset.prod_le_prod pattern. -/
theorem per_step_ineq' (n m : ℕ) (h : n ≤ m) (_hn : n > 0) :
    (3 * m + 1) * n ≤ (3 * n + 1) * m := by
  nlinarith

/-!
## Part B: Cycle Minimum Structure

For a cycle `nSeq n k = n`, we formalize the concept that
n is the **minimum** element on the cycle. Every finite cycle
(which visits only finitely many elements) has a minimum.
-/

/-- A cycle where `n` is the minimum element among all nSeq n j for j < k.
    This is without loss of generality: one can always relabel a cycle
    to start at its minimum element (since nSeq is periodic). -/
structure IsCycleMin (n k : ℕ) : Prop extends IsOddCycle n k where
  /-- n is the minimum element on the cycle -/
  is_min : ∀ j : ℕ, j < k → n ≤ nSeq n j

/-- The zeroth element of the sequence is n itself. -/
@[simp] theorem nSeq_zero' (n : ℕ) : nSeq n 0 = n := rfl

/-- Every element on a cycle is odd (since syracuseNext preserves parity). -/
theorem cycle_all_odd (n : ℕ) (hodd : n % 2 = 1) (j : ℕ) :
    nSeq n j % 2 = 1 := by
  induction j with
  | zero => simpa [nSeq]
  | succ j ih =>
    simp only [nSeq]
    exact syracuseNext_odd _

/-- Every element on a cycle is > 0. -/
theorem cycle_all_pos' (n : ℕ) (hn : n > 0) (j : ℕ) :
    nSeq n j > 0 :=
  nSeq_pos n hn j

/-!
## Part C: Steiner Equation Applied to Cycles

From `steiner_cycle_eq`: n · 2^S = 3^k · n + corrSum n k.
This gives: n · (2^S - 3^k) = corrSum n k (in mathematical ℤ).

In natural numbers (since 2^S > 3^k for a cycle):
  corrSum n k = n · 2^S - 3^k · n = n · (2^S - 3^k)

Combined with Baker: (2^S - 3^k) · k^6 ≥ 3^k,
we get: corrSum · k^6 ≥ n · 3^k, i.e., n ≤ corrSum · k^6 / 3^k.
-/

/-- **Additive form of the cycle gap**: corrSum n k + 3^k · n = n · 2^S.
    From steiner_cycle_eq: n · 2^S = 3^k · n + corrSum n k.
    This is the additive (subtraction-free) reformulation. -/
theorem corrSum_add_eq (n k : ℕ) (hcyc : IsOddCycle n k) :
    corrSum n k + 3 ^ k * n = n * 2 ^ aSumSeq n k := by
  have hsteiner := steiner_cycle_eq n k hcyc
  -- hsteiner: n * 2^S = 3^k * n + corrSum n k
  linarith

/-- **n is bounded by corrSum**: since corrSum = n·(2^S - 3^k) ≥ n·1 = n
    (because 2^S > 3^k for any cycle). -/
theorem n_le_corrSum (n k : ℕ) (hcyc : IsOddCycle n k) :
    n ≤ corrSum n k := by
  have hsteiner := steiner_cycle_eq n k hcyc
  have hgt := cycle_pow2_gt_pow3 n k hcyc
  -- From hsteiner: n * 2^S = 3^k * n + corrSum
  -- So corrSum = n * 2^S - 3^k * n = n * (2^S - 3^k)
  -- Since 2^S > 3^k: 2^S - 3^k ≥ 1, so corrSum ≥ n
  -- In ℕ: n * 2^S = 3^k * n + corrSum implies corrSum = n*2^S - 3^k*n
  -- And n*2^S > n*3^k (since 2^S > 3^k and n > 0)
  -- So corrSum ≥ n*(2^S - 3^k) ≥ n*1 = n
  have hn : n ≥ 1 := by obtain ⟨h1, _⟩ := hcyc; omega
  -- n * 2^S = 3^k * n + corrSum, and 2^S ≥ 3^k + 1
  -- So n * (3^k + 1) ≤ n * 2^S = 3^k * n + corrSum
  -- n * 3^k + n ≤ 3^k * n + corrSum
  -- n ≤ corrSum
  nlinarith [Nat.mul_le_mul_left n hgt]

/-- **Baker bounds n via corrSum**: combining Baker with the Steiner cycle eq.
    From Baker: (2^S - 3^k) · k^6 ≥ 3^k.
    From cycle: n · 2^S = 3^k · n + corrSum, i.e., corrSum = n · (2^S - 3^k).
    Therefore: corrSum · k^6 = n · (2^S - 3^k) · k^6 ≥ n · 3^k.

    In Lean we express: n · 3^k ≤ corrSum n k · k^6. -/
theorem baker_bounds_n_via_corrSum
    (ext : ExternalCycleHypotheses) (n k : ℕ) (hcyc : IsOddCycle n k) :
    n * 3 ^ k ≤ corrSum n k * k ^ 6 := by
  have hsteiner := steiner_cycle_eq n k hcyc
  have hgt := cycle_pow2_gt_pow3 n k hcyc
  have hS := cycle_sum_pos n k hcyc
  have hk2 : k ≥ 2 := cycle_k_ge_two n k hcyc
  have hbaker := ext.baker_separation (aSumSeq n k) k hS hk2 hgt
  -- hsteiner: n * 2^S = 3^k * n + corrSum
  -- hbaker: (2^S - 3^k) * k^6 ≥ 3^k
  --
  -- Lift to ℤ to handle subtraction properly.
  -- In ℤ: corrSum = n * 2^S - 3^k * n = n * (2^S - 3^k)
  -- corrSum * k^6 = n * (2^S - 3^k) * k^6 ≥ n * 3^k [by Baker]
  -- Key: 3^k ≤ 2^S (so subtraction is safe)
  have hle : 3 ^ k ≤ 2 ^ aSumSeq n k := Nat.le_of_lt hgt
  -- Lift to ℤ with the subtraction hint
  zify [hle] at hsteiner hbaker ⊢
  -- Now in ℤ: hsteiner: n * 2^S = 3^k * n + corrSum
  -- hbaker: (2^S - 3^k) * k^6 ≥ 3^k  [properly unfolded]
  -- Goal: n * 3^k ≤ corrSum * k^6
  -- From hsteiner: corrSum = n * 2^S - 3^k * n = n * (2^S - 3^k)
  -- Compute: corrSum * k^6 = n * (2^S - 3^k) * k^6 ≥ n * 3^k
  have hcorr : (corrSum n k : ℤ) = (n : ℤ) * ((2 : ℤ) ^ aSumSeq n k - (3 : ℤ) ^ k) := by linarith
  -- corrSum * k^6 = n * (2^S - 3^k) * k^6 ≥ n * 3^k
  -- since (2^S - 3^k) * k^6 ≥ 3^k (Baker) and n ≥ 0
  rw [hcorr]
  -- Goal: n * 3^k ≤ (n * (2^S - 3^k)) * k^6
  -- = n * ((2^S - 3^k) * k^6)
  -- ≥ n * 3^k [by hbaker and mul_le_mul]
  have hn_pos : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  calc (n : ℤ) * (3 : ℤ) ^ k
      ≤ (n : ℤ) * (((2 : ℤ) ^ aSumSeq n k - (3 : ℤ) ^ k) * (k : ℤ) ^ 6) :=
        mul_le_mul_of_nonneg_left hbaker hn_pos
    _ = (n : ℤ) * ((2 : ℤ) ^ aSumSeq n k - (3 : ℤ) ^ k) * (k : ℤ) ^ 6 := by ring

/-!
## Part D: Summary of the Derivation Path to B4

The algebraic infrastructure above shows:

1. **Per-step inequality** (proven): (3m+1)·n ≤ (3n+1)·m when n ≤ m
2. **Product bound** (requires Finset products over cycle):
   2^S · n^k ≤ (3n+1)^k
3. **Baker combination** (proven): n · 3^k ≤ corrSum · k^6
4. **Combined**: from (2) + Baker, 3^k·(k^6+1)·n^k ≤ k^6·(3n+1)^k

The remaining gap for full B4 derivation:
- **Step 2** requires formalizing `∏_{j<k} (2^{a_j} · n) ≤ ∏_{j<k} (3·nSeq_j + 1)`
  as a Finset product inequality, then combining with the cycle identity
  `2^S · ∏ nSeq_j = ∏ (3·nSeq_j + 1)`.
- **Step 4** requires showing that for n ≥ N(k), the combined inequality is
  violated, giving n < N(k). This N(k) = O(k^{μ+1}/3) depends on Baker's
  exponent μ, and NONE of the published μ values give N(k) < 2^71 for ALL k ≥ 92.

Therefore, B4 remains as a hypothesis in `ExternalCycleHypothesesFull`.
This is the correct mathematical state of affairs at this phase. B4 is later
DERIVED in Phase 56 via the Product Bound: n ≤ (k⁷+k)/3 combined with k ≤ 982
and Barina's 2^71 verification limit. See Phase 56 and HYPOTHESES.md.

## Total: 6 theorems + 1 structure, **0 sorry**, 0 axiom
-/

end

end ProjetCollatz
