import Mathlib
open BigOperators
open scoped BigOperators
/-
Lean CORE for the "hard lemma":
We work in ℚ to avoid divisibility headaches.
Later we can specialize to ℕ once we connect a_k = v2(3n_k+1).
-/

namespace CollatzCore

set_option linter.unnecessarySimpa false

-- Parameters:
-- N : ℕ → ℚ is the odd-to-odd trajectory (embedded in ℚ)
-- a : ℕ → ℕ are the 2-adic "payments" a_k
variable (N : ℕ → ℚ) (a : ℕ → ℕ)

-- Definition of one odd-to-odd step in ℚ
def step (k : ℕ) : Prop :=
  N (k+1) = (3 * N k + 1) / ( (2:ℚ) ^ (a k) )

/-- Assumption: the step equation holds for all k < K. -/
def steps_up_to (K : ℕ) : Prop :=
  ∀ k, k < K → step (N := N) (a := a) k

/-- The "hard lemma": after K odd-steps, we have a deterministic lower bound. -/
theorem hard_lower_bound (K : ℕ)
    (h : steps_up_to (N := N) (a := a) K) :
    N K ≥ N 0 * (3:ℚ)^K / ( (2:ℚ) ^ (Finset.sum (Finset.range K) (fun i => a i)) ) := by
  -- Proof idea:
  -- 1) From step: N(k+1) = (3 N k + 1) / 2^(a k)
  -- 2) Since (3 N k + 1) ≥ (3 N k), divide by positive => N(k+1) ≥ (3 N k) / 2^(a k)
  -- 3) Multiply inequalities for k=0..K-1 and simplify products into powers and sums.
  classical
  -- We prove the statement by induction on K.
  -- We work in the ≤ direction (rhs ≤ lhs) and then rewrite back to ≥.
  induction K with
  | zero =>
      -- K = 0 : N 0 ≥ N 0 * 3^0 / 2^0
      simpa
  | succ K ih =>
      -- Restrict the hypothesis to steps up to K.
      have hprev : steps_up_to (N := N) (a := a) K := by
        intro k hk
        exact h k (lt_trans hk (Nat.lt_succ_self K))

      -- Induction hypothesis for K.
      have ihK : N K ≥ N 0 * (3:ℚ)^K /
          ((2:ℚ) ^ (Finset.sum (Finset.range K) (fun i => a i))) :=
        ih hprev

      -- Step equation at k = K.
      have hstep : step (N := N) (a := a) K :=
        h K (Nat.lt_succ_self K)

      -- Denominator positivity.
      have hdenpos : (0:ℚ) < ((2:ℚ) ^ (a K)) := by
        have h2 : (0:ℚ) < (2:ℚ) := by norm_num
        exact pow_pos h2 _

      -- (3*N K) ≤ (3*N K + 1)
      have hnum : (3 * N K) ≤ (3 * N K + 1) := by linarith

      -- Divide by the positive denominator.
      -- (In this Mathlib version, we avoid a specialized lemma name and instead
      -- rewrite division as multiplication by the inverse.)
      have hdiv : (3 * N K) / ((2:ℚ) ^ (a K)) ≤ (3 * N K + 1) / ((2:ℚ) ^ (a K)) := by
        have hinv_nonneg : (0:ℚ) ≤ (((2:ℚ) ^ (a K)) : ℚ)⁻¹ := by
          exact inv_nonneg.2 (le_of_lt hdenpos)
        have hmul : (3 * N K) * (((2:ℚ) ^ (a K)) : ℚ)⁻¹ ≤ (3 * N K + 1) * (((2:ℚ) ^ (a K)) : ℚ)⁻¹ :=
          mul_le_mul_of_nonneg_right hnum hinv_nonneg
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

      -- Convert to a lower bound on N (K+1).
      have hNK1 : (3 * N K) / ((2:ℚ) ^ (a K)) ≤ N (K+1) := by
        -- Use the step equation to rewrite the RHS.
        -- hstep : N (K+1) = (3*N K + 1) / 2^(a K)
        calc
          (3 * N K) / ((2:ℚ) ^ (a K))
              ≤ (3 * N K + 1) / ((2:ℚ) ^ (a K)) := hdiv
          _ = N (K+1) := by
              simpa [pow_succ, mul_assoc] using hstep.symm

      -- Rewrite the induction hypothesis as rhs ≤ N K.
      have ihK_le :
          (N 0 * (3:ℚ)^K /
            ((2:ℚ) ^ (Finset.sum (Finset.range K) (fun i => a i)))) ≤ N K := by
        simpa [ge_iff_le] using ihK

      -- Nonnegativity of the multiplier (3 / 2^(a K)).
      have hfac_nonneg : (0:ℚ) ≤ ( (3:ℚ) / ((2:ℚ) ^ (a K)) ) := by
        have h3 : (0:ℚ) < (3:ℚ) := by norm_num
        exact le_of_lt (div_pos h3 hdenpos)

      -- Multiply the induction bound by the nonnegative factor.
      have hmul :
          ( (3:ℚ) / ((2:ℚ) ^ (a K)) ) *
              (N 0 * (3:ℚ)^K /
                ((2:ℚ) ^ (Finset.sum (Finset.range K) (fun i => a i))))
            ≤ ( (3:ℚ) / ((2:ℚ) ^ (a K)) ) * (N K) :=
        mul_le_mul_of_nonneg_left ihK_le hfac_nonneg

      -- Identify the left side with the desired rhs for K+1.
      have hrhs :
          N 0 * (3:ℚ)^(K+1) /
            ((2:ℚ) ^ (Finset.sum (Finset.range (K+1)) (fun i => a i)))
          ≤ (3 * N K) / ((2:ℚ) ^ (a K)) := by
        -- Use sum_range_succ and pow lemmas to normalize.
        -- Also rewrite multiplication/division consistently.
        simpa [Finset.sum_range_succ, pow_succ, pow_add, div_eq_mul_inv,
              mul_assoc, mul_left_comm, mul_comm] using hmul

      -- Chain everything: rhs(K+1) ≤ (3*N K)/2^(a K) ≤ N(K+1)
      have :
          N 0 * (3:ℚ)^(K+1) /
            ((2:ℚ) ^ (Finset.sum (Finset.range (K+1)) (fun i => a i)))
          ≤ N (K+1) :=
        le_trans hrhs hNK1

      -- Rewrite back to ≥.
      simpa [ge_iff_le] using this

/-- Corollary: if the average payment is bounded by t, we get a simpler bound. -/
theorem hard_lower_bound_mean (K : ℕ) (t : ℕ)
    (h : steps_up_to (N := N) (a := a) K)
    (hN0 : 0 ≤ N 0)
    (hmean : (Finset.sum (Finset.range K) (fun i => (a i : ℚ))) ≤ (t : ℚ) * (K : ℚ)) :
    N K ≥ N 0 * ((3:ℚ) / ((2:ℚ)^t))^K := by
  -- Combine hard_lower_bound with the inequality on the sum of a_i.
  -- Note: this requires a small lemma relating 2^(sum a_i) to (2^t)^K when sum a_i ≤ tK.
  classical
  -- Start from the hard lower bound.
  have hlb : N K ≥ N 0 * (3:ℚ)^K /
      ((2:ℚ) ^ (Finset.sum (Finset.range K) (fun i => a i))) :=
    hard_lower_bound (N := N) (a := a) K h

  -- Let S be the Nat-sum of the payments.
  let S : ℕ := Finset.sum (Finset.range K) (fun i => a i)

  -- Rewrite the mean bound into an inequality on S (in ℚ).
  have hS_q : (S : ℚ) ≤ (t : ℚ) * (K : ℚ) := by
    -- Cast-sum lemma: (S:ℚ) = ∑ (a i : ℚ)
    have hcast : (S : ℚ) = Finset.sum (Finset.range K) (fun i => (a i : ℚ)) := by
      -- Nat.cast_sum: cast of sum = sum of casts
      simpa [S] using (Nat.cast_sum (Finset.range K) (fun i => a i) :
        ((Finset.sum (Finset.range K) (fun i => a i) : ℕ) : ℚ) =
          Finset.sum (Finset.range K) (fun i => (a i : ℚ)))
    -- Use hmean and rewrite LHS.
    simpa [hcast] using hmean

  -- Convert to Nat inequality S ≤ t*K.
  have hS_nat : S ≤ t * K := by
    -- Both sides are casts of naturals.
    -- First rewrite RHS (t:ℚ)*(K:ℚ) as (t*K : ℚ).
    have : (S : ℚ) ≤ (t * K : ℚ) := by
      simpa [Nat.cast_mul] using hS_q
    exact_mod_cast this

  -- Compare denominators: 2^S ≤ 2^(t*K).
  -- We prove monotonicity for the specific base 2 in ℚ by elementary induction,
  -- to avoid relying on lemma names that can vary across Mathlib versions.
  have hpow : ((2:ℚ) ^ S) ≤ ((2:ℚ) ^ (t*K)) := by
    -- Step 1: show 1 ≤ 2^n for all n.
    have one_le_pow2 : ∀ n : ℕ, (1:ℚ) ≤ (2:ℚ) ^ n := by
      intro n
      induction n with
      | zero =>
          simpa
      | succ n ih =>
          -- 2^(n+1) = 2^n * 2, and x ≤ x*2 when x ≥ 0 and 1 ≤ 2.
          have hx_nonneg : (0:ℚ) ≤ (2:ℚ) ^ n := by
            exact pow_nonneg (by norm_num : (0:ℚ) ≤ (2:ℚ)) _
          have h2ge1 : (1:ℚ) ≤ (2:ℚ) := by
            norm_num
          have hstep : (1:ℚ) ≤ (2:ℚ) ^ n * (2:ℚ) := by
            exact le_trans ih (le_mul_of_one_le_right hx_nonneg h2ge1)
          simpa [pow_succ, mul_assoc] using hstep

    -- Step 2: rewrite the exponent as S + d where d = t*K - S.
    let d : ℕ := t * K - S
    have htk : S + d = t * K := by
      -- valid because hS_nat : S ≤ t*K
      simpa [d] using (Nat.add_sub_of_le hS_nat)

    -- Step 3: 2^(S+d) = 2^S * 2^d, and 2^d ≥ 1.
    have hd_ge1 : (1:ℚ) ≤ (2:ℚ) ^ d := by
      exact one_le_pow2 d
    have hS_nonneg : (0:ℚ) ≤ (2:ℚ) ^ S := by
      exact pow_nonneg (by norm_num : (0:ℚ) ≤ (2:ℚ)) _

    calc
      (2:ℚ) ^ S
          ≤ (2:ℚ) ^ S * (2:ℚ) ^ d := by
              -- x ≤ x*y if x ≥ 0 and 1 ≤ y
              exact le_mul_of_one_le_right hS_nonneg hd_ge1
      _ = (2:ℚ) ^ (S + d) := by
              simpa [pow_add, mul_comm, mul_left_comm, mul_assoc]
      _ = (2:ℚ) ^ (t*K) := by
              simpa [htk]

  have hposS : (0:ℚ) < ((2:ℚ) ^ S) := by
    have h2 : (0:ℚ) < (2:ℚ) := by norm_num
    exact pow_pos h2 _

  have hdiv_le : (1:ℚ) / ((2:ℚ) ^ (t*K)) ≤ (1:ℚ) / ((2:ℚ) ^ S) := by
    -- For positive numbers: if x ≤ y then 1/y ≤ 1/x
    -- Here x = 2^S, y = 2^(t*K).
    exact one_div_le_one_div_of_le hposS hpow

  -- Numerator nonnegativity.
  have hnum_nonneg : (0:ℚ) ≤ N 0 * (3:ℚ)^K := by
    have h3pow : (0:ℚ) ≤ (3:ℚ)^K := by
      exact pow_nonneg (by norm_num) _
    exact mul_nonneg hN0 h3pow

  -- Multiply inequality on one_div by the nonnegative numerator.
  have hfrac_le :
      (N 0 * (3:ℚ)^K) * ((1:ℚ) / ((2:ℚ) ^ (t*K)))
        ≤ (N 0 * (3:ℚ)^K) * ((1:ℚ) / ((2:ℚ) ^ S)) :=
    mul_le_mul_of_nonneg_left hdiv_le hnum_nonneg

  -- Rewrite these as divisions.
  have hfrac_le' :
      N 0 * (3:ℚ)^K / ((2:ℚ) ^ (t*K))
        ≤ N 0 * (3:ℚ)^K / ((2:ℚ) ^ S) := by
    simpa [div_eq_mul_inv, one_div] using hfrac_le

  -- From hlb (NK ≥ .../2^S) and hfrac_le' ( .../2^(t*K) ≤ .../2^S )
  -- we get NK ≥ .../2^(t*K).
  have hbound_t :
      N 0 * (3:ℚ)^K / ((2:ℚ) ^ (t*K)) ≤ N K := by
    -- hlb is NK ≥ rhsS, i.e. rhsS ≤ NK.
    have hlb_le :
        N 0 * (3:ℚ)^K /
          ((2:ℚ) ^ (Finset.sum (Finset.range K) (fun i => a i))) ≤ N K := by
      simpa [ge_iff_le] using hlb
    -- Unfold S and compare.
    have hlb_le' : N 0 * (3:ℚ)^K / ((2:ℚ) ^ S) ≤ N K := by
      simpa [S] using hlb_le
    exact le_trans hfrac_le' hlb_le'

  -- First rewrite the *factor* (without N 0) so simp does not try to cancel N 0.
  have hrew_factor : ((3:ℚ) / ((2:ℚ)^t))^K = (3:ℚ)^K / ((2:ℚ)^(t*K)) := by
    -- (a/b)^K = a^K / b^K and (2^t)^K = 2^(t*K)
    simpa [pow_mul] using (div_pow (3:ℚ) ((2:ℚ)^t) K)

  have hrew : N 0 * ((3:ℚ) / ((2:ℚ)^t))^K = N 0 * (3:ℚ)^K / ((2:ℚ)^(t*K)) := by
    -- Use the factor rewrite, then normalize the division placement.
    calc
      N 0 * ((3:ℚ) / ((2:ℚ)^t))^K
          = N 0 * ((3:ℚ)^K / ((2:ℚ)^(t*K))) := by simpa [hrew_factor]
      _ = N 0 * (3:ℚ)^K / ((2:ℚ)^(t*K)) := by
          -- (x * (y / z)) = (x*y) / z
          simpa [mul_div_assoc]

  -- Turn the bound into the desired ≥ form.
  -- We have (rhs ≤ NK); rewrite rhs to the statement target.
  have : N 0 * ((3:ℚ) / ((2:ℚ)^t))^K ≤ N K := by
    simpa [hrew] using hbound_t

  -- Goal is NK ≥ rhs.
  simpa [ge_iff_le] using this

/-- Non-attainment: if the lower bound is > 1, then N K > 1, hence no hit before K odd-steps. -/
theorem not_reach_one_before (K : ℕ)
    (h : steps_up_to (N := N) (a := a) K)
    (hgt : N 0 * (3:ℚ)^K / ((2:ℚ) ^ (Finset.sum (Finset.range K) (fun i => a i))) > 1) :
    N K > 1 := by
  -- Direct from hard_lower_bound + transitivity.
  have hlb := hard_lower_bound (N := N) (a := a) K h
  exact lt_of_lt_of_le hgt hlb

end CollatzCore
