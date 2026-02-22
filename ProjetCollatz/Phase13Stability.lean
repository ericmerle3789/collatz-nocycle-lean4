import ProjetCollatz.Phase12ReflectionCerts
import ProjetCollatz.ModularHierarchy

/-!
# Phase13Stability.lean — Stability Bridge: v2_mod_stable → certified_descent

## Strategic Context (Triade Cycle 72 — GPT NO-GO + Gemini GO Consensus)

The soundness chain was:
```
checkHybridCert(cert) = true
  → bridge → iteration_equation → descent_from_iteration → nSeq n m < n
```
But the MISSING LINK was: proving that for n ≡ r mod 2^k, the valuations
`aSeq n` match the certificate (computed from r).

**Key Discovery**: `v2_mod_stable` is ALREADY PROVED in `ModularHierarchy.lean`.
This file bridges the gap by:
1. Defining computable versions of v2Nat, syracuseNext, nSeq
2. Proving they agree with the noncomputable originals
3. Defining a computable stability checker
4. Proving single-step and congruence propagation
5. Assembling the FINAL certified_descent theorem

Date: 2026-02-16 (Sprint P13 — Phase 6a)
-/

namespace ProjetCollatz

/-!
## Step 1: Computable Versions of Syracuse Functions

The originals (v2Nat, syracuseNext, nSeq) are inside a `noncomputable section`
in SyracuseDefs.lean. We redefine them OUTSIDE that section with identical
definitions. This makes them usable in `Bool`-returning checkers.
-/

/-- Computable 2-adic valuation. Same definition as v2Nat but outside
    the noncomputable section. -/
def v2NatC : ℕ → ℕ
  | 0 => 0
  | (n + 1) =>
    if (n + 1) % 2 = 0 then
      1 + v2NatC ((n + 1) / 2)
    else
      0
termination_by n => n
decreasing_by
  simpa using (Nat.div_lt_self (Nat.succ_pos n) (by decide : (1 : ℕ) < 2))

/-- Computable v2(3n+1). -/
def v2C_3n1 (n : ℕ) : ℕ := v2NatC (3 * n + 1)

/-- Computable Syracuse macro-step. -/
def syracuseNextC (n : ℕ) : ℕ := (3 * n + 1) / (2 ^ v2C_3n1 n)

/-- Computable Syracuse sequence. -/
def nSeqC (start : ℕ) : ℕ → ℕ
  | 0 => start
  | k + 1 => syracuseNextC (nSeqC start k)

-- Quick sanity checks
example : v2NatC 10 = 1 := by native_decide
example : v2NatC 16 = 4 := by native_decide
example : syracuseNextC 3 = 5 := by native_decide
example : syracuseNextC 5 = 1 := by native_decide

/-!
## Step 2: Agreement Proofs (Computable = Noncomputable)

These theorems allow us to transfer results between the computable
world (checkers, native_decide) and the noncomputable world (proofs).
-/

/-- v2NatC agrees with v2Nat for all n. Proved by strong induction. -/
theorem v2NatC_eq_v2Nat : ∀ n : ℕ, v2NatC n = v2Nat n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => simp [v2NatC, v2Nat]
    | succ k =>
      simp only [v2NatC, v2Nat]
      by_cases h : (k + 1) % 2 = 0
      · -- Even case: both recurse on (k+1)/2
        simp only [h, ↓reduceIte]
        have hlt : (k + 1) / 2 < k + 1 :=
          Nat.div_lt_self (Nat.succ_pos k) (by decide)
        rw [ih _ hlt]
      · -- Odd case: both return 0
        simp only [h, ↓reduceIte]

/-- v2C_3n1 agrees with v2_3n1. -/
theorem v2C_3n1_eq_v2_3n1 (n : ℕ) : v2C_3n1 n = v2_3n1 n := by
  simp [v2C_3n1, v2_3n1, v2NatC_eq_v2Nat]

/-- syracuseNextC agrees with syracuseNext. -/
theorem syracuseNextC_eq_syracuseNext (n : ℕ) : syracuseNextC n = syracuseNext n := by
  simp [syracuseNextC, syracuseNext, v2C_3n1_eq_v2_3n1]

/-- nSeqC agrees with nSeq. -/
theorem nSeqC_eq_nSeq (start m : ℕ) : nSeqC start m = nSeq start m := by
  induction m with
  | zero => simp [nSeqC, nSeq]
  | succ m ih => simp [nSeqC, nSeq, syracuseNextC_eq_syracuseNext, ih]

/-!
## Step 3: Computable Stability Checker

Verifies that:
1. The trajectory of r has exactly the valuations in `vals`
2. Each valuation vi consumes < k - consumed bits (stability condition)

If both hold, then for ANY n ≡ r mod 2^k, the trajectory of n
has the same first m valuations as r (by v2_mod_stable).
-/

/-- Verify trajectory stability for residue r mod 2^k with valuations vals.
    Returns true iff:
    - Each step's actual v2 matches the declared valuation
    - The cumulative bit consumption stays strictly below k -/
def verifyStability (r k : ℕ) (vals : List ℕ) : Bool :=
  go r 0 vals
where
  /-- Inner loop: check trajectory from node n with consumed bits so far. -/
  go (n : ℕ) (consumed : ℕ) : List ℕ → Bool
    | [] => true
    | v :: rest =>
      let actual := v2NatC (3 * n + 1)
      actual == v && v + consumed < k && go (syracuseNextC n) (consumed + v) rest

/-!
## Step 4: Single-Step Stability Soundness

The core idea: if v2(3r+1) < k, then for n = r + 2^k * m,
v2(3n+1) = v2(3r+1). This is EXACTLY `v2_mod_stable` from
ModularHierarchy.lean!
-/

/-- Single-step stability: v2_mod_stable repackaged with explicit v. -/
theorem v2_single_step_stable (r k m v : ℕ)
    (hv_eq : v2Nat (3 * r + 1) = v) (hv_lt : v < k) :
    v2Nat (3 * (r + 2^k * m) + 1) = v := by
  rw [← hv_eq]; exact v2_mod_stable r k m (by omega)

/-!
## Step 5: Congruence Propagation

After one Syracuse step, if n ≡ r mod 2^k and v = v2(3r+1) < k,
then syracuseNext(n) ≡ syracuseNext(r) mod 2^(k-v).

This is the key lemma for propagating stability through multiple steps.
-/

/-- Syracuse step preserves congruence with reduced modulus.
    If n = r + 2^k * m and v2(3r+1) < k, then
    syracuseNext(n) = syracuseNext(r) + 2^(k-v) * q for some q. -/
theorem syracuseNext_cong (r k m : ℕ)
    (hv : v2Nat (3 * r + 1) < k) :
    ∃ q, syracuseNext (r + 2^k * m) = syracuseNext r + 2^(k - v2Nat (3 * r + 1)) * q := by
  set v := v2Nat (3 * r + 1) with hv_def
  set n := r + 2^k * m with hn_def
  -- v2Nat(3n+1) = v by v2_mod_stable
  have hv_eq : v2Nat (3 * n + 1) = v := v2_mod_stable r k m hv
  have hvn : v2_3n1 n = v := hv_eq
  have hvr : v2_3n1 r = v := rfl
  -- 3n+1 = 3r+1 + 3·2^k·m
  have hexp : 3 * n + 1 = (3 * r + 1) + 3 * 2^k * m := by
    simp only [hn_def]; ring
  -- 2^v divides (3r+1) and 3·2^k·m
  have hdvd_r : 2^v ∣ (3 * r + 1) := pow2_v2Nat_dvd (3 * r + 1)
  have hdvd_m : 2^v ∣ (3 * 2^k * m) := by
    calc (2:ℕ)^v ∣ 2^k := Nat.pow_dvd_pow 2 (by omega)
      _ ∣ 3 * 2^k := dvd_mul_left _ _
      _ ∣ 3 * 2^k * m := dvd_mul_right _ _
  -- Factor out 2^v
  obtain ⟨a, ha⟩ := hdvd_r
  obtain ⟨b, hb⟩ := hdvd_m
  have h2v_pos : 0 < 2^v := by positivity
  -- syracuseNext n = (3n+1)/2^v = a + b
  have h3n1 : 3 * n + 1 = 2^v * (a + b) := by rw [hexp, ha, hb]; ring
  have h_syr_n : syracuseNext n = a + b := by
    simp [syracuseNext, hvn, h3n1, Nat.mul_div_cancel_left _ h2v_pos]
  -- syracuseNext r = (3r+1)/2^v = a
  have h_syr_r : syracuseNext r = a := by
    simp [syracuseNext, hvr, ha, Nat.mul_div_cancel_left _ h2v_pos]
  -- b = 3·2^(k-v)·m
  have hb_eq : b = 3 * 2^(k - v) * m := by
    have h2k : 2^k = 2^v * 2^(k - v) := by rw [← Nat.pow_add]; congr 1; omega
    have h1 : 3 * 2^k * m = 2^v * b := hb
    have h2 : 3 * (2^v * 2^(k - v)) * m = 2^v * b := by rwa [← h2k]
    have h3 : 2^v * (3 * 2^(k - v) * m) = 2^v * b := by linarith
    exact (Nat.mul_left_cancel h2v_pos h3).symm
  -- Conclude
  rw [h_syr_n, h_syr_r, hb_eq]
  exact ⟨3 * m, by ring⟩

/-!
## Step 6: Assembly — The Certified Descent Theorem

The final theorem connects all pieces:
- checkFullCert = true gives: ratio + threshold + trajectory stability
- bridge connects vals to deltaCorr/partialSum
- iteration_equation + descent_from_iteration give the descent

The stability hypothesis (aSeq n agrees with vals) is stated explicitly.
For concrete certificates, this is verified by native_decide via verifyStability.
The theoretical proof that verifyStability implies aSeq agreement is the
multi-step induction (deferred to Sprint P13 Phase 6b).
-/

/-- The certified descent theorem: if the certificate passes all checks
    and aSeq n agrees with vals, then nSeq n m < n.

    The stability hypothesis will be discharged either:
    (a) By native_decide for concrete certificates, or
    (b) By the multi-step stability theorem (Sprint P13 Phase 6b). -/
theorem certified_descent_with_stability
    (vals : List ℕ) (_r _k n : ℕ)
    (hratio : pow3 vals.length < pow2 (listSum vals))
    (hthresh : computeThreshold vals ≤ n)
    (hstab : ∀ i, i < vals.length → aSeq n i = vals.getD i 0) :
    nSeq n vals.length < n := by
  set f := aSeq n
  set m := vals.length
  have hagree : ∀ i, i < m → f i = vals.getD i 0 := hstab
  -- Bridge: foldl = (deltaCorr, partialSum)
  have hbridge := bridge_foldl_deltaCorr_partialSum f vals hagree
  have hcds : computeDeltaAndSum vals = (deltaCorr f m, partialSum f m) := by
    rw [computeDeltaAndSum_eq_foldl]; exact hbridge
  have hdc : (computeDeltaAndSum vals).1 = deltaCorr f m := by rw [hcds]
  have hps_ls := computeDeltaAndSum_snd_eq_listSum vals
  have hps : (computeDeltaAndSum vals).2 = partialSum f m := by rw [hcds]
  have hps_eq : partialSum f m = listSum vals := by rw [← hps, hps_ls]
  -- Ratio: 3^m < 2^S
  have hS : 3 ^ m < 2 ^ (partialSum f m) := by
    rw [hps_eq, ← pow3_eq, ← pow2_eq]; exact hratio
  -- Threshold: Δ_m + 3^m·n < 2^S·n
  have hΔ : deltaCorr f m + 3 ^ m * n < 2 ^ (partialSum f m) * n := by
    have h_thr : computeThreshold vals ≤ n := hthresh
    simp only [computeThreshold] at h_thr
    have h_ratio_comp : pow3 m < pow2 (listSum vals) := hratio
    rw [dif_pos h_ratio_comp] at h_thr
    set delta := (computeDeltaAndSum vals).1
    set pow2s := pow2 (listSum vals)
    set pow3m := pow3 m
    have h_diff_pos : 0 < pow2s - pow3m := by omega
    have h_div_lt : delta / (pow2s - pow3m) < n := by omega
    have h_delta_lt : delta < n * (pow2s - pow3m) :=
      Nat.lt_mul_of_div_lt h_div_lt h_diff_pos
    rw [hdc] at h_delta_lt
    -- Rewrite pow2s and pow3m to standard form
    have h2 : pow2s = 2 ^ (listSum vals) := pow2_eq _
    have h3 : pow3m = 3 ^ m := pow3_eq _
    rw [h2, h3] at h_delta_lt
    -- h_delta_lt : deltaCorr f m < n * (2^(listSum vals) - 3^m)
    -- Goal: deltaCorr f m + 3^m * n < 2^(partialSum f m) * n
    rw [hps_eq]
    -- Goal: deltaCorr f m + 3^m * n < 2^(listSum vals) * n
    have hS2 : 3 ^ m ≤ 2 ^ (listSum vals) := by
      have := hS; rw [hps_eq] at this; exact Nat.le_of_lt this
    -- Key: (A - B) + B = A when B ≤ A, applied after multiplying by n
    -- h_delta_lt : deltaCorr f m < n * (2^S - 3^m)
    -- Unfold Nat subtraction: 2^S - 3^m + 3^m = 2^S (since 3^m ≤ 2^S)
    have hsub_cancel : 2 ^ listSum vals - 3 ^ m + 3 ^ m = 2 ^ listSum vals :=
      Nat.sub_add_cancel hS2
    -- delta + 3^m * n < n * (2^S - 3^m) + n * 3^m = n * 2^S = 2^S * n
    calc deltaCorr f m + 3 ^ m * n
        < n * (2 ^ listSum vals - 3 ^ m) + 3 ^ m * n := by omega
      _ = n * (2 ^ listSum vals - 3 ^ m) + n * 3 ^ m := by ring
      _ = n * (2 ^ listSum vals - 3 ^ m + 3 ^ m) := by ring
      _ = n * 2 ^ listSum vals := by rw [hsub_cancel]
      _ = 2 ^ listSum vals * n := by ring
  exact descent_from_iteration n m hS hΔ

/-!
## Step 7: Full Certificate Structure

A StabilityCert combines the descent certificate with stability information.
The checkFullCert function is PURELY COMPUTABLE (no sorry).
-/

/-- A full certificate combining descent and stability information. -/
structure StabilityCert where
  /-- The valuations v₂(3·sₖ+1) for each step k. -/
  valuations : List ℕ
  /-- The residue class representative (odd). -/
  residue : ℕ
  /-- The modulus exponent k (class is mod 2^k). -/
  modulus_exp : ℕ
  /-- Steps must be at least 1. -/
  steps_pos : valuations.length > 0 := by decide

/-- Full certificate check: descent ratio + threshold + stability. -/
def checkFullCert (cert : StabilityCert) : Bool :=
  let hcert : HybridCert := {
    valuations := cert.valuations
    steps_pos := cert.steps_pos
  }
  checkHybridCert hcert &&
  verifyStability cert.residue cert.modulus_exp cert.valuations

/-!
## Step 8: Concrete Examples

These demonstrate the full pipeline end-to-end, verified by native_decide.
-/

-- r=3 mod 2^8: 2 steps, v₂=[1, 4], sum=5
-- Stability: v2(10)=1 < 8 ✓, v2(16)=4, 4+1=5 < 8 ✓
def stabCert_r3 : StabilityCert where
  valuations := [1, 4]
  residue := 3
  modulus_exp := 8

example : checkFullCert stabCert_r3 = true := by native_decide

-- r=7 mod 2^8: 4 steps, v₂=[1,1,2,3], sum=7
-- Stability: 1<8, 1+1<8, 2+2<8, 3+4<8 ✓
def stabCert_r7 : StabilityCert where
  valuations := [1, 1, 2, 3]
  residue := 7
  modulus_exp := 8

example : checkFullCert stabCert_r7 = true := by native_decide

-- r=5 mod 2^8: 1 step, v₂=[4], sum=4
def stabCert_r5 : StabilityCert where
  valuations := [4]
  residue := 5
  modulus_exp := 8

example : checkFullCert stabCert_r5 = true := by native_decide

-- r=1 mod 2^8: 1 step, v₂=[2], sum=2
def stabCert_r1 : StabilityCert where
  valuations := [2]
  residue := 1
  modulus_exp := 8

example : checkFullCert stabCert_r1 = true := by native_decide

-- r=15 mod 2^10: 4 steps, v₂=[1,1,1,5], sum=8
-- Note: sum = 8, need modulus > 8. Using k=10.
-- Stability: 1<10, 1+1<10, 1+2<10, 5+3=8<10 ✓
def stabCert_r15 : StabilityCert where
  valuations := [1, 1, 1, 5]
  residue := 15
  modulus_exp := 10

example : checkFullCert stabCert_r15 = true := by native_decide

-- r=11 mod 2^8: 3 steps, v₂=[1,2,3], sum=6
def stabCert_r11 : StabilityCert where
  valuations := [1, 2, 3]
  residue := 11
  modulus_exp := 8

example : checkFullCert stabCert_r11 = true := by native_decide

/-!
## Multi-Step Stability — Phase 6b: The verifyStability Soundness Theorem

**Goal**: Prove that if `verifyStability r k vals = true` and `n ≡ r mod 2^k`,
then the first `vals.length` valuations of n's trajectory agree with `vals`.

**Strategy**: Induction on `vals` via a core helper `go_sound` that tracks:
- The current node in the reference trajectory (`node`)
- The cumulative bit consumption (`consumed`)
- The congruence invariant: `nSeq n i = node + 2^(k-consumed) * q`

At each step:
1. `v2_mod_stable` gives: same valuation (v2 stability)
2. `syracuseNext_cong` gives: congruence propagates with reduced modulus
-/

/-- Helper: unfold verifyStability.go for cons case. -/
private theorem go_cons_true (n consumed k : ℕ) (v : ℕ) (rest : List ℕ)
    (h : verifyStability.go k n consumed (v :: rest) = true) :
    v2NatC (3 * n + 1) = v ∧ v + consumed < k ∧
    verifyStability.go k (syracuseNextC n) (consumed + v) rest = true := by
  simp only [verifyStability.go, Bool.and_eq_true, beq_iff_eq,
             decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- Core lemma: if go checks pass for node/consumed, and nSeq n i ≡ node mod 2^(k-consumed),
    then aSeq n (i+j) = vals.getD j 0 for all j < vals.length.

    The key invariant tracked through the induction:
    - `node` is where the reference trajectory is (nSeqC r i)
    - `consumed` tracks how many bits have been used (sum of previous valuations)
    - `∃ q, nSeq n i = node + 2^(k-consumed) * q` is the congruence invariant -/
theorem go_sound (vals : List ℕ) (node consumed k i n : ℕ) (q : ℕ)
    (hgo : verifyStability.go k node consumed vals = true)
    (hcong : nSeq n i = node + 2^(k - consumed) * q)
    (hck : consumed ≤ k) :
    ∀ j, j < vals.length → aSeq n (i + j) = vals.getD j 0 := by
  induction vals generalizing node consumed i q with
  | nil =>
    intro j hj; simp at hj
  | cons v rest ih =>
    intro j hj
    -- Extract the three conditions from go
    obtain ⟨hv_eq, hv_lt, hrest⟩ := go_cons_true node consumed k v rest hgo
    -- Transfer to noncomputable world
    have hv_nc : v2Nat (3 * node + 1) = v := by
      rw [← v2NatC_eq_v2Nat]; exact hv_eq
    -- Stability condition: v < k - consumed
    have hv_small : v2Nat (3 * node + 1) < (k - consumed) := by omega
    -- nSeq n i = node + 2^(k-consumed) * q, so by v2_mod_stable:
    -- v2Nat(3 * nSeq n i + 1) = v2Nat(3 * node + 1)
    have h_v2_agree : v2Nat (3 * (nSeq n i) + 1) = v2Nat (3 * node + 1) := by
      rw [hcong]
      exact v2_mod_stable node (k - consumed) q hv_small
    cases j with
    | zero =>
      -- aSeq n i = v2_3n1 (nSeq n i) = v2Nat(3 * nSeq n i + 1) = v = (v::rest).getD 0 0
      simp only [aSeq, v2_3n1, Nat.add_zero, List.getD_cons_zero]
      rw [h_v2_agree, hv_nc]
    | succ j' =>
      -- Need: aSeq n (i + j' + 1) = rest.getD j' 0
      -- By IH with node' = syracuseNextC node, consumed' = consumed + v
      -- Need new congruence: nSeq n (i+1) ≡ syracuseNext node mod 2^(k-consumed-v)
      have h_syr_cong : ∃ q', syracuseNext (nSeq n i) =
          syracuseNext node + 2^(k - consumed - v) * q' := by
        rw [hcong]
        have hmod : k - consumed - v = k - consumed - v2Nat (3 * node + 1) := by
          rw [hv_nc]
        rw [hmod]
        exact syracuseNext_cong node (k - consumed) q hv_small
      obtain ⟨q', hq'⟩ := h_syr_cong
      -- nSeq n (i+1) = syracuseNext (nSeq n i)
      have h_nseq_step : nSeq n (i + 1) = syracuseNext (nSeq n i) := by
        simp [nSeq]
      -- syracuseNext node = syracuseNextC node
      have h_syr_eq : syracuseNext node = syracuseNextC node := by
        rw [← syracuseNextC_eq_syracuseNext]
      -- New congruence: nSeq n (i+1) = syracuseNextC node + 2^(k-(consumed+v)) * q'
      have h_exp_eq : k - consumed - v = k - (consumed + v) := by omega
      have h_new_cong : nSeq n (i + 1) = syracuseNextC node + 2^(k - (consumed + v)) * q' := by
        rw [h_nseq_step, hq', h_syr_eq, h_exp_eq]
      -- Apply IH
      have hj'_bound : j' < rest.length := by simp at hj; omega
      have hck' : consumed + v ≤ k := by omega
      have h_idx : i + (j' + 1) = (i + 1) + j' := by omega
      rw [h_idx]
      simp only [List.getD_cons_succ]
      exact ih (syracuseNextC node) (consumed + v) (i + 1) q' hrest h_new_cong hck' j' hj'_bound

/-- **Main theorem**: verifyStability soundness.
    If `verifyStability r k vals = true` and `n = r + 2^k * m`,
    then for all i < vals.length, `aSeq n i = vals.getD i 0`.

    This is the "maillon manquant" (missing link) connecting the computable
    checker to the theoretical descent proof. -/
theorem verifyStability_sound (vals : List ℕ) (r k n m : ℕ)
    (hstab : verifyStability r k vals = true)
    (hn : n = r + 2^k * m) :
    ∀ i, i < vals.length → aSeq n i = vals.getD i 0 := by
  -- verifyStability r k vals = go r 0 vals
  have hgo : verifyStability.go k r 0 vals = true := by
    simp [verifyStability] at hstab; exact hstab
  -- Initial congruence: nSeq n 0 = n = r + 2^k * m = r + 2^(k-0) * m
  have h_init : nSeq n 0 = r + 2^(k - 0) * m := by
    simp [nSeq, hn]
  -- Apply go_sound with i=0, consumed=0, node=r, q=m
  intro i hi
  have h := go_sound vals r 0 k 0 n m hgo h_init (Nat.zero_le k) i hi
  simpa using h

/-!
## Summary

### Definitions (8):
- v2NatC, v2C_3n1, syracuseNextC, nSeqC (computable versions)
- verifyStability, verifyStability.go (computable checker)
- StabilityCert, checkFullCert (certificate structure + checker)

### Theorems (10):
- v2NatC_eq_v2Nat: computable = noncomputable agreement ✓
- v2C_3n1_eq_v2_3n1: computable = noncomputable ✓
- syracuseNextC_eq_syracuseNext: computable = noncomputable ✓
- nSeqC_eq_nSeq: computable = noncomputable ✓
- v2_single_step_stable: single-step stability (via v2_mod_stable) ✓
- syracuseNext_cong: congruence propagation ✓
- go_sound: multi-step stability core lemma ✓ (Phase 6b)
- verifyStability_sound: THE MISSING LINK — checker → aSeq agreement ✓ (Phase 6b)
- certified_descent_with_stability: final descent theorem ✓

### Verified (native_decide):
- 4 sanity checks (v2NatC, syracuseNextC)
- 6 full certificates (checkFullCert)

### Sorry count: 0
ALL theorems including verifyStability_sound are sorry-free.

### Architecture — COMPLETE SOUNDNESS CHAIN:
```
checkFullCert cert = true
  ├── checkHybridCert: ratio + threshold ✓
  └── verifyStability: trajectory + stability ✓
       │ verifyStability_sound (Phase 6b — NOW PROVED)
       ↓
  aSeq n agrees with vals
       │ certified_descent_with_stability
       ↓
  bridge → iteration_equation → descent → nSeq n m < n
```
-/

/-!
## Step 9: Assembly — certified_descent_for_class (Sprint P14 Phase 4)

The culminating theorem: given a StabilityCert where checkFullCert = true,
any n in the residue class with n ≥ threshold descends.

### Two versions (per Triade Cycle 73 — GPT CRITICAL #3):

**Version 1** (Minimal, correct): Requires explicit `n ≥ threshold` hypothesis.
This is the mathematically rigorous statement.

**Version 2** (Strong): Assumes `threshold ≤ residue` (Conjecture NEXUS-N₀),
giving descent for ALL n in the class.

Date: 2026-02-16 (Sprint P14)
-/

/-- Helper: extract ratio condition from checkFullCert. -/
private theorem checkFullCert_ratio (cert : StabilityCert)
    (h : checkFullCert cert = true) :
    pow3 cert.valuations.length < pow2 (listSum cert.valuations) := by
  simp only [checkFullCert, Bool.and_eq_true] at h
  have hHybrid := h.1
  simp only [checkHybridCert, Bool.and_eq_true] at hHybrid
  have hRatio := hHybrid.1
  simp only [checkDescentRatio, decide_eq_true_eq] at hRatio
  exact hRatio

/-- Helper: extract stability from checkFullCert. -/
private theorem checkFullCert_stability (cert : StabilityCert)
    (h : checkFullCert cert = true) :
    verifyStability cert.residue cert.modulus_exp cert.valuations = true := by
  simp only [checkFullCert, Bool.and_eq_true] at h
  exact h.2

/-- **Version 1 — Certified descent for a class (with threshold hypothesis).**

    If checkFullCert cert = true, n is in the residue class r mod 2^k,
    and n ≥ computeThreshold(vals), then nSeq n m < n.

    This is the COMPLETE, CORRECT statement — no sorry, no gaps. -/
theorem certified_descent_for_class (cert : StabilityCert)
    (hcheck : checkFullCert cert = true)
    (n m : ℕ)
    (hn : n = cert.residue + 2^cert.modulus_exp * m)
    (hthresh : computeThreshold cert.valuations ≤ n) :
    nSeq n cert.valuations.length < n := by
  -- Extract components from checkFullCert
  have hratio := checkFullCert_ratio cert hcheck
  have hstab := checkFullCert_stability cert hcheck
  -- verifyStability_sound: stability checker → aSeq agreement
  have haSeq := verifyStability_sound cert.valuations cert.residue cert.modulus_exp n m hstab hn
  -- Assemble with certified_descent_with_stability
  exact certified_descent_with_stability cert.valuations cert.residue cert.modulus_exp n
    hratio hthresh haSeq

/-- **Version 2 — Strong descent (conditional on threshold ≤ residue).**

    If additionally the threshold is ≤ the residue (Conjecture NEXUS-N₀),
    then ALL n in the class descend (since n = r + 2^k·m ≥ r ≥ threshold). -/
theorem certified_descent_for_class_strong (cert : StabilityCert)
    (hcheck : checkFullCert cert = true)
    (hN0 : computeThreshold cert.valuations ≤ cert.residue)
    (n m : ℕ)
    (hn : n = cert.residue + 2^cert.modulus_exp * m) :
    nSeq n cert.valuations.length < n := by
  -- n = r + 2^k * m ≥ r ≥ threshold
  have h_n_ge_r : cert.residue ≤ n := by omega
  have hthresh : computeThreshold cert.valuations ≤ n := by omega
  exact certified_descent_for_class cert hcheck n m hn hthresh

/-!
## Step 10: Conjecture NEXUS-N₀ (Sprint P14 Phase 3)

**Conjecture**: For a valid StabilityCert, the threshold ≤ the residue.

If this holds, `certified_descent_for_class_strong` applies and ALL n in the
class descend — not just those ≥ threshold.

### Formalization strategy (per Triade Cycle 73):
1. Define a computable checker `checkN0` that verifies threshold ≤ residue
2. Prove soundness: checkN0 = true → computeThreshold ≤ residue
3. Extend `checkFullCert` to include N0 check → "full strong cert"
4. Verify by native_decide for concrete certificates

### Caveat (per GPT Cycle 73 CRITICAL #2):
N₀ depends on the certificate chosen (which vals, which m). This formalization
uses the specific certificate given, making N₀ a property of the *certificate*
not an intrinsic property of (r,k).

Date: 2026-02-16 (Sprint P14)
-/

/-- Check that the threshold is ≤ the residue (NEXUS-N₀ property). -/
def checkN0 (cert : StabilityCert) : Bool :=
  Nat.ble (computeThreshold cert.valuations) cert.residue

/-- Full strong certificate check: descent + stability + N₀. -/
def checkFullStrongCert (cert : StabilityCert) : Bool :=
  checkFullCert cert && checkN0 cert

/-- Soundness of checkN0: if true, then threshold ≤ residue. -/
theorem checkN0_sound (cert : StabilityCert)
    (h : checkN0 cert = true) :
    computeThreshold cert.valuations ≤ cert.residue := by
  simp [checkN0, Nat.ble_eq] at h
  exact h

/-- **The ultimate theorem**: if checkFullStrongCert passes, ALL n in the class descend. -/
theorem certified_descent_strong (cert : StabilityCert)
    (hcheck : checkFullStrongCert cert = true)
    (n m : ℕ)
    (hn : n = cert.residue + 2^cert.modulus_exp * m) :
    nSeq n cert.valuations.length < n := by
  simp only [checkFullStrongCert, Bool.and_eq_true] at hcheck
  exact certified_descent_for_class_strong cert hcheck.1 (checkN0_sound cert hcheck.2) n m hn

-- Verify NEXUS-N₀ for our example certificates
example : checkFullStrongCert stabCert_r3 = true := by native_decide
example : checkFullStrongCert stabCert_r7 = true := by native_decide
example : checkFullStrongCert stabCert_r5 = true := by native_decide
-- Note: stabCert_r1 has threshold=2 > residue=1, so checkN0 fails.
-- This is correct: n=1 gives syracuseNext(1)=1, no descent.
-- checkFullCert (without N0) still passes:
example : checkFullCert stabCert_r1 = true := by native_decide
example : checkFullStrongCert stabCert_r15 = true := by native_decide
example : checkFullStrongCert stabCert_r11 = true := by native_decide

end ProjetCollatz
