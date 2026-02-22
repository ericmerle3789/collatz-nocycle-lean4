import ProjetCollatz.CollatzCore
import ProjetCollatz.CollatzOddInst

/-!
# SyracuseDefs.lean

But : factoriser les **définitions** et **lemmes généraux** Syracuse/2-adique,
indépendamment des oracles data-level.

Ce fichier est conçu pour être importé par :
- `SyracuseInst.lean` (ponts vers Rule4b/Branch, etc.)
- `Hypotheses.lean` (déclaration de l'oracle concret sans cycle d'import)

Aucun axiome empirique ici.
-/

namespace ProjetCollatz

noncomputable section

/-- Valuation 2-adique sur `ℕ` (nombre de facteurs 2). Convention : `v2Nat 0 = 0`. -/
noncomputable def v2Nat : ℕ → ℕ
| 0 => 0
| (n + 1) =>
  if (n + 1) % 2 = 0 then
    1 + v2Nat ((n + 1) / 2)
  else
    0
termination_by
  n => n
decreasing_by
  -- la seule récursion est sur `(n+1)/2`, strictement plus petit que `n+1`
  simpa using (Nat.div_lt_self (Nat.succ_pos n) (by decide : (1:ℕ) < 2))

/-- Valuation canonique de `3*n+1` (convention Syracuse/TRUE‑K). -/
def v2_3n1 (n : ℕ) : ℕ := v2Nat (3 * n + 1)

/-- Déroulage (impair) : si `n % 2 ≠ 0`, alors `v2Nat n = 0`. -/
theorem v2Nat_eq_zero_of_mod2_ne0 (n : ℕ) (h : n % 2 ≠ 0) : v2Nat n = 0 := by
  cases n with
  | zero =>
      exact False.elim (h (by simp))
  | succ n =>
      simp [v2Nat, h]

/-- Déroulage (pair) : si `n ≠ 0` et `n % 2 = 0`, alors `v2Nat n = 1 + v2Nat (n/2)`. -/
theorem v2Nat_eq_succ_of_mod2_eq0 (n : ℕ) (hn : n ≠ 0) (h : n % 2 = 0) :
    v2Nat n = 1 + v2Nat (n / 2) := by
  cases n with
  | zero => cases hn rfl
  | succ n =>
      simp [v2Nat, h]

/-! ## Divisibilité par `2^(v2Nat n)` -/

/-- `2^(v2Nat n)` divise `n`. -/
theorem pow2_v2Nat_dvd (n : ℕ) : (2 ^ (v2Nat n)) ∣ n := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  cases n with
  | zero =>
      simp [v2Nat]
  | succ k =>
      let m : ℕ := k + 1
      by_cases h : m % 2 = 0
      · have h2 : 2 ∣ m := Nat.dvd_of_mod_eq_zero h
        let m2 : ℕ := m / 2
        have hm2 : m2 < m := by
          have : m2 < k + 1 := by
            simpa [m, m2] using (Nat.div_lt_self (Nat.succ_pos k) (by decide : (1:ℕ) < 2))
          simpa [m] using this
        have ihm2 : (2 ^ (v2Nat m2)) ∣ m2 := ih m2 (by simpa [m] using hm2)
        have hv : v2Nat m = 1 + v2Nat m2 := by
          simp [v2Nat, m, m2, h]
        have hp : (2 ^ (v2Nat m)) = 2 * (2 ^ (v2Nat m2)) := by
          have hpow : 2 ^ (v2Nat m2 + 1) = (2 ^ (v2Nat m2)) * 2 := by
            simpa [Nat.succ_eq_add_one] using (Nat.pow_succ 2 (v2Nat m2))
          calc
            2 ^ (v2Nat m)
                = 2 ^ (1 + v2Nat m2) := by simpa [hv]
            _ = 2 ^ (v2Nat m2 + 1) := by
                  rw [Nat.add_comm 1 (v2Nat m2)]
            _ = (2 ^ (v2Nat m2)) * 2 := hpow
            _ = 2 * (2 ^ (v2Nat m2)) := by simpa [Nat.mul_comm]
        have hm : m = 2 * m2 := by
          simpa [m2] using (Nat.mul_div_cancel' h2).symm
        rcases ihm2 with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        have hm2t : 2 * m2 = 2 * ((2 ^ (v2Nat m2)) * t) := by
          exact congrArg (fun x : ℕ => 2 * x) ht
        calc
          m = 2 * m2 := hm
          _ = 2 * ((2 ^ (v2Nat m2)) * t) := by exact hm2t
          _ = (2 * (2 ^ (v2Nat m2))) * t := by
                simp [Nat.mul_assoc]
          _ = (2 ^ (v2Nat m)) * t := by
                simpa [Nat.mul_assoc] using congrArg (fun x => x * t) hp.symm
      · have hv : v2Nat m = 0 := by
          simp [v2Nat, m, h]
        simpa [m, hv]

/-- `2^(v2_3n1 n)` divise `3*n+1`. -/
theorem pow2_v2_3n1_dvd (n : ℕ) : (2 ^ (v2_3n1 n)) ∣ (3 * n + 1) := by
  simpa [v2_3n1] using (pow2_v2Nat_dvd (3 * n + 1))

/-! ## Macro-pas Syracuse -/

/-- Macro-pas Syracuse : `n ↦ (3*n+1)/2^{v2(3*n+1)}`. -/
noncomputable def syracuseNext (n : ℕ) : ℕ := (3 * n + 1) / (2 ^ (v2_3n1 n))

/-- Spécification multiplicative : `syracuseNext n * 2^a = 3*n+1` avec `a = v2_3n1 n`. -/
theorem syracuseNext_spec : ∀ n : ℕ,
  syracuseNext n * (2 ^ (v2_3n1 n)) = 3 * n + 1 := by
  intro n
  let d : ℕ := 2 ^ (v2_3n1 n)
  have hd : d ∣ (3 * n + 1) := by
    simpa [d] using (pow2_v2_3n1_dvd n)
  have hmul : d * ((3 * n + 1) / d) = 3 * n + 1 := Nat.mul_div_cancel' hd
  have hmul' : ((3 * n + 1) / d) * d = 3 * n + 1 := by
    simpa [Nat.mul_comm] using hmul
  -- et on réécrit `syracuseNext`
  simpa [syracuseNext, d]
    using hmul'

/-! ## Maximalité de v2Nat (béton général) -/

/--
Maximalité : si `m ≠ 0` et `2^k ∣ m`, alors `k ≤ v2Nat m`.
-/
theorem pow2_dvd_le_v2Nat_pos : ∀ (m k : ℕ), m ≠ 0 → (2 ^ k) ∣ m → k ≤ v2Nat m := by
  intro m k
  induction k generalizing m with
  | zero =>
      intro hm hk
      simp
  | succ k ih =>
      intro hm hk
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      -- `2^(k+1) ∣ m` implique `2 ∣ m`
      have h2m : 2 ∣ m := by
        have h2pow : 2 ∣ (2 ^ (Nat.succ k)) := by
          refine ⟨2 ^ k, ?_⟩
          simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        exact Nat.dvd_trans h2pow hk
      have hm_ge2 : 2 ≤ m := Nat.le_of_dvd hmpos h2m
      let m2 : ℕ := m / 2
      have hm2_ne : m2 ≠ 0 := by
        intro h0
        have hm_lt2 : m < 2 := by
          have hd : 0 < 2 := by decide
          have := (Nat.div_eq_zero_iff_lt hd).1 h0
          simpa [m2] using this
        exact (Nat.not_lt_of_ge hm_ge2) hm_lt2
      have hk2 : (2 ^ k) ∣ m2 := by
        rcases hk with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        -- m2 = (2^(k+1)*t)/2 = 2^k*t
        have hdiv : 2 ∣ (2 * t) := by
          refine ⟨t, by simp [Nat.mul_assoc]⟩
        calc
          m2 = m / 2 := by rfl
          _ = (2 ^ (Nat.succ k) * t) / 2 := by simpa [m2, ht]
          _ = ((2 ^ k * 2) * t) / 2 := by
                simp [Nat.pow_succ, Nat.mul_assoc]
          _ = (2 ^ k * (2 * t)) / 2 := by
                simp [Nat.mul_assoc]
          _ = (2 ^ k) * ((2 * t) / 2) := by
                simpa [Nat.mul_assoc] using (Nat.mul_div_assoc (2 ^ k) hdiv)
          _ = (2 ^ k) * t := by simp
      have hk_le : k ≤ v2Nat m2 := ih m2 hm2_ne hk2
      have hmod : m % 2 = 0 := Nat.mod_eq_zero_of_dvd h2m
      have hv : v2Nat m = 1 + v2Nat m2 := by
        simpa [m2] using (v2Nat_eq_succ_of_mod2_eq0 m hm hmod)
      have hle : Nat.succ k ≤ 1 + v2Nat m2 := by
        have hle' : Nat.succ k ≤ Nat.succ (v2Nat m2) := Nat.succ_le_succ hk_le
        simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hle'
      simpa [hv] using hle

/-- Syracuse odd→odd : la sortie du macro-pas est impaire. -/
theorem syracuseNext_odd : ∀ n : ℕ, syracuseNext n % 2 = 1 := by
  intro n
  let a : ℕ := v2_3n1 n
  have hspec : syracuseNext n * (2 ^ a) = 3 * n + 1 := by
    simpa [a] using (syracuseNext_spec n)
  have h01 : syracuseNext n % 2 = 0 ∨ syracuseNext n % 2 = 1 := Nat.mod_two_eq_zero_or_one (syracuseNext n)
  cases h01 with
  | inl hmod0 =>
      have h2dvd : 2 ∣ syracuseNext n := Nat.dvd_of_mod_eq_zero hmod0
      have hpow : (2 ^ (a + 1)) ∣ (3 * n + 1) := by
        rcases h2dvd with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        calc
          3 * n + 1
              = syracuseNext n * (2 ^ a) := by
                  simpa [Nat.mul_comm] using hspec.symm
          _ = (2 * t) * (2 ^ a) := by
                  simpa [ht]
          _ = (2 ^ a * 2) * t := by
                  simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
          _ = (2 ^ (a + 1)) * t := by
                  simp [Nat.pow_succ, Nat.succ_eq_add_one, Nat.mul_assoc]
      have hle : a + 1 ≤ v2Nat (3 * n + 1) :=
        pow2_dvd_le_v2Nat_pos (3 * n + 1) (a + 1) (Nat.succ_ne_zero _) hpow
      have : a + 1 ≤ a := by
        simpa [v2_3n1, a] using hle
      exact False.elim ((Nat.not_succ_le_self a) this)
  | inr hmod1 =>
      exact hmod1

/-! ## Suites Syracuse et pont vers `Nrec` -/

/-- Suite Syracuse (odd→odd) à partir d'un `start_n`. -/
def nSeq (start_n : ℕ) : ℕ → ℕ
| 0 => start_n
| k+1 => syracuseNext (nSeq start_n k)

/-- Suite des valuations `a_k`. -/
def aSeq (start_n : ℕ) : ℕ → ℕ := fun k => v2_3n1 (nSeq start_n k)

/-- Injection de `start_n` côté ℚ pour alimenter `Nrec`. -/
def x0_of_start (start_n : ℕ) : ℚ := (start_n : ℚ)

/-- Trajectoire reconstruite par `Nrec` (défini dans `CollatzOddInst`). -/
def NrecSyr (start_n : ℕ) (k : ℕ) : ℚ :=
  _root_.CollatzOddInst.Nrec (x0_of_start start_n) (aSeq start_n) k

/-- Plomberie : `steps_up_to` est vrai par définition pour `Nrec` (cf. CollatzOddInst). -/
theorem steps_up_to_NrecSyr (start_n : ℕ) (K : ℕ) :
    _root_.CollatzCore.steps_up_to (fun k => NrecSyr start_n k) (aSeq start_n) K := by
  simpa [NrecSyr, x0_of_start] using
    _root_.CollatzOddInst.steps_up_to_Nrec (n0 := x0_of_start start_n) (a := aSeq start_n) K

end

end ProjetCollatz
