---
section: "2"
owner: worker
status: draft-day1
last_updated: 2026-04-24
---

# 2. Framework and notation

## 2.1 The Collatz map, the odd iterate, and odd cycles

The **Collatz map** `T : ℕ_{≥1} → ℕ_{≥1}` is defined by
`T(n) = n/2` when `n` is even, and `T(n) = (3n+1)/2` when `n` is odd.
The **odd iterate** `T_odd` compresses the halvings : starting from an
odd integer, `T_odd(n)` is the unique odd integer on the Collatz
trajectory of `n` reached after exactly one `3n+1/2` step followed by
all consecutive halvings. In the Lean 4 formalization accompanying
this paper `T_odd` is written `syracuseNext`, and its iterate is the
function `nSeq : ℕ → ℕ → ℕ` of `ProjetCollatz/SyracuseDefs.lean` line 213,
defined by `nSeq start 0 = start` and `nSeq start (k+1) = syracuseNext (nSeq start k)`.

**Definition 2.1 (odd Collatz cycle).** A pair `(n, k)` of natural
numbers is an *odd Collatz cycle* if `n > 1`, `n` is odd, `k ≥ 1`, and
`nSeq n k = n`. This is the predicate `IsOddCycle` of
`ProjetCollatz/Phase50CycleEquation.lean` line 27-28 :

```lean
def IsOddCycle (n : ℕ) (k : ℕ) : Prop :=
  n > 1 ∧ n % 2 = 1 ∧ k ≥ 1 ∧ nSeq n k = n
```

The exclusion `n > 1` removes the trivial fixed orbit at `1` ; every
reference below to "cycle" means *odd Collatz cycle* in this sense.
The cycle problem is the negative claim : no such `(n, k)` exists.

## 2.2 Parity vectors, the sum of halving exponents, and Steiner's identity

Fix an odd Collatz cycle `(n, k)`. Write `n_i := nSeq n i` for
`0 ≤ i ≤ k`, so that `n_0 = n_k = n` and each `n_i` is odd. Between
`n_i` and `n_{i+1}` there is exactly one `3n+1/2` step followed by some
number `s_{i+1} ≥ 0` of halvings, called the *i-th parity exponent*.
The list `(s_1, ..., s_k)` is the *parity vector* of the cycle, and
`s := s_1 + ... + s_k` its *sum of halving exponents*.

Collecting all `k` odd steps gives **Steiner's cycle identity** :

`n · (2^s - 3^k) = C_{n, k, s}`

where `C_{n, k, s} = Σ_{i=1}^{k} 3^{k-i} 2^{s_1 + ... + s_{i-1}}` is a
strictly positive integer (the "corrective sum"). The identity is the
discrete analogue of log-linearity of the Collatz dynamics and is the
conventional entry point to Baker-style arguments. Its Lean
formalization is in `ProjetCollatz/Phase52SteinerEquation.lean`
(`corrSum`, `steiner_eq`, `steiner_cycle_eq`, `corrSum_pos_of_cycle`
at lines 101-150).

A direct consequence of Steiner's identity is that `2^s > 3^k` for any
hypothetical non-trivial cycle (else the right-hand side would be
non-positive), so `s = ⌈k · log_2 3⌉` whenever the cycle is compatible
with the ambient inequality framework. This is the bridge to
continued-fraction approximation theory (§7).

## 2.3 The three structural hypotheses

Our central theorem depends on three `structure` fields, all declared
in `ProjetCollatz/Phase58PorteDeuxFinal.lean` :

**2.3.1 `BakerSeparation` (Phase58, lines 67-69).**

```lean
structure BakerSeparation where
  separation : ∀ (s k : ℕ), s ≥ 1 → k ≥ 2 → 2^s > 3^k →
    (2^s - 3^k) * k^6 ≥ 3^k
```

This is the effective version of Baker's 1966 theorem specialised to
the cycle problem, at irrationality-measure exponent `μ = 6` — a
strictly weaker constant than Rhin's 1987 bound `μ(log_2 3) ≤ 5.125`,
but sufficient for our derivation and straightforward to state. See §4.1.

**2.3.2 `BarinaVerification` (Phase58, lines 80-81).**

```lean
structure BarinaVerification where
  convergence : ∀ (n : ℕ), n > 0 → n < 2^71 → reaches_one n
```

Barina's 2025 computational verification that every positive integer
below `2^71` ultimately reaches `1`. See §4.2.

**2.3.3 `ProductBoundThreshold` (Phase58, lines 296-297).**

```lean
structure ProductBoundThreshold where
  cycle_length_bound : ∀ (n k : ℕ), IsOddCycle n k → k ≤ 982
```

This is the third hypothesis. Its origin is derived, not taken from a
single published paper : combining the Product Bound lemma of
`ProjetCollatz/Phase56*.lean` (which states `m ≤ (k^7 + k)/3` for a
cycle minimum `m`, a consequence of Baker's separation inequality) with
Barina's limit `2^71` produces the arithmetic inequality
`(982^7 + 982)/3 < 2^71 ≤ (983^7 + 983)/3`, and hence the threshold
`k ≤ 982` for any hypothetical cycle. The derivation is honest and
transparent, but the promotion of this hypothesis to a theorem is
structurally blocked : this is the content of §5. See also
`ProjetCollatz/HYPOTHESES.md` in the accompanying repository for the
full derivation chain and the distinction between `k` (number of odd
steps) and `m` (number of local minima as in Simons-de Weger 2005).

## 2.4 The central theorem (forward pointer)

**Theorem (informal statement, see §3 for the formal version).** Assume
`BakerSeparation`, `BarinaVerification`, and `ProductBoundThreshold`.
Then there is no odd Collatz cycle in the sense of Definition 2.1.

In the Lean formalization this is
`ProjetCollatz.no_nontrivial_cycle_final` in
`ProjetCollatz/Phase58PorteDeuxFinal.lean` line 339. Its proof is
discharged in six elementary steps, recorded verbatim in §3 and
documented with line numbers in §8.

## 2.5 Notation conventions

- `log_2 3` denotes the real number `Real.logb 2 3` of Mathlib 4.
- Continued-fraction convergents of `log_2 3` are written `p_n / q_n`
  with `q_n ∈ ℕ_{≥1}` the denominator ; these correspond to the
  Lean-side notation `q_n` of `ProjetCollatz/Phase61CFConvergents.lean`.
- The six *windows* used in §7 are defined by `W_n := [q_n, q_{n+1})`
  for `n ∈ {8, 9, 10, 11, 12, 13}`, the predicate `InWindow n k ↔
  q_n ≤ k < q_{n+1}` being the Lean abbreviation of
  `ProjetCollatz/Phase61CFConvergents.lean`.
- Numerical values : `q_8 = 665`, `q_9 = 15{\,}601`, `q_{10} = 31{\,}867`,
  `q_{11} = 79{\,}335`, `q_{12} = 111{\,}202`, `q_{13} = 190{\,}537`,
  `q_{14} = 10{\,}590{\,}737` (Phase59 `cf_nbound_*` constants).
- `reaches_one` is the Lean abbreviation for "the Collatz trajectory
  starting at `n` eventually hits `1`" ; used in the
  `BarinaVerification` field and in the contradiction-on-cycle proof.

All other symbols introduced later are local to their section.

---

## Style notes (Worker internal — remove before publication)

- Academic English, JIS / Acta Arithmetica register, same register as §1.
- Exact `structure` fields quoted verbatim from repository.
- Every Lean-side reference has a file path + line number.
- No claim beyond what is proved or cited.

## RT#1 checklist (to apply post-draft)

- [ ] Every symbol introduced is used somewhere in §3-§11.
- [ ] No symbol used before defined (`T_odd` introduced §2.1 before `nSeq`, etc.).
- [ ] The exact Phase58 `structure` fields match the repository — line-cited :
  - `BakerSeparation` L67-69 ✓
  - `BarinaVerification` L80-81 ✓
  - `ProductBoundThreshold` L296-297 ✓
- [ ] `IsOddCycle` verbatim from `Phase50CycleEquation.lean` L27-28 ✓
- [ ] `nSeq` recursion from `SyracuseDefs.lean` L213 ✓
- [ ] Steiner's identity sign convention consistent with `Phase52SteinerEquation.lean`.
- [ ] No hype ("elegant", "trivial", "easy") — scan before Commit #4.
- [ ] `q_n` numerical values match `Phase59ContinuedFractions.lean` (window constants).
- [ ] `reaches_one` name consistent with `BarinaVerification.convergence` field.

## Dependencies for finalization

- §3 central theorem statement must match §2.4 forward pointer signature.
- §4.1/§4.2/§4.3 must expand the three structures of §2.3 (one subsection each).
- §5 must cite `ProductBoundThreshold` from §2.3.3 by name (not rename).
- §7 must use the window predicate `InWindow` introduced in §2.5.
- §8 must re-cite the exact file paths + line numbers of §2.3 structures.
- §11 references.bib : `Baker1966`, `Barina2025`, `Khinchin1964`, `Lagarias1985`, `SteinerThesis1977` consistent with §4 + §6.
