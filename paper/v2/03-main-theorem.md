---
section: "3"
owner: session_c
status: imported-session-c-section-B
contributions:
  - "§3 content drafted by Session C Mathlib-Prover, mathnotes package 0018 §B (mailbox from_mathlib_prover/0018, 2026-04-24T19:40:00Z). Integrated by Worker per Session B authorization 0083 §5.3 + 0101 §5, with one editorial reconciliation note on the axiom-profile perspective (disclosed in Commit #7 preflight)."
source: mailbox/from_mathlib_prover/0018 §B
last_updated: 2026-04-24
---

# 3. Main theorem: conditional proof

## 3.1 Statement

We formalize the following conditional result in Lean 4 (Mathlib v4.27.0) :

**Theorem 3.1** (`ProjetCollatz.no_nontrivial_cycle_final`, declared at
`ProjetCollatz/Phase58PorteDeuxFinal.lean` line 339) :

> *Let `baker : BakerSeparation`, `barina : BarinaVerification`,
> `sdw : ProductBoundThreshold`. Then for all `n, k : ℕ`,
> `IsOddCycle n k → False`.*

Formal Lean statement (verbatim from the project) :

```lean
theorem no_nontrivial_cycle_final
    (baker : BakerSeparation) (barina : BarinaVerification)
    (sdw : ProductBoundThreshold)
    (n k : ℕ) (hcyc : IsOddCycle n k) : False
```

See §2.3 for the Lean `structure` fields underlying the three
hypothesis parameters, §4 for the mathematical origin of each
hypothesis, and §8.1 for the full aliases table listing the six
equivalent packagings of Theorem 3.1 exported by the repository.

## 3.2 Proof chain

1. Extract the cycle minimum `m` via `cycle_has_min` (Phase56, proved).
2. Apply `cycle_min_bound_nat` (Phase56, proved, uses Baker) :
   `m ≤ (k⁷ + k) / 3`.
3. Use `ProductBoundThreshold.cycle_length_bound` : `k ≤ 982`.
4. Apply `k982_bound` (Phase56, `native_decide`) :
   `(982⁷ + 982)/3 < 2⁷¹`.
5. Hence `m < 2⁷¹`. Combined with `m > 0` (from `IsOddCycle`), Barina
   gives `reaches_one m`.
6. `cycle_prevents_reaching_one` (Phase50, proved) yields contradiction.

## 3.3 Axiom profile

**Editorial note on perspective (added by Worker during integration,
parametric perspective primary).** `no_nontrivial_cycle_final` is
**declared parametrically** with `sdw : ProductBoundThreshold` as an
explicit parameter. The proof uses `sdw.cycle_length_bound` directly,
without unfolding any specific witness. Therefore, the
**theorem-as-declared has axiom profile** `[propext, Classical.choice,
Quot.sound]` (kernel-3), as machine-verified by `reproduce.sh` against
the `expected_axioms.md` baseline (see §8.6 / §8.7).

The alternative five-axiom reading below, under "Instantiated profile
(as reported by Session C mathnotes 0018 §B)", corresponds to the
**fully-instantiated** proof term obtained when a caller supplies the
concrete witness `k982_bound` (whose proof uses `native_decide`,
introducing `Lean.ofReduceBool` and `Lean.trustCompiler`). This
perspective is helpful for readers reconstructing the end-to-end
argument but does not modify the axiom profile of the parametric
theorem itself.

**Instantiated profile (as reported by Session C mathnotes 0018 §B)** :
`propext`, `Classical.choice`, `Quot.sound` (kernel-3) +
`Lean.ofReduceBool`, `Lean.trustCompiler` (from `native_decide` on
`k982_bound`). All documented in `expected_axioms.md`.

---

## Integration notes (Worker internal — remove before publication)

- Content of §3.1-§3.2 verbatim from Session C mathnotes 0018 §B
  (mailbox `from_mathlib_prover/0018`, lines 98-123). The sub-section
  split (§3.1 Statement / §3.2 Proof chain / §3.3 Axiom profile) is
  Worker-added for paper-style organisation matching §1 / §2 / §8
  structure. No word of §B substance was dropped.
- Integration glue (disclosed in Commit #7 preflight 0104) :
  - Added line-number reference `line 339` after the file path
    `Phase58PorteDeuxFinal.lean` (consistency with §8.1 table).
  - Added forward pointers (§2.3, §4, §8.1) in §3.1.
  - Added the "Editorial note on perspective" in §3.3 to reconcile
    Session C's instantiated axiom profile with §8.5's parametric
    profile. This is a substantive editorial addition, not a
    modification of §B content ; it flags a subtlety that would
    otherwise create an apparent paper-internal contradiction between
    §3 and §8.
- No other modifications. The six proof-chain steps, the Lean code
  block, the Theorem 3.1 statement, and the citations to Phase50 /
  Phase56 / Phase58 are all preserved verbatim.
