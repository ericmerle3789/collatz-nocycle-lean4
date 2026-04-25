---
section: "7"
owner: session_c
status: imported-session-c-section-F
contributions:
  - "§7 content drafted by Session C Mathlib-Prover, mathnotes package 0018 §F (mailbox from_mathlib_prover/0018, lines 267-283). Integrated by Worker per Session B authorization 0083 §5.3 + 0092 §5, with three minor Worker-imposed elements: (1) brief intro paragraph for narrative flow ; (2) §7.1/§7.2 subsection split for paper-style consistency with §3-§6 ; (3) one-sentence forward pointer to §8 (Phase63 Lean skeleton) and §5 (δ8 obstruction) for Lean-correspondence context. The placeholder's six-window CF disjunction content is NOT imported here (different scope ; belongs in §8, where Phase63 is already documented)."
source: mailbox/from_mathlib_prover/0018 §F
last_updated: 2026-04-25
---

# 7. Alternative framing via disjunction (δ7)

The conditional Theorem 3.1 admits a logically equivalent disjunctive
reformulation that frames the conditionality structurally rather than
operationally. This section presents the disjunctive form (« δ7 ») and
its interpretation under current SOTA bounds.

## 7.1 Statement

**Observation.** Our Theorem 3.1 is logically equivalent to the
disjunctive statement :

**Theorem 7.1** (equivalent form). *For every non-trivial Collatz
cycle `(n, k)`, we have `k ≤ 982` or `n > 2⁷¹`.*

**Proof.** Suppose a cycle `(n, k)` exists with `k > 982` and
`n ≤ 2⁷¹`. Then Barina (Phase58, §4.2) gives `reaches_one n`,
contradicting `IsOddCycle n k` via `cycle_prevents_reaching_one`
(Phase50). ∎

## 7.2 Interpretation

Theorem 7.1 is **vacuously true** under the Collatz no-cycle
conjecture. Any hypothetical counterexample must have either :

- Low cycle complexity (`k ≤ 982`) and `n ≤ 2⁷¹` — ruled out by
  Barina's computational verification, OR
- High cycle complexity (`k > 982`) and `n > 2⁷¹` — outside current
  methods.

Hercher (2023) `K > 1.375 · 10¹¹` rules out the first disjunct
independently. Our formalization combined with Hercher's result
therefore guarantees `n > 2⁷¹` for any hypothetical cycle.

**Consistency check.** `n > 2⁷¹` is **outside** current peer-reviewed
verification (Barina's `2⁷¹` is the SOTA). Any future extension of
Barina (or equivalent) to `n > 2⁷¹` would directly test hypothetical
cycles against our framework.

A finer-grained six-window continued-fraction refinement of the
high-complexity disjunct (`k ∈ W_8 ∪ … ∪ W_{13}` for the cycle-bound
range `k > 1322`) is documented as a Lean skeleton in
`ProjetCollatz/Phase63DerivedLargeKBoundTheorem.lean` (see §8) ; the
non-completion of that skeleton meets the structural obstruction of
§5 (δ8 / δ8'), which explains why the conditional theorem cannot be
closed unconditionally via further Diophantine refinement within the
Baker + CF paradigm.

