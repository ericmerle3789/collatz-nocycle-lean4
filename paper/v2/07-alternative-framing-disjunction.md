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

---

## Integration notes (Worker internal — remove before publication)

- §F intro framing « **Observation** : our Theorem 3.1 is logically
  equivalent to the disjunctive statement », Theorem 7.1 statement,
  proof, and the interpretation paragraphs (vacuous truth + Hercher
  consequence + consistency check) preserved verbatim from Session C
  mathnotes 0018 §F (lines 269-283).
- Worker integration elements (disclosed below) :
  - **Section intro paragraph** (between title and §7.1) is Worker-
    authored prose framing the disjunction as a *structural* (rather
    than operational) reformulation. No new claims ; substance is
    identical to the §F observation.
  - **§7.1 / §7.2 subsection split** is Worker-imposed paper-style
    organization for consistency with §3-§6 (each has 3-6 named
    subsections). §F is a single 15-line block ; the Worker split
    places (Observation + Theorem 7.1 + Proof) in §7.1 and
    (Interpretation + Hercher + Consistency) in §7.2. No content
    was reordered.
  - **Final paragraph in §7.2** (« A finer-grained six-window
    continued-fraction refinement... ») is Worker-authored. It serves
    two purposes :
    (a) cross-reference forward to §8 (Lean formalization),
    where the Phase63 skeleton is already documented, and to §5
    (δ8 obstruction), which explains why the high-complexity disjunct
    cannot be closed ;
    (b) clarify the relationship between §7's high-level disjunction
    (`k ≤ 982` or `n > 2⁷¹`) and the lower-level six-window CF
    framing (`k ∈ W_8 ∪ … ∪ W_{13}`) that the placeholder for §7
    originally anticipated. The six-window framing belongs in §8
    (where Phase63 lives), not here ; this paragraph routes readers
    appropriately.
- The placeholder file's « expected content » subsections (§7.1 disjunction
  structure, §7.2 disjunction over single bound, §7.3 coverage and
  k ≥ q_{14} tail, §7.4 Lean status) are NOT imported. They describe
  the six-window CF disjunction (a different scope from §F's high-
  level Theorem 7.1 reformulation). The Phase63 skeleton + §5 obstruction
  reference at the end of §7.2 provides the bridge to that material.
- Integration glue (disclosed in Commit #11 preflight) :
  - Heading-level promotion : §F uses `####` (level-4) ; the paper
    uses `##` (level-2) consistent with §3 / §4 / §5 / §6.
  - Typography normalization : `2^{71}` → `2⁷¹`, `1.375·10^{11}` →
    `1.375 · 10¹¹`. Math italics for `n`, `k` consistent with paper-
    style §1-§6.
  - "non-trivial cycle" hyphenated for paper-style consistency
    (§F uses "nontrivial").
- No new numerical claims. All numerical values (`982`, `2⁷¹`,
  `1.375 · 10¹¹`) are preserved verbatim from §F + already-committed
  §3 / §4 / §6.
- No critical corrections (no Brick 2 / Rozier-style issues in §F).
- No new IMPORTANT findings expected (steady-state per 0092 §5).
- No other modifications. The Theorem 7.1 statement, the proof, the
  interpretation bullets, the Hercher disjunct-elimination consequence,
  and the consistency check are all preserved verbatim from §F.
