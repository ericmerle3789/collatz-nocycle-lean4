---
section: "7"
owner: session_c
status: placeholder
source: mathnotes_0018_section_F
last_updated: 2026-04-24
---

# 7. Alternative framing via disjunction (δ7)

**Owner** : Session C Mathlib-Prover, via mathnotes package 0018 §F.

**Status** : awaiting import.

## Expected content

### 7.1 The disjunction structure
Session C's δ7 contribution : reframe the cycle bound `k > 1322` via a six-window disjunction `k ∈ W_8 ∪ ... ∪ W_{13}`, where `W_n = [q_n, q_{n+1})` (continued-fraction windows of `log_2 3`).

### 7.2 Why disjunction over a single Steiner-style bound
Per-window CF gap constants (Phase59 `cf_gap_n`) give sharp arithmetic bounds that a single-inequality approach cannot achieve. The disjunction is not a technical curiosity but a structural consequence of best-approximation theory.

### 7.3 Coverage and the k ≥ q_{14} tail
The six windows cover `k ∈ [665, 10{\,}590{\,}737)`. The tail `k ≥ q_{14}` is beyond current-generation Barina + CF reach; its treatment within the Product-Bound paradigm meets the obstruction of §5 (δ8/δ8').

### 7.4 Lean status
Phase63 Section 1 of `ProjetCollatz/Phase63DerivedLargeKBoundTheorem.lean` documents this disjunction as a skeleton. Sections 2-11 (helper lemma, six windows, synthesis, main theorem, replacement definition) are **not implemented** as of Day 1 paper v2 — the obstruction in §5 is the reason.

## Integration note

When importing Session C draft, preserve the δ7 disjunction as *alternative framing*, not *closing proof*. §8 will reference the Phase63 skeleton as the Lean artefact corresponding to δ7.
