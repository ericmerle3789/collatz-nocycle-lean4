---
section: "3"
owner: session_c
status: placeholder
source: mathnotes_0018_section_B
last_updated: 2026-04-24
---

# 3. Main theorem: conditional proof

**Owner** : Session C Mathlib-Prover, via mathnotes package 0018 §B.

**Status** : awaiting Session C English draft import from `mailbox/from_mathlib_prover/0018-MATHNOTES-PACKAGE-paper-v2-sections-3-to-7-verbatim-extractions-english-draft.md`.

## Expected content (per 0064 §3.2)

Restate of the Phase58 central theorem in paper prose :

- Statement : given `BakerSeparation`, `BarinaVerification`, `ProductBoundThreshold`, there exists no `(n, k)` with `n > 1`, `IsOddCycle n k`.
- Proof sketch : split `k ≤ 1322` (Barina) vs `k > 1322` (ProductBoundThreshold ⇒ `n < 2^71` ⇒ Barina).
- Reference to `ProjetCollatz.no_nontrivial_cycle_phase59` and its aliases (`final`, `derived`, `full`).

## Integration note for Worker

When importing Session C draft into this file, preserve :
- Verbatim claims in a numbered environment (no paraphrase drift).
- Cross-references to `ProjetCollatz/Phase58PorteDeuxFinal.lean` line numbers.
- The honest framing : this is **the conditional theorem**; the conditional nature is discussed in §4-§5.

**Do not modify** Session C prose without flagging via `to_auditor/`. Per 0065 policy, all Session C content is direct-verified.
