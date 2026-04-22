# expected_axioms.md

**Baseline for `probes/check_central_axioms.lean`** — snapshot of axiom dependencies for all central and auxiliary theorems of `collatz-nocycle-lean4`, as of G2 hardening (2026-04-22, commit `d2fa81a` + G1 commits).

Any commit that alters these expectations MUST update this file AND pass `reproduce.sh` EXIT 0.

---

## Legend

- **(S)** = one of the 3 standard Lean kernel axioms : `propext`, `Classical.choice`, `Quot.sound`
- **(N)** = `native_decide` axioms : `Lean.ofReduceBool`, `Lean.trustCompiler`
- `sorryAx` = Lean's sorry axiom — **FORBIDDEN** in every central or auxiliary theorem listed here

---

## Section 1 — Central theorem chain

All 7 theorems depend on exactly the 3 fundamental Mathlib axioms :

| Theorem | Expected axioms | Classification |
|---------|-----------------|----------------|
| `ProjetCollatz.no_nontrivial_cycle_phase59` | `[propext, Classical.choice, Quot.sound]` | Central (principal) |
| `ProjetCollatz.no_nontrivial_cycle_final` | `[propext, Classical.choice, Quot.sound]` | Central (variant/alias) |
| `ProjetCollatz.no_nontrivial_cycle_derived` | `[propext, Classical.choice, Quot.sound]` | Central (variant/alias) |
| `ProjetCollatz.no_nontrivial_cycle_full` | `[propext, Classical.choice, Quot.sound]` | Central (variant/alias) |
| `ProjetCollatz.no_cycle_k_le_1322` | `[propext, Classical.choice, Quot.sound]` | Central (sub-branch k ≤ 1322, Barina) |
| `ProjetCollatz.no_cycle_k_gt_1322` | `[propext, Classical.choice, Quot.sound]` | Central (sub-branch k > 1322, CF) |
| `ProjetCollatz.sdw_from_cf` | `[propext, Classical.choice, Quot.sound]` | Central (key conditional lemma) |

**All 3 axioms are standard Mathlib kernel axioms**, required by any non-constructive theorem using classical reasoning and quotient types. No user-declared `axiom` is ever introduced in `ProjetCollatz/`.

---

## Section 2 — Auxiliary native_decide lemmas

These 3 sampled lemmas (out of a broader family) use `native_decide` to verify arithmetic gap constants from continued-fractions theory :

| Theorem | Expected axioms | Role |
|---------|-----------------|------|
| `ProjetCollatz.cf_gap_8` | `[propext, Lean.ofReduceBool, Lean.trustCompiler]` | CF Window 8 arithmetic gap |
| `ProjetCollatz.cf_gap_13` | `[propext, Lean.ofReduceBool, Lean.trustCompiler]` | CF Window 13 arithmetic gap |
| `ProjetCollatz.cf_nbound_8` | `[propext, Lean.ofReduceBool, Lean.trustCompiler]` | CF Window 8 `n` bound |

**Important isolation property at G0/G1/G2** : these lemmas are **not** in the transitive axiom chain of `no_nontrivial_cycle_phase59`, because `DerivedLargeKBound` is a `structure` taken as a **parameter** by the central theorem. The `cf_gap_*` and `cf_nbound_*` lemmas are the mathematical justification of the structure's content (detailed in the paper) but are not composed into its proof in Lean.

---

## Section 3 — Forthcoming changes (Phase Legendre M3)

When `DerivedLargeKBound` is promoted from `structure` to a proven theorem via Legendre 1798 + `cf_gap_*` integration :

- **`Lean.ofReduceBool`** and **`Lean.trustCompiler`** will enter the central chain axioms of `no_nontrivial_cycle_phase59`
- This is **authorized** by MISSION_NASA §10 with explicit declaration
- This file MUST be updated with the new expected Section 1 axiom list BEFORE the M3 integration commit
- The paper MUST explicitly acknowledge these two `native_decide`-related axioms in the formal verification section

Anticipated Section 1 axiom set for M3+ :
```
[propext, Classical.choice, Quot.sound, Lean.ofReduceBool, Lean.trustCompiler]
```

---

## Section 3bis — Out-of-scope at G2 (not currently audited by reproduce.sh)

The following theorems and structures exist in `ProjetCollatz/` but are **not** in the authoritative probe at G2. They are either (a) definitions/structures, not theorems with proofs, or (b) lower-level lemmas not considered public API, or (c) deemed out-of-scope for the G2 hardening pass.

- `ProjetCollatz.BakerSeparation` — external hypothesis structure (definition, not a theorem)
- `ProjetCollatz.BarinaVerification` — external hypothesis structure
- `ProjetCollatz.DerivedLargeKBound` — external hypothesis structure (will become a theorem at M3)
- `ProjetCollatz.IsOddCycle` — definition, not a theorem
- `ProjetCollatz.steiner_equation` — internal lemma, not public API
- Other `cf_gap_*` / `cf_nbound_*` variants beyond the 3 sampled — content-similar, axiom pattern expected identical (to be audited exhaustively in S2.X if reviewer requests)

Reason for exclusion : G2 establishes the core axiom baseline for the **publicly claimed result** (`no_nontrivial_cycle_*` + its immediate dependencies). Exhaustive audit of every lemma in ProjetCollatz is reserved for a future rigor pass, with cost/benefit to be evaluated.

## Section 4 — Forbidden patterns

Any appearance of the following in the `#print axioms` output of a Section 1 or Section 2 theorem is a **BLOCKER**, detected by `reproduce.sh` :

- `sorryAx` → EXIT 4 (incomplete proof)
- Any user-declared `axiom` (e.g. `ProjetCollatz.some_axiom`) not listed in this file → EXIT 3 (unexpected axiom)
- Any unlisted axiom from a dependency → EXIT 3 (dependency drift)

---

## Verification

```bash
bash reproduce.sh
# EXIT 0 if baseline maintained
# EXIT 3 if axiom drift
# EXIT 4 if sorryAx detected
```

`reproduce.sh` parses the output of `probes/check_central_axioms.lean` and `probes/check_sorry.lean` against this file. CI (`.github/workflows/verify.yml`) enforces the same checks on every push and pull request.

---

## Historical note

- **2026-04-22 G0** : axiom baseline established via manual `#print axioms` probe (file : `docs/BIBLE/env-snapshots/2026-04-22-axioms-central.txt`, SHA256 `be074de13edec263f83a3acb72690081e872dccdb4f740f321ef6b995f8259dd`)
- **2026-04-22 G2** : this canonical document created + probes added + CI upgrade + Red Team HIGH mitigations applied (see `docs/BIBLE/redteam/2026-04-22-G2-hardening.md`)
- **M3 (planned)** : update expected Section 1 with `Lean.ofReduceBool, Lean.trustCompiler`
