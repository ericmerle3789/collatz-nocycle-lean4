---
section: "8"
owner: worker
status: skeleton
last_updated: 2026-04-24
---

# 8. Formalization in Lean 4 (Mathlib v4.27.0)

*[WIP — Day 2 draft planned per 0064 §4 timeline.]*

## Planned structure

### 8.1 The central conditional theorem
- `ProjetCollatz.no_nontrivial_cycle_phase59` and its aliases (`_final`, `_derived`, `_full`).
- File : `ProjetCollatz/Phase58PorteDeuxFinal.lean` (statement and proof).
- Axiom profile : `[propext, Classical.choice, Quot.sound]` (kernel-3 only at G2 baseline).
- The three structural hypotheses as `structure` parameters : `BakerSeparation`, `BarinaVerification`, `DerivedLargeKBound` (= `ProductBoundThreshold` in paper prose).

### 8.2 Infrastructure theorems (kernel-3)
- Phase60 `IrrationalityLog23` — `log_2 3` is irrational, used by δ8 product-bound obstruction reasoning.
- Phase61 `CFConvergents` — best-approximation infrastructure (`log23_convergent`, `q_n`, `InWindow`, `not_convergent_implies_far_approx`).
- Phase62 `BestApproxBridge` — `log23_abs_sub_convergent_le` (approximation bound), `log23_never_terminates`, parametric `log23_abs_sub_convergent_le_in_window`.

### 8.3 Arithmetic gap constants (native_decide)
- `cf_gap_8` .. `cf_gap_13`, `cf_nbound_8` .. `cf_nbound_13` in `ProjetCollatz/Phase59ContinuedFractions.lean`.
- Axiom profile : `[propext, Lean.ofReduceBool, Lean.trustCompiler]` (the two native_decide axioms are documented in `expected_axioms.md`).
- **Isolated from the central chain at G2** because `DerivedLargeKBound` is taken as a parameter.

### 8.4 Phase63 skeleton (preserved, not completed)
- `ProjetCollatz/Phase63DerivedLargeKBoundTheorem.lean` (175 lines Section 1 + M3.4 Pivot docstring) : module docstring + imports + namespace + opens.
- Sections 2-11 intentionally not implemented — see §5 Obstruction I (δ8).
- The file serves as a structured skeleton and formal pointer to §5 (docstring footer).

### 8.5 Expected axiom profile (`expected_axioms.md`)
Reference snapshot of the `#print axioms` baseline parsed by `reproduce.sh` :
- Central chain (7 theorems) : kernel-3.
- Auxiliary (3 sampled `cf_gap_*`/`cf_nbound_*`) : kernel-1 + 2 native_decide.
- M3 foundational (15 theorems Phase60/61/62) : kernel-3.
- Forthcoming (M3.4 commented block) : anticipates the 5-axiom profile if and when Phase63 Sections 2-11 are completed.

### 8.6 Reproducibility (`reproduce.sh`)
Exit-code contract : 0 = OK, 1 = toolchain, 2 = build, 3 = axiom drift, 4 = sorryAx detected. CI enforces the same checks on every push.

### 8.7 Integrity invariants
- Zero user `axiom` declaration project-wide.
- Zero `sorry`, `admit`, `stop`.
- All docstrings in English.
- RT findings HIGH/MEDIUM/LOW fixed pre-commit (zero-flag policy, Eric 2026-04-23).
- Anti-G3.11 15 min decantation pre-push.

## Deliverables Day 2

- [ ] Clean English prose of §8.1-§8.7, ~2-3 pages.
- [ ] Every file reference has a repo path; every theorem reference has a file + name.
- [ ] Current axiom profile quoted from actual `#print axioms` output (re-verify at time of writing).
- [ ] `reproduce.sh` exit codes quoted from the script header.

## RT#1 checklist (to apply post-draft)

- [ ] §8.1 structure fields match `ProjetCollatz/Phase58*.lean` (line-verified).
- [ ] No claim about Lean content that is not true *today* (integrity : §8 must reflect repo state exactly).
- [ ] No forward claim about Phase63 Sections 2-11 being "soon" — they are not.
- [ ] Mathlib version quoted correctly (`v4.27.0`).

## Blocked on

- Re-reading `ProjetCollatz/Phase58*.lean`, `Phase60*.lean`, `Phase61*.lean`, `Phase62*.lean` to ensure §8.1-§8.4 prose is anchored in repo reality.
- Final decision on whether to expand §8.5 with the full 35-theorem table or keep a summary.
