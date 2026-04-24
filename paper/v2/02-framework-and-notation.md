---
section: "2"
owner: worker
status: skeleton
last_updated: 2026-04-24
---

# 2. Framework and notation

*[WIP — Day 1 draft pending `ProjetCollatz/Phase58*.lean` re-read.]*

## Planned structure

### 2.1 The Collatz map and odd cycles
- Notation : `T`, odd iterate `T_odd`.
- Definition of an **odd Collatz cycle** : a pair `(n, k)` with `n` odd, `k ≥ 1`, and `T_odd^k(n) = n`.
- The trivial cycle `(1, 2)` (i.e., `1 → 1` after two odd iterates).
- Statement of the cycle problem : no `(n, k)` with `n > 1`.

### 2.2 Parity vectors, exponents, and the Steiner equation
- Parity vector `(s_1, ..., s_k)` encoding the number of halvings after each `3x+1/2` step.
- Sum-of-exponents `s = s_1 + ... + s_k`.
- The Steiner identity relating `n`, `k`, `s` via `2^s = 3^k · n + Σ 3^{k-i} 2^{s_1+...+s_{i-1}}`.
- Cross-reference to `ProjetCollatz/Phase56*.lean` for the Lean version (`steiner_equation`).

### 2.3 The three structural hypotheses (forward pointers)
Placeholder definitions quoting the Lean `structure` fields :

```lean
structure BakerSeparation where
  separation : ∀ (s k : ℕ), s ≥ 1 → k ≥ 2 → 2^s > 3^k →
    (2^s - 3^k) * k^6 ≥ 3^k

structure BarinaVerification where
  verified : ∀ n, n ≤ 2^71 → n > 1 → ¬ ∃ k, IsOddCycle n k

structure ProductBoundThreshold where
  threshold : ∀ (n k : ℕ), IsOddCycle n k → k > 1322 → n < 2^71
```

(For the exact fields as implemented in the repo, see `ProjetCollatz/Phase58PorteDeuxFinal.lean` lines 67-95.)

§4 gives the mathematical origin and published support of each; §5 gives the obstruction that forces `ProductBoundThreshold` to remain a hypothesis.

### 2.4 The central theorem (forward pointer)
Statement (paraphrase) : assuming the three hypotheses, there is no non-trivial odd cycle. The formal statement and proof are in §3 (content from mathnotes 0018 §B) and §8 (Lean formalization).

### 2.5 Notation conventions
- `log_2 3` denotes `Real.logb 2 3` (Mathlib).
- `q_n` denotes the denominator of the n-th convergent of `log_2 3` (Phase61 `q_n`).
- CF windows `W_n = [q_n, q_{n+1})` for `n = 8, ..., 13` (Phase59 constants).

## Deliverables Day 1

- [ ] Clean English prose of §2.1-§2.5, ~2-3 pages.
- [ ] Every Lean-side reference has a repo file path + line number.
- [ ] Cross-references forward to §3-§8 added consistently.

## RT#1 checklist (to apply post-draft)

- [ ] Every symbol introduced is used somewhere in §3-§11.
- [ ] No symbol used before defined.
- [ ] The exact Phase58 `structure` fields match the repository (line-cite).
- [ ] `IsOddCycle` definition consistent with `ProjetCollatz/Phase58PorteDeuxFinal.lean`.

## Blocked on

- Re-reading `ProjetCollatz/Phase58PorteDeuxFinal.lean` for exact structure fields.
- mathnotes 0018 §B content (Session C main theorem restate).
