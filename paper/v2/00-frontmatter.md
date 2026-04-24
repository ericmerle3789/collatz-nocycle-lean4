---
section: frontmatter
owner: worker
status: skeleton
last_updated: 2026-04-24
---

# Frontmatter

## Title

**On the non-existence of non-trivial Collatz cycles: a conditional formal proof with documented structural obstructions**

## Authors

Eric Merle.

Formalization and drafting assisted by an AI workflow (Claude Opus 4.7 1M context, 2026-04) under NASA-grade protocols (ADR-001/002/003, zero-flag, 4-eyes review).

## Abstract

*[WIP — to be drafted Day 1-2 after §1+§2 stabilize.]*

Planned content :
- One-sentence statement of the main theorem (Phase58 conditional).
- The three structural hypotheses (BakerSeparation, BarinaVerification, ProductBoundThreshold).
- The five original contributions (δ7, δ8, δ8', δ9, 6α).
- The honest framing : we prove a conditional result, document the obstruction preventing removal of ProductBoundThreshold, and situate our work within the 1977-2026 literature.
- Lean 4 formalization under Mathlib v4.27.0, fully reproducible (`reproduce.sh` EXIT 0, expected axiom profile listed).

Target length : 150-200 words.

## Keywords

Collatz conjecture, 3x+1 problem, Collatz cycles, linear forms in logarithms, Baker's theorem, continued fractions, log₂ 3, formal verification, Lean 4, Mathlib.

## MSC 2020

11B83 (Special sequences), 11J86 (Linear forms in logarithms), 11Y55 (Calculation of integer sequences), 68V15 (Theorem proving (deduction, resolution, etc.)).
