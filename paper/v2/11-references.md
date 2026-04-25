---
section: "11"
owner: worker
status: draft-section-11-verify-pass-in-progress
last_updated: 2026-04-25
---

# 11. References

*[Draft — §11 References VERIFY pass in progress (Commit #13). Also maintained in `references.bib` for pandoc BibTeX build.]*

This section is generated from `references.bib` at build time. The list below is the normative human-readable view; every entry must correspond to a `@article{...}` / `@book{...}` / `@misc{...}` entry in `references.bib`.

## Peer-reviewed (≥ 14 required)

1. A. Baker, *Linear forms in the logarithms of algebraic numbers I*, Mathematika 13 (1966), 204-216.
2. R. Terras, *A stopping time problem on the positive integers*, Acta Arithmetica 30 (1976), 241-252. *[verify]*
3. C. J. Steiner, *On the QP-problem of Collatz*, 1977 thesis / Nihonkai Math. J. *[verify — via Lagarias 1985 survey]*
4. R. E. Crandall, *On the "3x+1" problem*, Mathematics of Computation 32 (1978), 1281-1292. *[verify — via Lagarias 1985]*
5. A. Y. Khinchin, *Continued Fractions*, Dover Publications, 1964. (Direct-verified via Krishnan 2016 Cornell lecture notes, Theorems 4.8, 4.14.)
6. J. C. Lagarias, *The 3x+1 problem and its generalizations*, American Mathematical Monthly 92 (1985), 3-23. (Direct-verified PDF pp. 14-15.)
7. D. Applegate and J. C. Lagarias, *Density bounds for the 3x+1 problem I, II*, Mathematics of Computation 64 (1995), 411-426 and 427-438. *[verify abstract]*
8. G. Rhin, *Approximants de Padé et mesures effectives d'irrationalité*, Progress in Mathematics 71 (1987), 155-164.
9. E. M. Matveev, *An explicit lower bound for a homogeneous rational linear form in logarithms of algebraic numbers. II*, Izv. Math. 64 (2000), 1217-1269. *[verify]*
10. J. L. Simons and B. M. M. de Weger, *Theoretical and computational bounds for m-cycles of the 3n+1 problem*, Acta Arithmetica 117 (2005), 51-70. *[verify abstract]*
11. S. Eliahou, *The 3x+1 problem: new lower bounds on nontrivial cycle lengths*, Discrete Mathematics 118 (1993), 45-56. *[verify abstract]*
12. J. C. Lagarias, editor, *The Ultimate Challenge: The 3x+1 Problem*, AMS, 2010.
13. C. Hercher and M. Puchert, *Parity vectors of the 3x+1 problem*, 2018. *[verify]*
14. T. Tao, *Almost all orbits of the Collatz map attain almost bounded values*, Forum of Mathematics, Pi 10 (2022), e12, arXiv:1909.03562 (2019). *[verify abstract]*
15. D. Barina, *Convergence verification of the Collatz problem*, J. Supercomp. 81 (2025), *[DOI to fill]*.
16. C. Hercher, *There are no cycles with less than 92 odd elements*, J. Integer Seq. 26 (2023), Article 23.6.5. (Direct-verified via ar5iv.)
17. S. Knight, *No high cycles in the 3x+1 problem*, Discrete Mathematics 349 (2026), no. 3, 114357. *[access blocked — see mailbox 0065 §6.5 formulation]*

## Preprints (not peer-reviewed, cited with disclosure)

18. R. Santana, *Towards the Collatz conjecture* (title placeholder), arXiv:2601.03297v4 (2026). (Direct-verified ar5iv; rigour gap documented §6.)
19. M. Honarvar, *On Collatz cycles* (title placeholder), arXiv:2601.04289 (2026). *[verify — if cited]*
20. O. Rozier and C. Terracol, *Paradoxical behavior in Collatz sequences*, arXiv:2502.00948 (2026), to appear *Discrete Math.* 349, 115167. (Direct-verified; Theorem 1.1 and Proposition 6.3 used.)
21. V. Dhiman and A. Pandey, (title placeholder), arXiv:2601.12772 (2026). (Abstract direct-verified.)

## Online and informal sources (cited with disclosure as non-peer-reviewed)

22. T. Tao, *The Collatz conjecture, Littlewood-Offord theory, and powers of 2 and 3*, blog post on `terrytao.wordpress.com`, 25 August 2011. (Direct-verified WebFetch 2026-04-25. Cited in §5.3 footnote ‡ as origin of the « transcendence theory or exponential separation between powers of 2 and 3 » phrase initially misattributed to Rozier-Terracol 2026; verification chain Phase IX 0021 → Phase XI 0059 §1.4 → Worker 2026-04-25.)

## Software and data

23. The Mathlib Community, *The Lean Mathematical Library*, v4.27.0 (2026). https://leanprover-community.github.io/mathlib4/
24. E. Merle, *collatz-nocycle-lean4*, repository accompanying this paper (commit : to be filled at submission time).

## Notes

- Every `*[verify]*` entry must be WebFetch/abstract-confirmed before final submission (policy mailbox 0065 §6).
- Knight 2025 retained with the `[INDIRECT]` handling policy from mailbox 0065 §6.5.
- Entries 1, 5, 6, 16, 18, 20, 21 are Session-C direct-verified and can be cited without Worker re-verification.
- Entry 22 (Tao 2011 blog post) is Worker-verified directly via WebFetch on 2026-04-25 ; it is cited only in §5.3 footnote ‡ as the origin of the « transcendence theory or exponential separation » phrase. The phrase was initially misattributed to Rozier-Terracol 2026 in mathnotes 0018 §D.5.3 ; the correction chain runs Phase IX 0021 (NOT in Rozier) → Phase XI 0059 §1.4 (verbatim in Tao 2011) → Worker 2026-04-25 (independent re-verification). The §5.3 closing sentence retains neutral, unattributed wording per `from_mathlib_prover/0021 §3.1` (a blog comment is not a citable basis for a meta-mathematical claim ; the citation is a *disclosure* of provenance, not a load-bearing reference).
- §11 cycle status (Commit #13 in progress) :
  - **Resolved this cycle** : Tao 2011 attribution amendment (item 3 of the EXPANDED 7-item forward-flagged list).
  - **Pending** : items 1 (Yoneda 1985 cite-key), 2 (Barina year inconsistency §6.1 vs §4.2), 6 partial (Rhin 1987 already in `references.bib` ; Kloosterman 1926 / Weil 1948 / Vinogradov 1937 deferred to §9 polish phase per items 4-5-7 deferred).
  - **Deferred to §9 polish phase (Commit #14+)** : items 4, 5, 7 (§9.X infrastructure additions per Phase XI 0060/0061 — Theorem 0060.1, Conjecture 0060.2, Phase XII research-program framing).
  - **Awaiting RT#2 explicit** per `to_worker/0096 §10.6` (publication-grade scope decision warrants 4-eyes review).

## BibTeX build

```bash
make references.bib   # regenerates from 11-references.md if authored cross-consistently
```

