---
section: "11"
owner: worker
status: skeleton
last_updated: 2026-04-24
---

# 11. References

*[WIP — Day 3 draft. Also maintained in `references.bib` for pandoc BibTeX build.]*

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

## Software and data

22. The Mathlib Community, *The Lean Mathematical Library*, v4.27.0 (2026). https://leanprover-community.github.io/mathlib4/
23. E. Merle, *collatz-nocycle-lean4*, repository accompanying this paper (commit : to be filled at submission time).

## Notes

- Every `*[verify]*` entry must be WebFetch/abstract-confirmed before final submission (policy mailbox 0065 §6).
- Knight 2025 retained with the `[INDIRECT]` handling policy from mailbox 0065 §6.5.
- Entries 1-5 and 16, 18, 20, 21 are Session-C direct-verified and can be cited without Worker re-verification.

## BibTeX build

```bash
make references.bib   # regenerates from 11-references.md if authored cross-consistently
```

## RT#1 checklist

- [ ] 14+ peer-reviewed entries (count satisfied : 17 above).
- [ ] No `*[verify]*` flags in final submission version.
- [ ] Every citation in §1-§10 appears here.
- [ ] DOIs filled where available.
