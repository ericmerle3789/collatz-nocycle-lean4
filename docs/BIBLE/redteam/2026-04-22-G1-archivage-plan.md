# Red Team — G1 Archival Plan

**Date** : 2026-04-22
**Target** : `docs/BIBLE/decisions/G1-archival-plan.md` + `docs/BIBLE/decisions/G1-archive-readme-drafts.md`
**Agent** : general-purpose subagent, hostile-reviewer mode
**Prompt** : cf. §5.1 MISSION_NASA, 15 cibles d'attaque (external citation, broken links, git log, co-authors, Zenodo/arXiv, meta-repo, lineage, timing, archive side-effects, dilution, language strength, self-consistency, reviewer attacks)

---

## Findings (copie brute)

### HIGH severity (must fix before execution)

- **External citation verification incomplete** (plan.md:40-47) — plan claims "Aucun DOI Zenodo pointant vers le repo (vérifié 2026-04-22)" but does not document the check methodology. DOIs are only one vector; the plan did NOT verify: Google Scholar citations of the repo URL, arXiv preprints citing the raw GitHub URL, ResearchGate/HAL/OSF/Semantic Scholar mentions, Zulip/Lean Community forum threads linking to the repos, Twitter/Mastodon announcements with URLs, or personal webpage backlinks. A single archived citation breaks a live reference trail. Document the exact search queries run.

- **Git log co-author verification missing** (plan.md:40-47) — plan does not verify Git history for external contributors. `git log --format='%ae' | sort -u` on both repos was never documented. If anyone other than `ericmerle3789` ever authored a commit (even a typo fix via web UI), they should be informed per open-science norms. Add explicit `git shortlog -sne` output as a precondition artifact.

- **No preservation of Junction Theorem lineage in nocycle-lean4** (plan.md:30-34, draft.md:16-20) — archival severs the conceptual trail. If nocycle-lean4 README does not explicitly acknowledge the Junction Theorem as predecessor and explain WHY the pivot occurred, a paper reviewer sees an archived conditional proof and a new "unconditional" claim with no narrative bridge. Add a `docs/LINEAGE.md` or README §History in nocycle-lean4 BEFORE archiving, not after.

- **Draft 2 language is too soft on the known-error module** (draft.md:40) — "Use this repo only for research reference; do not build on the erroneous module" understates the risk. A researcher skimming the archived repo might copy lemmas from `range-exclusion/` without reading `AUDIT_CORRSUM.md`. The banner must state WHICH files are erroneous, name the specific formula, and instruct readers NOT to cite any theorem from that module. Current phrasing is liability-adjacent.

- **Attack surface for paper reviewers** (Q15) — the plan does NOT preempt the attack: "author archived conditional-on-GRH Junction because they couldn't finish it, then claims unconditional in nocycle-lean4 which itself uses `DerivedLargeKBound`." The note mentions "3 fundamental Lean axioms only" (draft.md:18) but `DerivedLargeKBound` is a Lean definition, not an axiom — a reviewer conflating the two will mis-attack. Add a plain-English statement in the archive note clarifying the logical status of each artifact.

### MEDIUM severity (should address)

- **"Aucun issue ouvert" verification is a point-in-time claim** (plan.md:44) — between sign-off and exec (potentially 48h+), an issue could be opened. Add pre-execution re-check as final step of §2.1.

- **GitHub Pages / webhooks / collaborators not enumerated** (Q11) — plan.md:156 says "destruction not in plan" but does not enumerate archive side-effects: `gh repo view --json hasIssuesEnabled,hasProjectsEnabled,hasWikiEnabled,url` should be captured BEFORE archival to confirm no GitHub Pages site, no active webhooks, no external collaborators losing write access. Archive locks these silently.

- **Option B for collatz-audit-2026 contradicts METAPROMPT §2 dilution warning** (Q12, draft.md:72-73, 78) — "maintenance documentaire ponctuelle possible" literally means maintaining a non-archived public repo alongside the official one. If METAPROMPT §2 warns against attention dilution, recommending Option B undermines the whole consolidation rationale. Either bite the bullet (Option A) or commit in writing to "no further commits, period" on audit-2026 — current phrasing is the worst of both worlds.

- **Plan cites METAPROMPT §3 S1 but doesn't quote it** (plan.md:36, 40) — "explicites METAPROMPT §3 S1" is unverifiable by the reviewer (me) without access. Attach the quoted excerpt as appendix.

- **Draft 1 and Draft 2 redirect issues to active repo issues, but issues on active repo were 0** (plan.md:16, draft.md:22, 44) — routing archived-repo users to open issues on `collatz-nocycle-lean4/issues` is fine only if that channel is actually monitored. Confirm issue notifications are on.

- **48h decantation is arbitrary** (plan.md:4, 181) — there is no stated reason why 48h specifically. If waiting for a specific Triade/reviewer audit cycle, say so; if purely cooling-off, state that. Unmotivated numbers raise eyebrows.

### LOW severity (optional improvements)

- **Commit message is weak** (plan.md:93) — `"docs: archive notice — consolidated into collatz-nocycle-lean4"` omits the commit-date-of-last-real-work reference. Better: append `Last substantive commit: <HEAD_PRE>. No further changes expected.`

- **No screenshot/diff artifact for the README modification** (plan.md:89) — `head -20 README.md` is visual-only; capture `git diff HEAD~1 README.md` as signed artifact.

- **`Collatz-Junction-N2-Merge/` backup confirmation** (plan.md:180) — open question #2 should be PRE-resolved, not left for sign-off. An accidental push of local preprint drafts would be worse than the archival itself.

### Questions the plan doesn't answer

- Has Eric searched his own Gmail/Notion/Drive for old emails/messages referencing these repo URLs (co-authors, reviewers, peers) that should be notified?
- Does the Lean code inside `collatz-nocycle-lean4` contain any import path, comment, or bibliography entry pointing to the to-be-archived repos? `grep -r "Collatz-Junction-Theorem\|collatz-cycles-lean" /Users/ericmerle/Documents/collatz-nocycle-lean4-work/` was not documented.
- Are GitHub stars/forks actually zero across ALL audit dates, or only today? A fork existing at ANY point creates an orphan downstream.
- Does the archival note in Draft 1 break the repo's own internal links (relative links to `docs/`, images, etc.)? Inserting content at the top can shift anchor offsets.
- Is there a `CITATION.cff` file in either repo? The plan never checks. If present, it must be updated to point to nocycle-lean4 BEFORE archival locks it.
- Does `collatz-audit-2026`'s README have a last-updated timestamp? Option B requires a dated "state-of-the-art as of March 2026" banner for honesty.

### Defense suggestions (how to preempt paper-reviewer attacks)

- **Add a public `CHANGELOG.md` to nocycle-lean4** documenting: "2026-04-XX: Junction Theorem approach (conditional on GRH + Conjecture 7.4) archived; this repo supersedes with continued-fractions approach under 3 fundamental Lean axioms only. Rationale: [2-3 sentences]." Reviewers then see the pivot as deliberate scientific progress, not abandonment.
- **Publish a Zenodo DOI for nocycle-lean4 BEFORE archival** so the archived repos can point to a stable citation target, not a mutable GitHub URL.
- **Explicit axiom statement in both archive notes**: quote `#print axioms` output verbatim in the note. This is the strongest defense against the "different flavor of conditional" attack.
- **Preserve the Junction Theorem preprint PDF as a release asset** on the archived repo (before archiving) so the artifact is frozen even if GitHub changes policy.
- **Add a signed commit** (GPG or Sigstore) for the archive notice, so provenance of the archival decision is cryptographically verifiable — useful if the paper is ever contested.
- **Document in JOURNAL.md** the exact search queries + results used to claim "no external citations," so the audit trail is reviewable.

---

## Actions prises suite au Red Team (à compléter au fil de l'intégration)

[Voir `G1-archival-plan-v2.md` — version révisée intégrant les HIGH findings]

**Sign-off Eric sur arbitrages** : [EN ATTENTE]
