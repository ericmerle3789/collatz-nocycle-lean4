# DECISIONS — ADR registry for collatz-nocycle-lean4

Index of Architectural Decision Records. Each ADR is append-only after "accepted" status. Changes = new ADR that supersedes.

---

## Accepted

| ID | Title | Date | Status | Location |
|----|-------|------|--------|----------|
| ADR-001 | Délégation de supervision opérationnelle à la session auditor | 2026-04-22 | accepted (Eric GO ADR-001) | **External** : `/Users/ericmerle/Documents/Collatz-Session-Handoff-2026-04-22/ADR-001-delegation.md`. Not committed to repo (meta-process decision). |
| ADR-002 | Junction-N2-Merge backup policy | 2026-04-22 | accepted (autosigned by auditor per Eric delegation ADR-001) | `docs/BIBLE/decisions/ADR-002-junction-backup-policy.md` |

## Proposed / draft

_(none yet)_

## Deprecated / superseded

_(none yet)_

---

## Rules

1. ADR numbering is monotonically increasing. Never reuse a number.
2. "Accepted" ADRs are append-only. To change, write a new ADR "supersedes ADR-NNN".
3. Each ADR must reference an Eric sign-off event (direct confirmation or via ADR-001 delegation path).
4. External ADRs (like ADR-001, which governs the delegation protocol itself) are listed here with their location but not committed, to avoid circular dependencies between process and repo state.
