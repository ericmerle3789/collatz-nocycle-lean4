# G1 — Drafts de notes d'archivage pour READMEs externes

**Statut** : DRAFT LOCAL, non commité, destiné à être publié sur les repos à archiver APRÈS sign-off Eric G1.

**Procédure** : pour chaque repo à archiver, ces notes sont à insérer **en entête du README existant** (sans supprimer le contenu original), puis commit/push, puis `gh repo archive`.

---

## Draft 1 — `ericmerle3789/Collatz-Junction-Theorem`

Note à insérer au tout début du `README.md` actuel (avant le titre existant) :

```markdown
> **⚠️ This repository has been archived on 2026-04-XX.**
>
> The active formalization effort is consolidated at **[collatz-nocycle-lean4](https://github.com/ericmerle3789/collatz-nocycle-lean4)**, which is now the official project repo for the "no nontrivial Collatz cycle" formalization.
>
> The two approaches are complementary but distinct:
> - **collatz-nocycle-lean4** (active) uses continued fractions of log₂3 (Baker 1966 + Barina 2025 + CF derivation) under the 3 fundamental Lean axioms only (`propext`, `Classical.choice`, `Quot.sound`). Target: unconditional publication-grade formalization after Phase Legendre.
> - **This repo (Junction Theorem, archived)** uses entropic barriers + blocking mechanism (conditional on GRH + Conjecture 7.4). It is preserved for historical reference and citation continuity.
>
> No further maintenance is planned in this repo. Issues or questions → open them at the [active repo](https://github.com/ericmerle3789/collatz-nocycle-lean4/issues).
>
> — Eric Merle, 2026-04-XX

---
```

---

## Draft 2 — `ericmerle3789/collatz-cycles-lean`

Note à insérer au tout début du `README.md` actuel :

```markdown
> **⚠️ This repository has been archived on 2026-04-XX.**
>
> The active formalization effort is consolidated at **[collatz-nocycle-lean4](https://github.com/ericmerle3789/collatz-nocycle-lean4)**, the official project repo for the "no nontrivial Collatz cycle" formalization.
>
> **Important for readers** : this archived repo documents a known formula error in `lean/range-exclusion/` (see `docs/AUDIT_CORRSUM.md` for the full analysis). The correct proofs are preserved in `lean/verified/` (k = 3..15, 280 theorems, 0 sorry, 0 axiom) and `lean/skeleton/` (Junction Theorem approach, conditional). Use this repo only for research reference; do not build on the erroneous module.
>
> The `collatz-nocycle-lean4` repo supersedes this one with a cleaner approach, a single consolidated Lean tree (36 files, 393 theorems, 0 sorry), and stricter probe protocols (`#print axioms` verification, 3 fundamental axioms only).
>
> No further maintenance is planned here. Issues or questions → open them at the [active repo](https://github.com/ericmerle3789/collatz-nocycle-lean4/issues).
>
> — Eric Merle, 2026-04-XX

---
```

---

## Draft 3 (optionnel — à décider par Eric) — `ericmerle3789/collatz-audit-2026`

Ce repo est meta : il pointe vers les 3 autres (Junction, cycles-lean, nocycle-lean4). Après archivage des 2 premiers, il devient partiellement obsolète.

**Trois options à soumettre à Eric** :

### Option A — Archiver aussi (cohérent avec consolidation stricte)
```markdown
> **⚠️ This repository has been archived on 2026-04-XX.**
>
> This was a meta-audit repo cross-referencing three Collatz research repos (March 2026). After consolidation, the active project is at **[collatz-nocycle-lean4](https://github.com/ericmerle3789/collatz-nocycle-lean4)**.
>
> Audit artifacts remain here for historical reference. Two of the three audited repos (`Collatz-Junction-Theorem`, `collatz-cycles-lean`) have been archived as part of the consolidation.
>
> — Eric Merle, 2026-04-XX

---
```

### Option B — Mettre à jour sans archiver (garder comme "state of the art" Mars 2026)
Modifier le README pour indiquer explicitement que Junction et cycles-lean sont archivés, que nocycle-lean4 est l'actif, et que ce repo reste une référence historique de l'état en Mars 2026. Pas d'archivage, maintenance documentaire ponctuelle possible.

### Option C — Transformer en preprint annexe ou déplacer vers site web
Le contenu `audit/SYNTHESE_MARS2026.md` est potentiellement du matériel qui aurait sa place ailleurs (preprint complémentaire, blog, site web académique personnel). À envisager hors-scope G1.

**Recommandation Claude** : **Option B** (mise à jour sans archivage). Le repo a une valeur documentaire distincte (audit Mars 2026), le fermer supprime du contexte utile. Mais Option A aussi défendable si Eric veut la consolidation maximale.

**Décision requise Eric** avant exécution.

---

## Repos HORS-SCOPE G1 (ne PAS toucher)

| Repo | Justification |
|------|---------------|
| `ericmerle3789/PROMETHEUS` | Projet actif distinct (Spectral Framework AI Mathematician, approche IA, pas formalisation Lean officielle). Non mentionné METAPROMPT §3 S1. |
| `ericmerle3789/MATHEVO` | Projet OMEGA IA math tabula rasa depuis Peano. Hors scope Collatz proof. |
| `ericmerle3789/Projet_Collatz` | **Déjà archivé** (2026-04-01, `isArchived: true`). Pas d'action requise. |
