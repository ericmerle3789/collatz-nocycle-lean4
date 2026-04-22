# G1 — Plan d'archivage GitHub (pour sign-off Eric)

**Date** : 2026-04-22
**Classification** : **P1** (action publique GitHub, partiellement réversible via `gh repo unarchive`)
**Autorité** : Eric Merle — sign-off écrit requis avant exécution + 48h décantation
**Statut** : DRAFT — pas d'exécution avant "GO G1 execute" explicite

---

## 0. Inventaire complet (2026-04-22)

7 repos sur le compte `ericmerle3789` :

| # | Nom | Description courte | Last push | Archived ? | Stars | Issues | PRs |
|---|-----|-------------------|-----------|-----------|-------|--------|-----|
| 1 | `collatz-nocycle-lean4` | No nontrivial cycle (Lean 4, 3 axiomes) | 2026-04-19 | ❌ | 0 | 0 | 0 |
| 2 | `MATHEVO` | OMEGA IA tabula rasa depuis Peano | 2026-04-09 | ❌ | 0 | 0 | 0 |
| 3 | `collatz-audit-2026` | Audit meta (pointe vers 1+4+5) | 2026-03-31 | ❌ | 0 | ? | ? |
| 4 | `PROMETHEUS` | AI Mathematician Collatz | 2026-03-29 | ❌ | 0 | 0 | 0 |
| 5 | `Collatz-Junction-Theorem` | Junction Theorem (GRH conditional) | 2026-03-27 | ❌ | 0 | 0 | 0 |
| 6 | `collatz-cycles-lean` | Companion code + range-exclusion bug | 2026-03-26 | ❌ | 0 | 0 | 0 |
| 7 | `Projet_Collatz` | NEXUS Collatz (legacy) | 2026-02-24 | ✅ déjà | 0 | — | — |

Inventaire complet : `docs/BIBLE/env-snapshots/2026-04-22-github-repos-inventory.json`

---

## 1. Décisions par repo

### 1.1 GARDER OFFICIEL (1 repo)

| Repo | Raison |
|------|--------|
| `collatz-nocycle-lean4` | Repo cible de consolidation. Aucun changement GitHub-side. |

### 1.2 À ARCHIVER (2 repos, explicites METAPROMPT §3 S1)

| Repo | Raison | Cross-références | DOI Zenodo |
|------|--------|-------------------|------------|
| `Collatz-Junction-Theorem` | Approche Junction superseded par nocycle-lean4 (cf. METAPROMPT §3 S1). Preprint complet 280 théorèmes Lean 4.15, conditionnel GRH + Conjecture 7.4. | Cité dans `collatz-audit-2026` uniquement | Aucun (aucune citation externe à briser) |
| `collatz-cycles-lean` | Companion code contenant bug documenté `range-exclusion/` (cf. `docs/AUDIT_CORRSUM.md` du repo). | Cité dans `collatz-audit-2026` uniquement | Aucun |

**Préconditions archivage** :
- Aucun issue ouvert (vérifié 2026-04-22)
- Aucun PR ouvert (vérifié 2026-04-22)
- Aucun DOI Zenodo pointant vers le repo (vérifié 2026-04-22)
- Backup local `Collatz-Junction-N2-Merge/` existe et contient preprint v5 (788 lignes), templates, probes (vérifié 2026-04-22)

### 1.3 DÉCISION REQUISE ERIC (1 repo)

| Repo | 3 options (voir `G1-archive-readme-drafts.md` §Draft 3) |
|------|--------------------------------------------------------|
| `collatz-audit-2026` | A. Archiver (consolidation max) / **B. Update README sans archiver** (recommandation Claude) / C. Transformer en preprint annexe (hors scope G1) |

### 1.4 HORS-SCOPE G1 (3 repos, ne PAS toucher)

| Repo | Raison |
|------|--------|
| `PROMETHEUS` | Projet actif distinct (AI Mathematician approche IA). Non mentionné dans METAPROMPT §3 S1. |
| `MATHEVO` | Projet IA math distinct, hors scope Collatz. |
| `Projet_Collatz` | Déjà archivé 2026-04-01. Aucune action. |

---

## 2. Procédure exacte d'exécution (APRÈS sign-off G1)

### 2.1 Pré-exécution (commune aux 2 repos à archiver)

Pour CHAQUE repo dans `{Collatz-Junction-Theorem, collatz-cycles-lean}` :

```bash
REPO="Collatz-Junction-Theorem"  # ou "collatz-cycles-lean"

# Créer un tmpdir de travail (ne pas polluer le work tree)
WORK=$(mktemp -d)
cd "$WORK"

# Clone propre
git clone "https://github.com/ericmerle3789/$REPO" .
git log -1 --oneline  # noter le HEAD pour traçabilité
git rev-parse HEAD > /Users/ericmerle/Documents/collatz-nocycle-lean4-work/docs/BIBLE/signoffs/G1-pre-archive-$REPO-HEAD.txt

# Insérer la note d'archivage au début du README
# (note = contenu de docs/BIBLE/decisions/G1-archive-readme-drafts.md §Draft correspondant)
# Méthode : éditer README.md en ajoutant les lignes de note AU DÉBUT, avant toute autre ligne
# (pas de replace_all, pas de substitution — strictement append en tête)

# Vérification visuelle de l'édition
head -20 README.md

# Commit + push (sur main — classification P1)
git add README.md
git commit -m "docs: archive notice — consolidated into collatz-nocycle-lean4"
git push origin main

# Snapshot post-commit du hash
git rev-parse HEAD > /Users/ericmerle/Documents/collatz-nocycle-lean4-work/docs/BIBLE/signoffs/G1-post-readme-$REPO-HEAD.txt

# Archive proprement dit
gh repo archive ericmerle3789/$REPO --yes

# Vérification
gh repo view ericmerle3789/$REPO --json isArchived | jq
# Attendu : { "isArchived": true }

# Cleanup tmpdir
cd /Users/ericmerle/Documents/collatz-nocycle-lean4-work
rm -rf "$WORK"
```

### 2.2 Vérifications post-archivage (obligatoires)

```bash
# Pour chaque repo archivé
for REPO in Collatz-Junction-Theorem collatz-cycles-lean; do
  STATUS=$(gh repo view ericmerle3789/$REPO --json isArchived --jq '.isArchived')
  echo "$REPO : archived=$STATUS"
done
# Attendu : les deux "archived=true"

# Sanity : collatz-nocycle-lean4 non affecté
gh repo view ericmerle3789/collatz-nocycle-lean4 --json isArchived
# Attendu : { "isArchived": false }
```

### 2.3 Journal

Entrée `docs/BIBLE/JOURNAL.md` append-only :

```markdown
## 2026-04-XX — G1 Execution [P1] Archivage Junction + cycles-lean

**Sign-off Eric** : "GO G1 execute" reçu YYYY-MM-DD HH:MM (+ 48h décantation respectée)
**Repos archivés** : Collatz-Junction-Theorem (HEAD pre/post: voir signoffs/G1-*), collatz-cycles-lean (idem)
**Note README ajoutée** : drafts G1-archive-readme-drafts.md §Draft 1 et §Draft 2
**Vérification post** : 2/2 archived=true, nocycle-lean4 non affecté
**Révocable** : oui via `gh repo unarchive`
```

---

## 3. Réversibilité

Toute action est réversible via :

```bash
# Un-archiver
gh repo unarchive ericmerle3789/$REPO

# Révoquer la note d'archivage
cd $WORK_CLONE
git revert <commit-hash-de-la-note>
git push origin main
```

**La destruction (`gh repo delete`) n'est PAS dans le plan. Interdit P0.**

---

## 4. Interdits stricts jusqu'à "GO G1 execute" écrit

- ❌ `gh repo archive` sur tout repo
- ❌ Commit/push des notes d'archivage (drafts restent locaux dans `docs/BIBLE/decisions/G1-archive-readme-drafts.md`)
- ❌ `gh repo delete` **jamais**, même après sign-off (P0)
- ❌ Annonce publique de la consolidation (Twitter, Slack, email) avant archivage effectif
- ❌ Modifier les repos hors-scope (PROMETHEUS, MATHEVO, Projet_Collatz déjà archivé)

## 5. Autorisés sans attendre

- ✅ Inventaire lecture seule (`gh repo list`, `gh api`, `gh repo view`)
- ✅ Red Team sur ce plan (agent hostile-reviewer)
- ✅ Rédaction de drafts README d'archivage (local)
- ✅ Mise à jour de JOURNAL, RISK_REGISTER, LIMITATIONS

---

## 6. Questions ouvertes pour Eric avant sign-off

1. **`collatz-audit-2026`** : Option A (archiver), B (update README sans archiver — recommandation Claude), ou C (hors-scope G1) ?
2. **Confirmation** : `Collatz-Junction-N2-Merge/` local (backup) ne doit jamais être poussé sur GitHub. Mémoire vérifiée côté Claude, demande confirmation Eric.
3. **Date cible d'exécution** : après Red Team sign-off + 48h décantation. Proposition : si sign-off reçu 2026-04-23, exécution au plus tôt 2026-04-25.

---

**Ce plan est à transmettre au Red Team (§5 manuel NASA) avant soumission à Eric.**
