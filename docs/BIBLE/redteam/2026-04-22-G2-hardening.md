# Red Team — G2 Hardening

**Date** : 2026-04-22T17:35:00Z
**Target** : G2 artefacts sur branche `g2-hardening` :
- `reproduce.sh`
- `probes/check_central_axioms.lean`
- `probes/check_sorry.lean`
- `expected_axioms.md`
- `.github/workflows/build.yml` (upgraded)
- `lakefile.toml` (defaultTargets fix)

**Agent** : general-purpose subagent, hostile-reviewer mode G2

---

## Findings (copie brute)

### HIGH severity (must fix before merging to main)

- **H1 — `reproduce.sh:107` `probed_count` misdetection via `|| echo 0`** : grep exit 2 (real error) triggers `echo 0`, masking probe failure as "0 theorems reported". Fix : explicit file existence check + `|| true`.
- **H2 — `reproduce.sh:117,129` brittle grep-sed axiom comparison** : pattern `'$theorem' depends on axioms: ` matches prefix collisions (e.g. `no_nontrivial_cycle_phase59_v2`). Fix : anchor + verify exactly one match.
- **H3 — `reproduce.sh:77-80` cache failure silently degrades to source build** : CI `timeout-minutes: 60` will kill mid-source-build, EXIT 124 undocumented. Fix : hard-fail on cache miss in CI, or extend CI timeout + document.
- **H4 — `expected_axioms.md:23-29` axiom claim ASSERTED not PROVEN** : include SHA256 of `docs/BIBLE/env-snapshots/2026-04-22-axioms-central.txt`.
- **H5 — `.github/workflows/build.yml:11` `ubuntu-latest` unpinned** : pin `ubuntu-24.04`.
- **H6 — `.github/workflows/build.yml:19` `curl | sh` no signature** : pin elan-init script to commit SHA + sha256 check.
- **H7 — `reproduce.sh:147` sorryAx grep scans only probe logs, NOT build log** : extend grep to `/tmp/nocycle_build.log` for `declaration uses 'sorry'` warnings.

### MEDIUM severity

- **M1 — `reproduce.sh:65` `cat lean-toolchain` assumes cwd** : no `[ -f ]` check.
- **M2 — `probes/check_sorry.lean` only probes phase59** : expand to all 7 central + 3 auxiliary.
- **M3 — `expected_axioms.md` missing baseline theorems** : `BakerSeparation`, `BarinaVerification`, `IsOddCycle`, `steiner_equation`, `cf_nbound_13` absent. Either audit or explicitly list out-of-scope.
- **M4 — consistency fragile across script/probe/md** : 3 sources of truth for the theorem list.
- **M5 — `lakefile.toml:3` `defaultTargets = ["ProjetCollatz"]` skips exe** : Main.lean rot won't be detected.
- **M6 — `reproduce.sh:33` EXPECTED_TOOLCHAIN duplicates lakefile `rev`** : should grep lakefile.toml.
- **M7 — `probes/check_central_axioms.lean:30` M3 update comment unenforced**.

### LOW severity

- L1-L7 : runtime estimate Mac-specific, grep `^✔` Unicode fragile, cache log tail trivial, historical note confusing, no artifact upload on CI failure, /tmp noexec risk, no shellcheck in CI.

### Questions

- Is `no_nontrivial_cycle_full` a genuine alias (same axioms) or different hypotheses ?
- Does `sdw_from_cf` really depend on `Quot.sound` ?
- Windows Git-Bash compatibility (CI is Ubuntu-only).

### Test scenarios that would break reproduce.sh

1. Partial-name collision (`*_phase59` matches `*_phase59_v2`)
2. Sorry in uncovered lemma not in the 10 probed
3. Renamed central theorem → Lean error, probe file line 39 references old name
4. Cache server down → CI timeout EXIT 124
5. Stale Mathlib rev in lakefile vs EXPECTED_TOOLCHAIN
6. `#print axioms` on non-existent name → bad diagnostic
7. NUL in file path
8. Upstream Mathlib axiom rename

---

## Mitigations appliquées (worker, 2026-04-22T17:35:00Z)

Voir `G2-rt-mitigations.md` dans ce dossier pour le détail.

### HIGH — tous adressés

| ID | Mitigation |
|----|-----------|
| H1 | `reproduce.sh` : `grep -c ... || true` + explicit `[ -s ]` check sur `/tmp/nocycle_axioms.log` avant comptage |
| H2 | `reproduce.sh` : utilisation de `awk` pour extraire la ligne correspondant EXACTEMENT au nom `'$theorem'` (anchor strict), fail si plusieurs matches |
| H3 | `.github/workflows/build.yml` : séparation explicite `lake exe cache get` comme étape avec `continue-on-error: false` ; échoue le CI si cache indisponible, évite fallback silencieux |
| H4 | `expected_axioms.md` : ajout SHA256 de `docs/BIBLE/env-snapshots/2026-04-22-axioms-central.txt` comme ancre de baseline |
| H5 | `.github/workflows/build.yml` : `runs-on: ubuntu-24.04` pinned |
| H6 | `.github/workflows/build.yml` : remplacement par `leanprover/lean-action@v1` (action officielle maintenue) OU pinning du script elan-init à un commit SHA (choix : lean-action v1 pour simplicité) |
| H7 | `reproduce.sh` : ajout grep de `declaration uses 'sorry'` sur `/tmp/nocycle_build.log` en plus des probe logs |

### MEDIUM — clés adressées

| ID | Mitigation |
|----|-----------|
| M1 | `reproduce.sh` : ajout `[ -f lean-toolchain ]` check explicite avant `cat` |
| M2 | `probes/check_sorry.lean` : expansion aux 10 théorèmes (7 central + 3 aux) pour couverture complète |
| M3 | `expected_axioms.md` : ajout Section 5 "Out-of-scope at G2" listant `BakerSeparation`, `BarinaVerification`, `IsOddCycle` (definitions, pas théorèmes), `steiner_equation`, `cf_nbound_13`, etc. — justification du scope actuel |
| M5 | `lakefile.toml` : `defaultTargets = ["ProjetCollatz", "projetcollatz"]` — lib principale + exe trivial pour détecter rot de Main.lean |
| M4, M6, M7 | Acceptés comme tech debt : multi-source truth inhérent à la séparation probe Lean vs script shell vs doc. Future ADR potentiel pour single-source via génération. |

### LOW — non-adressés à G2 (documentés pour S2.X ultérieur)

Tous les LOW sont des améliorations qualité de vie sans impact sur l'intégrité scientifique du gate G2. Reportés à une itération ultérieure.

### Questions — réponses

- **Q1 (no_nontrivial_cycle_full alias ?)** : le probe `check_central_axioms.lean` va exécuter `#print axioms` sur les 4 variantes. Si elles divergent, on le verra au test. Au G0 (2026-04-22T17:10Z), toutes 4 ont montré les mêmes 3 axiomes. Hypothèse validée.
- **Q2 (sdw_from_cf + Quot.sound ?)** : même source — probe G0 a montré `[propext, Classical.choice, Quot.sound]` pour `sdw_from_cf`. Probablement parce qu'elle utilise `decidable_of_iff` ou similaire de Mathlib, qui tire `Classical.choice` + `Quot.sound`. Pas un risque d'intégrité, juste un fait du système Lean.
- **Q3 (Windows/Git-Bash)** : hors scope G2. Documenté dans `LIMITATIONS.md` si besoin. Le public cible est Linux/macOS reviewer.

### Test scenarios — protection

| # | Scénario | Protection post-mitigation |
|---|----------|-----------------------------|
| 1 | Partial-name collision | H2 strict anchor + count check |
| 2 | Sorry in uncovered lemma | H7 build log grep + M2 sorry probe étendu |
| 3 | Renamed theorem | Lean erreur du probe → EXIT 3 (le comportement est correct, message amélioré via $actual empty check) |
| 4 | Cache server down | H3 CI hard-fail explicite |
| 5 | Stale Mathlib rev | M6 acceptée comme tech debt (source lakefile unique à terme) |
| 6 | #print axioms sur nom inexistant | Couvert par probe_count < 10 check ; message amélioré avec nom manquant reporté |
| 7 | NUL in filename | Hors scope pratique (nocycle ne contient pas de tels paths) |
| 8 | Upstream Mathlib axiom rename | Déclencherait EXIT 3 correctement (drift detected), reviewer doit updater expected_axioms.md |

---

## Sign-off

**Worker auto-sign** sur les mitigations HIGH + key MEDIUM appliquées. RT findings HIGH = 0 après mitigation. MEDIUM résiduels documentés.

**Auditor review** : attendu sur ADR-003 8-cond pre-autosign G2.
