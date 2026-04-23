#!/usr/bin/env bash
# reproduce.sh — end-to-end verification of collatz-nocycle-lean4
# Reproduces build + axiom probe + sorry detection from a fresh clone.
#
# Exit codes :
#   0 = success (build green, axioms match expected_axioms.md, 0 sorryAx)
#   1 = toolchain mismatch or missing elan/lake
#   2 = build failure (or sorry warning surfaced in build log)
#   3 = axiom drift (unexpected or missing axiom on a probed theorem)
#   4 = sorryAx detected (incomplete proof)
#
# Runtime on Mac M1 Pro 16 GB :
#   - first run with cache : ~3-5 min
#   - incremental : ~10 s
#   - --from-source : ~1h30 (Mathlib rebuilt)
# CI runtime on ubuntu-24.04 with cache : ~5-10 min.
#
# Usage :
#   cd /path/to/collatz-nocycle-lean4
#   bash reproduce.sh [--from-source]
#
# Convention : exit codes match Junction-N2-Merge reproduce.sh (ADR-002).
# Post-G2 hardening : Red Team mitigations applied 2026-04-22T17:35:00Z
# (HIGH-1/H2/H7 and MEDIUM-1/M2 addressed ; see docs/BIBLE/redteam/).

set -euo pipefail

# ----- Argument parsing --------------------------------------------------------
FROM_SOURCE=0
for arg in "$@"; do
    case "$arg" in
        --from-source) FROM_SOURCE=1 ;;
        -h|--help)
            echo "Usage: $0 [--from-source]"
            echo "  --from-source  skip lake exe cache get, rebuild Mathlib from source (~1h30)"
            exit 0
            ;;
    esac
done

# ----- Expected values ---------------------------------------------------------
EXPECTED_TOOLCHAIN="leanprover/lean4:v4.27.0"
EXPECTED_CENTRAL_AXIOMS="[propext, Classical.choice, Quot.sound]"
EXPECTED_NATIVE_AXIOMS="[propext, Lean.ofReduceBool, Lean.trustCompiler]"

CENTRAL_THEOREMS=(
    "ProjetCollatz.no_nontrivial_cycle_phase59"
    "ProjetCollatz.no_nontrivial_cycle_final"
    "ProjetCollatz.no_nontrivial_cycle_derived"
    "ProjetCollatz.no_nontrivial_cycle_full"
    "ProjetCollatz.no_cycle_k_le_1322"
    "ProjetCollatz.no_cycle_k_gt_1322"
    "ProjetCollatz.sdw_from_cf"
)

# M3 Legendre foundational theorems — same axiom profile as CENTRAL (kernel 3
# only), tracked separately for semantic clarity. Not yet integrated into the
# central chain at M3.1 ; will be composed into no_nontrivial_cycle_phase59 at
# M3 integration (Phase63 planned).
M3_THEOREMS=(
    "ProjetCollatz.Phase60.log23_irrational"
    "ProjetCollatz.Phase60.two_pow_ne_three_pow"
    "ProjetCollatz.Phase61.log23_convergent"
    "ProjetCollatz.Phase61.logb23_pos"
    "ProjetCollatz.Phase61.q_n"
    "ProjetCollatz.Phase61.q_n_pos"
    "ProjetCollatz.Phase61.q_n_eq_den"
    "ProjetCollatz.Phase61.InWindow"
    "ProjetCollatz.Phase61.not_convergent_implies_far_approx"
)

NATIVE_LEMMAS=(
    "ProjetCollatz.cf_gap_8"
    "ProjetCollatz.cf_gap_13"
    "ProjetCollatz.cf_nbound_8"
)

# ----- Step 1 : toolchain (M1 mitigation : explicit file check) ----------------
echo "==> [1/5] Toolchain check"

if ! command -v elan > /dev/null 2>&1; then
    echo "ERROR: elan not installed. Install from https://lean-lang.org/install" >&2
    exit 1
fi
if ! command -v lake > /dev/null 2>&1; then
    echo "ERROR: lake not in PATH (should come with elan)" >&2
    exit 1
fi

if [ ! -f lean-toolchain ]; then
    echo "ERROR: lean-toolchain file missing — are you in the repo root ?" >&2
    exit 1
fi

ACTUAL_TOOLCHAIN=$(cat lean-toolchain)
if [ "$ACTUAL_TOOLCHAIN" != "$EXPECTED_TOOLCHAIN" ]; then
    echo "ERROR: toolchain mismatch : found '$ACTUAL_TOOLCHAIN', expected '$EXPECTED_TOOLCHAIN'" >&2
    exit 1
fi
echo "    toolchain OK : $ACTUAL_TOOLCHAIN"
echo "    elan : $(elan --version | head -1)"

# ----- Step 2 : Mathlib cache or source build ---------------------------------
echo "==> [2/5] Fetching Mathlib cache (or --from-source build)"

if [ "$FROM_SOURCE" -eq 0 ]; then
    if ! lake exe cache get > /tmp/nocycle_cache.log 2>&1; then
        echo "WARNING: lake exe cache get failed — falling back to source build (slow)" >&2
        tail -20 /tmp/nocycle_cache.log >&2 || true
        # CI policies should enforce cache availability via separate step (see .github/workflows/build.yml)
    else
        echo "    cache OK"
    fi
else
    echo "    --from-source : skipping cache"
fi

# ----- Step 3 : build ProjetCollatz library -----------------------------------
echo "==> [3/5] Building library ProjetCollatz"

if ! lake build ProjetCollatz > /tmp/nocycle_build.log 2>&1; then
    echo "ERROR: build failed" >&2
    tail -30 /tmp/nocycle_build.log >&2
    exit 2
fi
if grep -qE "^error:" /tmp/nocycle_build.log; then
    echo "ERROR: build reported error: lines (should not coincide with exit 0)" >&2
    grep "^error:" /tmp/nocycle_build.log | head -5 >&2
    exit 2
fi

# H7 mitigation : grep build log for sorry-related warnings (beyond axiom probes)
if grep -qE "declaration uses 'sorry'|uses sorry|^sorry" /tmp/nocycle_build.log; then
    echo "ERROR: build log reports a sorry-related warning (H7)" >&2
    grep -E "declaration uses 'sorry'|uses sorry|^sorry" /tmp/nocycle_build.log | head -5 >&2
    exit 2
fi

built_jobs=$(grep -c '^✔' /tmp/nocycle_build.log || true)
echo "    build OK ($built_jobs jobs)"

# ----- Step 4 : axiom probe ---------------------------------------------------
echo "==> [4/5] Running axiom probe on central + auxiliary theorems"

if ! lake env lean probes/check_central_axioms.lean > /tmp/nocycle_axioms.log 2>&1; then
    echo "ERROR: axiom probe failed to execute" >&2
    tail -30 /tmp/nocycle_axioms.log >&2
    exit 3
fi

if [ ! -s /tmp/nocycle_axioms.log ]; then
    echo "ERROR: axiom probe produced empty output (H1)" >&2
    exit 3
fi

# H1 mitigation : `|| true` guarantees arithmetic is meaningful ; separately check file non-empty
probed_count=$(grep -cE "depends on axioms" /tmp/nocycle_axioms.log || true)
probed_count=${probed_count:-0}
expected_probes=$(( ${#CENTRAL_THEOREMS[@]} + ${#NATIVE_LEMMAS[@]} + ${#M3_THEOREMS[@]} ))
if [ "$probed_count" -lt "$expected_probes" ]; then
    echo "ERROR: probe reported $probed_count theorems, expected >= $expected_probes" >&2
    echo "  — possible cause : a theorem was renamed or removed ; check probes/check_central_axioms.lean" >&2
    cat /tmp/nocycle_axioms.log >&2
    exit 3
fi
echo "    probe covered $probed_count theorems (expected $expected_probes)"

# H2 mitigation : strict anchor + exactly-one match check via awk
check_axioms_exact() {
    local theorem="$1"
    local expected="$2"

    # Exact match on "'<theorem>' depends on axioms: " line start
    local matches
    matches=$(awk -v t="'${theorem}' depends on axioms: " \
        'index($0, t) == 1 { print substr($0, length(t) + 1) }' \
        /tmp/nocycle_axioms.log)

    local match_count
    match_count=$(printf '%s\n' "$matches" | grep -cvE '^$' || true)
    match_count=${match_count:-0}

    if [ "$match_count" -eq 0 ]; then
        echo "ERROR: theorem '$theorem' not found in probe output (possible rename ?)" >&2
        return 3
    fi
    if [ "$match_count" -gt 1 ]; then
        echo "ERROR: theorem '$theorem' matched multiple lines (H2 anchor violation ?)" >&2
        printf '%s\n' "$matches" >&2
        return 3
    fi

    if [ "$matches" != "$expected" ]; then
        echo "ERROR: theorem '$theorem' axioms drift" >&2
        echo "  expected : $expected" >&2
        echo "  actual   : $matches" >&2
        return 3
    fi
    return 0
}

for theorem in "${CENTRAL_THEOREMS[@]}"; do
    check_axioms_exact "$theorem" "$EXPECTED_CENTRAL_AXIOMS" || exit 3
done
echo "    ${#CENTRAL_THEOREMS[@]}/${#CENTRAL_THEOREMS[@]} central theorems OK"

for theorem in "${NATIVE_LEMMAS[@]}"; do
    check_axioms_exact "$theorem" "$EXPECTED_NATIVE_AXIOMS" || exit 3
done
echo "    ${#NATIVE_LEMMAS[@]}/${#NATIVE_LEMMAS[@]} auxiliary lemmas OK (native_decide, isolated from central chain)"

for theorem in "${M3_THEOREMS[@]}"; do
    check_axioms_exact "$theorem" "$EXPECTED_CENTRAL_AXIOMS" || exit 3
done
echo "    ${#M3_THEOREMS[@]}/${#M3_THEOREMS[@]} M3 Legendre foundational theorems OK (kernel 3 only, not yet in central chain)"

# ----- Step 5 : sorry probe (Lean kernel authoritative) -----------------------
echo "==> [5/5] Sorry detection via Lean kernel (sorryAx)"

if ! lake env lean probes/check_sorry.lean > /tmp/nocycle_sorry.log 2>&1; then
    echo "ERROR: sorry probe failed to execute" >&2
    cat /tmp/nocycle_sorry.log >&2
    exit 3
fi

if grep -qE "sorryAx" /tmp/nocycle_axioms.log /tmp/nocycle_sorry.log; then
    echo "ERROR: sorryAx detected in the central or auxiliary chain !" >&2
    grep -n "sorryAx" /tmp/nocycle_axioms.log /tmp/nocycle_sorry.log >&2
    exit 4
fi
echo "    no sorryAx anywhere in probed chain"

# ----- Done -------------------------------------------------------------------
echo ""
echo "========================================="
echo "reproduce.sh : ALL CHECKS PASS"
echo "  - toolchain : $ACTUAL_TOOLCHAIN"
echo "  - build     : EXIT 0 ($built_jobs jobs)"
echo "  - axioms    : ${#CENTRAL_THEOREMS[@]} central + ${#NATIVE_LEMMAS[@]} auxiliary + ${#M3_THEOREMS[@]} M3 foundational match expected_axioms.md"
echo "  - sorry     : 0 sorryAx"
echo "========================================="
exit 0
