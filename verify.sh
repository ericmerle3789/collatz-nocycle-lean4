#!/bin/bash
# Verification script for Collatz NoCycle formal proof
# Usage: ./verify.sh

set -e

echo "=== Collatz NoCycle Verification ==="
echo "Date: $(date)"
echo "Lean version: $(lean --version 2>/dev/null || echo 'not installed')"
echo ""

# Build
echo "Building..."
lake build ProjetCollatz 2>&1 | tail -5
EXIT=${PIPESTATUS[0]}
echo "Build exit code: $EXIT"
echo ""

# Axiom check
AXIOMS=$(grep -rn '^axiom' ProjetCollatz/*.lean 2>/dev/null | wc -l | tr -d ' ')
echo "Axioms: $AXIOMS"

# Sorry check (as tactic, not in comments)
SORRY=$(grep -rn '  sorry$\|:= sorry\|by sorry' ProjetCollatz/*.lean 2>/dev/null | wc -l | tr -d ' ')
echo "Sorry (as tactic): $SORRY"

# Theorem count (strict: only declarations, not comments)
THEOREMS=$(grep -rcE '^(private |protected )?(theorem|lemma) ' ProjetCollatz/*.lean 2>/dev/null | awk -F: '{s+=$2} END {print s}')
echo "Theorems + Lemmas: $THEOREMS"

# File count
FILES=$(ls ProjetCollatz/*.lean 2>/dev/null | wc -l | tr -d ' ')
echo "Lean files: $FILES"

# Main theorem check
MAIN=$(grep -c 'theorem no_nontrivial_cycle_phase59' ProjetCollatz/Phase59ContinuedFractions.lean 2>/dev/null)
echo "Main theorem present: $([ "$MAIN" -gt 0 ] && echo YES || echo NO)"
echo ""

# Verdict
if [ "$EXIT" -eq 0 ] && [ "$AXIOMS" -eq 0 ] && [ "$SORRY" -eq 0 ] && [ "$MAIN" -gt 0 ]; then
  echo "VERIFICATION PASSED"
else
  echo "VERIFICATION FAILED"
  [ "$EXIT" -ne 0 ] && echo "  - Build failed"
  [ "$AXIOMS" -ne 0 ] && echo "  - Found $AXIOMS axioms"
  [ "$SORRY" -ne 0 ] && echo "  - Found $SORRY sorry"
  [ "$MAIN" -eq 0 ] && echo "  - Main theorem not found"
fi
