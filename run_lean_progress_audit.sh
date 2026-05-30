#!/usr/bin/env bash
set +e

STAMP=$(date +"%Y%m%d_%H%M%S")
REPORT="lean_progress_audit_${STAMP}.txt"

cat > LeanProgressReport.lean <<'LEANEOF'
import RHFormalization.FinalConditionalSpine

set_option pp.all true
set_option pp.universes true

namespace RHFormalization

-- A. Print the exact top-level RH spine signature.
#check @finalConditionalRHSpine

-- B. Print axiom dependencies of the final conditional spine.
#print axioms finalConditionalRHSpine

-- C. Intentionally ask Lean: what is still missing if we try to prove RH now?
-- The unsolved goals here are the top-level remaining inputs.
example : RiemannHypothesis :=
  finalConditionalRHSpine ?ZF ?Y ?X ?E ?ONFP

end RHFormalization
LEANEOF

{
echo "===== LEAN 4 PROGRESS AUDIT ====="
echo "Date: $(date)"
echo "Directory: $(pwd)"
echo ""

echo "===== 1. GIT SNAPSHOT ====="
git rev-parse --short HEAD 2>/dev/null || echo "No git commit detected"
git status --short 2>/dev/null || echo "No git status available"
echo ""

echo "===== 2. FULL LAKE BUILD ====="
lake build
echo "LAKE_BUILD_EXIT_CODE=$?"
echo ""

echo "===== 3. FINAL SPINE SIGNATURE / AXIOMS / REMAINING GOALS ====="
lake env lean LeanProgressReport.lean
echo "LEAN_PROGRESS_REPORT_EXIT_CODE=$?"
echo ""

echo "===== 4. FILE COUNT ====="
find RHFormalization -name '*.lean' | wc -l
echo ""

echo "===== 5. SORRY / ADMIT / SORRYAX SCAN ====="
grep -RIn --include='*.lean' -E '\bsorry\b|\badmit\b|sorryAx' RHFormalization || echo "No sorry/admit/sorryAx found"
echo ""

echo "===== 6. EXPLICIT AXIOM / CONSTANT / OPAQUE SCAN ====="
grep -RIn --include='*.lean' -E '^[[:space:]]*(axiom|constant|opaque)[[:space:]]' RHFormalization || echo "No explicit axiom/constant/opaque declarations found"
echo ""

echo "===== 7. TRUE-PLACEHOLDER SCAN ====="
grep -RIn --include='*.lean' -E '→[[:space:]]*True\b|=>[[:space:]]*True\b|:[[:space:]]*True\b' RHFormalization || echo "No obvious True placeholders found"
echo ""

echo "===== 8. DEFAULT CONSTRUCTOR SCAN ====="
grep -RIn --include='*.lean' -E '^[[:space:]]*(noncomputable[[:space:]]+)?def[[:space:]]+default' RHFormalization || echo "No default constructors found"
echo ""

echo "===== 9. FINAL SPINE SOURCE SNIPPET ====="
grep -n -A 40 -B 5 'finalConditionalRHSpine' RHFormalization/FinalConditionalSpine.lean || echo "Could not find finalConditionalRHSpine source"
echo ""

echo "===== 10. MAIN THEOREM / RH KEYWORD SCAN ====="
grep -RIn --include='*.lean' -E 'RiemannHypothesis|final.*RH|Final.*RH|RHSpine|finalConditionalRHSpine' RHFormalization || echo "No RH-spine keywords found"
echo ""

echo "===== END LEAN 4 PROGRESS AUDIT ====="
} 2>&1 | tee "$REPORT"

echo ""
echo "Saved report to: $REPORT"
