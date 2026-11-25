#!/usr/bin/env bash
set -euo pipefail
lake exe cache get
lake build
cat > AxiomCheck.lean << 'LEAN'
import RHFormalization.StageAUnconditional
#print axioms RHFormalization.RH_from_pairedTransform_only_dense
#print axioms RHFormalization.RH_semantic_lock
#print axioms RHFormalization.RH_from_pairedTransform_only_dense_mathlib
#print axioms RHFormalization.hPdense_of_vonKoch
#print axioms RHFormalization.HPdense_iff_RH
#print axioms RHFormalization.HPdense_iff_RH_unconditional
#print axioms RHFormalization.HPdense_iff_RH_mathlib
LEAN
EXPECTED=7
out=$(lake env lean AxiomCheck.lean 2>&1) || { echo "$out"; echo "FAIL: AxiomCheck did not compile"; exit 1; }
echo "$out"
n=$(echo "$out" | grep -cE "depends on axioms|does not depend on any axioms" || true)
bad=$(echo "$out" | grep "depends on axioms" | sed -E 's/.*\[(.*)\].*/\1/' | tr ',' '\n' \
      | sed 's/ //g' | grep -vxE 'propext|Classical\.choice|Quot\.sound' || true)
if [ "$n" -ne "$EXPECTED" ]; then echo "FAIL: expected $EXPECTED axiom reports, got $n"; exit 1; fi
if [ -n "$bad" ]; then echo "FAIL: unexpected axioms: $bad"; exit 1; fi
echo "PASS: $EXPECTED endpoints, only [propext, Classical.choice, Quot.sound]"
