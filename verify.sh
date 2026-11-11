#!/usr/bin/env bash
set -euo pipefail
lake exe cache get
lake build
cat > AxiomCheck.lean << 'LEAN'
import RHFormalization
#print axioms RHFormalization.RH_from_pairedTransform_only_dense
#print axioms RHFormalization.RH_of_denseQV_uniform
#print axioms RHFormalization.RH_semantic_lock
#print axioms RHFormalization.RH_from_pairedTransform_only_dense_mathlib
#print axioms RHFormalization.RH_from_vmDiscrepancy_polylog
#print axioms RHFormalization.RH_from_vmDiscrepancy_power
#print axioms RHFormalization.quasiRH_from_holomorphic_remainder
#print axioms RHFormalization.quasiRH_from_vmDiscrepancy_halfplane
#print axioms RHFormalization.primeGraph_trace_formula
#print axioms RHFormalization.primeGraph_levels_real
#print axioms RHFormalization.secularDet_hasDerivAt
#print axioms RHFormalization.primeGraph_logDeriv_eq_orbit_sum
#print axioms RHFormalization.primeGraph_composite_orbit_limit
#print axioms RHFormalization.graphEuler_tendsto_logDeriv_zeta
#print axioms RHFormalization.graph_logDeriv_tendsto_zeta
LEAN
EXPECTED=15
out=$(lake env lean AxiomCheck.lean 2>&1) || { echo "$out"; echo "FAIL: AxiomCheck did not compile"; exit 1; }
echo "$out"
n=$(echo "$out" | grep -cE "depends on axioms|does not depend on any axioms" || true)
bad=$(echo "$out" | grep "depends on axioms" | sed -E 's/.*\[(.*)\].*/\1/' | tr ',' '\n' \
      | sed 's/ //g' | grep -vxE 'propext|Classical\.choice|Quot\.sound' || true)
if [ "$n" -ne "$EXPECTED" ]; then echo "FAIL: expected $EXPECTED axiom reports, got $n"; exit 1; fi
if [ -n "$bad" ]; then echo "FAIL: unexpected axioms: $bad"; exit 1; fi
echo "PASS: $EXPECTED endpoints, only [propext, Classical.choice, Quot.sound]"
