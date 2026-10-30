#!/usr/bin/env bash
set -e
lake exe cache get
lake build
printf 'import RHFormalization.DenseSealB8\nimport RHFormalization.RHSemanticLock\nimport RHFormalization.PolylogEndpoint\nimport RHFormalization.PowerEndpoint\nimport RHFormalization.QuasiRHFlatTerminus\n#print axioms RHFormalization.RH_from_pairedTransform_only_dense\n#print axioms RHFormalization.RH_of_denseQV_uniform\n#print axioms RHFormalization.RH_semantic_lock\n#print axioms RHFormalization.RH_from_pairedTransform_only_dense_mathlib\n#print axioms RHFormalization.RH_from_vmDiscrepancy_polylog\n#print axioms RHFormalization.RH_from_vmDiscrepancy_power\n#print axioms RHFormalization.quasiRH_from_holomorphic_remainder\n' > AxiomCheck.lean
echo '=== Endpoint axiom check ==='
lake env lean AxiomCheck.lean
echo '=== Expected: [propext, Classical.choice, Quot.sound] on all seven ==='
