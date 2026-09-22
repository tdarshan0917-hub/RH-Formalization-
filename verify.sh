#!/usr/bin/env bash
set -e
lake exe cache get
lake build
printf 'import RHFormalization.DenseSealB8\nimport RHFormalization.RHSemanticLock\n#print axioms RHFormalization.RH_from_pairedTransform_only_dense\n#print axioms RHFormalization.RH_of_denseQV_uniform\n#print axioms RHFormalization.RH_semantic_lock\n#print axioms RHFormalization.RH_from_pairedTransform_only_dense_mathlib\n' > AxiomCheck.lean
echo '=== Endpoint axiom check ==='
lake env lean AxiomCheck.lean
echo '=== Expected: [propext, Classical.choice, Quot.sound] on all four ==='
