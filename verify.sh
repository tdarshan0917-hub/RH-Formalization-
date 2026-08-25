#!/usr/bin/env bash
set -e
lake exe cache get
lake build
printf 'import RHFormalization.DenseSealEndpoint\n#print axioms RHFormalization.RH_from_pairedTransform_only_dense\n' > AxiomCheck.lean
echo '=== Endpoint axiom check ==='
lake env lean AxiomCheck.lean
echo '=== Expected: [propext, Classical.choice, Quot.sound] ==='
