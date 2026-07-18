#!/bin/zsh
# Builds the file ALREADY on disk. Does not regenerate it.
lake build RHFormalization.ConvergenceInfrastructure 2>&1 | tee c1_a.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" c1_a.log; then
  echo "FAILED -> file kept for inspection (errors below)"
  grep -B2 -A16 "error" c1_a.log | head -120
  exit 1
fi
for thm in compact_uniform_pole_distance subtypeStage_tendsto subtypeStage_sum_eq; do
  if ! grep -q "$thm' depends on axioms: \[propext, Classical.choice, Quot.sound\]" c1_a.log; then
    echo "AXIOM CHECK FAILED ($thm)"; exit 1
  fi
done
grep -qxF "import RHFormalization.ConvergenceInfrastructure" RHFormalization.lean || printf '\nimport RHFormalization.ConvergenceInfrastructure\n' >> RHFormalization.lean
lake build 2>&1 | tee c1_root.log | tail -3
grep -q "Build completed successfully" c1_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_CONV_C1.tar.gz . && echo "SNAPSHOT SAVED: CONV_C1"
