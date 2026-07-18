#!/bin/zsh
lake build RHFormalization.MeromorphyAssembly 2>&1 | tee mas_a.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" mas_a.log; then
  echo "FAILED -> removing (errors below)"
  grep -B2 -A16 "error" mas_a.log | head -110
  rm RHFormalization/MeromorphyAssembly.lean
  exit 1
fi
for thm in fullPartial_differentiableOn zpole_analyticAt_nonpole offCritical_of_polePoint_mem_Omega meromorphicOn_from_convergence; do
  if ! grep -q "$thm' depends on axioms: \[propext, Classical.choice, Quot.sound\]" mas_a.log; then
    echo "AXIOM CHECK FAILED ($thm) -> removing"; rm RHFormalization/MeromorphyAssembly.lean; exit 1
  fi
done
grep -qxF "import RHFormalization.MeromorphyAssembly" RHFormalization.lean || printf '\nimport RHFormalization.MeromorphyAssembly\n' >> RHFormalization.lean
lake build 2>&1 | tee mas_root.log | tail -3
grep -q "Build completed successfully" mas_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_MERO_GOAL.tar.gz . && echo "SNAPSHOT SAVED: MERO_GOAL"
