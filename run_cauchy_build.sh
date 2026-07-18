#!/bin/zsh
lake build RHFormalization.HPPCauchyUpgrade 2>&1 | tee cup_a.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" cup_a.log; then
  echo "FAILED -> removing (errors below)"
  grep -B2 -A16 "error" cup_a.log | head -110
  rm RHFormalization/HPPCauchyUpgrade.lean
  exit 1
fi
if ! grep -q "remainder_uniform_limit' depends on axioms: \[propext, Classical.choice, Quot.sound\]" cup_a.log; then
  echo "AXIOM CHECK FAILED -> removing"; rm RHFormalization/HPPCauchyUpgrade.lean; exit 1
fi
grep -qxF "import RHFormalization.HPPCauchyUpgrade" RHFormalization.lean || printf '\nimport RHFormalization.HPPCauchyUpgrade\n' >> RHFormalization.lean
lake build 2>&1 | tee cup_root.log | tail -3
grep -q "Build completed successfully" cup_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_CAUCHY.tar.gz . && echo "SNAPSHOT SAVED: CAUCHY"
