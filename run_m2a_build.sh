#!/bin/zsh
lake build RHFormalization.MeromorphyAwayFromPoles 2>&1 | tee m2a_a.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" m2a_a.log; then
  echo "FAILED -> removing (errors below)"
  grep -B2 -A16 "error" m2a_a.log | head -110
  rm RHFormalization/MeromorphyAwayFromPoles.lean
  exit 1
fi
if ! grep -q "nonpole_isolated' depends on axioms: \[propext, Classical.choice, Quot.sound\]" m2a_a.log; then
  echo "AXIOM CHECK FAILED -> removing"; rm RHFormalization/MeromorphyAwayFromPoles.lean; exit 1
fi
grep -qxF "import RHFormalization.MeromorphyAwayFromPoles" RHFormalization.lean || printf '\nimport RHFormalization.MeromorphyAwayFromPoles\n' >> RHFormalization.lean
lake build 2>&1 | tee m2a_root.log | tail -3
grep -q "Build completed successfully" m2a_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_MERO_M2A.tar.gz . && echo "SNAPSHOT SAVED: MERO_M2A"
