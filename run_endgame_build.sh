#!/bin/zsh
lake build RHFormalization.HPPEndgame 2>&1 | tee end_a.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" end_a.log; then
  echo "FAILED -> removing (errors below)"
  grep -B2 -A16 "error" end_a.log | head -110
  rm RHFormalization/HPPEndgame.lean
  exit 1
fi
if ! grep -q "h_pp_from_convergence' depends on axioms: \[propext, Classical.choice, Quot.sound\]" end_a.log; then
  echo "AXIOM CHECK FAILED -> removing"; rm RHFormalization/HPPEndgame.lean; exit 1
fi
grep -qxF "import RHFormalization.HPPEndgame" RHFormalization.lean || printf '\nimport RHFormalization.HPPEndgame\n' >> RHFormalization.lean
lake build 2>&1 | tee end_root.log | tail -3
grep -q "Build completed successfully" end_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_ENDGAME.tar.gz . && echo "SNAPSHOT SAVED: ENDGAME"
