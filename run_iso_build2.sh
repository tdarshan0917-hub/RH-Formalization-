#!/bin/zsh
lake build RHFormalization.PairPoleIsolation 2>&1 | tee iso_a.log | grep -e "error" -e "Build completed"
if grep -q "error" iso_a.log; then
  echo "FAILED -> removing (errors below)"
  grep -B2 -A12 "error" iso_a.log | head -90
  rm RHFormalization/PairPoleIsolation.lean
  exit 1
fi
echo "===== axiom check ====="
cat >> RHFormalization/PairPoleIsolation.lean <<'EOF2'

namespace RHFormalization
#print axioms pairPole_isolated
end RHFormalization
EOF2
lake build RHFormalization.PairPoleIsolation 2>&1 | tee iso_b.log | grep -e "error" -e "pairPole_isolated"
if grep -q "error" iso_b.log; then
  echo "AXIOM PASS BUILD FAILED -> removing"; rm RHFormalization/PairPoleIsolation.lean; exit 1
fi
if ! grep -q "pairPole_isolated' depends on axioms: \[propext, Classical.choice, Quot.sound\]" iso_b.log; then
  echo "AXIOM CHECK FAILED -> removing"; rm RHFormalization/PairPoleIsolation.lean; exit 1
fi
grep -qxF "import RHFormalization.PairPoleIsolation" RHFormalization.lean || printf '\nimport RHFormalization.PairPoleIsolation\n' >> RHFormalization.lean
lake build 2>&1 | tee iso_root.log | tail -3
grep -q "Build completed successfully" iso_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_ISOLATION.tar.gz . && echo "SNAPSHOT SAVED: ISOLATION"
