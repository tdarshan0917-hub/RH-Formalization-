#!/bin/zsh
pkill -f "lake build" 2>/dev/null; pkill -f "leanprover.*bin/lean" 2>/dev/null; sleep 2
echo "===== resume root build (cached modules skip instantly) ====="
lake build 2>&1 | tail -10 | tee finish_root.log
echo "===== verdict ====="
grep -n -e "error" -e "RH_current_frontier" -e "normalFormCodiscreteIdentity" -e "depends on axioms" -e "Build completed" finish_root.log
if grep -q "Build completed successfully" finish_root.log; then
  tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_ONFI_REPAIRED.tar.gz .
  echo "SNAPSHOT SAVED"
fi
