#!/bin/zsh
echo "===== 1. what is the orphan file ====="
sed -n '1,40p' RHFormalization/OmegaCodiscreteIdentityFromNormalForms.lean
echo "..."
sed -n '80,95p' RHFormalization/OmegaCodiscreteIdentityFromNormalForms.lean
echo "===== 2. who references it ====="
grep -rn "OmegaCodiscreteIdentityFromNormalForms" RHFormalization.lean RHFormalization/ --include='*.lean' | grep -v "OmegaCodiscreteIdentityFromNormalForms.lean:"
echo "===== 3. neutralize: park file, drop import ====="
mv RHFormalization/OmegaCodiscreteIdentityFromNormalForms.lean RHFormalization/OmegaCodiscreteIdentityFromNormalForms.lean.parked
grep -v "OmegaCodiscreteIdentityFromNormalForms" RHFormalization.lean > /tmp/root.lean && mv /tmp/root.lean RHFormalization.lean
echo "===== 4. root build ====="
lake build 2>&1 | tail -8 | tee cleanup_build.log
grep -n -e "error" -e "RH_current_frontier" -e "depends on axioms" -e "Build completed" cleanup_build.log
echo "===== 5. snapshot if clean ====="
if grep -q "Build completed successfully" cleanup_build.log; then
  tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_OPP_BANKED_FRONTIER_OCI.tar.gz .
  echo "SNAPSHOT SAVED"
fi
