#!/bin/zsh
mv RHFormalization/OmegaCodiscreteIdentityFromNormalForms.lean.parked RHFormalization/OmegaCodiscreteIdentityFromNormalForms.lean
grep -qxF "import RHFormalization.OmegaCodiscreteIdentityFromNormalForms" RHFormalization.lean || printf '\nimport RHFormalization.OmegaCodiscreteIdentityFromNormalForms\n' >> RHFormalization.lean
python3 - <<'PY'
p='RHFormalization/OmegaCodiscreteIdentityFromNormalForms.lean'
s=open(p).read()
s=s.replace("mainTheorem_from_default_connectedOmega_meromorphicAlgebra_codiscreteIdentity_preperfect",
            "mainTheorem_from_default_connectedOmega_meromorphicAlgebra_omegaPuncturedIdentity")
s=s.replace("(buildOmegaCodiscreteIdentityFromNormalForms ONFI)",
            "(buildOmegaPuncturedIdentityFromCodiscrete (buildOmegaCodiscreteIdentityFromNormalForms ONFI) defaultOmegaPreperfectAPI)")
open(p,'w').write(s)
print("PATCHED")
PY
echo "===== build repaired module ====="
lake build RHFormalization.OmegaCodiscreteIdentityFromNormalForms 2>&1 | tail -6 | tee repair_a.log
if grep -q "error" repair_a.log; then
  echo "REPAIR FAILED -> PARK BOTH, RESTORE GREEN ROOT"
  mv RHFormalization/OmegaCodiscreteIdentityFromNormalForms.lean RHFormalization/OmegaCodiscreteIdentityFromNormalForms.lean.parked
  mv RHFormalization/OmegaNormalFormPropagationEndpoint.lean RHFormalization/OmegaNormalFormPropagationEndpoint.lean.parked 2>/dev/null
  grep -v -e "OmegaCodiscreteIdentityFromNormalForms" -e "OmegaNormalFormPropagationEndpoint" RHFormalization.lean > /tmp/r.lean && mv /tmp/r.lean RHFormalization.lean
fi
echo "===== root build ====="
lake build 2>&1 | tail -8 | tee repair_root.log
grep -n -e "error" -e "RH_current_frontier" -e "normalFormCodiscreteIdentity" -e "depends on axioms" -e "Build completed" repair_root.log
if grep -q "Build completed successfully" repair_root.log; then
  tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_ONFI_REPAIRED.tar.gz .
  echo "SNAPSHOT SAVED"
fi
