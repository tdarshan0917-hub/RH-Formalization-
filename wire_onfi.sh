#!/bin/zsh
echo "===== 1. ground truth: current endpoint ====="
cat RHFormalization/CurrentFrontierEndpoint.lean
cp RHFormalization/CurrentFrontierEndpoint.lean /tmp/cfe.bak
echo "===== 2. patch: OCI input -> ONFI input ====="
python3 - <<'PY'
p='RHFormalization/CurrentFrontierEndpoint.lean'
s=open(p).read()
if "import RHFormalization.OmegaCodiscreteIdentityFromNormalForms" not in s:
    s=s.replace("import RHFormalization.DefaultOmegaPreperfect",
                "import RHFormalization.DefaultOmegaPreperfect\nimport RHFormalization.OmegaCodiscreteIdentityFromNormalForms",1)
s=s.replace("(OCI : OmegaCodiscreteMeromorphicIdentityAPI)",
            "(ONFI : OmegaNormalFormCodiscreteIdentityAPI)")
s=s.replace("OCI defaultOmegaPreperfectAPI",
            "(buildOmegaCodiscreteIdentityFromNormalForms ONFI) defaultOmegaPreperfectAPI")
open(p,'w').write(s)
print("PATCHED")
PY
echo "===== 3. build endpoint module (live) ====="
lake build RHFormalization.CurrentFrontierEndpoint 2>&1 | tee wire_a.log
if grep -q "error" wire_a.log; then
  echo "PATCH FAILED -> restoring known-good endpoint"
  cp /tmp/cfe.bak RHFormalization/CurrentFrontierEndpoint.lean
  lake build RHFormalization.CurrentFrontierEndpoint 2>&1 | tail -4
else
  echo "===== 4. warm root replay ====="
  lake build 2>&1 | tail -6 | tee wire_root.log
  grep -q "Build completed successfully" wire_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_FRONTIER_ONFI.tar.gz . && echo "SNAPSHOT SAVED: FRONTIER_ONFI"
fi
