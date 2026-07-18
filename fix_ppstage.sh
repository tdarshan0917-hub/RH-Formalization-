#!/bin/zsh
python3 - <<'PY'
# regenerate with the two fixes by patching the failed draft inline
src = open('install_ppstage.sh').read()
i = src.find("cat > RHFormalization/PrimePowerDFiniteStage.lean <<'EOF'")
j = src.find("EOF", i)
body = src[src.find("\n", i)+1:j]
body = body.replace("open Complex", "open Complex\nopen scoped Classical", 1)
body = body.replace("""  exact Filter.tendsto_atTop_add_const_right _ 1
    Filter.tendsto_natCast_atTop_atTop""",
"""  refine Filter.tendsto_atTop_add_const_right _ 1 ?_
  first
    | exact tendsto_natCast_atTop_atTop
    | exact tendsto_nat_cast_atTop_atTop
    | exact Nat.tendsto_cast_atTop_atTop""")
open('RHFormalization/PrimePowerDFiniteStage.lean','w').write(body)
print("file regenerated with fixes")
PY
lake build RHFormalization.PrimePowerDFiniteStage 2>&1 | tee pps_b.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" pps_b.log; then
  echo "FAILED -> removing (errors below)"
  grep -B2 -A10 "error" pps_b.log | head -60
  rm RHFormalization/PrimePowerDFiniteStage.lean
  exit 1
fi
grep -qxF "import RHFormalization.PrimePowerDFiniteStage" RHFormalization.lean || printf '\nimport RHFormalization.PrimePowerDFiniteStage\n' >> RHFormalization.lean
lake build 2>&1 | tee pps_root.log | tail -3
grep -q "Build completed successfully" pps_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_PP_STAGE.tar.gz . && echo "SNAPSHOT SAVED: PP_STAGE"
