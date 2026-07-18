#!/bin/zsh
python3 - <<'PY'
import sys

def extract(scriptpath, marker):
    src = open(scriptpath).read()
    i = src.find(marker)
    if i < 0: print(f"MARKER MISSING in {scriptpath}"); sys.exit(1)
    start = src.find("\n", i) + 1
    j = src.find("\nEOF\n", start)
    if j < 0: print(f"TERMINATOR MISSING in {scriptpath}"); sys.exit(1)
    return src[start:j+1]

# 1. regenerate the prime-power stage with the two fixes
body = extract('install_ppstage.sh', "cat > RHFormalization/PrimePowerDFiniteStage.lean <<'EOF'")
body = body.replace("open Complex", "open Complex\nopen scoped Classical", 1)
body = body.replace("""  exact Filter.tendsto_atTop_add_const_right _ 1
    Filter.tendsto_natCast_atTop_atTop""",
"""  refine Filter.tendsto_atTop_add_const_right _ 1 ?_
  first
    | exact tendsto_natCast_atTop_atTop
    | exact tendsto_nat_cast_atTop_atTop
    | exact Nat.tendsto_cast_atTop_atTop""")
if "def primePowerStage" not in body: print("PPSTAGE BODY BAD"); sys.exit(1)
open('RHFormalization/PrimePowerDFiniteStage.lean','w').write(body)
print(f"ppstage regenerated: {len(body)} chars")

# 2. regenerate DesignedRCutoffS verbatim
body2 = extract('install_S.sh', "cat > RHFormalization/DesignedRCutoffS.lean <<'EOF'")
if "def designedRCutoffS" not in body2: print("S BODY BAD"); sys.exit(1)
open('RHFormalization/DesignedRCutoffS.lean','w').write(body2)
print(f"designedRCutoffS regenerated: {len(body2)} chars")
PY
if [ $? -ne 0 ]; then echo "EXTRACTION FAILED -> cleaning"; rm -f RHFormalization/DesignedRCutoffS.lean; exit 1; fi
echo "===== build stage ladder (must show primePowerStage axioms) ====="
lake build RHFormalization.PrimePowerDFiniteStage 2>&1 | tee pps_c.log | grep -e "error" -e "primePowerStage" -e "Build completed"
if grep -q "error" pps_c.log; then
  echo "STAGE FAILED (errors below)"; grep -B2 -A10 "error" pps_c.log | head -50
  rm -f RHFormalization/DesignedRCutoffS.lean; exit 1
fi
if ! grep -q "primePowerStage" pps_c.log; then echo "STAGE EMPTY AGAIN -> abort"; rm -f RHFormalization/DesignedRCutoffS.lean; exit 1; fi
echo "===== build S instance ====="
lake build RHFormalization.DesignedRCutoffS 2>&1 | tee drs_b.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" drs_b.log; then
  echo "S FAILED (errors below)"; grep -B2 -A12 "error" drs_b.log | head -70
  rm RHFormalization/DesignedRCutoffS.lean
  lake build 2>&1 | tail -2; exit 1
fi
grep -qxF "import RHFormalization.DesignedRCutoffS" RHFormalization.lean || printf '\nimport RHFormalization.DesignedRCutoffS\n' >> RHFormalization.lean
lake build 2>&1 | tee drs_root.log | tail -3
grep -q "Build completed successfully" drs_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_DESIGNED_S.tar.gz . && echo "SNAPSHOT SAVED: DESIGNED_S"
