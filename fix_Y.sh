#!/bin/zsh
python3 - <<'PY'
import sys
src = open('install_Y.sh').read()
marker = "cat > RHFormalization/DesignedDetailedConstruction.lean <<'EOF'"
i = src.find(marker)
if i < 0: print("MARKER MISSING"); sys.exit(1)
start = src.find("\n", i) + 1
j = src.find("\nEOF\n", start)
if j < 0: print("TERMINATOR MISSING"); sys.exit(1)
body = src[start:j+1]
old = """        show dC.Bshared s = _ + (0 : ℂ)
        rw [hm, add_zero] }"""
new = """        show dC.Bshared s = _ + (0 : ℂ)
        rw [hm, add_zero]
        first
          | rfl
          | simp [buildDBcanLimitDataFromOperatorFiniteCanonicalLimit,
              buildDBcanLimitDataFromOperatorPrimePowerLimit] }"""
if old not in body: print("PROOF ANCHOR MISSING"); sys.exit(1)
body = body.replace(old, new)
if "def designedY" not in body: print("BODY BAD"); sys.exit(1)
open('RHFormalization/DesignedDetailedConstruction.lean','w').write(body)
print(f"regenerated with overlap fix: {len(body)} chars")
PY
if [ $? -ne 0 ]; then echo "PATCH FAILED"; rm -f RHFormalization/DesignedDetailedConstruction.lean; exit 1; fi
lake build RHFormalization.DesignedDetailedConstruction 2>&1 | tee dy_b.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" dy_b.log; then
  echo "FAILED -> removing (errors below)"
  grep -B3 -A14 "error" dy_b.log | head -60
  rm RHFormalization/DesignedDetailedConstruction.lean
  exit 1
fi
if ! grep -q "designedY' depends on axioms: \[propext, Classical.choice, Quot.sound\]" dy_b.log; then
  echo "AXIOM CHECK FAILED (sorry present or empty) -> removing"
  rm RHFormalization/DesignedDetailedConstruction.lean
  exit 1
fi
grep -qxF "import RHFormalization.DesignedDetailedConstruction" RHFormalization.lean || printf '\nimport RHFormalization.DesignedDetailedConstruction\n' >> RHFormalization.lean
lake build 2>&1 | tee dy_root.log | tail -3
grep -q "Build completed successfully" dy_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_DESIGNED_Y.tar.gz . && echo "SNAPSHOT SAVED: DESIGNED_Y"
