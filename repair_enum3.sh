#!/bin/zsh
cp RHFormalization/CanonicalPrimePowerCutoffMassEnumeration.lean /tmp/enum.bak
cp RHFormalization/AppendixDSpikePairCodeFromCutoff.lean /tmp/spike.bak
python3 - <<'PY'
import sys, re
p1='RHFormalization/CanonicalPrimePowerCutoffMassEnumeration.lean'
lines=open(p1).read().split('\n')

fi=None
for i,l in enumerate(lines):
    if l.strip()=="h_mem_belowCutoff :": fi=i; break
if fi is None: print("E1: field not found"); sys.exit(1)
ci=None
for j in range(fi, min(fi+8, len(lines))):
    if lines[j].strip()=="q.center ≤ R →": ci=j; break
if ci is None: print("E2: center line not found"); sys.exit(1)
indent=lines[ci][:len(lines[ci])-len(lines[ci].lstrip())]
lines.insert(ci, indent+"IsPrimePowerPair q →")

di=None
for i,l in enumerate(lines):
    if l.strip().startswith("def PrimePowerWeightCutoffEnumerationData.toMassBoundData"): di=i; break
if di is None: print("E3: toMassBoundData not found"); sys.exit(1)
ins=di
k=di-1
while k>=0 and k>di-8:
    if lines[k].strip().startswith("/--"): ins=k; break
    k-=1
helper=[
"/-- Invalid pairs carry zero weight: the validity guard on the enumeration is conservative. -/",
"theorem PrimePowerPair.weightReal_eq_zero_of_invalid",
"    (q : PrimePowerPair) (h : ¬ IsPrimePowerPair q) :",
"    q.weightReal = 0 := by",
"  classical",
"  simp [PrimePowerPair.weightReal, h]",
""]
lines[ins:ins]=helper

si=None
for i,l in enumerate(lines):
    if l.strip().startswith("h_weightC_mass_le_of_center_le := by"): si=i; break
if si is None: print("E4: proof head not found"); sys.exit(1)
ei=None
for j in range(si, min(si+25, len(lines))):
    if "norm_nonneg q.weightC) }" in lines[j]: ei=j; break
if ei is None: print("E5: proof tail not found"); sys.exit(1)
newproof=[
"    h_weightC_mass_le_of_center_le := by",
"      classical",
"      intro I R hcenter",
"      have hfil :",
"          (I.filter IsPrimePowerPair).sum",
"              (fun q : PrimePowerPair => ‖q.weightC‖) =",
"            I.sum (fun q : PrimePowerPair => ‖q.weightC‖) := by",
"        apply Finset.sum_filter_of_ne",
"        intro q _hq hne",
"        by_contra hnot",
"        exact hne (by",
"          simp [PrimePowerPair.weightC,",
"            PrimePowerPair.weightReal_eq_zero_of_invalid q hnot])",
"      rw [← hfil]",
"      exact",
"        Finset.sum_le_sum_of_subset_of_nonneg",
"          (fun q hq =>",
"            E.h_mem_belowCutoff R q",
"              (Finset.mem_filter.mp hq).2",
"              (hcenter q (Finset.mem_filter.mp hq).1))",
"          (fun q hq hqnot =>",
"            norm_nonneg q.weightC) }"]
lines[si:ei+1]=newproof
open(p1,'w').write('\n'.join(lines))

p2='RHFormalization/AppendixDSpikePairCodeFromCutoff.lean'
t=open(p2).read()
pat=re.compile(r"Enum\.h_mem_belowCutoff\s+R\s+q\s+hqcenter")
t2,nsub=pat.subn("Enum.h_mem_belowCutoff R q hqvalid hqcenter", t)
if nsub==0:
    print("E6: regex found zero matches; neighborhood dump follows")
    for i,l in enumerate(t.split('\n')):
        if "h_mem_belowCutoff" in l:
            print(f"LINE {i+1}: {repr(l)}")
    sys.exit(1)
open(p2,'w').write(t2)
print(f"edits applied (call-site substitutions: {nsub})")
PY
if [ $? -ne 0 ]; then echo "ANCHOR FAILURE -> restoring"; cp /tmp/enum.bak RHFormalization/CanonicalPrimePowerCutoffMassEnumeration.lean; cp /tmp/spike.bak RHFormalization/AppendixDSpikePairCodeFromCutoff.lean; exit 1; fi
echo "===== sanity: guarded field ====="
grep -A5 "h_mem_belowCutoff :" RHFormalization/CanonicalPrimePowerCutoffMassEnumeration.lean | head -7
echo "===== build repaired modules ====="
lake build RHFormalization.CanonicalPrimePowerCutoffMassEnumeration RHFormalization.AppendixDSpikePairCodeFromCutoff 2>&1 | tee enum_a.log | grep -e "error" -e "Build completed"
if grep -q "error" enum_a.log; then
  echo "FAILED -> restoring (errors below)"; grep -B2 -A10 "error" enum_a.log | head -50
  cp /tmp/enum.bak RHFormalization/CanonicalPrimePowerCutoffMassEnumeration.lean
  cp /tmp/spike.bak RHFormalization/AppendixDSpikePairCodeFromCutoff.lean
  lake build RHFormalization.CanonicalPrimePowerCutoffMassEnumeration 2>&1 | tail -3; exit 1
fi
echo "===== root replay + snapshot ====="
lake build 2>&1 | tee enum_root.log | tail -4
grep -q "Build completed successfully" enum_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_ENUM_REPAIRED.tar.gz . && echo "SNAPSHOT SAVED: ENUM_REPAIRED"
