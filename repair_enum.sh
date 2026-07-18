#!/bin/zsh
cp RHFormalization/CanonicalPrimePowerCutoffMassEnumeration.lean /tmp/enum.bak
cp RHFormalization/AppendixDSpikePairCodeFromCutoff.lean /tmp/spike.bak
python3 - <<'PY'
import sys
p1='RHFormalization/CanonicalPrimePowerCutoffMassEnumeration.lean'
s=open(p1).read()

old_field="""  h_mem_belowCutoff :
    ∀ R : ℝ,
    ∀ q : PrimePowerPair,
      q.center ≤ R →
        q ∈ belowCutoff R"""
new_field="""  h_mem_belowCutoff :
    ∀ R : ℝ,
    ∀ q : PrimePowerPair,
      IsPrimePowerPair q →
      q.center ≤ R →
        q ∈ belowCutoff R"""
if old_field not in s: print("FIELD ANCHOR MISSING"); sys.exit(1)
s=s.replace(old_field,new_field)

old_proof="""    h_weightC_mass_le_of_center_le := by
      intro I R hcenter

      exact
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun q hq =>
            E.h_mem_belowCutoff R q (hcenter q hq))
          (fun q hq hqnot =>
            norm_nonneg q.weightC) }"""
new_proof="""    h_weightC_mass_le_of_center_le := by
      classical
      intro I R hcenter
      have hfil :
          (I.filter IsPrimePowerPair).sum
              (fun q : PrimePowerPair => ‖q.weightC‖) =
            I.sum (fun q : PrimePowerPair => ‖q.weightC‖) := by
        apply Finset.sum_filter_of_ne
        intro q _hq hne
        by_contra hnot
        exact hne (by
          simp [PrimePowerPair.weightC,
            PrimePowerPair.weightReal_eq_zero_of_invalid q hnot])
      rw [← hfil]
      exact
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun q hq =>
            E.h_mem_belowCutoff R q
              (Finset.mem_filter.mp hq).2
              (hcenter q (Finset.mem_filter.mp hq).1))
          (fun q hq hqnot =>
            norm_nonneg q.weightC) }"""
if old_proof not in s: print("PROOF ANCHOR MISSING"); sys.exit(1)
s=s.replace(old_proof,new_proof)

helper="""
/-- Invalid pairs carry zero weight: the guard repair is conservative. -/
theorem PrimePowerPair.weightReal_eq_zero_of_invalid
    (q : PrimePowerPair) (h : ¬ IsPrimePowerPair q) :
    q.weightReal = 0 := by
  classical
  simp [PrimePowerPair.weightReal, h]

"""
anchor="/--\nBuild the abstract cutoff mass-bound data from a concrete finite enumeration."
if anchor not in s: print("HELPER ANCHOR MISSING"); sys.exit(1)
s=s.replace(anchor, helper+anchor, 1)
open(p1,'w').write(s)

p2='RHFormalization/AppendixDSpikePairCodeFromCutoff.lean'
t=open(p2).read()
old_call="Enum.h_mem_belowCutoff R q hqcenter"
new_call="Enum.h_mem_belowCutoff R q hqvalid hqcenter"
if old_call not in t: print("CALL ANCHOR MISSING"); sys.exit(1)
t=t.replace(old_call,new_call)
open(p2,'w').write(t)
print("edits applied")
PY
if [ $? -ne 0 ]; then echo "ANCHOR FAILURE -> restoring"; cp /tmp/enum.bak RHFormalization/CanonicalPrimePowerCutoffMassEnumeration.lean; cp /tmp/spike.bak RHFormalization/AppendixDSpikePairCodeFromCutoff.lean; exit 1; fi
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
