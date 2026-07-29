import RHFormalization.AppendixDPrimePowerPairCode
import RHFormalization.CanonicalPrimePowerCutoffMassEnumeration

namespace RHFormalization

noncomputable section

open scoped BigOperators

#check PrimePowerWeightCutoffEnumerationData
#check PrimePowerWeightCutoffEnumerationData.belowCutoff
#check PrimePowerWeightCutoffEnumerationData.h_mem_belowCutoff
#check ppCode
#check ppDecode
#check ppDecode_ppCode
#check ppDecode_injective

/--
The valid prime-power pairs selected below cutoff `R`, using an existing
cutoff-enumeration object but filtering it to keep only genuine valid pairs
below the stage cutoff.
-/
noncomputable def activePrimePowerPairsBelow
    (Enum : PrimePowerWeightCutoffEnumerationData)
    (R : ℝ) :
    Finset PrimePowerPair := by
  classical
  exact
    (Enum.belowCutoff R).filter
      (fun q : PrimePowerPair => IsPrimePowerPair q ∧ q.center ≤ R)

/-- The active Nat spike codes corresponding to the selected prime-power pairs. -/
noncomputable def activePrimePowerCodesBelow
    (Enum : PrimePowerWeightCutoffEnumerationData)
    (R : ℝ) :
    Finset ℕ := by
  classical
  exact (activePrimePowerPairsBelow Enum R).image ppCode

theorem activePrimePowerPairsBelow_mem
    (Enum : PrimePowerWeightCutoffEnumerationData)
    (R : ℝ)
    (q : PrimePowerPair) :
    q ∈ activePrimePowerPairsBelow Enum R ↔
      q ∈ Enum.belowCutoff R ∧ IsPrimePowerPair q ∧ q.center ≤ R := by
  classical
  simp [activePrimePowerPairsBelow]

theorem activePrimePowerCodesBelow_active
    (Enum : PrimePowerWeightCutoffEnumerationData)
    (R : ℝ)
    (n : ℕ)
    (hn : n ∈ activePrimePowerCodesBelow Enum R) :
    ∃ q : PrimePowerPair,
      q ∈ activePrimePowerPairsBelow Enum R ∧ ppCode q = n := by
  classical
  simpa [activePrimePowerCodesBelow] using Finset.mem_image.mp hn

theorem activePrimePowerCodesBelow_valid
    (Enum : PrimePowerWeightCutoffEnumerationData)
    (R : ℝ)
    (n : ℕ)
    (hn : n ∈ activePrimePowerCodesBelow Enum R) :
    IsPrimePowerPair (ppDecode n) := by
  classical
  rcases activePrimePowerCodesBelow_active Enum R n hn with ⟨q, hqmem, hcode⟩
  have hqall := (activePrimePowerPairsBelow_mem Enum R q).1 hqmem
  rcases hqall with ⟨_hbelow, hvalid, _hcenter⟩
  have hdecode : ppDecode n = q := by
    rw [← hcode]
    exact ppDecode_ppCode q
  simpa [hdecode] using hvalid

theorem activePrimePowerCodesBelow_center_le_R
    (Enum : PrimePowerWeightCutoffEnumerationData)
    (R : ℝ)
    (n : ℕ)
    (hn : n ∈ activePrimePowerCodesBelow Enum R) :
    (ppDecode n).center ≤ R := by
  classical
  rcases activePrimePowerCodesBelow_active Enum R n hn with ⟨q, hqmem, hcode⟩
  have hqall := (activePrimePowerPairsBelow_mem Enum R q).1 hqmem
  rcases hqall with ⟨_hbelow, _hvalid, hcenter⟩
  have hdecode : ppDecode n = q := by
    rw [← hcode]
    exact ppDecode_ppCode q
  simpa [hdecode] using hcenter

theorem activePrimePowerCodesBelow_toPP_inj
    (Enum : PrimePowerWeightCutoffEnumerationData)
    (R : ℝ)
    (m : ℕ)
    (_hm : m ∈ activePrimePowerCodesBelow Enum R)
    (n : ℕ)
    (_hn : n ∈ activePrimePowerCodesBelow Enum R)
    (h : ppDecode m = ppDecode n) :
    m = n := by
  exact ppDecode_injective h

theorem activePrimePowerCodesBelow_complete
    (Enum : PrimePowerWeightCutoffEnumerationData)
    (R : ℝ)
    (q : PrimePowerPair)
    (hqvalid : IsPrimePowerPair q)
    (hqcenter : q.center ≤ R) :
    ∃ n : ℕ,
      n ∈ activePrimePowerCodesBelow Enum R ∧ ppDecode n = q := by
  classical
  have hbelow : q ∈ Enum.belowCutoff R :=
    Enum.h_mem_belowCutoff R q hqvalid hqcenter
  have hactive : q ∈ activePrimePowerPairsBelow Enum R := by
    rw [activePrimePowerPairsBelow_mem]
    exact ⟨hbelow, hqvalid, hqcenter⟩
  refine ⟨ppCode q, ?_, ppDecode_ppCode q⟩
  exact Finset.mem_image.mpr ⟨q, hactive, rfl⟩

#check activePrimePowerPairsBelow
#check activePrimePowerCodesBelow
#check activePrimePowerCodesBelow_valid
#check activePrimePowerCodesBelow_center_le_R
#check activePrimePowerCodesBelow_toPP_inj
#check activePrimePowerCodesBelow_complete

end

end RHFormalization
