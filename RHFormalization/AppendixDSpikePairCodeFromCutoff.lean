import RHFormalization.AppendixDPrimePowerPairCode
import RHFormalization.CanonicalPrimePowerCutoffMassEnumeration

/-!
# RHFormalization.AppendixDSpikePairCodeFromCutoff

Finite active Nat spike codes built from cutoff enumeration of prime-power pairs.

This bridges the existing cutoff enumeration

  `PrimePowerWeightCutoffEnumerationData.belowCutoff R`

to the `DFiniteStage` Nat-index interface using the pair-code helpers

  `ppCode : PrimePowerPair → ℕ`
  `ppDecode : ℕ → PrimePowerPair`.
-/

namespace RHFormalization

noncomputable section

open scoped BigOperators

/--
The valid prime-power pairs selected below cutoff `R`.

We use the existing cutoff enumeration and filter it to retain the valid
prime-power pairs below the stage cutoff.
-/
noncomputable def activePrimePowerPairsBelow
    (Enum : PrimePowerWeightCutoffEnumerationData)
    (R : ℝ) :
    Finset PrimePowerPair := by
  classical
  exact
    (Enum.belowCutoff R).filter
      (fun q : PrimePowerPair => IsPrimePowerPair q ∧ q.center ≤ R)

/--
The active Nat spike codes corresponding to the selected prime-power pairs.
-/
noncomputable def activePrimePowerCodesBelow
    (Enum : PrimePowerWeightCutoffEnumerationData)
    (R : ℝ) :
    Finset ℕ := by
  classical
  exact (activePrimePowerPairsBelow Enum R).image ppCode

/--
Membership in the active pair set is exactly membership in the cutoff
enumeration plus validity plus the cutoff bound.
-/
theorem activePrimePowerPairsBelow_mem
    (Enum : PrimePowerWeightCutoffEnumerationData)
    (R : ℝ)
    (q : PrimePowerPair) :
    q ∈ activePrimePowerPairsBelow Enum R ↔
      q ∈ Enum.belowCutoff R ∧ IsPrimePowerPair q ∧ q.center ≤ R := by
  classical
  simp [activePrimePowerPairsBelow]

/--
Every active Nat code comes from an active prime-power pair.
-/
theorem activePrimePowerCodesBelow_active
    (Enum : PrimePowerWeightCutoffEnumerationData)
    (R : ℝ)
    (n : ℕ)
    (hn : n ∈ activePrimePowerCodesBelow Enum R) :
    ∃ q : PrimePowerPair,
      q ∈ activePrimePowerPairsBelow Enum R ∧ ppCode q = n := by
  classical
  simpa [activePrimePowerCodesBelow] using Finset.mem_image.mp hn

/--
Decoded active Nat codes are valid prime-power pairs.
-/
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

/--
Decoded active Nat codes lie below the cutoff.
-/
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

/--
The Nat-to-prime-power map is injective on active codes.
-/
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

/--
Every valid prime-power pair below cutoff is represented by an active Nat code.
-/
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

end

end RHFormalization
