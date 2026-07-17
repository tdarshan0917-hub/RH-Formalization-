import RHFormalization.AppendixDGuardedCenterCutoffFinite
import RHFormalization.AppendixDPrimePowerPairCode

/-!
# RHFormalization.AppendixDActiveSpikeCodesFromCenterCutoff

Direct finite active Nat spike codes for Appendix-D structural finite stages.

This file avoids an external cutoff-enumeration object.  It builds the active
finite Nat-index set directly from the finite guarded center-cutoff set

  `{q : PrimePowerPair | IsPrimePowerPair q ∧ q.center ≤ R}`

and then maps prime-power pairs to Nat codes using `ppCode`.
-/

namespace RHFormalization

noncomputable section

/--
The valid prime-power pairs with center at most `R`, as a `Finset`.
-/
noncomputable def activePrimePowerPairsCenterBelow (R : ℝ) :
    Finset PrimePowerPair :=
  (valid_primePower_center_le_finite R).toFinset

/--
The active Nat spike codes corresponding to valid prime-power pairs below `R`.
-/
noncomputable def activePrimePowerCodesCenterBelow (R : ℝ) :
    Finset ℕ :=
  (activePrimePowerPairsCenterBelow R).image ppCode

/--
Membership in the direct active prime-power pair set is exactly validity plus
the center cutoff bound.
-/
theorem activePrimePowerPairsCenterBelow_mem
    (R : ℝ)
    (q : PrimePowerPair) :
    q ∈ activePrimePowerPairsCenterBelow R ↔
      IsPrimePowerPair q ∧ q.center ≤ R := by
  classical
  simp [activePrimePowerPairsCenterBelow]

/--
Every active Nat code comes from an active prime-power pair.
-/
theorem activePrimePowerCodesCenterBelow_active
    (R : ℝ)
    (n : ℕ)
    (hn : n ∈ activePrimePowerCodesCenterBelow R) :
    ∃ q : PrimePowerPair,
      q ∈ activePrimePowerPairsCenterBelow R ∧ ppCode q = n := by
  classical
  simpa [activePrimePowerCodesCenterBelow] using Finset.mem_image.mp hn

/--
Decoded active Nat codes are valid prime-power pairs.
-/
theorem activePrimePowerCodesCenterBelow_valid
    (R : ℝ)
    (n : ℕ)
    (hn : n ∈ activePrimePowerCodesCenterBelow R) :
    IsPrimePowerPair (ppDecode n) := by
  classical
  rcases activePrimePowerCodesCenterBelow_active R n hn with ⟨q, hqmem, hcode⟩
  have hqall := (activePrimePowerPairsCenterBelow_mem R q).1 hqmem
  rcases hqall with ⟨hvalid, _hcenter⟩
  have hdecode : ppDecode n = q := by
    rw [← hcode]
    exact ppDecode_ppCode q
  simpa [hdecode] using hvalid

/--
Decoded active Nat codes lie below the center cutoff.
-/
theorem activePrimePowerCodesCenterBelow_center_le_R
    (R : ℝ)
    (n : ℕ)
    (hn : n ∈ activePrimePowerCodesCenterBelow R) :
    (ppDecode n).center ≤ R := by
  classical
  rcases activePrimePowerCodesCenterBelow_active R n hn with ⟨q, hqmem, hcode⟩
  have hqall := (activePrimePowerPairsCenterBelow_mem R q).1 hqmem
  rcases hqall with ⟨_hvalid, hcenter⟩
  have hdecode : ppDecode n = q := by
    rw [← hcode]
    exact ppDecode_ppCode q
  simpa [hdecode] using hcenter

/--
The Nat-to-prime-power decoder is injective on active codes.
-/
theorem activePrimePowerCodesCenterBelow_toPP_inj
    (R : ℝ)
    (m : ℕ)
    (_hm : m ∈ activePrimePowerCodesCenterBelow R)
    (n : ℕ)
    (_hn : n ∈ activePrimePowerCodesCenterBelow R)
    (h : ppDecode m = ppDecode n) :
    m = n := by
  exact ppDecode_injective h

/--
Every valid prime-power pair below cutoff is represented by an active Nat code.
-/
theorem activePrimePowerCodesCenterBelow_complete
    (R : ℝ)
    (q : PrimePowerPair)
    (hqvalid : IsPrimePowerPair q)
    (hqcenter : q.center ≤ R) :
    ∃ n : ℕ,
      n ∈ activePrimePowerCodesCenterBelow R ∧ ppDecode n = q := by
  classical
  have hactive : q ∈ activePrimePowerPairsCenterBelow R := by
    rw [activePrimePowerPairsCenterBelow_mem]
    exact ⟨hqvalid, hqcenter⟩
  refine ⟨ppCode q, ?_, ppDecode_ppCode q⟩
  exact Finset.mem_image.mpr ⟨q, hactive, rfl⟩

/--
The active predicate we will use in the structural `DFiniteStage` witness.
-/
def centerCutoffSpikeActive (R : ℝ) (n : ℕ) : Prop :=
  n ∈ activePrimePowerCodesCenterBelow R

/--
Soundness of the finite active code set for the active predicate.
-/
theorem centerCutoffSpikeActive_sound
    (R : ℝ)
    (n : ℕ)
    (hn : n ∈ activePrimePowerCodesCenterBelow R) :
    centerCutoffSpikeActive R n := by
  exact hn

/--
Completeness of the finite active code set for the active predicate.
-/
theorem centerCutoffSpikeActive_complete
    (R : ℝ)
    (n : ℕ)
    (hn : centerCutoffSpikeActive R n) :
    n ∈ activePrimePowerCodesCenterBelow R := by
  exact hn

end

end RHFormalization
