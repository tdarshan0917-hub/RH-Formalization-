import RHFormalization.SelectedFiniteTraceSpikePayloadFromImageBridge

/-!
Scratch-only integrity check.

Do not commit this file.

Purpose:
test whether `SelectedFiniteTraceSpikePayload` can be inhabited by empty/zero
data.  If this builds, the current payload API is underconstrained and the next
real move is to strengthen the payload specification, not to keep searching.
-/

namespace RHFormalization

noncomputable section

private def scratchZeroStage : DFiniteStage → ℂ → ℂ :=
  fun _ _ => 0

private def scratchEmptyActiveIndices : DFiniteStage → Finset ℕ :=
  fun _ => ∅

private def scratchZeroSpikeKernel : DFiniteStage → ℕ → ℂ → ℂ :=
  fun _ _ _ => 0

private def scratchToPP : DFiniteStage → ℕ → PrimePowerPair :=
  fun _ _ => (0, 0)

private def scratchKcan : DFiniteStage → CanonicalKernelC :=
  fun _ => fun _ _ => 0

private theorem scratch_stage_split :
    ∀ (α : DFiniteStage), ∀ s ∈ RightHalfPlane (0 : ℝ),
      scratchZeroStage α s =
        scratchZeroStage α s + scratchZeroStage α s := by
  intro α s hs
  simp [scratchZeroStage]

private theorem scratch_active :
    ∀ (α : DFiniteStage), ∀ q ∈ scratchEmptyActiveIndices α,
      α.diagonalSpikeActive q := by
  intro α q hq
  simp [scratchEmptyActiveIndices] at hq

private theorem scratch_B_stage_eq_diagonal_sum :
    ∀ (α : DFiniteStage) (s : ℂ),
      scratchZeroStage α s =
        finiteNatSpikePackage
          (scratchEmptyActiveIndices α)
          α.diagonalSpikeContribution
          (scratchZeroSpikeKernel α)
          s := by
  intro α s
  simp [scratchZeroStage, scratchEmptyActiveIndices, finiteNatSpikePackage]

private theorem scratch_inj :
    ∀ (α : DFiniteStage), ∀ m ∈ scratchEmptyActiveIndices α,
      ∀ n ∈ scratchEmptyActiveIndices α,
        scratchToPP α m = scratchToPP α n → m = n := by
  intro α m hm
  simp [scratchEmptyActiveIndices] at hm

private theorem scratch_coeff :
    ∀ (α : DFiniteStage), ∀ n ∈ scratchEmptyActiveIndices α,
      α.canonicalSpikeContribution n =
        (scratchToPP α n).weightC := by
  intro α n hn
  simp [scratchEmptyActiveIndices] at hn

private theorem scratch_kernel :
    ∀ (α : DFiniteStage), ∀ n ∈ scratchEmptyActiveIndices α, ∀ s : ℂ,
      scratchZeroSpikeKernel α n s =
        scratchKcan α (scratchToPP α n).center s := by
  intro α n hn s
  simp [scratchEmptyActiveIndices] at hn

def scratchEmptySelectedFiniteTraceSpikePayload :
    SelectedFiniteTraceSpikePayload :=
  buildSelectedFiniteTraceSpikePayloadFromImageBridge
    scratchZeroStage
    scratchZeroStage
    scratchZeroStage
    0
    scratch_stage_split
    scratchEmptyActiveIndices
    scratchZeroSpikeKernel
    scratch_active
    scratch_B_stage_eq_diagonal_sum
    scratchToPP
    scratchKcan
    scratch_inj
    scratch_coeff
    scratch_kernel

#check scratchEmptySelectedFiniteTraceSpikePayload
#print axioms scratchEmptySelectedFiniteTraceSpikePayload

end

end RHFormalization
