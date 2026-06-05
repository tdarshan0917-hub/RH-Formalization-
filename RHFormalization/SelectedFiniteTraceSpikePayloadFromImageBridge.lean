import RHFormalization.SelectedFiniteTraceSpikePayload
import RHFormalization.FiniteNatPrimePowerBridge

/-!
# Selected finite trace/spike payload from image bridge

This file uses the generic finite Nat→PrimePower image bridge to remove
the `ppIndices` / `ppKernel` / canonical-package equality burden from the
selected payload instance.

The remaining real data are:
* finite-stage trace functions `F_stage`, `B_stage`, `R_stage`;
* the stage split;
* Nat-indexed active diagonal spike data;
* a finite injection from active Nat indices to `PrimePowerPair`;
* coefficient/kernel compatibility.
-/

namespace RHFormalization

noncomputable section

/--
Build a `SelectedFiniteTraceSpikePayload` from finite-stage extraction data
plus a finite image bridge from Nat indices to prime-power indices.
-/
def buildSelectedFiniteTraceSpikePayloadFromImageBridge
    (F_stage B_stage R_stage : DFiniteStage → ℂ → ℂ)
    (sigma0 : ℝ)
    (h_stage_split :
      ∀ (α : DFiniteStage), ∀ s ∈ RightHalfPlane sigma0,
        F_stage α s = B_stage α s + R_stage α s)
    (activeIndices : DFiniteStage → Finset ℕ)
    (spikeKernel : DFiniteStage → ℕ → ℂ → ℂ)
    (h_activeIndices_active :
      ∀ (α : DFiniteStage), ∀ q ∈ activeIndices α,
        α.diagonalSpikeActive q)
    (h_B_stage_eq_diagonal_sum :
      ∀ (α : DFiniteStage) (s : ℂ),
        B_stage α s =
          finiteNatSpikePackage
            (activeIndices α)
            α.diagonalSpikeContribution
            (spikeKernel α)
            s)
    (toPP : DFiniteStage → ℕ → PrimePowerPair)
    (Kcan : DFiniteStage → CanonicalKernelC)
    (hinj :
      ∀ (α : DFiniteStage), ∀ m ∈ activeIndices α, ∀ n ∈ activeIndices α,
        toPP α m = toPP α n → m = n)
    (hcoeff :
      ∀ (α : DFiniteStage), ∀ n ∈ activeIndices α,
        α.canonicalSpikeContribution n = (toPP α n).weightC)
    (hkernel :
      ∀ (α : DFiniteStage), ∀ n ∈ activeIndices α, ∀ s : ℂ,
        spikeKernel α n s = Kcan α (toPP α n).center s) :
    SelectedFiniteTraceSpikePayload :=
{
  F_stage := F_stage
  B_stage := B_stage
  R_stage := R_stage
  sigma0 := sigma0
  h_stage_split := h_stage_split
  activeIndices := activeIndices
  spikeKernel := spikeKernel
  h_activeIndices_active := h_activeIndices_active
  h_B_stage_eq_diagonal_sum := h_B_stage_eq_diagonal_sum
  ppIndices := fun α => (activeIndices α).image (toPP α)
  ppKernel := Kcan
  h_canonical_sum_eq_finiteCanonical := by
    intro α s
    exact
      finiteNatSpikePackage_eq_finiteCanonicalPrimePowerPackage_image
        (activeIndices α)
        (toPP α)
        α.canonicalSpikeContribution
        (spikeKernel α)
        (Kcan α)
        (hinj α)
        (hcoeff α)
        (hkernel α)
        s
}

end

end RHFormalization
