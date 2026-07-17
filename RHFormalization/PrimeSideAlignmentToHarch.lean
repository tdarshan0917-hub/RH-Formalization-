import RHFormalization.PrimeSideAlignmentContract
import RHFormalization.CurrentFrontierEndpoint

/-!
# RHFormalization.PrimeSideAlignmentToHarch

This file makes the alignment contract operational.

Given a corrected prime-side object `Btr` from `PrimeSideAlignmentContract`,
and a proof that `Btr + ZpoleSeries` is holomorphic on Ω, we package that
sum as an `HArchPackage`.

This bypasses the paused displacement-kernel branch and prepares the route
back into the older `HArchPackage`/`h_split` RH spine.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter
open scoped BigOperators

/--
The H-side holomorphic package associated to an aligned prime-side transform.

The remaining analytic content is now explicit:

  `HolomorphicOnC (fun s => Btr s + ZpoleSeries M s) Ω`.

This is the corrected explicit-formula holomorphy target.
-/
def alignedHarchPackage
    (M : ZeroMultiplicityData)
    (D : OperatorResolventBridge)
    (A : PrimeSideAlignmentContract M D)
    (h_holo :
      HolomorphicOnC
        (fun s : ℂ => A.Btr s + ZpoleSeries M s)
        Ω) :
    HArchPackage :=
  { Harch := fun s : ℂ => A.Btr s + ZpoleSeries M s
    h_Harch_holo := h_holo }

/--
On the Appendix-D overlap, the aligned Harch package satisfies the split

  `D.B = Harch - ZpoleSeries`.

This is the key algebraic bridge back into the old `HArchPackage`/`h_split`
spine.
-/
theorem alignedHarch_split_on_D_overlap
    (M : ZeroMultiplicityData)
    (D : OperatorResolventBridge)
    (A : PrimeSideAlignmentContract M D)
    (h_holo :
      HolomorphicOnC
        (fun s : ℂ => A.Btr s + ZpoleSeries M s)
        Ω) :
    ∀ s : ℂ, s ∈ RightHalfPlane D.sigma0 →
      D.B s =
        (alignedHarchPackage M D A h_holo).Harch s
          - ZpoleSeries M s := by
  intro s hs
  dsimp [alignedHarchPackage]
  rw [← A.h_Btr_matches_D_on_overlap s hs]
  ring

/--
Variant for a target B-function known to agree with `D.B` on the same overlap.

This is the exact adapter we will need for the designed shared package, where
the target is expected to be `designedY.B.Cshared.Bshared`.
-/
theorem alignedHarch_split_for_Btarget_on_D_overlap
    (M : ZeroMultiplicityData)
    (D : OperatorResolventBridge)
    (A : PrimeSideAlignmentContract M D)
    (h_holo :
      HolomorphicOnC
        (fun s : ℂ => A.Btr s + ZpoleSeries M s)
        Ω)
    (Btarget : ℂ → ℂ)
    (hBtarget_eq_D :
      ∀ s : ℂ, s ∈ RightHalfPlane D.sigma0 →
        Btarget s = D.B s) :
    ∀ s : ℂ, s ∈ RightHalfPlane D.sigma0 →
      Btarget s =
        (alignedHarchPackage M D A h_holo).Harch s
          - ZpoleSeries M s := by
  intro s hs
  calc
    Btarget s = D.B s := hBtarget_eq_D s hs
    _ =
        (alignedHarchPackage M D A h_holo).Harch s
          - ZpoleSeries M s :=
        alignedHarch_split_on_D_overlap M D A h_holo s hs

#check alignedHarchPackage
#check alignedHarch_split_on_D_overlap
#check alignedHarch_split_for_Btarget_on_D_overlap
#check RH_from_raw_inputs
#check RH_from_designed_D_convergence

end

end RHFormalization
