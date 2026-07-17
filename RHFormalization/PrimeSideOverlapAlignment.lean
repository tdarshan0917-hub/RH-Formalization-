import RHFormalization.PrimeSideAlignmentDesignedBridge

/-!
# RHFormalization.PrimeSideOverlapAlignment

A weaker, sharper alignment route.

The previous `PrimeSideAlignmentContract` included principal-part and
away-from-witness regularity fields.  But the Harch/split consumer only needs:

* a corrected prime-side transform `Btr`;
* agreement with the Appendix-D `D.B` on the overlap half-plane;
* holomorphy of `Btr + ZpoleSeries` on Ω.

This file removes the unused obligations and gives the cleanest current
explicit-formula frontier.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter
open scoped BigOperators

/--
Overlap-only alignment.

`Btr` is the corrected transformed prime-side object.  It only has to match
the Appendix-D exported `D.B` on the overlap half-plane.
-/
structure PrimeSideOverlapAlignment
    (D : OperatorResolventBridge) where
  Btr : ℂ → ℂ
  h_Btr_matches_D_on_overlap :
    ∀ s : ℂ, s ∈ RightHalfPlane D.sigma0 →
      Btr s = D.B s

/--
The Harch package associated to an overlap-aligned prime-side transform.
-/
def overlapAlignedHarchPackage
    (M : ZeroMultiplicityData)
    (D : OperatorResolventBridge)
    (A : PrimeSideOverlapAlignment D)
    (h_holo :
      HolomorphicOnC
        (fun s : ℂ => A.Btr s + ZpoleSeries M s)
        Ω) :
    HArchPackage :=
  { Harch := fun s : ℂ => A.Btr s + ZpoleSeries M s
    h_Harch_holo := h_holo }

/--
On the D-overlap, the overlap-aligned Harch package satisfies

`D.B = Harch - ZpoleSeries`.
-/
theorem overlapAlignedHarch_split_on_D_overlap
    (M : ZeroMultiplicityData)
    (D : OperatorResolventBridge)
    (A : PrimeSideOverlapAlignment D)
    (h_holo :
      HolomorphicOnC
        (fun s : ℂ => A.Btr s + ZpoleSeries M s)
        Ω) :
    ∀ s : ℂ, s ∈ RightHalfPlane D.sigma0 →
      D.B s =
        (overlapAlignedHarchPackage M D A h_holo).Harch s
          - ZpoleSeries M s := by
  intro s hs
  dsimp [overlapAlignedHarchPackage]
  rw [← A.h_Btr_matches_D_on_overlap s hs]
  ring

/--
Target-B variant: if `Btarget = D.B` on the overlap, then `Btarget` satisfies
the Harch split.
-/
theorem overlapAlignedHarch_split_for_Btarget_on_D_overlap
    (M : ZeroMultiplicityData)
    (D : OperatorResolventBridge)
    (A : PrimeSideOverlapAlignment D)
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
        (overlapAlignedHarchPackage M D A h_holo).Harch s
          - ZpoleSeries M s := by
  intro s hs
  calc
    Btarget s = D.B s := hBtarget_eq_D s hs
    _ =
        (overlapAlignedHarchPackage M D A h_holo).Harch s
          - ZpoleSeries M s :=
        overlapAlignedHarch_split_on_D_overlap M D A h_holo s hs

/--
Designed-Y split from overlap-only alignment.

This uses the already banked theorem

`designedY_Cshared_Bshared_eq_operatorBridge_B_on_overlap`.
-/
theorem overlapAlignedHarch_split_for_designedY
    (A :
      PrimeSideOverlapAlignment
        designedY.toOperatorResolventBridge)
    (h_holo :
      HolomorphicOnC
        (fun s : ℂ =>
          A.Btr s + ZpoleSeries defaultZeroMultiplicityData s)
        Ω) :
    ∀ s : ℂ,
      s ∈ RightHalfPlane designedY.toOperatorResolventBridge.sigma0 →
        designedY.B.Cshared.Bshared s =
          (overlapAlignedHarchPackage
            defaultZeroMultiplicityData
            designedY.toOperatorResolventBridge
            A
            h_holo).Harch s
            - ZpoleSeries defaultZeroMultiplicityData s :=
  overlapAlignedHarch_split_for_Btarget_on_D_overlap
    defaultZeroMultiplicityData
    designedY.toOperatorResolventBridge
    A
    h_holo
    designedY.B.Cshared.Bshared
    designedY_Cshared_Bshared_eq_operatorBridge_B_on_overlap

/--
Current sharp alignment theorem.

This bypasses the old displacement-kernel principal-part branch and also avoids
the over-strong principal-part/regularity fields from `PrimeSideAlignmentContract`.

Remaining explicit-formula content here is exactly:

`HolomorphicOnC (fun s => A.Btr s + ZpoleSeries defaultZeroMultiplicityData s) Ω`.
-/
theorem RH_from_primeSideOverlapAlignment_designed_convergence
    (h_real_zero_free :
      ∀ s : ℂ,
        s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (convergence :
      ZeroPoleLocalUniformConvergenceAPI
        defaultZeroMultiplicityData
        defaultZeroExhaustion
        (ZpoleSeries defaultZeroMultiplicityData))
    (poleSeriesMeromorphic :
      ZpoleMeromorphicFromSeriesAPI
        defaultZeroMultiplicityData
        defaultZeroExhaustion
        (ZpoleSeries defaultZeroMultiplicityData))
    (A :
      PrimeSideOverlapAlignment
        designedY.toOperatorResolventBridge)
    (h_holo :
      HolomorphicOnC
        (fun s : ℂ =>
          A.Btr s + ZpoleSeries defaultZeroMultiplicityData s)
        Ω)
    (hσ :
      0 ≤ designedY.toOperatorResolventBridge.sigma0) :
    RiemannHypothesis :=
  RH_from_designed_D_convergence
    h_real_zero_free
    (ZpoleSeries defaultZeroMultiplicityData)
    convergence
    poleSeriesMeromorphic
    (overlapAlignedHarchPackage
      defaultZeroMultiplicityData
      designedY.toOperatorResolventBridge
      A
      h_holo)
    designedY.toOperatorResolventBridge.sigma0
    hσ
    (overlapAlignedHarch_split_for_designedY A h_holo)

#check PrimeSideOverlapAlignment
#check overlapAlignedHarchPackage
#check overlapAlignedHarch_split_for_designedY
#check RH_from_primeSideOverlapAlignment_designed_convergence
#print axioms RH_from_primeSideOverlapAlignment_designed_convergence

end

end RHFormalization
