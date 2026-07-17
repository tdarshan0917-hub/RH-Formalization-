import RHFormalization.PrimeSideOverlapAlignment
import RHFormalization.HExplicitFormulaHolomorphyLocal
import RHFormalization.ExplicitFormulaRegularBranch
import RHFormalization.MeromorphyAssembly

/-!
# RHFormalization.PrimeSideOverlapAlignmentLocalEF

Local-EF reduction for the corrected prime-side object `A.Btr`.

This file does not use the old displacement-kernel principal-part target.
It reduces the good alignment theorem's global holomorphy input

  HolomorphicOnC (fun s => A.Btr s + ZpoleSeries M s) Ω

to local witness extensions plus regularity of `A.Btr` away from witness poles.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter
open scoped BigOperators

/--
Generic local-EF holomorphy for an overlap-aligned prime-side transform.

At witness points, we assume a local holomorphic extension of `Btr + Zpole`.
Away from witness points, `A.Btr` is holomorphic by `hB_regular`, and `Zpole`
is holomorphic by the zero-side convergence/regularity machinery.
-/
theorem overlapAlignment_holo_from_localEF
    (ZF : ZetaZeroFacts)
    (M : ZeroMultiplicityData)
    (Zpole : ℂ → ℂ)
    (conv :
      ZeroPoleLocalUniformConvergenceAPI
        M
        defaultZeroExhaustion
        Zpole)
    (D : OperatorResolventBridge)
    (A : PrimeSideOverlapAlignment D)
    (h_witness :
      ∀ W : ZeroWitness,
        ∃ h : ℂ → ℂ,
          HolomorphicAtC h W.s0 ∧
            LocalEqAtC h
              (fun s : ℂ => A.Btr s + Zpole s)
              W.s0)
    (hB_regular :
      ∀ z : ℂ,
        z ∈ Ω →
          (∀ W : ZeroWitness, z ≠ W.s0) →
            HolomorphicAtC A.Btr z) :
    HolomorphicOnC
      (fun s : ℂ => A.Btr s + Zpole s)
      Ω := by
  apply holomorphicOnC_of_local_holomorphic_extensions
  intro z hzΩ
  by_cases hw : ∃ W : ZeroWitness, z = W.s0
  · rcases hw with ⟨W, rfl⟩
    exact h_witness W
  · have hnotW : ∀ W : ZeroWitness, z ≠ W.s0 := by
      intro W hEq
      exact hw ⟨W, hEq⟩
    have hznp :=
      not_zeroPoleSet_of_not_zeroWitness ZF z hzΩ hnotW
    have hB :
        HolomorphicAtC A.Btr z :=
      hB_regular z hzΩ hnotW
    have hZ :
        HolomorphicAtC Zpole z :=
      zpole_analyticAt_nonpole M Zpole conv z hzΩ hznp
    exact
      ⟨fun s : ℂ => A.Btr s + Zpole s,
        ⟨AnalyticAt.add hB hZ, EventuallyEq.rfl⟩⟩

/--
RH through the good overlap-alignment route, with global `h_holo` replaced by
local explicit-formula data for `A.Btr`.

This is the real E-side reduction target now.
-/
theorem RH_from_primeSideOverlapAlignment_localEF
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
    (ZF : ZetaZeroFacts)
    (h_witness :
      ∀ W : ZeroWitness,
        ∃ h : ℂ → ℂ,
          HolomorphicAtC h W.s0 ∧
            LocalEqAtC h
              (fun s : ℂ =>
                A.Btr s + ZpoleSeries defaultZeroMultiplicityData s)
              W.s0)
    (hB_regular :
      ∀ z : ℂ,
        z ∈ Ω →
          (∀ W : ZeroWitness, z ≠ W.s0) →
            HolomorphicAtC A.Btr z)
    (hσ :
      0 ≤ designedY.toOperatorResolventBridge.sigma0) :
    RiemannHypothesis :=
  RH_from_primeSideOverlapAlignment_designed_convergence
    h_real_zero_free
    convergence
    poleSeriesMeromorphic
    A
    (overlapAlignment_holo_from_localEF
      ZF
      defaultZeroMultiplicityData
      (ZpoleSeries defaultZeroMultiplicityData)
      convergence
      designedY.toOperatorResolventBridge
      A
      h_witness
      hB_regular)
    hσ

#check overlapAlignment_holo_from_localEF
#check RH_from_primeSideOverlapAlignment_localEF
#print axioms RH_from_primeSideOverlapAlignment_localEF

end

end RHFormalization
