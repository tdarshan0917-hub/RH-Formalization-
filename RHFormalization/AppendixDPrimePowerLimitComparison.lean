import RHFormalization.AppendixDPrimePowerFiniteFormulaTarget

/-!
# RHFormalization.AppendixDPrimePowerLimitComparison

Appendix-D finite-to-limit comparison skeleton.

This file does not create an RH endpoint.

It proves the abstract limiting principle needed after the finite-stage formula:

If

* `P.B_stage (α n)` tends to `Bcan`,
* the corresponding finite canonical prime-power packages tend to `Bshared`, and
* stagewise `P.B_stage = finiteCanonicalPrimePowerPackage`,

then `Bcan = Bshared` on the overlap.

The remaining analytic work is to prove the two convergence hypotheses from the
actual Appendix-D construction.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
If two sequences are pointwise equal and converge to two limits in `ℂ`, then the
limits are equal.
-/
theorem complex_limit_eq_of_eventuallyEq_tendsto
    {u v : ℕ → ℂ}
    {a b : ℂ}
    (hu : Tendsto u Filter.atTop (𝓝 a))
    (hv : Tendsto v Filter.atTop (𝓝 b))
    (huv : u =ᶠ[Filter.atTop] v) :
    a = b := by
  have hv_to_a : Tendsto v Filter.atTop (𝓝 a) :=
    Filter.Tendsto.congr' huv hu
  exact tendsto_nhds_unique hv_to_a hv

/--
Pointwise finite-to-limit comparison for the D-side canonical prime-power package.

Here `α : ℕ → DFiniteStage` is the chosen ordered cutoff/window exhaustion.
-/
theorem DFiniteStageCanonicalPrimePowerFormula.limit_eq_shared
    {P : DFiniteStagePackage}
    (F : DFiniteStageCanonicalPrimePowerFormula P)
    (α : ℕ → DFiniteStage)
    (Bcan : ℂ → ℂ)
    (Bshared : ℂ → ℂ)
    (sigma : ℝ)
    (h_B_stage_tendsto_Bcan :
      ∀ s : ℂ, s ∈ RightHalfPlane sigma →
        Tendsto
          (fun n : ℕ => P.B_stage (α n) s)
          Filter.atTop
          (𝓝 (Bcan s)))
    (h_finiteCanonical_tendsto_Bshared :
      ∀ s : ℂ, s ∈ RightHalfPlane sigma →
        Tendsto
          (fun n : ℕ =>
            finiteCanonicalPrimePowerPackage
              (F.indices (α n))
              (F.kernel (α n))
              s)
          Filter.atTop
          (𝓝 (Bshared s))) :
    ∀ s : ℂ, s ∈ RightHalfPlane sigma →
      Bcan s = Bshared s := by
  intro s hs
  exact
    complex_limit_eq_of_eventuallyEq_tendsto
      (h_B_stage_tendsto_Bcan s hs)
      (h_finiteCanonical_tendsto_Bshared s hs)
      (Filter.Eventually.of_forall
        (fun n : ℕ =>
          F.h_B_stage_eq_finiteCanonical (α n) s))

/--
Package-level D-side limit target.

This is the data needed to turn the finite-stage formula into the D-side matching
evidence `Bcan = Cshared.Bshared` on an overlap half-plane.
-/
structure DPrimePowerLimitComparisonData
    (P : DFiniteStagePackage)
    (F : DFiniteStageCanonicalPrimePowerFormula P)
    (Bcan : ℂ → ℂ)
    (C : CanonicalPrimePowerPackage) where
  alpha : ℕ → DFiniteStage
  sigma : ℝ
  hsigma_ge_P : P.sigma0 ≤ sigma
  hsigma_ge_C : C.sigma0 ≤ sigma
  h_B_stage_tendsto_Bcan :
    ∀ s : ℂ, s ∈ RightHalfPlane sigma →
      Tendsto
        (fun n : ℕ => P.B_stage (alpha n) s)
        Filter.atTop
        (𝓝 (Bcan s))
  h_finiteCanonical_tendsto_Bshared :
    ∀ s : ℂ, s ∈ RightHalfPlane sigma →
      Tendsto
        (fun n : ℕ =>
          finiteCanonicalPrimePowerPackage
            (F.indices (alpha n))
            (F.kernel (alpha n))
            s)
        Filter.atTop
        (𝓝 (C.Bshared s))

/--
Extract the D-side matching equation from finite-stage formula plus convergence.
-/
theorem DPrimePowerLimitComparisonData.h_Bcan_eq_shared
    {P : DFiniteStagePackage}
    {F : DFiniteStageCanonicalPrimePowerFormula P}
    {Bcan : ℂ → ℂ}
    {C : CanonicalPrimePowerPackage}
    (L : DPrimePowerLimitComparisonData P F Bcan C) :
    ∀ s : ℂ, s ∈ RightHalfPlane L.sigma →
      Bcan s = C.Bshared s :=
  F.limit_eq_shared
    L.alpha
    Bcan
    C.Bshared
    L.sigma
    L.h_B_stage_tendsto_Bcan
    L.h_finiteCanonical_tendsto_Bshared

end

end RHFormalization
