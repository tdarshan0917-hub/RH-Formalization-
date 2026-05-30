import RHFormalization.DOperatorExport
import RHFormalization.CanonicalPrimePowerPackage

/-!
# RHFormalization.AppendixDPrimePowerFiniteFormulaTarget

Concrete Appendix-D finite-stage package target.

This file does not create a new RH endpoint.

It isolates the next real D-side proof obligation:

`P.B_stage α` should be exactly the finite canonical prime-power package
built from a finite prime-power index set and a stage kernel.

This is the finite-stage theorem that eventually feeds the D-side limiting
evidence

`DBcanLimitData.h_Bcan_matches_shared`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Finite-stage evidence that the D-side finite package `P.B_stage α` is the
finite canonical prime-power package with the manuscript's frozen normalization.
-/
structure DFiniteStageCanonicalPrimePowerFormula
    (P : DFiniteStagePackage) where
  indices :
    DFiniteStage → Finset PrimePowerPair

  kernel :
    DFiniteStage → CanonicalKernelC

  h_B_stage_eq_finiteCanonical :
    ∀ α : DFiniteStage,
    ∀ s : ℂ,
      P.B_stage α s =
        finiteCanonicalPrimePowerPackage
          (indices α)
          (kernel α)
          s

/--
A named target for the D-side proof work.

This is the exact theorem shape we need from Appendix D before taking the
cutoff/window limit to the shared canonical package.
-/
abbrev AppendixDFinitePackageFormulaTarget
    (P : DFiniteStagePackage) : Type 1 :=
  DFiniteStageCanonicalPrimePowerFormula P

/--
The finite-stage formula immediately gives a pointwise package equality for
each stage.
-/
theorem DFiniteStageCanonicalPrimePowerFormula.eq_on_stage
    {P : DFiniteStagePackage}
    (F : DFiniteStageCanonicalPrimePowerFormula P)
    (α : DFiniteStage)
    (s : ℂ) :
    P.B_stage α s =
      finiteCanonicalPrimePowerPackage
        (F.indices α)
        (F.kernel α)
        s :=
  F.h_B_stage_eq_finiteCanonical α s

end

end RHFormalization
