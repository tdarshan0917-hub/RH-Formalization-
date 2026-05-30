import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Operations
import RHFormalization.AnalyticWrappers
import RHFormalization.Basic

/-!
# RHFormalization.ConcreteHBzero

Concrete H-side logarithmic derivative tied to Mathlib's `riemannZeta`.

This is the first non-parameter H-side function:
  concreteBzero s = -ζ'(s)/ζ(s).

The point is not to finish the H package here. The point is to stop treating
`Bzero` as an abstract field and begin tying it to Mathlib's zeta.
-/

namespace RHFormalization

noncomputable section

open Complex

/-- The concrete H-side logarithmic derivative `-ζ'/ζ`. -/
noncomputable def concreteBzero (s : ℂ) : ℂ :=
  -deriv riemannZeta s / riemannZeta s

/-- `riemannZeta` is meromorphic on all of `ℂ`. -/
theorem riemannZeta_meromorphicOn_univ :
    MeromorphicOn riemannZeta (Set.univ : Set ℂ) := by
  intro s _
  by_cases h : s = 1
  · subst h
    exact (riemannZeta_residue_one).meromorphicAt
  · exact (differentiableAt_riemannZeta h).analyticAt.meromorphicAt

/-- `deriv riemannZeta` is meromorphic on all of `ℂ`. -/
theorem deriv_riemannZeta_meromorphicOn_univ :
    MeromorphicOn (deriv riemannZeta) (Set.univ : Set ℂ) :=
  riemannZeta_meromorphicOn_univ.deriv

/-- `concreteBzero = -ζ'/ζ` is meromorphic on all of `ℂ`. -/
theorem concreteBzero_meromorphicOn_univ :
    MeromorphicOn concreteBzero (Set.univ : Set ℂ) := by
  unfold concreteBzero
  exact
    (deriv_riemannZeta_meromorphicOn_univ.neg).div
      riemannZeta_meromorphicOn_univ

/-- Therefore `concreteBzero` is meromorphic on `Ω`. -/
theorem concreteBzero_meromorphicOn :
    MeromorphicOnC concreteBzero Ω :=
  concreteBzero_meromorphicOn_univ.mono (Set.subset_univ _)

end

end RHFormalization
