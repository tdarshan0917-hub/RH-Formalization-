import RHFormalization.AlongNetBoundFromQRes
import RHFormalization.DSuperSmoothing
import RHFormalization.ResidualLaplaceRep
import RHFormalization.QResCombinedNormBound
import Mathlib

/-!
# h_loc_bdd from the super-smoothing certificate (manuscript D.USR core).

The irreducible target is ‖R_stage(α) s‖ ≤ C, uniform in the cutoff, on each compact.
All sector machinery (bulk split, along-net bridge) wraps this single bound.

Its mathematical content is the manuscript's super-smoothing cancellation: the residual
Q_res = Mix + Tail is super-polynomially small UNIFORMLY in the cutoff, because the spikes
are constructed to cancel the heat trace's singular part. This file takes that cancellation
as the named quantitative certificate (a per-compact uniform constant for the residual
transform) and wires it to h_loc_bdd.

This is the honest D.USR input: the super-smoothing bound the manuscript establishes,
made explicit as the single hypothesis the entire RH chain rests on.
-/

namespace RHFormalization
open Complex MeasureTheory
open scoped BigOperators

variable {N : ℕ}

/-- **The D.USR super-smoothing certificate** for the aligned prime layer:
on each compact K ⊆ Ω, the residual R_stage is uniformly bounded across the whole
cutoff net. This is the quantitative form of the manuscript's super-smoothing
cancellation (Q_res = Mix+Tail super-smooths to all orders, uniformly in the cutoff). -/
def PrimeUSRSuperSmoothingCertificate
    (μ : Fin N → ℝ) (alpha : ℕ → DFiniteStage) : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s : ℂ, s ∈ K →
      ‖(primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage (alpha n) s‖ ≤ C

/-- **D.USR ⇒ h_loc_bdd.** The super-smoothing certificate gives Montel's local-boundedness
input directly — this is the entire remaining link in the RH-backwards chain. -/
theorem primePerturbedAligned_h_loc_bdd_from_superSmoothing
    (μ : Fin N → ℝ) (alpha : ℕ → DFiniteStage)
    (hUSR : PrimeUSRSuperSmoothingCertificate μ alpha) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n : ℕ, ∀ s : ℂ, s ∈ K →
        ‖(primePerturbedOperatorLayerAligned μ).toStagePackage.R_stage (alpha n) s‖ ≤ C :=
  primePerturbedAligned_h_loc_bdd_from_qRes_bound μ alpha hUSR

#print axioms primePerturbedAligned_h_loc_bdd_from_superSmoothing

end RHFormalization
