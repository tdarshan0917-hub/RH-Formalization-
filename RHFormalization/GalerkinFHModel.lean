/-
GalerkinFHModel.lean

FH FOR FRONT F, FROM THE BANKED ENGINE: the shifted diagonal limiting
spectrum lamDiag + SupVConst instantiates DiscreteResolventModel (nonneg +
pi^2 quadratic growth, both banked), so its resolvent trace

  galerkinFH s = \sum'_k 1/(s + lamDiag k + SupVConst)

is DEFINED and HOLOMORPHIC ON OMEGA by the banked April engine
(resolvent_trace_holo_from_sq_growth). This is the limit object of the
manuscript-faithful shifted stage F-slots; what remains of Front F is the
compact-local trace convergence F_stage(alpha n) -> galerkinFH.
-/
import RHFormalization.GalerkinDiagLimit
import RHFormalization.DiscreteResolventModel

namespace RHFormalization

noncomputable section

open Complex Filter

/-- Growth constant: pi^2 works, positive. -/
theorem pi_sq_pos : (0:ℝ) < Real.pi ^ 2 := by positivity

/-- **THE FH MODEL** for the genuine galerkin exhaustion: the shifted
diagonal limiting spectrum as a DiscreteResolventModel. -/
def galerkinFHModel : DiscreteResolventModel where
  lam := fun k => lamDiag k + SupVConst
  nonneg := lamDiag_shifted_nonneg
  growthConst := Real.pi ^ 2
  growthConst_pos := pi_sq_pos
  growth := lamDiag_shifted_growth

/-- **FH, the D-side limit object of Front F.** -/
def galerkinFH : ℂ → ℂ := galerkinFHModel.FH

/-- **FH is holomorphic on Omega** -- from the banked resolvent engine,
no new analysis. This is DFHLimitData.h_FH_holo, discharged. -/
theorem galerkinFH_holo : HolomorphicOnC galerkinFH Ω :=
  galerkinFHModel.FH_holo

/-- FH unfolds to the resolvent trace of the shifted diagonal spectrum. -/
theorem galerkinFH_eq_tsum (s : ℂ) :
    galerkinFH s = ∑' k : ℕ, (s + ((lamDiag k + SupVConst : ℝ) : ℂ))⁻¹ := by
  rfl

/-- Per-index convergence of the SHIFTED diagonal eigenvalues to the
model's spectrum -- the head-term input for the trace convergence. -/
theorem diagLamAt_shifted_tendsto (k : ℕ) :
    Tendsto (fun j => diagLamAt k j + SupVConst) atTop
      (nhds (galerkinFHModel.lam k)) := by
  show Tendsto (fun j => diagLamAt k j + SupVConst) atTop
    (nhds (lamDiag k + SupVConst))
  exact (diagLamAt_tendsto_lamDiag k).add tendsto_const_nhds

#print axioms galerkinFHModel
#print axioms galerkinFH
#print axioms galerkinFH_holo
#print axioms galerkinFH_eq_tsum
#print axioms diagLamAt_shifted_tendsto

end

end RHFormalization
