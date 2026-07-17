import RHFormalization.PerturbedEigenvalueSum
import RHFormalization.FiniteStageSpectrum

/-!
# Gate 4, brick 1: the REAL perturbed residual (honest statement, not the bound)

Wires `perturbedEigenvalues` (the genuine spectrum of H_N = D + V) into a real
`F_stage`: the resolvent trace `∑_i 1/(s + λ_i(H_N))` of the PERTURBED operator,
via `FstageFinite`. Then defines the honest residual `R = F_perturbed - B`
against an arbitrary finite prime package `B`.

This makes the residual be about the RIGHT operator (the perturbed one) for the
first time — previously `R_stage` used the designed/free `F_stage` (≡ 0 or free
resolvent). The residual `perturbedResidual` is a concrete, sorry-free object.

NOTE: this is the residual *object*, not the D.EXPORT *bound*. The bound — that
this residual is uniformly bounded on Ω-compacts along the cutoff net — is the
open analytic content (Q1/Q2, only numerically tested). This brick makes Gate 4
STATEABLE about the correct operator; it does not prove it.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

variable {N : ℕ}

/-- **The perturbed F_stage**: resolvent trace of the genuine perturbed spectrum
`∑_i 1/(s + λ_i(H_N))`. -/
noncomputable def perturbedFStage (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian) (s : ℂ) : ℂ :=
  FstageFinite (perturbedEigenvalues μ hV) s

/-- The perturbed F_stage is holomorphic on Ω, provided the perturbed spectrum
is nonnegative (the globally-shifted regime). -/
theorem perturbedFStage_holo (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian)
    (hpos : ∀ i, 0 ≤ perturbedEigenvalues μ hV i) :
    HolomorphicOnC (perturbedFStage μ hV) Ω :=
  FstageFinite_holo_on_Omega (perturbedEigenvalues μ hV) hpos

/-- **The honest perturbed residual**: `R(s) = F_perturbed(s) - B(s)` against an
arbitrary finite prime package `B`. This is the residual *of the perturbed
operator* — the object D.EXPORT must bound. -/
noncomputable def perturbedResidual (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian)
    (B : ℂ → ℂ) (s : ℂ) : ℂ :=
  perturbedFStage μ hV s - B s

/-- **Gate 4, stated honestly about the right operator** (NOT proven): the
perturbed residual is uniformly bounded on an Ω-compact `K`. This is the exact
D.EXPORT obligation for the perturbed operator — the open analytic frontier. -/
def PerturbedDExport (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian)
    (B : ℂ → ℂ) (K : Set ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ K, ‖perturbedResidual μ hV B s‖ ≤ C

#print axioms perturbedFStage
#print axioms perturbedFStage_holo
#print axioms perturbedResidual

end

end RHFormalization
