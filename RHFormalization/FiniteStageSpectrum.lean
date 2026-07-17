import RHFormalization.ResolventTraceHolo
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Analytic.Constructions

/-!
# RHFormalization.FiniteStageSpectrum

Path-2 brick: instantiate the stage eigenvalues `λ` from a GENUINE finite-dim
symmetric operator (Mathlib's `LinearMap.IsSymmetric.eigenvalues`), define the
finite resolvent-trace `F_stage(s) = ∑ᵢ 1/(s+λᵢ)`, and prove it holomorphic on Ω.

This is the step where `λ` stops being a free variable: it is the real spectrum
of an actual self-adjoint (symmetric, finite-dim) operator.  No trace-class
theory, no unbounded-operator spectral theorem — just Mathlib's finite-dim
diagonalization, which suffices because the paper's stages are finite-volume.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The real eigenvalues of a finite-dim symmetric operator, from Mathlib's
spectral theorem. This is the genuine spectrum, not an assumed sequence. -/
noncomputable def stageEigenvalues (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) : Fin n → ℝ :=
  hT.eigenvalues hn

/-- The finite resolvent-trace function `F_stage(s) = ∑ᵢ 1/(s + λᵢ)`. -/
noncomputable def FstageFinite (lam : Fin n → ℝ) (s : ℂ) : ℂ :=
  ∑ i, (s + (lam i : ℂ))⁻¹

/-- **Finite resolvent trace is holomorphic on Ω**, for any real shift vector
`λ` with nonneg entries. A finite sum of resolvent terms, each holomorphic on Ω. -/
theorem FstageFinite_holo_on_Omega (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) :
    HolomorphicOnC (FstageFinite lam) Ω := by
  intro z hz
  -- each term analytic at z, finite sum analytic at z, then within Ω
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      AnalyticAt ℂ (fun s => (s + (lam i : ℂ))⁻¹) z :=
    fun i _ => resolvent_term_analyticAt (lam i) (hlam i) hz
  have hsum : AnalyticAt ℂ (fun s => ∑ i, (s + (lam i : ℂ))⁻¹) z :=
    Finset.analyticAt_fun_sum _ hterm
  exact (hsum.congr (by rfl)).analyticWithinAt

/-- The eigenvalue version: if the operator is nonnegative (spectrum ≥ 0), its
finite resolvent trace is holomorphic on Ω. -/
theorem FstageFinite_holo_of_operator
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n)
    (hpos : ∀ i, 0 ≤ stageEigenvalues T hT hn i) :
    HolomorphicOnC (FstageFinite (stageEigenvalues T hT hn)) Ω :=
  FstageFinite_holo_on_Omega _ hpos

#print axioms stageEigenvalues
#print axioms FstageFinite
#print axioms FstageFinite_holo_on_Omega
#print axioms FstageFinite_holo_of_operator
