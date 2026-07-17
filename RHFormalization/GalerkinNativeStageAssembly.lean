import RHFormalization.GalerkinNativeStage
import RHFormalization.PerturbedGroundStateFormBound
import RHFormalization.PerturbedFormBound

namespace RHFormalization
noncomputable section
open LinearPMap Matrix ContinuousLinearMap RCLike

variable {N : ℕ}

/-- The prime CLM's adjoint equals itself (from self-adjointness). -/
theorem galerkinOpCLM_adjoint_eq (μ : Fin N → ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (M : ℝ) :
    ContinuousLinearMap.adjoint (galerkinOpCLM μ δ qs w L M) = galerkinOpCLM μ δ qs w L M := by
  have hsa := galerkinOpCLM_isSelfAdjoint μ δ qs w L M
  rw [IsSelfAdjoint] at hsa
  rw [← ContinuousLinearMap.star_eq_adjoint]
  exact hsa

/-- `galerkinOpPMap` is self-adjoint. -/
theorem galerkinOpPMap_isSelfAdjoint (μ : Fin N → ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (M : ℝ) :
    IsSelfAdjoint (galerkinOpPMap μ δ qs w L M) := by
  have hdense : Dense ((⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin N))) : Set (EuclideanSpace ℂ (Fin N))) := by
    rw [Submodule.top_coe]; exact dense_univ
  have key : (galerkinOpPMap μ δ qs w L M).adjoint
      = (ContinuousLinearMap.adjoint (galerkinOpCLM μ δ qs w L M)).toPMap ⊤ :=
    ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense (A := galerkinOpCLM μ δ qs w L M) hdense
  rw [LinearPMap.isSelfAdjoint_def, key, galerkinOpCLM_adjoint_eq]
  rfl

#print axioms galerkinOpPMap_isSelfAdjoint
end
end RHFormalization

namespace RHFormalization
noncomputable section
open LinearPMap Matrix ContinuousLinearMap RCLike

variable {N : ℕ}

/-- The PMap quadratic form equals the CLM quadratic form on the domain. -/
theorem galerkinOpPMap_form_eq (μ : Fin N → ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (M : ℝ)
    (x : (galerkinOpPMap μ δ qs w L M).domain) :
    (inner ℂ (x : EuclideanSpace ℂ (Fin N)) (galerkinOpPMap μ δ qs w L M x : EuclideanSpace ℂ (Fin N)))
      = inner ℂ (x : EuclideanSpace ℂ (Fin N)) (galerkinOpCLM μ δ qs w L M (x : EuclideanSpace ℂ (Fin N))) := by
  rfl

/-- **Lower-semibounded**: trivially, the bounded prime operator's quadratic form is
bounded below by `-‖CLM‖·‖x‖²`. -/
theorem galerkinOpPMap_lowerSemibounded (μ : Fin N → ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (M : ℝ) :
    LinearPMapLowerSemibounded (galerkinOpPMap μ δ qs w L M) := by
  refine ⟨‖galerkinOpCLM μ δ qs w L M‖, ?_⟩
  intro x
  rw [galerkinOpPMap_form_eq]
  have hbound : -(‖galerkinOpCLM μ δ qs w L M‖ * ‖(x : EuclideanSpace ℂ (Fin N))‖ ^ 2)
      ≤ RCLike.re (inner ℂ (x : EuclideanSpace ℂ (Fin N))
      (galerkinOpCLM μ δ qs w L M (x : EuclideanSpace ℂ (Fin N)))) := by
    have h1 : |RCLike.re (inner ℂ (x : EuclideanSpace ℂ (Fin N))
        (galerkinOpCLM μ δ qs w L M (x : EuclideanSpace ℂ (Fin N))))|
        ≤ ‖(x : EuclideanSpace ℂ (Fin N))‖ * ‖galerkinOpCLM μ δ qs w L M (x : EuclideanSpace ℂ (Fin N))‖ := by
      calc |RCLike.re (inner ℂ (x : EuclideanSpace ℂ (Fin N))
              (galerkinOpCLM μ δ qs w L M (x : EuclideanSpace ℂ (Fin N))))|
          ≤ ‖inner ℂ (x : EuclideanSpace ℂ (Fin N))
              (galerkinOpCLM μ δ qs w L M (x : EuclideanSpace ℂ (Fin N)))‖ := by
            exact RCLike.abs_re_le_norm _
        _ ≤ ‖(x : EuclideanSpace ℂ (Fin N))‖ * ‖galerkinOpCLM μ δ qs w L M (x : EuclideanSpace ℂ (Fin N))‖ :=
            norm_inner_le_norm _ _
    have h2 : ‖galerkinOpCLM μ δ qs w L M (x : EuclideanSpace ℂ (Fin N))‖
        ≤ ‖galerkinOpCLM μ δ qs w L M‖ * ‖(x : EuclideanSpace ℂ (Fin N))‖ :=
      (galerkinOpCLM μ δ qs w L M).le_opNorm _
    have h3 := abs_le.mp h1
    have hsq : ‖(x : EuclideanSpace ℂ (Fin N))‖ * (‖galerkinOpCLM μ δ qs w L M‖ * ‖(x : EuclideanSpace ℂ (Fin N))‖)
        = ‖galerkinOpCLM μ δ qs w L M‖ * ‖(x : EuclideanSpace ℂ (Fin N))‖ ^ 2 := by ring
    nlinarith [h3.1, h2, norm_nonneg (x : EuclideanSpace ℂ (Fin N)), norm_nonneg (galerkinOpCLM μ δ qs w L M)]
  calc -‖galerkinOpCLM μ δ qs w L M‖ * ‖(x : EuclideanSpace ℂ (Fin N))‖ ^ 2
      = -(‖galerkinOpCLM μ δ qs w L M‖ * ‖(x : EuclideanSpace ℂ (Fin N))‖ ^ 2) := by ring
    _ ≤ _ := hbound

#print axioms galerkinOpPMap_lowerSemibounded
end
end RHFormalization

namespace RHFormalization
noncomputable section
open LinearPMap Matrix ContinuousLinearMap RCLike

variable {N : ℕ}

/-- **Shifted nonnegativity under an explicit shift hypothesis.** If the quadratic
form of the prime operator is pointwise nonneg (the manuscript's globally-shifted
regime, guaranteed for `M` large enough), the operator is nonnegative. We take this
pointwise form-nonnegativity as the honest shift condition `hnn`. -/
theorem galerkinOpPMap_nonnegative (μ : Fin N → ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (M : ℝ)
    (hnn : ∀ y : EuclideanSpace ℂ (Fin N),
      0 ≤ RCLike.re (inner ℂ y (galerkinOpCLM μ δ qs w L M y))) :
    LinearPMapNonnegative (galerkinOpPMap μ δ qs w L M) := by
  intro x
  rw [galerkinOpPMap_form_eq]
  exact hnn (x : EuclideanSpace ℂ (Fin N))

/-- **The prime native D-stage**: the genuine self-adjoint, lower-semibounded,
nonnegative prime operator `H₀ + V_prime + M·I`, assembled as a `NativeUnboundedDStage`.
This is the real operator replacing `zeroNativeStage`. -/
def galerkinNativeStage (μ : Fin N → ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (M : ℝ)
    (hnn : ∀ y : EuclideanSpace ℂ (Fin N),
      0 ≤ RCLike.re (inner ℂ y (galerkinOpCLM μ δ qs w L M y))) :
    NativeUnboundedDStage (EuclideanSpace ℂ (Fin N)) :=
  { H := galerkinOpPMap μ δ qs w L M
    h_selfAdjoint := galerkinOpPMap_isSelfAdjoint μ δ qs w L M
    h_lowerSemibounded := galerkinOpPMap_lowerSemibounded μ δ qs w L M
    h_shiftedNonnegative := galerkinOpPMap_nonnegative μ δ qs w L M hnn }

#print axioms galerkinOpPMap_nonnegative
#print axioms galerkinNativeStage
end
end RHFormalization
