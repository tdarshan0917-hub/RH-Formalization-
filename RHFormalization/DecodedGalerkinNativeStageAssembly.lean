import RHFormalization.DecodedGalerkinNativeStage
import RHFormalization.PerturbedGroundStateFormBound
import RHFormalization.PerturbedFormBound

-- SENTINEL: decoded-native-stage-assembly-v1

namespace RHFormalization
noncomputable section
open LinearPMap Matrix ContinuousLinearMap RCLike

variable {N : ℕ}

/-- The prime CLM's adjoint equals itself (from self-adjointness). -/
theorem decodedGalerkinOpCLM_adjoint_eq (μ : Fin N → ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (M : ℝ) :
    ContinuousLinearMap.adjoint (decodedGalerkinOpCLM μ δ qs w L M) = decodedGalerkinOpCLM μ δ qs w L M := by
  have hsa := decodedGalerkinOpCLM_isSelfAdjoint μ δ qs w L M
  rw [IsSelfAdjoint] at hsa
  rw [← ContinuousLinearMap.star_eq_adjoint]
  exact hsa

/-- `decodedGalerkinOpPMap` is self-adjoint. -/
theorem decodedGalerkinOpPMap_isSelfAdjoint (μ : Fin N → ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (M : ℝ) :
    IsSelfAdjoint (decodedGalerkinOpPMap μ δ qs w L M) := by
  have hdense : Dense ((⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin N))) : Set (EuclideanSpace ℂ (Fin N))) := by
    rw [Submodule.top_coe]; exact dense_univ
  have key : (decodedGalerkinOpPMap μ δ qs w L M).adjoint
      = (ContinuousLinearMap.adjoint (decodedGalerkinOpCLM μ δ qs w L M)).toPMap ⊤ :=
    ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense (A := decodedGalerkinOpCLM μ δ qs w L M) hdense
  rw [LinearPMap.isSelfAdjoint_def, key, decodedGalerkinOpCLM_adjoint_eq]
  rfl

#print axioms decodedGalerkinOpPMap_isSelfAdjoint
end
end RHFormalization

namespace RHFormalization
noncomputable section
open LinearPMap Matrix ContinuousLinearMap RCLike

variable {N : ℕ}

/-- The PMap quadratic form equals the CLM quadratic form on the domain. -/
theorem decodedGalerkinOpPMap_form_eq (μ : Fin N → ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (M : ℝ)
    (x : (decodedGalerkinOpPMap μ δ qs w L M).domain) :
    (inner ℂ (x : EuclideanSpace ℂ (Fin N)) (decodedGalerkinOpPMap μ δ qs w L M x : EuclideanSpace ℂ (Fin N)))
      = inner ℂ (x : EuclideanSpace ℂ (Fin N)) (decodedGalerkinOpCLM μ δ qs w L M (x : EuclideanSpace ℂ (Fin N))) := by
  rfl

/-- **Lower-semibounded**: trivially, the bounded prime operator's quadratic form is
bounded below by `-‖CLM‖·‖x‖²`. -/
theorem decodedGalerkinOpPMap_lowerSemibounded (μ : Fin N → ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (M : ℝ) :
    LinearPMapLowerSemibounded (decodedGalerkinOpPMap μ δ qs w L M) := by
  refine ⟨‖decodedGalerkinOpCLM μ δ qs w L M‖, ?_⟩
  intro x
  rw [decodedGalerkinOpPMap_form_eq]
  have hbound : -(‖decodedGalerkinOpCLM μ δ qs w L M‖ * ‖(x : EuclideanSpace ℂ (Fin N))‖ ^ 2)
      ≤ RCLike.re (inner ℂ (x : EuclideanSpace ℂ (Fin N))
      (decodedGalerkinOpCLM μ δ qs w L M (x : EuclideanSpace ℂ (Fin N)))) := by
    have h1 : |RCLike.re (inner ℂ (x : EuclideanSpace ℂ (Fin N))
        (decodedGalerkinOpCLM μ δ qs w L M (x : EuclideanSpace ℂ (Fin N))))|
        ≤ ‖(x : EuclideanSpace ℂ (Fin N))‖ * ‖decodedGalerkinOpCLM μ δ qs w L M (x : EuclideanSpace ℂ (Fin N))‖ := by
      calc |RCLike.re (inner ℂ (x : EuclideanSpace ℂ (Fin N))
              (decodedGalerkinOpCLM μ δ qs w L M (x : EuclideanSpace ℂ (Fin N))))|
          ≤ ‖inner ℂ (x : EuclideanSpace ℂ (Fin N))
              (decodedGalerkinOpCLM μ δ qs w L M (x : EuclideanSpace ℂ (Fin N)))‖ := by
            exact RCLike.abs_re_le_norm _
        _ ≤ ‖(x : EuclideanSpace ℂ (Fin N))‖ * ‖decodedGalerkinOpCLM μ δ qs w L M (x : EuclideanSpace ℂ (Fin N))‖ :=
            norm_inner_le_norm _ _
    have h2 : ‖decodedGalerkinOpCLM μ δ qs w L M (x : EuclideanSpace ℂ (Fin N))‖
        ≤ ‖decodedGalerkinOpCLM μ δ qs w L M‖ * ‖(x : EuclideanSpace ℂ (Fin N))‖ :=
      (decodedGalerkinOpCLM μ δ qs w L M).le_opNorm _
    have h3 := abs_le.mp h1
    have hsq : ‖(x : EuclideanSpace ℂ (Fin N))‖ * (‖decodedGalerkinOpCLM μ δ qs w L M‖ * ‖(x : EuclideanSpace ℂ (Fin N))‖)
        = ‖decodedGalerkinOpCLM μ δ qs w L M‖ * ‖(x : EuclideanSpace ℂ (Fin N))‖ ^ 2 := by ring
    nlinarith [h3.1, h2, norm_nonneg (x : EuclideanSpace ℂ (Fin N)), norm_nonneg (decodedGalerkinOpCLM μ δ qs w L M)]
  calc -‖decodedGalerkinOpCLM μ δ qs w L M‖ * ‖(x : EuclideanSpace ℂ (Fin N))‖ ^ 2
      = -(‖decodedGalerkinOpCLM μ δ qs w L M‖ * ‖(x : EuclideanSpace ℂ (Fin N))‖ ^ 2) := by ring
    _ ≤ _ := hbound

#print axioms decodedGalerkinOpPMap_lowerSemibounded
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
theorem decodedGalerkinOpPMap_nonnegative (μ : Fin N → ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (M : ℝ)
    (hnn : ∀ y : EuclideanSpace ℂ (Fin N),
      0 ≤ RCLike.re (inner ℂ y (decodedGalerkinOpCLM μ δ qs w L M y))) :
    LinearPMapNonnegative (decodedGalerkinOpPMap μ δ qs w L M) := by
  intro x
  rw [decodedGalerkinOpPMap_form_eq]
  exact hnn (x : EuclideanSpace ℂ (Fin N))

/-- **The prime native D-stage**: the genuine self-adjoint, lower-semibounded,
nonnegative prime operator `H₀ + V_prime + M·I`, assembled as a `NativeUnboundedDStage`.
This is the real operator replacing `zeroNativeStage`. -/
def decodedGalerkinNativeStage (μ : Fin N → ℝ) (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (M : ℝ)
    (hnn : ∀ y : EuclideanSpace ℂ (Fin N),
      0 ≤ RCLike.re (inner ℂ y (decodedGalerkinOpCLM μ δ qs w L M y))) :
    NativeUnboundedDStage (EuclideanSpace ℂ (Fin N)) :=
  { H := decodedGalerkinOpPMap μ δ qs w L M
    h_selfAdjoint := decodedGalerkinOpPMap_isSelfAdjoint μ δ qs w L M
    h_lowerSemibounded := decodedGalerkinOpPMap_lowerSemibounded μ δ qs w L M
    h_shiftedNonnegative := decodedGalerkinOpPMap_nonnegative μ δ qs w L M hnn }

#print axioms decodedGalerkinOpPMap_nonnegative
#print axioms decodedGalerkinNativeStage
end
end RHFormalization
