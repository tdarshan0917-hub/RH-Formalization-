import RHFormalization.PrimeNativeStage
import RHFormalization.PerturbedGroundStateFormBound
import RHFormalization.PerturbedFormBound

namespace RHFormalization
noncomputable section
open LinearPMap Matrix ContinuousLinearMap RCLike

variable {N : ℕ}

/-- The prime CLM's adjoint equals itself (from self-adjointness). -/
theorem primeOpCLM_adjoint_eq (μ : Fin N → ℝ) (w : Fin N → ℝ) (M : ℝ) :
    ContinuousLinearMap.adjoint (primeOpCLM μ w M) = primeOpCLM μ w M := by
  have hsa := primeOpCLM_isSelfAdjoint μ w M
  rw [IsSelfAdjoint] at hsa
  rw [← ContinuousLinearMap.star_eq_adjoint]
  exact hsa

/-- `primeOpPMap` is self-adjoint. -/
theorem primeOpPMap_isSelfAdjoint (μ : Fin N → ℝ) (w : Fin N → ℝ) (M : ℝ) :
    IsSelfAdjoint (primeOpPMap μ w M) := by
  have hdense : Dense ((⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin N))) : Set (EuclideanSpace ℂ (Fin N))) := by
    rw [Submodule.top_coe]; exact dense_univ
  have key : (primeOpPMap μ w M).adjoint
      = (ContinuousLinearMap.adjoint (primeOpCLM μ w M)).toPMap ⊤ :=
    ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense (A := primeOpCLM μ w M) hdense
  rw [LinearPMap.isSelfAdjoint_def, key, primeOpCLM_adjoint_eq]
  rfl

#print axioms primeOpPMap_isSelfAdjoint
end
end RHFormalization

namespace RHFormalization
noncomputable section
open LinearPMap Matrix ContinuousLinearMap RCLike

variable {N : ℕ}

/-- The PMap quadratic form equals the CLM quadratic form on the domain. -/
theorem primeOpPMap_form_eq (μ : Fin N → ℝ) (w : Fin N → ℝ) (M : ℝ)
    (x : (primeOpPMap μ w M).domain) :
    (inner ℂ (x : EuclideanSpace ℂ (Fin N)) (primeOpPMap μ w M x : EuclideanSpace ℂ (Fin N)))
      = inner ℂ (x : EuclideanSpace ℂ (Fin N)) (primeOpCLM μ w M (x : EuclideanSpace ℂ (Fin N))) := by
  rfl

/-- **Lower-semibounded**: trivially, the bounded prime operator's quadratic form is
bounded below by `-‖CLM‖·‖x‖²`. -/
theorem primeOpPMap_lowerSemibounded (μ : Fin N → ℝ) (w : Fin N → ℝ) (M : ℝ) :
    LinearPMapLowerSemibounded (primeOpPMap μ w M) := by
  refine ⟨‖primeOpCLM μ w M‖, ?_⟩
  intro x
  rw [primeOpPMap_form_eq]
  have hbound : -(‖primeOpCLM μ w M‖ * ‖(x : EuclideanSpace ℂ (Fin N))‖ ^ 2)
      ≤ RCLike.re (inner ℂ (x : EuclideanSpace ℂ (Fin N))
      (primeOpCLM μ w M (x : EuclideanSpace ℂ (Fin N)))) := by
    have h1 : |RCLike.re (inner ℂ (x : EuclideanSpace ℂ (Fin N))
        (primeOpCLM μ w M (x : EuclideanSpace ℂ (Fin N))))|
        ≤ ‖(x : EuclideanSpace ℂ (Fin N))‖ * ‖primeOpCLM μ w M (x : EuclideanSpace ℂ (Fin N))‖ := by
      calc |RCLike.re (inner ℂ (x : EuclideanSpace ℂ (Fin N))
              (primeOpCLM μ w M (x : EuclideanSpace ℂ (Fin N))))|
          ≤ ‖inner ℂ (x : EuclideanSpace ℂ (Fin N))
              (primeOpCLM μ w M (x : EuclideanSpace ℂ (Fin N)))‖ := by
            exact RCLike.abs_re_le_norm _
        _ ≤ ‖(x : EuclideanSpace ℂ (Fin N))‖ * ‖primeOpCLM μ w M (x : EuclideanSpace ℂ (Fin N))‖ :=
            norm_inner_le_norm _ _
    have h2 : ‖primeOpCLM μ w M (x : EuclideanSpace ℂ (Fin N))‖
        ≤ ‖primeOpCLM μ w M‖ * ‖(x : EuclideanSpace ℂ (Fin N))‖ :=
      (primeOpCLM μ w M).le_opNorm _
    have h3 := abs_le.mp h1
    have hsq : ‖(x : EuclideanSpace ℂ (Fin N))‖ * (‖primeOpCLM μ w M‖ * ‖(x : EuclideanSpace ℂ (Fin N))‖)
        = ‖primeOpCLM μ w M‖ * ‖(x : EuclideanSpace ℂ (Fin N))‖ ^ 2 := by ring
    nlinarith [h3.1, h2, norm_nonneg (x : EuclideanSpace ℂ (Fin N)), norm_nonneg (primeOpCLM μ w M)]
  calc -‖primeOpCLM μ w M‖ * ‖(x : EuclideanSpace ℂ (Fin N))‖ ^ 2
      = -(‖primeOpCLM μ w M‖ * ‖(x : EuclideanSpace ℂ (Fin N))‖ ^ 2) := by ring
    _ ≤ _ := hbound

#print axioms primeOpPMap_lowerSemibounded
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
theorem primeOpPMap_nonnegative (μ : Fin N → ℝ) (w : Fin N → ℝ) (M : ℝ)
    (hnn : ∀ y : EuclideanSpace ℂ (Fin N),
      0 ≤ RCLike.re (inner ℂ y (primeOpCLM μ w M y))) :
    LinearPMapNonnegative (primeOpPMap μ w M) := by
  intro x
  rw [primeOpPMap_form_eq]
  exact hnn (x : EuclideanSpace ℂ (Fin N))

/-- **The prime native D-stage**: the genuine self-adjoint, lower-semibounded,
nonnegative prime operator `H₀ + V_prime + M·I`, assembled as a `NativeUnboundedDStage`.
This is the real operator replacing `zeroNativeStage`. -/
def primeNativeStage (μ : Fin N → ℝ) (w : Fin N → ℝ) (M : ℝ)
    (hnn : ∀ y : EuclideanSpace ℂ (Fin N),
      0 ≤ RCLike.re (inner ℂ y (primeOpCLM μ w M y))) :
    NativeUnboundedDStage (EuclideanSpace ℂ (Fin N)) :=
  { H := primeOpPMap μ w M
    h_selfAdjoint := primeOpPMap_isSelfAdjoint μ w M
    h_lowerSemibounded := primeOpPMap_lowerSemibounded μ w M
    h_shiftedNonnegative := primeOpPMap_nonnegative μ w M hnn }

#print axioms primeOpPMap_nonnegative
#print axioms primeNativeStage
end
end RHFormalization
