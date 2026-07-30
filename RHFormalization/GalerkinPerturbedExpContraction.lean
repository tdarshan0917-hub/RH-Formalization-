-- SENTINEL: galerkin-perturbed-exp-contraction-v2
import RHFormalization.GalerkinMatrices
import Mathlib

/-!
# E(s) contraction: sum-of-squares bound for the Galerkin semigroups
TARGET: `expNeg_mulVec_sumSq_le` and the two legs (free / perturbed), exponent
orientation matching QuadRemainderSandwichNormSplit verbatim.
DOWNSTREAM CONSUMER: quadRemainder integrand bound → h_conv along α.
SEMANTIC: Grönwall: f(s)=‖E(s)a‖² has f' = −2·form_A(E(s)a) ≤ 0 ⟹ f(s) ≤ f(0).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section
open Matrix
open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedSpace
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- Entry-of-mulVec as a linear map in the matrix argument. -/
noncomputable def mulVecEntryLM (a : Fin N → ℝ) (i : Fin N) :
    Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ where
  toFun M := M.mulVec a i
  map_add' M M' := by
    show ((M + M').mulVec a) i = (M.mulVec a) i + (M'.mulVec a) i
    first
      | rw [Matrix.add_mulVec, Pi.add_apply]
      | simp [Matrix.add_mulVec]
      | simp [Matrix.mulVec, Matrix.dotProduct, add_mul,
          Finset.sum_add_distrib]
      | simp [Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib]
  map_smul' c M := by
    show ((c • M).mulVec a) i = (RingHom.id ℝ) c • ((M.mulVec a) i)
    first
      | rw [Matrix.smul_mulVec_assoc, Pi.smul_apply, RingHom.id_apply]
      | simp [Matrix.smul_mulVec_assoc]
      | simp [Matrix.mulVec, Matrix.dotProduct, Finset.mul_sum, mul_assoc]
      | simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem mulVecEntryLM_apply (a : Fin N → ℝ) (i : Fin N)
    (M : Matrix (Fin N) (Fin N) ℝ) :
    mulVecEntryLM a i M = M.mulVec a i := rfl

/-- Derivative of `t ↦ exp (t • (-A))` with the factor on the left. -/
theorem hasDerivAt_exp_neg_smul
    (A : Matrix (Fin N) (Fin N) ℝ) (hN : 0 < N) (s : ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • (-A)))
      ((-A) * NormedSpace.exp (s • (-A))) s := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hcomm : Commute (-A) (NormedSpace.exp (s • (-A))) := by
    have h1 : Commute (-A) (s • (-A)) := (Commute.refl (-A)).smul_right s
    first
      | exact h1.exp_right
      | exact Commute.exp_right h1
      | exact h1.exp_right ℝ
  first
    | exact NormedSpace.hasDerivAt_exp_smul_const' (-A) s
    | exact hasDerivAt_exp_smul_const' (-A) s
    | { have h := NormedSpace.hasDerivAt_exp_smul_const (-A) s
        rwa [← hcomm.eq] at h }
    | { have h := hasDerivAt_exp_smul_const (-A) s
        rwa [← hcomm.eq] at h }
    | { have h := NormedSpace.hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) s
        rwa [← hcomm.eq] at h }

/-- Componentwise derivative of the semigroup orbit. -/
theorem hasDerivAt_exp_neg_smul_mulVec
    (A : Matrix (Fin N) (Fin N) ℝ) (hN : 0 < N)
    (a : Fin N → ℝ) (i : Fin N) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • (-A))).mulVec a i)
      (((-A) * NormedSpace.exp (s • (-A))).mulVec a i) s := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hexp := hasDerivAt_exp_neg_smul (N := N) A hN s
  have hL :=
    ((mulVecEntryLM (N := N) a i).toContinuousLinearMap).hasFDerivAt
      (x := NormedSpace.exp (s • (-A)))
  have hcomp := hL.comp_hasDerivAt s hexp
  first
    | simpa [mulVecEntryLM_apply, LinearMap.coe_toContinuousLinearMap]
        using hcomp
    | simpa [mulVecEntryLM_apply] using hcomp
    | simpa [mulVecEntryLM, LinearMap.coe_toContinuousLinearMap] using hcomp

/-- Summed orbit derivative, stated directly in lambda form. -/
theorem hasDerivAt_sumSq_orbit
    (A : Matrix (Fin N) (Fin N) ℝ) (hN : 0 < N)
    (a : Fin N → ℝ) (t : ℝ) :
    HasDerivAt
      (fun v : ℝ => ∑ i : Fin N,
        (NormedSpace.exp (v • (-A))).mulVec a i
          * (NormedSpace.exp (v • (-A))).mulVec a i)
      (∑ i : Fin N,
        (((-A) * NormedSpace.exp (t • (-A))).mulVec a i
            * (NormedSpace.exp (t • (-A))).mulVec a i
          + (NormedSpace.exp (t • (-A))).mulVec a i
            * (((-A) * NormedSpace.exp (t • (-A))).mulVec a i))) t := by
  have hterm : ∀ i : Fin N,
      HasDerivAt
        (fun v : ℝ =>
          (NormedSpace.exp (v • (-A))).mulVec a i
            * (NormedSpace.exp (v • (-A))).mulVec a i)
        ((((-A) * NormedSpace.exp (t • (-A))).mulVec a i
            * (NormedSpace.exp (t • (-A))).mulVec a i
          + (NormedSpace.exp (t • (-A))).mulVec a i
            * (((-A) * NormedSpace.exp (t • (-A))).mulVec a i))) t :=
    fun i => (hasDerivAt_exp_neg_smul_mulVec A hN a i t).mul
      (hasDerivAt_exp_neg_smul_mulVec A hN a i t)
  have h := HasDerivAt.sum
    (u := (Finset.univ : Finset (Fin N)))
    (fun i _ => hterm i)
  first
    | simpa [Finset.sum_fn] using h
    | simpa [Finset.sum_apply] using h
    | { have heq :
          (∑ i ∈ (Finset.univ : Finset (Fin N)),
            fun v : ℝ =>
              (NormedSpace.exp (v • (-A))).mulVec a i
                * (NormedSpace.exp (v • (-A))).mulVec a i)
          = fun v : ℝ => ∑ i : Fin N,
              (NormedSpace.exp (v • (-A))).mulVec a i
                * (NormedSpace.exp (v • (-A))).mulVec a i := by
          funext v
          simp [Finset.sum_apply]
        rwa [heq] at h }

/-- **THE CONTRACTION.** Nonneg quadratic form of `A` ⟹ `exp (s • (-A))` is an
ℓ²-contraction (sum-of-squares form) for `0 ≤ s`. Instance-free boundary. -/
theorem expNeg_mulVec_sumSq_le
    (A : Matrix (Fin N) (Fin N) ℝ) (hN : 0 < N)
    (hform : ∀ v : Fin N → ℝ,
      0 ≤ ∑ m : Fin N, ∑ n : Fin N, v m * v n * A m n)
    (a : Fin N → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    ∑ i : Fin N, ((NormedSpace.exp (s • (-A))).mulVec a i) ^ 2
      ≤ ∑ i : Fin N, (a i) ^ 2 := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  simp only [pow_two]
  have hder := fun t : ℝ => hasDerivAt_sumSq_orbit A hN a t
  have hdiff : Differentiable ℝ
      (fun v : ℝ => ∑ i : Fin N,
        (NormedSpace.exp (v • (-A))).mulVec a i
          * (NormedSpace.exp (v • (-A))).mulVec a i) :=
    fun t => (hder t).differentiableAt
  have hD0 : ∀ t : ℝ,
      (∑ i : Fin N,
        (((-A) * NormedSpace.exp (t • (-A))).mulVec a i
            * (NormedSpace.exp (t • (-A))).mulVec a i
          + (NormedSpace.exp (t • (-A))).mulVec a i
            * (((-A) * NormedSpace.exp (t • (-A))).mulVec a i))) ≤ 0 := by
    intro t
    set b : Fin N → ℝ := (NormedSpace.exp (t • (-A))).mulVec a with hb
    have hw : ((-A) * NormedSpace.exp (t • (-A))).mulVec a
        = -(A.mulVec b) := by
      rw [hb]
      first
        | rw [Matrix.neg_mul, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]
        | rw [Matrix.neg_mul, Matrix.neg_mulVec, Matrix.mulVec_mulVec]
        | rw [Matrix.neg_mul, ← Matrix.mulVec_mulVec, Matrix.neg_mulVec]
        | rw [Matrix.neg_mul, Matrix.mulVec_mulVec, Matrix.neg_mulVec]
        | simp [Matrix.neg_mul, Matrix.neg_mulVec, Matrix.mulVec_mulVec]
    have hterm : ∀ i : Fin N,
        (((-A) * NormedSpace.exp (t • (-A))).mulVec a i * b i
          + b i * (((-A) * NormedSpace.exp (t • (-A))).mulVec a i))
        = -(2 * (b i * (A.mulVec b) i)) := by
      intro i
      rw [hw]
      simp only [Pi.neg_apply]
      ring
    have hkey : ∑ i : Fin N, b i * (A.mulVec b) i
        = ∑ m : Fin N, ∑ n : Fin N, b m * b n * A m n := by
      apply Finset.sum_congr rfl
      intro m _
      have happ : (A.mulVec b) m = ∑ n : Fin N, A m n * b n := by
        first
          | simp [Matrix.mulVec, Matrix.dotProduct]
          | simp [Matrix.mulVec, dotProduct]
          | rfl
      rw [happ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    have hsum :
        (∑ i : Fin N,
          (((-A) * NormedSpace.exp (t • (-A))).mulVec a i * b i
            + b i * (((-A) * NormedSpace.exp (t • (-A))).mulVec a i)))
        = -(2 * ∑ m : Fin N, ∑ n : Fin N, b m * b n * A m n) := by
      rw [Finset.sum_congr rfl (fun i _ => hterm i)]
      rw [← hkey]
      first
        | rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        | simp [Finset.mul_sum]
        | simp [Finset.mul_sum, neg_mul]
        | { rw [Finset.mul_sum]
            exact (Finset.sum_neg_distrib).symm }
    rw [hb] at hsum
    rw [hsum]
    have hS := hform ((NormedSpace.exp (t • (-A))).mulVec a)
    linarith
  have hanti :
      AntitoneOn
        (fun v : ℝ => ∑ i : Fin N,
          (NormedSpace.exp (v • (-A))).mulVec a i
            * (NormedSpace.exp (v • (-A))).mulVec a i)
        (Set.Icc (0:ℝ) s) := by
    first
      | exact antitoneOn_of_deriv_nonpos (convex_Icc (0:ℝ) s)
          hdiff.continuous.continuousOn
          (fun t _ => (hdiff t).differentiableWithinAt)
          (fun t _ => by rw [(hder t).deriv]; exact hD0 t)
      | exact antitoneOn_of_deriv_nonpos (convex_Icc (0:ℝ) s)
          hdiff.continuous.continuousOn
          hdiff.differentiableOn
          (fun t _ => by rw [(hder t).deriv]; exact hD0 t)
      | exact antitoneOn_of_deriv_nonpos (convex_Icc (0:ℝ) s)
          hdiff.continuous.continuousOn
          (fun t _ => by rw [(hder t).deriv]; exact hD0 t)
  have hle := hanti (Set.left_mem_Icc.mpr hs) (Set.right_mem_Icc.mpr hs) hs
  have h0 :
      ∑ i : Fin N,
        (NormedSpace.exp ((0:ℝ) • (-A))).mulVec a i
          * (NormedSpace.exp ((0:ℝ) • (-A))).mulVec a i
      = ∑ i : Fin N, a i * a i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec]
  calc ∑ i : Fin N,
        (NormedSpace.exp (s • (-A))).mulVec a i
          * (NormedSpace.exp (s • (-A))).mulVec a i
      ≤ ∑ i : Fin N,
          (NormedSpace.exp ((0:ℝ) • (-A))).mulVec a i
            * (NormedSpace.exp ((0:ℝ) • (-A))).mulVec a i := hle
    _ = ∑ i : Fin N, a i * a i := h0

/-- The free kinetic form is nonnegative: diagonal of squares. -/
theorem galerkinK_form_nonneg (L : ℝ) (v : Fin N → ℝ) :
    0 ≤ ∑ m : Fin N, ∑ n : Fin N, v m * v n * galerkinK (N := N) L m n := by
  have hterm : ∀ m : Fin N,
      ∑ n : Fin N, v m * v n * galerkinK (N := N) L m n
        = v m ^ 2 * ((((m : ℝ) + 1) * Real.pi / L) ^ 2) := by
    intro m
    rw [Finset.sum_eq_single m]
    · unfold galerkinK
      rw [Matrix.diagonal_apply_eq]
      ring
    · intro n _ hnm
      unfold galerkinK
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hnm), mul_zero]
    · intro hm
      exact absurd (Finset.mem_univ m) hm
  rw [Finset.sum_congr rfl (fun m _ => hterm m)]
  apply Finset.sum_nonneg
  intro m _
  positivity

/-- Nonneg K-form + nonneg V-form ⟹ nonneg (K+V)-form. -/
theorem galerkinKplusV_form_nonneg
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ)
    (hV : ∀ v : Fin N → ℝ,
      0 ≤ ∑ m : Fin N, ∑ n : Fin N,
        v m * v n * galerkinV (N := N) δ qs w L m n)
    (v : Fin N → ℝ) :
    0 ≤ ∑ m : Fin N, ∑ n : Fin N,
        v m * v n
          * (galerkinK (N := N) L + galerkinV (N := N) δ qs w L) m n := by
  have hsplit :
      ∑ m : Fin N, ∑ n : Fin N,
        v m * v n
          * (galerkinK (N := N) L + galerkinV (N := N) δ qs w L) m n
      = (∑ m : Fin N, ∑ n : Fin N, v m * v n * galerkinK (N := N) L m n)
        + ∑ m : Fin N, ∑ n : Fin N,
            v m * v n * galerkinV (N := N) δ qs w L m n := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [Matrix.add_apply]
    ring
  rw [hsplit]
  exact add_nonneg (galerkinK_form_nonneg L v) (hV v)

/-- **E(s) leg.** Perturbed-semigroup contraction, exponent orientation exactly
as in QuadRemainderSandwichNormSplit: `exp (s • -(galerkinK + galerkinV))`. -/
theorem galerkinPerturbedExp_mulVec_sumSq_le
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (hN : 0 < N)
    (hV : ∀ v : Fin N → ℝ,
      0 ≤ ∑ m : Fin N, ∑ n : Fin N,
        v m * v n * galerkinV (N := N) δ qs w L m n)
    (a : Fin N → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    ∑ i : Fin N,
      ((NormedSpace.exp
          (s • -(galerkinK (N := N) L
            + galerkinV (N := N) δ qs w L))).mulVec a i) ^ 2
      ≤ ∑ i : Fin N, (a i) ^ 2 :=
  expNeg_mulVec_sumSq_le _ hN (galerkinKplusV_form_nonneg δ qs w L hV) a hs

/-- **Free leg.** Free-heat contraction: `exp (r • -galerkinK)`. -/
theorem galerkinFreeExp_mulVec_sumSq_le
    (L : ℝ) (hN : 0 < N) (a : Fin N → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ∑ i : Fin N,
      ((NormedSpace.exp (r • -(galerkinK (N := N) L))).mulVec a i) ^ 2
      ≤ ∑ i : Fin N, (a i) ^ 2 :=
  expNeg_mulVec_sumSq_le _ hN (galerkinK_form_nonneg L) a hr

#print axioms mulVecEntryLM_apply
#print axioms hasDerivAt_exp_neg_smul
#print axioms hasDerivAt_exp_neg_smul_mulVec
#print axioms hasDerivAt_sumSq_orbit
#print axioms expNeg_mulVec_sumSq_le
#print axioms galerkinK_form_nonneg
#print axioms galerkinKplusV_form_nonneg
#print axioms galerkinPerturbedExp_mulVec_sumSq_le
#print axioms galerkinFreeExp_mulVec_sumSq_le
