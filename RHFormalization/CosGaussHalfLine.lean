import RHFormalization.CosGaussPartitionError
import RHFormalization.GaussianIoiTail
import RHFormalization.IntegralCosGaussianReal
import Mathlib

/-!
# Half-line cosine-Gaussian landing — G3-ii-b sub-brick 5b
SENTINEL: cosgauss-halfline-v2

ROUTE CARD
1. `integral_cosGauss_Ioi`: ∫_{Ioi 0} cosGauss = (1/2)√(π/t)e^{−a²/4t} —
   evenness halving of the banked integral_cos_mul_gaussian_real.
2. `cosGauss_interval_vs_Ioi`: |∫₀^B − ∫_{Ioi 0}| ≤ tail(B) — the banked
   Gaussian Ioi tail dominates the difference.
3. `cosGauss_sum_vs_halfline` — THE COSINE COMPARISON (the gate's last
   lemma at the integrand level): |h·Σ_{k<N} f((k+1)h) − (1/2)√(π/t)e^{−a²/4t}|
   ≤ h(1+|a|√(π/t)) + e^{−t(Nh)²}/(t·Nh).
-/

set_option autoImplicit false

namespace RHFormalization

open MeasureTheory

/-- cosGauss is even in ξ. -/
theorem cosGauss_even (t a : ℝ) : ∀ ξ : ℝ, cosGauss t a (-ξ) = cosGauss t a ξ := by
  intro ξ
  unfold cosGauss
  rw [neg_sq]
  congr 1
  rw [neg_mul, Real.cos_neg]

/-- cosGauss is integrable on ℝ (Gaussian domination). -/
theorem cosGauss_integrable (t a : ℝ) (ht : 0 < t) :
    Integrable (cosGauss t a) := by
  have hg : Integrable (fun ξ : ℝ => Real.exp (-t * ξ ^ 2)) :=
    integrable_exp_neg_mul_sq ht
  apply hg.mono
  · exact ((Real.continuous_exp.comp (by continuity)).mul
      (Real.continuous_cos.comp (by continuity))).aestronglyMeasurable
  · filter_upwards with ξ
    unfold cosGauss
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    have h1 : |Real.exp (-(t * ξ ^ 2))| = Real.exp (-(t * ξ ^ 2)) :=
      abs_of_pos (Real.exp_pos _)
    have h2 : |Real.exp (-t * ξ ^ 2)| = Real.exp (-t * ξ ^ 2) :=
      abs_of_pos (Real.exp_pos _)
    rw [h1, h2]
    have hshape : Real.exp (-(t * ξ ^ 2)) = Real.exp (-t * ξ ^ 2) := by
      congr 1; ring
    rw [hshape]
    have hcos : |Real.cos (ξ * a)| ≤ 1 :=
      abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    calc Real.exp (-t * ξ ^ 2) * |Real.cos (ξ * a)|
        ≤ Real.exp (-t * ξ ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left hcos (Real.exp_pos _).le
      _ = Real.exp (-t * ξ ^ 2) := by ring

/-- **Evenness halving**: the Ioi-integral is half the banked full line. -/
theorem integral_cosGauss_Ioi (t a : ℝ) (ht : 0 < t) :
    (∫ ξ in Set.Ioi (0:ℝ), cosGauss t a ξ)
      = (1 / 2) * (Real.sqrt (Real.pi / t) * Real.exp (-a ^ 2 / (4 * t))) := by
  have hint := cosGauss_integrable t a ht
  -- full line = Iic 0 + Ioi 0
  have hsplit : (∫ ξ : ℝ, cosGauss t a ξ)
      = (∫ ξ in Set.Iic (0:ℝ), cosGauss t a ξ)
        + ∫ ξ in Set.Ioi (0:ℝ), cosGauss t a ξ := by
    have hcompl : (Set.Iic (0:ℝ))ᶜ = Set.Ioi (0:ℝ) := Set.compl_Iic
    rw [← hcompl]
    exact (MeasureTheory.integral_add_compl measurableSet_Iic hint).symm
  -- reflection: ∫_{Iic 0} = ∫_{Ioi 0} by evenness
  have hreflect : (∫ ξ in Set.Iic (0:ℝ), cosGauss t a ξ)
      = ∫ ξ in Set.Ioi (0:ℝ), cosGauss t a ξ := by
    have h := integral_comp_neg_Iic (0:ℝ) (cosGauss t a)
    rw [neg_zero] at h
    rw [← h]
    apply setIntegral_congr_fun measurableSet_Iic
    intro ξ _
    exact (cosGauss_even t a ξ).symm
  -- the full line is the banked evaluation
  have hfull : (∫ ξ : ℝ, cosGauss t a ξ)
      = Real.sqrt (Real.pi / t) * Real.exp (-a ^ 2 / (4 * t)) := by
    have hb := integral_cos_mul_gaussian_real a t ht
    rw [← hb]
    apply integral_congr_ae
    filter_upwards with ξ
    unfold cosGauss
    rw [mul_comm (Real.exp _) (Real.cos _)]
    congr 2
    · rw [mul_comm]
    · ring
  rw [hsplit, hreflect] at hfull
  linarith

/-- **Finite-to-Ioi comparison**: the truncation error is the Gaussian tail. -/
theorem cosGauss_interval_vs_Ioi (t a B : ℝ) (ht : 0 < t) (hB : 0 < B) :
    |(∫ ξ in (0:ℝ)..B, cosGauss t a ξ)
        - ∫ ξ in Set.Ioi (0:ℝ), cosGauss t a ξ|
      ≤ Real.exp (-(t * B ^ 2)) / (t * B) := by
  have hint := cosGauss_integrable t a ht
  have hIoiB : IntegrableOn (cosGauss t a) (Set.Ioi B) volume :=
    hint.integrableOn
  have hIoi0 : IntegrableOn (cosGauss t a) (Set.Ioi (0:ℝ)) volume :=
    hint.integrableOn
  -- ∫_{Ioi 0} = ∫_{Ioc 0 B} + ∫_{Ioi B}
  have hsplit : (∫ ξ in Set.Ioi (0:ℝ), cosGauss t a ξ)
      = (∫ ξ in Set.Ioc (0:ℝ) B, cosGauss t a ξ)
        + ∫ ξ in Set.Ioi B, cosGauss t a ξ := by
    rw [← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi hint.integrableOn hint.integrableOn]
    congr 1
    rw [Set.Ioc_union_Ioi_eq_Ioi hB.le]
  have hival : (∫ ξ in (0:ℝ)..B, cosGauss t a ξ)
      = ∫ ξ in Set.Ioc (0:ℝ) B, cosGauss t a ξ :=
    intervalIntegral.integral_of_le hB.le
  rw [hival, hsplit]
  have habs : |(∫ ξ in Set.Ioc (0:ℝ) B, cosGauss t a ξ)
      - ((∫ ξ in Set.Ioc (0:ℝ) B, cosGauss t a ξ)
        + ∫ ξ in Set.Ioi B, cosGauss t a ξ)|
      = |∫ ξ in Set.Ioi B, cosGauss t a ξ| := by
    rw [show (∫ ξ in Set.Ioc (0:ℝ) B, cosGauss t a ξ)
        - ((∫ ξ in Set.Ioc (0:ℝ) B, cosGauss t a ξ)
          + ∫ ξ in Set.Ioi B, cosGauss t a ξ)
      = -(∫ ξ in Set.Ioi B, cosGauss t a ξ) by ring]
    exact abs_neg _
  rw [habs]
  -- |∫_{Ioi B} cosGauss| ≤ ∫_{Ioi B} e^{−tξ²} ≤ tail bound
  calc |∫ ξ in Set.Ioi B, cosGauss t a ξ|
      ≤ ∫ ξ in Set.Ioi B, |cosGauss t a ξ| := by
        exact abs_integral_le_integral_abs
    _ ≤ ∫ ξ in Set.Ioi B, Real.exp (-t * ξ ^ 2) := by
        apply setIntegral_mono_on hIoiB.abs
          (integrable_exp_neg_mul_sq ht).integrableOn measurableSet_Ioi
        intro ξ _
        unfold cosGauss
        rw [abs_mul]
        have h1 : |Real.exp (-(t * ξ ^ 2))| = Real.exp (-t * ξ ^ 2) := by
          rw [abs_of_pos (Real.exp_pos _)]
          congr 1; ring
        rw [h1]
        have hcos : |Real.cos (ξ * a)| ≤ 1 :=
          abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
        calc Real.exp (-t * ξ ^ 2) * |Real.cos (ξ * a)|
            ≤ Real.exp (-t * ξ ^ 2) * 1 :=
              mul_le_mul_of_nonneg_left hcos (Real.exp_pos _).le
          _ = Real.exp (-t * ξ ^ 2) := by ring
    _ ≤ Real.exp (-(t * B ^ 2)) / (t * B) :=
        gaussian_Ioi_tail_le t B ht hB

/-- **THE COSINE COMPARISON — the gate's last lemma (integrand level)**. -/
theorem cosGauss_sum_vs_halfline (t a h : ℝ) (ht : 0 < t) (hh : 0 < h)
    (N : ℕ) (hN : 0 < N) :
    |(∑ k ∈ Finset.range N, h * cosGauss t a (((k : ℝ) + 1) * h))
        - (1 / 2) * (Real.sqrt (Real.pi / t) * Real.exp (-a ^ 2 / (4 * t)))|
      ≤ h * (1 + |a| * Real.sqrt (Real.pi / t))
        + Real.exp (-(t * ((N : ℝ) * h) ^ 2)) / (t * ((N : ℝ) * h)) := by
  have hNh : (0:ℝ) < (N : ℝ) * h := by positivity
  have h1 := cosGauss_partition_error t a h ht hh N
  have h2 := cosGauss_interval_vs_Ioi t a ((N : ℝ) * h) ht hNh
  rw [integral_cosGauss_Ioi t a ht] at h2
  calc |(∑ k ∈ Finset.range N, h * cosGauss t a (((k : ℝ) + 1) * h))
        - (1 / 2) * (Real.sqrt (Real.pi / t) * Real.exp (-a ^ 2 / (4 * t)))|
      ≤ |(∑ k ∈ Finset.range N, h * cosGauss t a (((k : ℝ) + 1) * h))
            - ∫ x in (0:ℝ)..((N : ℝ) * h), cosGauss t a x|
          + |(∫ x in (0:ℝ)..((N : ℝ) * h), cosGauss t a x)
            - (1 / 2) * (Real.sqrt (Real.pi / t)
                * Real.exp (-a ^ 2 / (4 * t)))| := by
        exact abs_sub_le _ _ _
    _ ≤ h * (1 + |a| * Real.sqrt (Real.pi / t))
          + Real.exp (-(t * ((N : ℝ) * h) ^ 2)) / (t * ((N : ℝ) * h)) :=
        add_le_add h1 h2

#print axioms cosGauss_even
#print axioms cosGauss_integrable
#print axioms integral_cosGauss_Ioi
#print axioms cosGauss_interval_vs_Ioi
#print axioms cosGauss_sum_vs_halfline

end RHFormalization
