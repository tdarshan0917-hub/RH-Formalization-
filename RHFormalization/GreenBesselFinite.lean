import RHFormalization.DirichletGreenKernel
import RHFormalization.DirichletLaplacianEigenpairs
import RHFormalization.DirichletEigenfunOrthogonal
import RHFormalization.DirichletEigenfunNorm
import RHFormalization.GreenSineCoefficient
import RHFormalization.GalerkinDuhamelUniformBound

/-!
# RHFormalization.GreenBesselFinite
**P2-B3: the finite-stage Bessel inequality for the Dirichlet Green kernel.**
For any finite mode set `S`:
`(2/L)·Σ_{m∈S} sin²(((m+1)π/L)a)/(κ²+λ_m)² ≤ ∫₀^L G(x,a)² dx`, `λ_m = galerkinLam L m`.
Route: `0 ≤ ∫ (G − Σ (2/L)·c_m·φ_{m+1})²`, expanded via banked
`green_sine_coefficient`, `eigenfun_orthogonal`, `integral_dirichletEigenfun_sq`.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace RHFormalization

noncomputable section

open Real intervalIntegral

/-- Bessel coefficient of the Green kernel against mode `m+1`. -/
noncomputable def besselCoeff (κ L a : ℝ) (m : ℕ) : ℝ :=
  Real.sin ((((m : ℝ) + 1) * Real.pi / L) * a) / (κ ^ 2 + galerkinLam L m)

/-- Finite Bessel projection onto modes `m+1`, `m ∈ S`. -/
noncomputable def besselProj (κ L a : ℝ) (S : Finset ℕ) (x : ℝ) : ℝ :=
  ∑ m ∈ S, (2 / L) * besselCoeff κ L a m * dirichletEigenfun (m + 1) L x

theorem dirichletEigenfun_continuous (n : ℕ) (L : ℝ) :
    Continuous (dirichletEigenfun n L) := by
  unfold dirichletEigenfun
  fun_prop

theorem dirichletGreen_continuous_left (L κ a : ℝ) :
    Continuous (fun x => dirichletGreen L κ x a) := by
  unfold dirichletGreen
  exact ((Real.continuous_sinh.comp
      (continuous_const.mul (continuous_id.min continuous_const))).mul
    (Real.continuous_sinh.comp
      (continuous_const.mul
        (continuous_const.sub (continuous_id.max continuous_const))))).div_const _

/-- `∫ G·φ_{m+1} = c_m`. -/
theorem green_inner_eigenfun (κ L a : ℝ) (m : ℕ)
    (hκ : 0 < κ) (hL : 0 < L) (ha0 : 0 ≤ a) (haL : a ≤ L) :
    (∫ x in (0:ℝ)..L, dirichletGreen L κ x a * dirichletEigenfun (m + 1) L x)
      = besselCoeff κ L a m := by
  have hLne : L ≠ 0 := ne_of_gt hL
  set b : ℝ := ((m : ℝ) + 1) * Real.pi / L with hb_def
  have heig : ∀ x : ℝ, dirichletEigenfun (m + 1) L x = Real.sin (b * x) := by
    intro x
    unfold dirichletEigenfun
    congr 1
    rw [hb_def]
    push_cast
    ring
  have hden : κ ^ 2 + b ^ 2 ≠ 0 := by positivity
  have hbL : b * L = ((m : ℝ) + 1) * Real.pi := by
    rw [hb_def]
    exact div_mul_cancel₀ _ hLne
  have hsinbL : Real.sin (b * L) = 0 := by
    rw [hbL, show ((m : ℝ) + 1) * Real.pi = (((m + 1 : ℕ)) : ℝ) * Real.pi by
      push_cast; ring]
    exact Real.sin_nat_mul_pi (m + 1)
  simp_rw [heig]
  rw [green_sine_coefficient κ b L a hκ hL ha0 haL hden hsinbL]
  have hlam : galerkinLam L m = b ^ 2 := by
    rw [hb_def]
    rfl
  unfold besselCoeff
  rw [hlam, ← hb_def]

/-- `∫ G·P = (2/L)·Σ c²`. -/
theorem integral_green_mul_proj (κ L a : ℝ) (S : Finset ℕ)
    (hκ : 0 < κ) (hL : 0 < L) (ha0 : 0 ≤ a) (haL : a ≤ L) :
    (∫ x in (0:ℝ)..L, dirichletGreen L κ x a * besselProj κ L a S x)
      = (2 / L) * ∑ m ∈ S, besselCoeff κ L a m ^ 2 := by
  have hpt : ∀ x : ℝ, dirichletGreen L κ x a * besselProj κ L a S x
      = ∑ m ∈ S, ((2 / L) * besselCoeff κ L a m)
          * (dirichletGreen L κ x a * dirichletEigenfun (m + 1) L x) := by
    intro x
    unfold besselProj
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  have hint : ∀ m ∈ S, IntervalIntegrable
      (fun x => ((2 / L) * besselCoeff κ L a m)
          * (dirichletGreen L κ x a * dirichletEigenfun (m + 1) L x))
      MeasureTheory.volume 0 L := by
    intro m _
    exact (continuous_const.mul
      ((dirichletGreen_continuous_left L κ a).mul
        (dirichletEigenfun_continuous (m + 1) L))).intervalIntegrable 0 L
  simp_rw [hpt]
  rw [show (∫ x in (0:ℝ)..L, ∑ m ∈ S, ((2 / L) * besselCoeff κ L a m)
          * (dirichletGreen L κ x a * dirichletEigenfun (m + 1) L x))
      = ∑ m ∈ S, ∫ x in (0:ℝ)..L, ((2 / L) * besselCoeff κ L a m)
          * (dirichletGreen L κ x a * dirichletEigenfun (m + 1) L x) from
    intervalIntegral.integral_finset_sum hint]
  have hterm : ∀ m ∈ S,
      (∫ x in (0:ℝ)..L, ((2 / L) * besselCoeff κ L a m)
          * (dirichletGreen L κ x a * dirichletEigenfun (m + 1) L x))
        = (2 / L) * besselCoeff κ L a m ^ 2 := by
    intro m _
    rw [intervalIntegral.integral_const_mul,
        green_inner_eigenfun κ L a m hκ hL ha0 haL]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]

/-- `∫ P² = (2/L)·Σ c²`: orthogonality collapses the double sum. -/
theorem integral_proj_sq (κ L a : ℝ) (S : Finset ℕ) (hL : 0 < L) :
    (∫ x in (0:ℝ)..L, besselProj κ L a S x ^ 2)
      = (2 / L) * ∑ m ∈ S, besselCoeff κ L a m ^ 2 := by
  have hLne : L ≠ 0 := ne_of_gt hL
  have hpt : ∀ x : ℝ, besselProj κ L a S x ^ 2
      = ∑ m ∈ S, ∑ n ∈ S,
          ((2 / L) * besselCoeff κ L a m * ((2 / L) * besselCoeff κ L a n))
            * (dirichletEigenfun (m + 1) L x * dirichletEigenfun (n + 1) L x) := by
    intro x
    unfold besselProj
    rw [pow_two, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  have houter : ∀ m ∈ S, IntervalIntegrable
      (fun x => ∑ n ∈ S,
          ((2 / L) * besselCoeff κ L a m * ((2 / L) * besselCoeff κ L a n))
            * (dirichletEigenfun (m + 1) L x * dirichletEigenfun (n + 1) L x))
      MeasureTheory.volume 0 L := by
    intro m _
    apply Continuous.intervalIntegrable
    apply continuous_finset_sum
    intro n _
    exact continuous_const.mul
      ((dirichletEigenfun_continuous (m + 1) L).mul
        (dirichletEigenfun_continuous (n + 1) L))
  simp_rw [hpt]
  rw [show (∫ x in (0:ℝ)..L, ∑ m ∈ S, ∑ n ∈ S,
          ((2 / L) * besselCoeff κ L a m * ((2 / L) * besselCoeff κ L a n))
            * (dirichletEigenfun (m + 1) L x * dirichletEigenfun (n + 1) L x))
      = ∑ m ∈ S, ∫ x in (0:ℝ)..L, ∑ n ∈ S,
          ((2 / L) * besselCoeff κ L a m * ((2 / L) * besselCoeff κ L a n))
            * (dirichletEigenfun (m + 1) L x * dirichletEigenfun (n + 1) L x) from
    intervalIntegral.integral_finset_sum houter]
  have hinner : ∀ m ∈ S,
      (∫ x in (0:ℝ)..L, ∑ n ∈ S,
          ((2 / L) * besselCoeff κ L a m * ((2 / L) * besselCoeff κ L a n))
            * (dirichletEigenfun (m + 1) L x * dirichletEigenfun (n + 1) L x))
        = (2 / L) * besselCoeff κ L a m ^ 2 := by
    intro m hm
    have hin : ∀ n ∈ S, IntervalIntegrable
        (fun x =>
          ((2 / L) * besselCoeff κ L a m * ((2 / L) * besselCoeff κ L a n))
            * (dirichletEigenfun (m + 1) L x * dirichletEigenfun (n + 1) L x))
        MeasureTheory.volume 0 L := by
      intro n _
      exact (continuous_const.mul
        ((dirichletEigenfun_continuous (m + 1) L).mul
          (dirichletEigenfun_continuous (n + 1) L))).intervalIntegrable 0 L
    rw [intervalIntegral.integral_finset_sum hin]
    have hzero : ∀ n ∈ S, n ≠ m →
        (∫ x in (0:ℝ)..L,
            ((2 / L) * besselCoeff κ L a m * ((2 / L) * besselCoeff κ L a n))
              * (dirichletEigenfun (m + 1) L x * dirichletEigenfun (n + 1) L x))
          = 0 := by
      intro n _ hnm
      rw [intervalIntegral.integral_const_mul,
          eigenfun_orthogonal (m + 1) (n + 1) L hLne (by omega), mul_zero]
    rw [Finset.sum_eq_single_of_mem m hm hzero,
        intervalIntegral.integral_const_mul]
    have hsq : (∫ x in (0:ℝ)..L,
        dirichletEigenfun (m + 1) L x * dirichletEigenfun (m + 1) L x) = L / 2 := by
      simp_rw [← pow_two]
      exact integral_dirichletEigenfun_sq (m + 1) L hL (by omega)
    rw [hsq]
    first
      | (field_simp; ring)
      | field_simp
      | ring
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]

/-- **P2-B3: the finite-stage Bessel inequality.** -/
theorem green_bessel_finite (κ L a : ℝ) (S : Finset ℕ)
    (hκ : 0 < κ) (hL : 0 < L) (ha0 : 0 ≤ a) (haL : a ≤ L) :
    (2 / L) * ∑ m ∈ S,
        Real.sin ((((m : ℝ) + 1) * Real.pi / L) * a) ^ 2
          / (κ ^ 2 + galerkinLam L m) ^ 2
      ≤ ∫ x in (0:ℝ)..L, dirichletGreen L κ x a ^ 2 := by
  have hGc : Continuous (fun x => dirichletGreen L κ x a) :=
    dirichletGreen_continuous_left L κ a
  have hPc : Continuous (besselProj κ L a S) := by
    unfold besselProj
    apply continuous_finset_sum
    intro m _
    exact continuous_const.mul (dirichletEigenfun_continuous (m + 1) L)
  have h0 : (0:ℝ) ≤ ∫ x in (0:ℝ)..L,
      (dirichletGreen L κ x a - besselProj κ L a S x) ^ 2 :=
    intervalIntegral.integral_nonneg hL.le (fun u _ => sq_nonneg _)
  have hexp : ∀ x : ℝ,
      (dirichletGreen L κ x a - besselProj κ L a S x) ^ 2
        = dirichletGreen L κ x a ^ 2
            - 2 * (dirichletGreen L κ x a * besselProj κ L a S x)
            + besselProj κ L a S x ^ 2 := by
    intro x
    ring
  have hIG2 : IntervalIntegrable (fun x => dirichletGreen L κ x a ^ 2)
      MeasureTheory.volume 0 L := (hGc.pow 2).intervalIntegrable 0 L
  have hIGP : IntervalIntegrable
      (fun x => 2 * (dirichletGreen L κ x a * besselProj κ L a S x))
      MeasureTheory.volume 0 L :=
    (continuous_const.mul (hGc.mul hPc)).intervalIntegrable 0 L
  have hIP2 : IntervalIntegrable (fun x => besselProj κ L a S x ^ 2)
      MeasureTheory.volume 0 L := (hPc.pow 2).intervalIntegrable 0 L
  have hsplit : (∫ x in (0:ℝ)..L,
        (dirichletGreen L κ x a - besselProj κ L a S x) ^ 2)
      = (∫ x in (0:ℝ)..L, dirichletGreen L κ x a ^ 2)
        - 2 * (∫ x in (0:ℝ)..L,
            dirichletGreen L κ x a * besselProj κ L a S x)
        + (∫ x in (0:ℝ)..L, besselProj κ L a S x ^ 2) := by
    simp_rw [hexp]
    rw [intervalIntegral.integral_add (hIG2.sub hIGP) hIP2,
        intervalIntegral.integral_sub hIG2 hIGP,
        intervalIntegral.integral_const_mul]
  rw [hsplit, integral_green_mul_proj κ L a S hκ hL ha0 haL,
      integral_proj_sq κ L a S hL] at h0
  have hAeq : (∑ m ∈ S,
        Real.sin ((((m : ℝ) + 1) * Real.pi / L) * a) ^ 2
          / (κ ^ 2 + galerkinLam L m) ^ 2)
      = ∑ m ∈ S, besselCoeff κ L a m ^ 2 := by
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold besselCoeff
    rw [div_pow]
  rw [hAeq]
  linarith

#print axioms besselCoeff
#print axioms green_inner_eigenfun
#print axioms integral_green_mul_proj
#print axioms integral_proj_sq
#print axioms green_bessel_finite

end

end RHFormalization
