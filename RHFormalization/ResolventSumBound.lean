import RHFormalization.HeatSumSqrtBound
import RHFormalization.CompletedZetaGrowth
import RHFormalization.QuadRemainderTransformGlobal

/-!
# RHFormalization.ResolventSumBound
**Main-term twin 2: the resolvent eigenvalue-sum bound.**
`Σ_{m:Fin N} (τ+λ_m)⁻¹ ≤ Γ(1/2)·(L/(2√π))·τ^{−1/2}` for `τ>0` — N-uniform,
L-linear (killed downstream by `1/(2L)`). Route: termwise Laplace
(Γ-kit at a=1), finite swap, heat-sum √-donor at general L (squaring
massage), majorant domination, Γ at a=1/2.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace RHFormalization

noncomputable section

open Real MeasureTheory Set

variable {N : ℕ}

/-- General-L sqrt massage, by squaring both sides. -/
theorem sqrt_pi_div_arg_L (L : ℝ) (hL : 0 < L) (u : ℝ) (hu : 0 < u) :
    Real.sqrt (Real.pi / (u * (Real.pi / L) ^ 2))
      = L * (1 / (Real.sqrt Real.pi * Real.sqrt u)) := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hsπ : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr hπ
  have hsu : (0:ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu
  have harg : Real.pi / (u * (Real.pi / L) ^ 2)
      = (L * (1 / (Real.sqrt Real.pi * Real.sqrt u))) ^ 2 := by
    have h1 : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt hπ.le
    have h2 : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu.le
    field_simp
    rw [h1, h2]
    ring
  rw [harg]
  exact Real.sqrt_sq (by positivity)

/-- Termwise Laplace: `c⁻¹ = ∫₀^∞ e^{−c·u} du` for `c > 0`. -/
theorem inv_eq_integral_exp (c : ℝ) (hc : 0 < c) :
    c⁻¹ = ∫ u in Ioi (0:ℝ), Real.exp (-c * u) := by
  have h := integral_rpow_mul_exp_eq_gamma (a := (1:ℝ)) (b := c) one_pos hc
  rw [show (1:ℝ) - 1 = 0 by norm_num] at h
  have hsimp : (fun t : ℝ => t ^ (0:ℝ) * Real.exp (-c * t))
      = fun t : ℝ => Real.exp (-c * t) := by
    funext t
    rw [Real.rpow_zero, one_mul]
  rw [hsimp] at h
  rw [h, Real.Gamma_one, mul_one]
  rw [Real.rpow_neg_one]

/-- **Twin 2: the resolvent sum bound.** N-uniform, explicit L-linear. -/
theorem resolvent_sum_le (L : ℝ) (hL : 0 < L) (τ : ℝ) (hτ : 0 < τ) :
    ∑ m : Fin N, (τ + galerkinLam L m)⁻¹
      ≤ Real.Gamma ((1/2):ℝ) * (L / (2 * Real.sqrt Real.pi))
          * τ ^ (-(1/2):ℝ) := by
  have hlam : ∀ m : Fin N, 0 ≤ galerkinLam L m := by
    intro m
    unfold galerkinLam
    positivity
  have hterm : ∀ m : Fin N, 0 < τ + galerkinLam L m := by
    intro m
    have := hlam m
    linarith
  have hint : ∀ m ∈ (Finset.univ : Finset (Fin N)), IntegrableOn
      (fun u : ℝ => Real.exp (-(τ + galerkinLam L m) * u)) (Ioi (0:ℝ)) := by
    intro m _
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := (0:ℝ)) (b := τ + galerkinLam L m)
      (by norm_num) (by norm_num) (hterm m)
    refine h.congr_fun (fun u hu => ?_) measurableSet_Ioi
    simp [Real.rpow_one, Real.rpow_zero]
  have hswap : ∑ m : Fin N, (τ + galerkinLam L m)⁻¹
      = ∫ u in Ioi (0:ℝ), ∑ m : Fin N,
          Real.exp (-(τ + galerkinLam L m) * u) := by
    rw [show (∑ m : Fin N, (τ + galerkinLam L m)⁻¹)
        = ∑ m : Fin N, ∫ u in Ioi (0:ℝ),
            Real.exp (-(τ + galerkinLam L m) * u) from
      Finset.sum_congr rfl (fun m _ => inv_eq_integral_exp _ (hterm m))]
    exact (MeasureTheory.integral_finset_sum _ hint).symm
  rw [hswap]
  set C : ℝ := L / (2 * Real.sqrt Real.pi) with hC
  have hCnn : 0 ≤ C := by
    rw [hC]
    have := Real.sqrt_pos.mpr Real.pi_pos
    positivity
  have hptw : ∀ u ∈ Ioi (0:ℝ),
      (∑ m : Fin N, Real.exp (-(τ + galerkinLam L m) * u))
        ≤ C * (u ^ (-(1/2):ℝ) * Real.exp (-τ * u)) := by
    intro u hu
    have hfac : ∀ m : Fin N, Real.exp (-(τ + galerkinLam L m) * u)
        = Real.exp (-τ * u) * heatWeight (N := N) L u m := by
      intro m
      unfold heatWeight
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [hfac]
    rw [← Finset.mul_sum]
    have hsum := sum_heatWeight_le_sqrt (N := N) L hL u hu
    have hexp : (0:ℝ) < Real.exp (-τ * u) := Real.exp_pos _
    have hrpow : u ^ (-(1/2) : ℝ) = 1 / Real.sqrt u := by
      rw [Real.rpow_neg (le_of_lt hu), Real.sqrt_eq_rpow, one_div]
    calc Real.exp (-τ * u) * ∑ m : Fin N, heatWeight (N := N) L u m
        ≤ Real.exp (-τ * u)
            * (Real.sqrt (Real.pi / (u * (Real.pi / L) ^ 2)) / 2) :=
          mul_le_mul_of_nonneg_left hsum hexp.le
      _ = Real.exp (-τ * u)
            * (L * (1 / (Real.sqrt Real.pi * Real.sqrt u)) / 2) := by
          rw [sqrt_pi_div_arg_L L hL u hu]
      _ = C * (u ^ (-(1/2):ℝ) * Real.exp (-τ * u)) := by
          rw [hrpow, hC]
          have hsπ : (0:ℝ) < Real.sqrt Real.pi :=
            Real.sqrt_pos.mpr Real.pi_pos
          have hsu : (0:ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu
          field_simp
          ring
  have hI : IntegrableOn (fun u : ℝ => u ^ (-(1/2):ℝ) * Real.exp (-τ * u))
      (Ioi (0:ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := (-(1/2):ℝ)) (b := τ) (by norm_num) (by norm_num) hτ
    refine h.congr_fun (fun u hu => ?_) measurableSet_Ioi
    simp only [Real.rpow_one]
  have hfInt : IntegrableOn (fun u : ℝ => ∑ m : Fin N,
      Real.exp (-(τ + galerkinLam L m) * u)) (Ioi (0:ℝ)) := by
    first
      | exact MeasureTheory.integrable_finset_sum Finset.univ hint
      | exact MeasureTheory.integrable_finset_sum (s := Finset.univ) hint
      | (apply MeasureTheory.integrable_finset_sum
         exact hint)
  have hmono : (∫ u in Ioi (0:ℝ), ∑ m : Fin N,
      Real.exp (-(τ + galerkinLam L m) * u))
      ≤ ∫ u in Ioi (0:ℝ), C * (u ^ (-(1/2):ℝ) * Real.exp (-τ * u)) := by
    apply MeasureTheory.setIntegral_mono_on hfInt (hI.const_mul C)
      measurableSet_Ioi
    intro u hu
    exact hptw u hu
  refine le_trans hmono (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul]
  have hg : ∫ u in Ioi (0:ℝ), u ^ (-(1/2):ℝ) * Real.exp (-τ * u)
      = τ ^ (-(1/2):ℝ) * Real.Gamma ((1/2):ℝ) := by
    have h := integral_rpow_mul_exp_eq_gamma
      (a := ((1/2):ℝ)) (b := τ) (by norm_num) hτ
    rw [show ((1/2):ℝ) - 1 = (-(1/2):ℝ) by norm_num] at h
    rw [h]
  rw [hg, hC]
  ring

#print axioms sqrt_pi_div_arg_L
#print axioms inv_eq_integral_exp
#print axioms resolvent_sum_le

end

end RHFormalization
