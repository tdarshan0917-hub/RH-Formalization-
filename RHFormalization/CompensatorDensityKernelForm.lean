import RHFormalization.SeamMainTermDensityIntegral
import RHFormalization.DBFFCompensatorHolo
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex MeasureTheory

/-!
# CompensatorDensityKernelForm — C-REP: the compensator over the common atom

EXACT on Ω:  compensatorM n s
  = ∫₀^{admR n} e^{u/2}·shiftedLaplaceHeatKernelC u s du  +  pole(s),
pole(s) = (1/(2w))·(1/((1/2)−w)), w = √(s+1/4). Same atom function as
galBTail's spikes: THE cancellation (C2) becomes density-vs-points over
one kernel. No estimates.
-/

/-- The n-independent pole of the compensator split. -/
noncomputable def compensatorPole (s : ℂ) : ℂ :=
  (1 / (2 * Complex.sqrt (s + (1/4:ℂ)))) *
    (1 / ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))))

/-- **C-REP**: the compensator is the density-weighted kernel integral plus
the explicit pole (exact on Ω). -/
theorem compensatorM_eq_densityKernelIntegral_add_pole
    (n : ℕ) {s : ℂ} (hs : s ∈ Ω) :
    compensatorM n s
      = (∫ u in (0:ℝ)..(admR n),
          Complex.exp ((u:ℂ)/2) * shiftedLaplaceHeatKernelC u s)
        + compensatorPole s := by
  set w := Complex.sqrt (s + (1/4:ℂ)) with hw
  have hw0 : w ≠ 0 := sqrt_ne_zero' hs
  have hane : ((1/2:ℂ) - w) ≠ 0 := by
    intro h0
    have : w = (1/2:ℂ) := by linear_combination -h0
    exact (sqrt_ne_half hs) this
  have hker : ∀ u : ℝ,
      Complex.exp ((u:ℂ)/2) * shiftedLaplaceHeatKernelC u s
        = (1/(2*w)) * Complex.exp (((1/2:ℂ) - w) * (u:ℂ)) := by
    intro u
    unfold shiftedLaplaceHeatKernelC
    rw [← hw]
    have hcomb : Complex.exp ((u:ℂ)/2) * Complex.exp (-(u:ℂ) * w)
        = Complex.exp (((1/2:ℂ) - w) * (u:ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    calc Complex.exp ((u:ℂ)/2) * ((1:ℂ)/(2*w) * Complex.exp (-(u:ℂ) * w))
        = (1/(2*w)) * (Complex.exp ((u:ℂ)/2) * Complex.exp (-(u:ℂ) * w)) := by
          ring
      _ = (1/(2*w)) * Complex.exp (((1/2:ℂ) - w) * (u:ℂ)) := by rw [hcomb]
  have hint : (∫ u in (0:ℝ)..(admR n),
      Complex.exp ((u:ℂ)/2) * shiftedLaplaceHeatKernelC u s)
      = (1/(2*w)) * ∫ u in (0:ℝ)..(admR n),
          Complex.exp (((1/2:ℂ) - w) * (u:ℂ)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    exact hker u
  rw [hint, ← exp_sub_one_div_eq_integral _ hane (admR n)]
  unfold compensatorM compensatorPole
  rw [← hw]
  field_simp
  ring

#print axioms compensatorPole
#print axioms compensatorM_eq_densityKernelIntegral_add_pole

end

end RHFormalization
