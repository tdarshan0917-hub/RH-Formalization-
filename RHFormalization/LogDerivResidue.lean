import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import RHFormalization.AnalyticWrappers

/-!
# RHFormalization.LogDerivResidue
**The argument-principle brick.** If `f` is analytic at `z` with a zero of order `k`,
then `logDeriv f = f'/f` has a simple pole at `z` with residue `k`. No `sorry`.
-/

set_option autoImplicit false

namespace RHFormalization

open Complex Filter Topology

/-- **Local factorization at a zero of finite order.** -/
theorem analytic_factor_at_zero
    {f : ℂ → ℂ} {z : ℂ} {k : ℕ}
    (hf : AnalyticAt ℂ f z)
    (hk : analyticOrderAt f z = (k : ℕ)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, f w = (w - z) ^ k * g w := by
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (hf.analyticOrderAt_eq_natCast).mp hk
  refine ⟨g, hg_an, hg_ne, ?_⟩
  filter_upwards [hg_eq] with w hw
  simpa [smul_eq_mul] using hw

/-- `logDeriv f` has a simple pole at a zero of order `k` with residue `k`:
the **argument principle**, local form. -/
theorem logDeriv_hasPrincipalPart_at_zero
    {f : ℂ → ℂ} {z : ℂ} {k : ℕ}
    (hf : AnalyticAt ℂ f z)
    (hk : analyticOrderAt f z = (k : ℕ)) :
    HasPrincipalPartAtC (logDeriv f) z (k : ℂ) := by
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := analytic_factor_at_zero hf hk
  refine ⟨logDeriv g, ?_, ?_⟩
  · have hdg : AnalyticAt ℂ (deriv g) z := hg_an.deriv
    have hq : AnalyticAt ℂ (fun w => deriv g w / g w) z := hdg.div hg_an hg_ne
    have heq : (logDeriv g) = (fun w => deriv g w / g w) := by
      funext w; rw [logDeriv_apply]
    rw [heq]; exact hq
  · have hgnhds : ∀ᶠ w in 𝓝 z, g w ≠ 0 := hg_an.continuousAt.eventually_ne hg_ne
    have hgdiff : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ g w :=
      hg_an.eventually_analyticAt.mono (fun _ h => h.differentiableAt)
    filter_upwards [eventually_eventually_nhds.mpr hg_eq, hgnhds, hgdiff]
      with w hw_nb hgw hgdw
    intro hwz
    have hsub_ne : (w - z) ≠ 0 := sub_ne_zero.mpr hwz
    have hpow_ne : (w - z) ^ k ≠ 0 := pow_ne_zero k hsub_ne
    have hw : f w = (w - z) ^ k * g w := hw_nb.self_of_nhds
    have hfeq : f =ᶠ[𝓝 w] (fun u => (u - z) ^ k * g u) := hw_nb
    have hderiv : deriv f w = deriv (fun u => (u - z) ^ k * g u) w := hfeq.deriv_eq
    have hlog : logDeriv f w = logDeriv (fun u => (u - z) ^ k * g u) w := by
      rw [logDeriv_apply, logDeriv_apply, hderiv, hw]
    rw [hlog]
    have hdpow : DifferentiableAt ℂ (fun u : ℂ => (u - z) ^ k) w :=
      ((differentiableAt_id).sub_const z).pow k
    rw [logDeriv_mul w hpow_ne hgw hdpow hgdw]
    have hpowlog : logDeriv (fun u => (u - z) ^ k) w = (k : ℂ) / (w - z) := by
      have hid : DifferentiableAt ℂ (fun u : ℂ => u - z) w :=
        (differentiableAt_id).sub_const z
      rw [logDeriv_fun_pow hid k]
      have hl : logDeriv (fun u : ℂ => u - z) w = 1 / (w - z) := by
        rw [logDeriv_apply]
        have hdd : deriv (fun u : ℂ => u - z) w = 1 := by simp
        rw [hdd]
      rw [hl]
      field_simp
    rw [hpowlog]

#print axioms analytic_factor_at_zero
#print axioms logDeriv_hasPrincipalPart_at_zero

end RHFormalization
