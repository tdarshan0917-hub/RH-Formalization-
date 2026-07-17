import RHFormalization.RemovableDiv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Analytic.Composition

set_option autoImplicit false
namespace RHFormalization
open Complex Filter Topology

theorem hasPrincipalPart_comp
    {g φ : ℂ → ℂ} {s0 ρ c : ℂ}
    (hg : HasPrincipalPartAtC g ρ c)
    (hφ : AnalyticAt ℂ φ s0)
    (hφρ : φ s0 = ρ)
    (hφ' : deriv φ s0 ≠ 0) :
    HasPrincipalPartAtC (fun w => g (φ w)) s0 (c / deriv φ s0) := by
  obtain ⟨h, hh_an, hh_eq⟩ := hg
  have hΦ : AnalyticAt ℂ (fun w => φ w - ρ) s0 := hφ.sub analyticAt_const
  have hΦ0 : (fun w => φ w - ρ) s0 = 0 := by simp [hφρ]
  have hΦd : deriv (fun w => φ w - ρ) s0 = deriv φ s0 := by
    have : HasDerivAt (fun w => φ w - ρ) (deriv φ s0) s0 :=
      (hφ.differentiableAt.hasDerivAt).sub_const ρ
    exact this.deriv
  have hord1 : analyticOrderAt (fun w => φ w - ρ) s0 = 1 :=
    hΦ.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hΦ0 (by rw [hΦd]; exact hφ')
  have hord : analyticOrderAt (fun w => φ w - ρ) s0 = ((1 : ℕ) : ℕ∞) := by
    rw [hord1]; rfl
  obtain ⟨ψ, hψ_an, hψ_ne, hψ_eq⟩ := analytic_factor_at_zero hΦ hord
  -- normalize the factorization to drop the ^1
  have hψ_eq' : ∀ᶠ w in 𝓝 s0, φ w - ρ = (w - s0) * ψ w := by
    filter_upwards [hψ_eq] with w hw; simpa [pow_one] using hw
  have hψ_val : ψ s0 = deriv φ s0 := by
    have hd : HasDerivAt (fun w => φ w - ρ) (deriv φ s0) s0 := by
      rw [← hΦd]; exact hΦ.differentiableAt.hasDerivAt
    have h1 : HasDerivAt (fun w : ℂ => w - s0) 1 s0 := (hasDerivAt_id s0).sub_const s0
    have h2 : HasDerivAt ψ (deriv ψ s0) s0 := hψ_an.differentiableAt.hasDerivAt
    have hm : HasDerivAt (fun w => (w - s0) * ψ w)
        (1 * ψ s0 + (s0 - s0) * deriv ψ s0) s0 := h1.mul h2
    have hcongr : HasDerivAt (fun w => φ w - ρ) (1 * ψ s0 + (s0 - s0) * deriv ψ s0) s0 := by
      apply hm.congr_of_eventuallyEq
      filter_upwards [hψ_eq'] with w hw; exact hw
    have := hd.unique hcongr
    simpa using this.symm
  have hq_an : AnalyticAt ℂ (fun w => c / ψ w) s0 := analyticAt_const.div hψ_an hψ_ne
  have hN_an : AnalyticAt ℂ (fun w => c / ψ w - c / deriv φ s0) s0 := hq_an.sub analyticAt_const
  have hN0 : (fun w => c / ψ w - c / deriv φ s0) s0 = 0 := by simp [hψ_val]
  obtain ⟨R, hR_an, hR_eq⟩ := removable_div_exists hN_an hN0
  have hhφ_an : AnalyticAt ℂ (fun w => h (φ w)) s0 :=
    hh_an.comp_of_eq' hφ hφρ
  refine ⟨fun w => R w + h (φ w), hR_an.add hhφ_an, ?_⟩
  -- transport: ψ ≠ 0 near s0, and h-identity through φ
  have hψ_ev : ∀ᶠ w in 𝓝 s0, ψ w ≠ 0 :=
    hψ_an.continuousAt.eventually_ne hψ_ne
  have hφ_cont : ContinuousAt φ s0 := hφ.continuousAt
  have hh_pull : ∀ᶠ w in 𝓝 s0, φ w ≠ ρ → g (φ w) = c / (φ w - ρ) + h (φ w) := by
    have : Tendsto φ (𝓝 s0) (𝓝 ρ) := hφρ ▸ hφ_cont.tendsto
    exact this.eventually hh_eq
  filter_upwards [hψ_eq', hR_eq, hψ_ev, hh_pull] with w hwψ' hwR hwψ0 hwh
  intro hwne
  have hsub : w - s0 ≠ 0 := sub_ne_zero.mpr hwne
  have hφw_ne : φ w ≠ ρ := by
    rw [← sub_ne_zero, hwψ']; exact mul_ne_zero hsub hwψ0
  -- now compute
  rw [hwh hφw_ne]
  -- c/(φ w - ρ) = c/((w-s0)*ψ w); and R w = (c/ψ w - c/φ'(s0))/(w-s0)
  rw [hwψ']
  have hRval : R w = (c / ψ w - c / deriv φ s0) / (w - s0) := (hwR hwne).symm
  rw [hRval]
  field_simp
  ring

#print axioms hasPrincipalPart_comp

end RHFormalization
