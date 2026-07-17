import RHFormalization.LogDerivResidue
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# RHFormalization.ZetaLogDerivPrincipalPart
**Step 1: the argument principle applied to ζ.** At any zero `ρ ≠ 1` of `riemannZeta`,
`logDeriv riemannZeta = ζ'/ζ` has a simple pole with residue the order `k ≥ 1` of the
zero. Built on `logDeriv_hasPrincipalPart_at_zero`. No `sorry`.
-/

set_option autoImplicit false

namespace RHFormalization

open Complex Filter Topology

/-- `riemannZeta` is analytic at every `s ≠ 1`. -/
theorem analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  apply DifferentiableOn.analyticAt (s := {(1 : ℂ)}ᶜ) differentiableOn_riemannZeta
  exact (isOpen_compl_singleton).mem_nhds hs

/-- `riemannZeta` is not eventually zero near any point `ρ ≠ 1`: its zeros are isolated. -/
theorem riemannZeta_not_eventually_zero {ρ : ℂ} (hρ1 : ρ ≠ 1) :
    ¬ (∀ᶠ z in 𝓝 ρ, riemannZeta z = 0) := by
  intro hev
  -- if ζ ≡ 0 near ρ, then in particular ζ vanishes on an open ball around ρ;
  -- but ζ is nonzero at points with re > 1, contradicting analytic continuation.
  -- Use: eventually-zero ⟹ analyticOrderAt = ⊤, but pick a concrete nonzero witness.
  have hAn : AnalyticAt ℂ riemannZeta ρ := analyticAt_riemannZeta hρ1
  -- the set where ζ = 0 contains a neighborhood of ρ; ζ analytic on connected {1}ᶜ ∋ ρ.
  -- A cleaner finish: eventually-zero at ρ forces ζ to vanish on all of {1}ᶜ (identity thm),
  -- contradicting ζ(2) ≠ 0.
  have h2 : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  -- identity theorem on the preconnected open set {1}ᶜ
  have hpreconn : IsPreconnected ({(1:ℂ)}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp [rank_real_complex]) 1).isPreconnected
  have hAnOn : AnalyticOnNhd ℂ riemannZeta {(1:ℂ)}ᶜ :=
    differentiableOn_riemannZeta.analyticOnNhd (isOpen_compl_singleton)
  have hρmem : ρ ∈ ({(1:ℂ)}ᶜ : Set ℂ) := hρ1
  have h2mem : (2 : ℂ) ∈ ({(1:ℂ)}ᶜ : Set ℂ) := by norm_num
  have := hAnOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hpreconn hρmem hev
  exact h2 (this h2mem)

/-- **The argument principle for ζ.** At a zero `ρ ≠ 1` of `riemannZeta`, `logDeriv riemannZeta`
has a simple pole with residue equal to the (positive) order of the zero. -/
theorem zeta_logDeriv_principalPart_at_zero
    {ρ : ℂ} (hρ1 : ρ ≠ 1) (hρ : riemannZeta ρ = 0) :
    ∃ k : ℕ, 0 < k ∧
      HasPrincipalPartAtC (logDeriv riemannZeta) ρ (k : ℂ) := by
  have hAn : AnalyticAt ℂ riemannZeta ρ := analyticAt_riemannZeta hρ1
  have hne0 : analyticOrderAt riemannZeta ρ ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨hAn, hρ⟩
  have hneTop : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]
    exact riemannZeta_not_eventually_zero hρ1
  set k := analyticOrderNatAt riemannZeta ρ with hk_def
  have hk_cast : analyticOrderAt riemannZeta ρ = (k : ℕ) := by
    rw [hk_def, Nat.cast_analyticOrderNatAt hneTop]
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, Nat.cast_zero] at hk_cast; exact absurd hk_cast hne0
    · exact hpos
  exact ⟨k, hkpos, logDeriv_hasPrincipalPart_at_zero hAn hk_cast⟩

#print axioms analyticAt_riemannZeta
#print axioms zeta_logDeriv_principalPart_at_zero

end RHFormalization
