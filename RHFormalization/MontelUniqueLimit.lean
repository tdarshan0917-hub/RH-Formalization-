import RHFormalization.AnalyticWrappers
import RHFormalization.Basic
import Mathlib

/-!
# Holomorphic Montel — uniqueness assembly (identity theorem pins the limit)

The p178 uniqueness step: a holomorphic function `g` on `Ω` agreeing with `RH` on a
nonempty open `U ⊆ Ω` (the overlap `U_σ₀`) equals `RH` on all of `Ω`, by the identity
theorem on the connected slit plane. This forces every subsequential limit of the normal
family to equal the single `RH`, hence full convergence.

Part of discharging `HolomorphicMontelConvergence` (D.CAN-REM's last gap, p178).
-/

namespace RHFormalization
open Filter Topology Complex

/-- `Ω = ℂ ∖ (-∞,0]` is exactly Mathlib's `slitPlane` (De Morgan). -/
theorem Omega_eq_slitPlane : Ω = slitPlane := by
  ext s
  simp only [Omega, NonpositiveRealAxis, slitPlane, Set.mem_setOf_eq, not_and, not_le]
  constructor
  · intro h
    rcases eq_or_ne s.im 0 with him | him
    · exact Or.inl (h him)
    · exact Or.inr him
  · intro h him
    rcases h with hre | himne
    · exact hre
    · exact absurd him himne

/-- `Ω` is open. -/
theorem isOpen_Omega : IsOpen Ω := by
  rw [Omega_eq_slitPlane]; exact isOpen_slitPlane

/-- `Ω` is preconnected (star-convex from `1`). -/
theorem isPreconnected_Omega : IsPreconnected Ω := by
  rw [Omega_eq_slitPlane]
  have h1 : (1 : ℂ) ∈ slitPlane := by
    simp only [slitPlane, Set.mem_setOf_eq]
    left; norm_num
  exact (starConvex_one_slitPlane.isPathConnected h1).isConnected.isPreconnected

/-- **Montel uniqueness (identity theorem).** -/
theorem eqOn_Omega_of_eqOn_open
    {g RH : ℂ → ℂ} (hg : HolomorphicOnC g Ω) (hRH : HolomorphicOnC RH Ω)
    {U : Set ℂ} (hUopen : IsOpen U) (hUne : U.Nonempty) (hUsub : U ⊆ Ω)
    (hagree : Set.EqOn g RH U) :
    Set.EqOn g RH Ω := by
  obtain ⟨z₀, hz₀U⟩ := hUne
  have hz₀Ω : z₀ ∈ Ω := hUsub hz₀U
  have hgN : AnalyticOnNhd ℂ g Ω :=
    (isOpen_Omega.analyticOn_iff_analyticOnNhd).mp hg
  have hRHN : AnalyticOnNhd ℂ RH Ω :=
    (isOpen_Omega.analyticOn_iff_analyticOnNhd).mp hRH
  have hev : g =ᶠ[𝓝 z₀] RH := by
    filter_upwards [hUopen.mem_nhds hz₀U] with z hz using hagree hz
  exact hgN.eqOn_of_preconnected_of_eventuallyEq hRHN isPreconnected_Omega hz₀Ω hev

#print axioms eqOn_Omega_of_eqOn_open

end RHFormalization
