import RHFormalization.DefaultZeroMultiplicity
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Analytic.Order

namespace RHFormalization

open Complex Filter Topology

/-- `ζ` and the completed `Λ` have the same analytic order at any `ρ` with
`re ρ > 0` and `ρ ≠ 1`: they differ by the everywhere-analytic, locally
nonvanishing unit `Γℝ⁻¹`. -/
theorem analyticOrderAt_zeta_eq_completed
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ ≠ 1) :
    analyticOrderAt riemannZeta ρ = analyticOrderAt completedRiemannZeta ρ := by
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have hΓne : Gammaℝ ρ ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0
  -- Λ analytic at ρ (ρ ≠ 0, ρ ≠ 1)
  have hΛ_an : AnalyticAt ℂ completedRiemannZeta ρ := by
    have hopen : ({0, 1} : Set ℂ)ᶜ ∈ 𝓝 ρ := by
      apply (Set.Finite.isClosed (Set.toFinite _)).isOpen_compl.mem_nhds
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hρ0, h1⟩
    have hdon : DifferentiableOn ℂ completedRiemannZeta ({0, 1} : Set ℂ)ᶜ := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
      exact (differentiableAt_completedZeta hx.1 hx.2).differentiableWithinAt
    exact hdon.analyticAt hopen
  -- Γℝ⁻¹ analytic everywhere
  have hΓinv_an : AnalyticAt ℂ (fun s => (Gammaℝ s)⁻¹) ρ :=
    differentiable_Gammaℝ_inv.analyticAt ρ
  -- ζ =ᶠ[𝓝 ρ] Λ • Γℝ⁻¹  (i.e. Λ * Γℝ⁻¹) near ρ
  have hΓinv_ne : (Gammaℝ ρ)⁻¹ ≠ 0 := inv_ne_zero hΓne
  have heq : riemannZeta =ᶠ[𝓝 ρ] (fun s => completedRiemannZeta s * (Gammaℝ s)⁻¹) := by
    -- on the set s ≠ 0 (a nbhd of ρ since ρ ≠ 0), ζ s = Λ s / Γℝ s = Λ s * (Γℝ s)⁻¹
    have hU : {s : ℂ | s ≠ 0} ∈ 𝓝 ρ := isOpen_ne.mem_nhds hρ0
    filter_upwards [hU] with s hs
    rw [riemannZeta_def_of_ne_zero hs, div_eq_mul_inv]
  rw [analyticOrderAt_congr heq]
  -- order(Λ * Γℝ⁻¹) = order(Λ) + order(Γℝ⁻¹) = order(Λ) + 0
  have hsmul : (fun s => completedRiemannZeta s * (Gammaℝ s)⁻¹)
      = (fun s => completedRiemannZeta s) • (fun s => (Gammaℝ s)⁻¹) := by
    funext s; simp [smul_eq_mul]
  rw [hsmul, analyticOrderAt_smul hΛ_an hΓinv_an]
  have hord0 : analyticOrderAt (fun s => (Gammaℝ s)⁻¹) ρ = 0 :=
    hΓinv_an.analyticOrderAt_eq_zero.mpr hΓinv_ne
  rw [hord0, add_zero]

/-- The completed `Λ` has equal analytic order at `ρ` and `1 - ρ`
(functional equation `Λ(1-s) = Λ(s)` plus affine-reflection invariance). -/
theorem analyticOrderAt_completed_reflection (ρ : ℂ) :
    analyticOrderAt completedRiemannZeta ρ
      = analyticOrderAt completedRiemannZeta (1 - ρ) := by
  -- refl s = 1 - s is analytic with derivative -1 ≠ 0, refl ρ = 1 - ρ
  have hrefl_an : AnalyticAt ℂ (fun s => 1 - s) ρ :=
    (analyticAt_const.sub analyticAt_id)
  have hrefl_deriv : deriv (fun s => 1 - s) ρ ≠ 0 := by
    have : deriv (fun s : ℂ => 1 - s) ρ = -1 := by
      simp
    rw [this]; norm_num
  -- Λ ∘ refl has order at ρ = order of Λ at refl ρ = 1 - ρ
  have hcomp : analyticOrderAt (completedRiemannZeta ∘ (fun s => 1 - s)) ρ
      = analyticOrderAt completedRiemannZeta (1 - ρ) :=
    analyticOrderAt_comp_of_deriv_ne_zero hrefl_an hrefl_deriv
  -- but Λ ∘ refl = Λ globally (functional equation)
  have hfe : (completedRiemannZeta ∘ (fun s => 1 - s)) = completedRiemannZeta := by
    funext s
    simp only [Function.comp_apply]
    exact completedRiemannZeta_one_sub s
  rw [hfe] at hcomp
  exact hcomp

/-- **Multiplicity symmetry:** `zetaZeroMult ρ = zetaZeroMult (1 - ρ)` for
`ρ` in the critical strip (`0 < re ρ`, `ρ ≠ 1`, and `re ρ < 1` so `1-ρ` is
also off the pole). This dissolves the sqrt-branch ambiguity. -/
theorem zetaZeroMult_reflection
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    zetaZeroMult ρ = zetaZeroMult (1 - ρ) := by
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at h1; simp at h1
  have hsub0 : 0 < (1 - ρ).re := by
    simp only [Complex.sub_re, Complex.one_re]; linarith
  have hsub1 : (1 - ρ) ≠ 1 := by
    intro h
    have : ρ = 0 := by
      have := congrArg (fun z => 1 - z) h
      simpa using this
    rw [this] at h0; simp at h0
  -- Prove the order equality at the ℕ∞ level, then take toNat.
  have hord : analyticOrderAt riemannZeta ρ = analyticOrderAt riemannZeta (1 - ρ) := by
    rw [analyticOrderAt_zeta_eq_completed h0 hρ1,
        analyticOrderAt_completed_reflection ρ,
        ← analyticOrderAt_zeta_eq_completed hsub0 hsub1]
  unfold zetaZeroMult
  rw [hord]

#print axioms zetaZeroMult_reflection

end RHFormalization
