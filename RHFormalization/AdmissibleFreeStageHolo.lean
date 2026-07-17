import RHFormalization.AdmissibleFreeRiemannSum

/-!
# RHFormalization.AdmissibleFreeStageHolo

**Front F-adm, brick 1b.** The admissible free stage is (i) a constant times a
finite resolvent trace with nonneg spectrum, hence (ii) holomorphic on Ω; and
(iii) the compact-uniform majorant `‖(s+SupV+u²)⁻¹‖ ≤ C_K(1+u²)⁻¹` for ALL
`s ∈ K` — the E2-tail workhorse for bricks 1c/1d.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- Bridge: the admissible free stage is `admDensityC n · FstageFinite (SupV + μ)`. -/
theorem admissibleFreeStage_eq_FstageFinite (n : ℕ) (s : ℂ) :
    admissibleFreeStage n s
      = admDensityC n *
          FstageFinite (fun i : Fin (admN n) =>
            SupVConst + galerkinFreeMu (admN n) (admL n) i) s := by
  first
    | rfl
    | (unfold admissibleFreeStage FstageFinite; rfl)
    | simp [admissibleFreeStage, FstageFinite]

/-- The shifted free spectrum is nonnegative. -/
theorem admissibleFreeSpectrum_nonneg (n : ℕ) (i : Fin (admN n)) :
    0 ≤ SupVConst + galerkinFreeMu (admN n) (admL n) i := by
  have h2 : 0 ≤ galerkinFreeMu (admN n) (admL n) i := by
    first
      | exact galerkinFreeMu_nonneg _ _ i
      | (unfold galerkinFreeMu; positivity)
      | exact sq_nonneg _
  have h1 := SupVConst_nonneg_adm
  linarith

/-- **Brick 1b: the admissible free stage is holomorphic on Ω.** -/
theorem admissibleFreeStage_holo (n : ℕ) :
    HolomorphicOnC (fun s => admissibleFreeStage n s) Ω := by
  have h : HolomorphicOnC
      (FstageFinite (fun i : Fin (admN n) =>
        SupVConst + galerkinFreeMu (admN n) (admL n) i)) Ω :=
    FstageFinite_holo_on_Omega _ (admissibleFreeSpectrum_nonneg n)
  have heq : (fun s => admissibleFreeStage n s)
      = fun s => admDensityC n *
          FstageFinite (fun i : Fin (admN n) =>
            SupVConst + galerkinFreeMu (admN n) (admL n) i) s := by
    funext s
    exact admissibleFreeStage_eq_FstageFinite n s
  rw [heq]
  first
    | exact analyticOn_const.mul h
    | exact (show AnalyticOn ℂ (fun _ : ℂ => admDensityC n) Ω from
        analyticOn_const).mul h
    | exact h.const_mul (admDensityC n)
    | exact AnalyticOn.mul analyticOn_const h

/-- **Compact-uniform majorant** for the free integrand: a single `C_K` with
`‖(s + SupV + u²)⁻¹‖ ≤ C_K·(1+u²)⁻¹` for ALL `s ∈ K` and ALL `u` — the
K-uniform version of brick 1a's pointwise bound; drives the E2 tail. -/
theorem freeResolvent_norm_le_on_compact
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ K, ∀ u : ℝ,
      ‖freeResolventIntegrand s u‖ ≤ C * ((1:ℝ) + u ^ 2)⁻¹ := by
  obtain ⟨C, hCpos, hC⟩ := inv_norm_le_on_compact K hK hKO
  refine ⟨C, hCpos, ?_⟩
  intro s hs u
  show ‖(s + ((SupVConst + u ^ 2 : ℝ) : ℂ))⁻¹‖ ≤ C * ((1:ℝ) + u ^ 2)⁻¹
  have hlam : (0:ℝ) ≤ SupVConst + u ^ 2 :=
    add_nonneg SupVConst_nonneg_adm (sq_nonneg u)
  have h1 := hC s hs (SupVConst + u ^ 2) hlam
  have hb : (0:ℝ) < 1 + u ^ 2 := by positivity
  have hle : (1:ℝ) + u ^ 2 ≤ 1 + (SupVConst + u ^ 2) := by
    have := SupVConst_nonneg_adm
    linarith
  have h2 : ((1:ℝ) + (SupVConst + u ^ 2))⁻¹ ≤ ((1:ℝ) + u ^ 2)⁻¹ := by
    first
      | gcongr
      | exact inv_le_inv_of_le hb hle
  exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hCpos.le)

#print axioms admissibleFreeStage_eq_FstageFinite
#print axioms admissibleFreeStage_holo
#print axioms freeResolvent_norm_le_on_compact

end

end RHFormalization
