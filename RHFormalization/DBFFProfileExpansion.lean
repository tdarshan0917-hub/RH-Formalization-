import RHFormalization.AdmissibleContinuationEndpoint
import RHFormalization.MontelUniqueLimit

/-!
# D.BFF finite-profile expansion scaffold (manuscript D.BFF / D.BULK-UNIFORM)

ROUTE CARD
1. Target: infrastructure for the live endpoints `RH_from_admissible_continuation`
   / `RH_from_model_continuation`.
2. F/B/R used: NONE — generic in an abstract residual family `Rbulk`.
3. Raw B on Ω required?  NO.
4. R = F − raw B forced on Ω by per-stage holomorphy + overlap?  NO
   (no stage split appears in this file).
5. Satisfiable / non-vacuous?  YES — instantiated by the manuscript's canonical
   bulk remainder (D.BFF.6, canonical normalization, ε ≡ 0 allowed).
6. Manuscript object: `R_α = Σ_{j≤J} c_{α,j}·Φ_j + ε_α` (D.BFF.6), J finite and
   fixed, Φ_j fixed Ω-holomorphic profiles, density-normalized coefficients;
   D.BULK-UNIFORM local boundedness; D.CAN-REM canonical form.
7. Named consumer: `RH_from_DBFF_expansion` (RHFromDBFFExpansion.lean).

Pin facts encoded here: `HolomorphicOnC = AnalyticOn ℂ` (abbrev, AnalyticWrappers);
`IsCompact.exists_bound_of_continuousOn` returns 2 components (no nonneg);
`add_le_add_right` unifies with the flipped shape in this pin — avoided.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter Metric

open scoped BigOperators Topology

/-- **D.BFF profile expansion data**: a residual family expanded over finitely
many fixed Ω-holomorphic profiles with uniformly bounded coefficients and a
locally bounded error. -/
structure DBFFProfileExpansionData where
  J : ℕ
  Phi : Fin J → ℂ → ℂ
  coeff : ℕ → Fin J → ℂ
  eps : ℕ → ℂ → ℂ
  Rbulk : ℕ → ℂ → ℂ
  h_expansion : ∀ n : ℕ, ∀ s ∈ Ω,
    Rbulk n s = (∑ j : Fin J, coeff n j * Phi j s) + eps n s
  h_Phi_holo : ∀ j : Fin J, HolomorphicOnC (Phi j) Ω
  h_coeff_bdd : ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ n : ℕ, ∀ j : Fin J, ‖coeff n j‖ ≤ Cc
  h_eps_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
    ∃ Ce : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖eps n s‖ ≤ Ce

namespace DBFFProfileExpansionData

variable (D : DBFFProfileExpansionData)

/-- Each profile is bounded (with a nonnegative constant) on every Ω-compact. -/
theorem Phi_bound_on_compact (j : Fin D.J)
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ s ∈ K, ‖D.Phi j s‖ ≤ Cj := by
  have hcont : ContinuousOn (D.Phi j) K :=
    ((D.h_Phi_holo j).continuousOn).mono hKO
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max C0 0, le_max_right _ _, fun s hs => ?_⟩
  exact le_trans (hC0 s hs) (le_max_left _ _)

/-- **D.BULK-UNIFORM (abstract form)**: the profile expansion gives local
boundedness of the residual family on Ω-compacts — Montel's input. -/
theorem loc_bdd :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖D.Rbulk n s‖ ≤ C := by
  intro K hK hKO
  obtain ⟨Cc, hCc0, hCc⟩ := D.h_coeff_bdd
  obtain ⟨Ce, hCe⟩ := D.h_eps_bdd K hK hKO
  choose CP hCP0 hCP using fun j => D.Phi_bound_on_compact j K hK hKO
  refine ⟨Cc * (∑ j : Fin D.J, CP j) + Ce, ?_⟩
  intro n s hs
  rw [D.h_expansion n s (hKO hs)]
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin D.J)),
      ‖D.coeff n j * D.Phi j s‖ ≤ Cc * CP j := by
    intro j _
    rw [norm_mul]
    exact mul_le_mul (hCc n j) (hCP j s hs) (norm_nonneg _) hCc0
  calc ‖(∑ j : Fin D.J, D.coeff n j * D.Phi j s) + D.eps n s‖
      ≤ ‖∑ j : Fin D.J, D.coeff n j * D.Phi j s‖ + ‖D.eps n s‖ :=
        norm_add_le _ _
    _ ≤ (∑ j : Fin D.J, ‖D.coeff n j * D.Phi j s‖) + Ce :=
        add_le_add (norm_sum_le _ _) (hCe n s hs)
    _ ≤ (∑ j : Fin D.J, Cc * CP j) + Ce :=
        add_le_add (Finset.sum_le_sum hterm) le_rfl
    _ = Cc * (∑ j : Fin D.J, CP j) + Ce := by rw [Finset.mul_sum]

/-- **D.CAN-REM from converging coefficients (canonical normalized form)**:
when the coefficients converge and the error tends to 0 on Ω-compacts, the
residual family converges in the exact `DMasterResidualData` eps-N shape to
the finite profile limit — no Montel needed. -/
theorem tendsto_profile_limit
    (climit : Fin D.J → ℂ)
    (h_cconv : ∀ j : Fin D.J,
        Tendsto (fun n => D.coeff n j) atTop (𝓝 (climit j)))
    (h_eps0 : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ s ∈ K, ‖D.eps n s‖ ≤ ε) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ s ∈ K,
          dist (D.Rbulk n s) (∑ j : Fin D.J, climit j * D.Phi j s) < ε := by
  intro K hK hKO ε hε
  choose CP hCP0 hCP using fun j => D.Phi_bound_on_compact j K hK hKO
  have hS0 : (0 : ℝ) ≤ ∑ j : Fin D.J, CP j :=
    Finset.sum_nonneg fun j _ => hCP0 j
  have hS1 : (0 : ℝ) < (∑ j : Fin D.J, CP j) + 1 := by linarith
  set δ : ℝ := ε / (2 * ((∑ j : Fin D.J, CP j) + 1)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    positivity
  choose Nj hNj using fun j : Fin D.J =>
    (Metric.tendsto_atTop.mp (h_cconv j)) δ hδpos
  set N0 : ℕ := Finset.univ.sup Nj with hN0def
  have hcoefN : ∀ n : ℕ, N0 ≤ n → ∀ j : Fin D.J,
      ‖D.coeff n j - climit j‖ < δ := by
    intro n hn j
    have hj : Nj j ≤ N0 := Finset.le_sup (Finset.mem_univ j)
    have := hNj j n (le_trans hj hn)
    rwa [dist_eq_norm] at this
  have hε4 : (0 : ℝ) < ε / 4 := by positivity
  have heps := h_eps0 K hK hKO (ε / 4) hε4
  have hcoefEv : ∀ᶠ n in atTop, ∀ j : Fin D.J,
      ‖D.coeff n j - climit j‖ < δ :=
    Filter.eventually_atTop.mpr ⟨N0, hcoefN⟩
  filter_upwards [hcoefEv, heps] with n h1 h2
  intro s hs
  rw [dist_eq_norm, D.h_expansion n s (hKO hs)]
  have hsplit : (∑ j : Fin D.J, D.coeff n j * D.Phi j s) + D.eps n s
        - ∑ j : Fin D.J, climit j * D.Phi j s
      = (∑ j : Fin D.J, (D.coeff n j - climit j) * D.Phi j s)
          + D.eps n s := by
    have h3 : ∑ j : Fin D.J, (D.coeff n j - climit j) * D.Phi j s
        = ∑ j : Fin D.J,
            (D.coeff n j * D.Phi j s - climit j * D.Phi j s) :=
      Finset.sum_congr rfl (fun j _ => sub_mul _ _ _)
    rw [h3, Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  have hterm : ∀ j : Fin D.J,
      ‖(D.coeff n j - climit j) * D.Phi j s‖ ≤ δ * CP j := by
    intro j
    rw [norm_mul]
    exact mul_le_mul (le_of_lt (h1 j)) (hCP j s hs)
      (norm_nonneg _) hδpos.le
  have hsum : ‖∑ j : Fin D.J, (D.coeff n j - climit j) * D.Phi j s‖
      ≤ δ * (∑ j : Fin D.J, CP j) := by
    calc ‖∑ j : Fin D.J, (D.coeff n j - climit j) * D.Phi j s‖
        ≤ ∑ j : Fin D.J, ‖(D.coeff n j - climit j) * D.Phi j s‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j : Fin D.J, δ * CP j :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = δ * (∑ j : Fin D.J, CP j) := by rw [Finset.mul_sum]
  have hδS : δ * (∑ j : Fin D.J, CP j) ≤ ε / 2 := by
    have hδS1 : δ * ((∑ j : Fin D.J, CP j) + 1) = ε / 2 := by
      rw [hδdef]
      field_simp
    have h4 : δ * (∑ j : Fin D.J, CP j)
        ≤ δ * ((∑ j : Fin D.J, CP j) + 1) := by
      have := hδpos.le
      nlinarith
    linarith
  calc ‖(∑ j : Fin D.J, (D.coeff n j - climit j) * D.Phi j s) + D.eps n s‖
      ≤ ‖∑ j : Fin D.J, (D.coeff n j - climit j) * D.Phi j s‖
          + ‖D.eps n s‖ := norm_add_le _ _
    _ ≤ δ * (∑ j : Fin D.J, CP j) + ε / 4 := add_le_add hsum (h2 s hs)
    _ ≤ ε / 2 + ε / 4 := add_le_add hδS le_rfl
    _ < ε := by linarith

/-- The finite profile limit is holomorphic on Ω. -/
theorem profile_limit_holo (climit : Fin D.J → ℂ) :
    HolomorphicOnC (fun s => ∑ j : Fin D.J, climit j * D.Phi j s) Ω := by
  change AnalyticOn ℂ (fun s => ∑ j : Fin D.J, climit j * D.Phi j s) Ω
  let F : Fin D.J → ℂ → ℂ := fun j s => climit j * D.Phi j s
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin D.J)),
      AnalyticOn ℂ (F j) Ω := by
    intro j _
    dsimp [F]
    first
      | exact analyticOn_const.mul (D.h_Phi_holo j)
      | exact (analyticOnNhd_const.analyticOn).mul (D.h_Phi_holo j)
  have hsum : AnalyticOn ℂ (∑ j : Fin D.J, F j) Ω :=
    Finset.analyticOn_sum (Finset.univ : Finset (Fin D.J)) hterm
  have hfun :
      (fun s => ∑ j : Fin D.J, climit j * D.Phi j s)
        = (∑ j : Fin D.J, F j) := by
    funext s
    simp [F]
  rw [hfun]
  exact hsum

end DBFFProfileExpansionData

#print axioms DBFFProfileExpansionData.Phi_bound_on_compact
#print axioms DBFFProfileExpansionData.loc_bdd
#print axioms DBFFProfileExpansionData.tendsto_profile_limit
#print axioms DBFFProfileExpansionData.profile_limit_holo

end

end RHFormalization
