import RHFormalization.AdmissibleFreeFiniteRange

/-!
# RHFormalization.AdmissibleFreeTailAssembly

**Front F-adm, brick 1d-ii (closes the free part).** Tail bound + assembly:

  `admissibleFreeStage_to_FHadmFree` — compact ε–N convergence of the
  density-normalized free stages to `FHadmFree`, in the exact
  `DFHLimitData.h_F_stage_to_FH` shape.

Budget on K (δ = cut-distance, C = majorant const, both banked-compact):
finite range `π²/(2(n+2)δ²)` (telescoped, 1d-i) + tail
`(1/2π)·C·(π/2 − arctan((n+2)π))` (via `integral_Ioi_inv_one_add_sq`);
both → 0 along the admissible schedule.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex MeasureTheory

/-- **Schedule identity**: the grid endpoint at the admissible stage is
`U_n = (n+2)·π`. -/
theorem freeGridPt_adm_eq (n : ℕ) :
    freeGridPt (admL n) (admN n) = ((n : ℝ) + 2) * Real.pi := by
  unfold freeGridPt admL admN
  push_cast
  first
    | (rw [div_eq_iff (show ((((n:ℝ)) + 2) ^ 3 : ℝ) ≠ 0 by positivity)]; ring)
    | (field_simp; ring)
    | field_simp

/-- **Bound simplification**: the 1d-i finite-range bound at the admissible
schedule equals `π²/(2(n+2)δ²)`. -/
theorem admFiniteRangeBound_eq {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    1 / (2 * Real.pi) *
        (Real.pi / admL n / δ ^ 2 * freeGridPt (admL n) (admN n) ^ 2)
      = Real.pi ^ 2 / (2 * ((n : ℝ) + 2) * δ ^ 2) := by
  rw [freeGridPt_adm_eq n]
  unfold admL
  have hn : ((n : ℝ) + 2) ≠ 0 := by positivity
  have hδ' : δ ≠ 0 := hδ.ne'
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  first
    | (field_simp; ring)
    | field_simp
    | ring_nf

/-- **Split of the free limit** at any `U ≥ 0`: finite range plus tail. -/
theorem FHadmFree_split {s : ℂ} (hs : s ∈ Ω) (U : ℝ) (hU : 0 ≤ U) :
    FHadmFree s
      = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ u in Set.Ioc (0 : ℝ) U, freeResolventIntegrand s u)
        + ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (∫ u in Set.Ioi U, freeResolventIntegrand s u) := by
  unfold FHadmFree
  rw [← mul_add]
  congr 1
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) U) (Set.Ioi U) := by
    rw [Set.disjoint_left]
    intro x hx hx2
    exact absurd hx.2 (not_le.mpr hx2)
  have hf1 : IntegrableOn (freeResolventIntegrand s) (Set.Ioc (0 : ℝ) U) :=
    (freeResolventIntegrand_integrableOn hs).mono_set Set.Ioc_subset_Ioi_self
  have hf2 : IntegrableOn (freeResolventIntegrand s) (Set.Ioi U) :=
    (freeResolventIntegrand_integrableOn hs).mono_set (Set.Ioi_subset_Ioi hU)
  rw [← Set.Ioc_union_Ioi_eq_Ioi hU]
  first
    | exact setIntegral_union hdisj measurableSet_Ioi hf1 hf2
    | exact MeasureTheory.integral_union hdisj measurableSet_Ioi hf1 hf2

/-- **Tail bound**: beyond `U ≥ 0`, the free integral is controlled by
`C·(π/2 − arctan U)` given the compact majorant. -/
theorem freeResolvent_tail_norm_le {s : ℂ} (hs : s ∈ Ω)
    {C : ℝ}
    (hmaj : ∀ u : ℝ, ‖freeResolventIntegrand s u‖ ≤ C * ((1 : ℝ) + u ^ 2)⁻¹)
    {U : ℝ} (hU : 0 ≤ U) :
    ‖∫ u in Set.Ioi U, freeResolventIntegrand s u‖
      ≤ C * (Real.pi / 2 - Real.arctan U) := by
  have hf2 : IntegrableOn (freeResolventIntegrand s) (Set.Ioi U) :=
    (freeResolventIntegrand_integrableOn hs).mono_set (Set.Ioi_subset_Ioi hU)
  have hg : IntegrableOn (fun u : ℝ => C * ((1 : ℝ) + u ^ 2)⁻¹)
      (Set.Ioi U) :=
    (integrable_inv_one_add_sq.integrableOn).const_mul C
  calc ‖∫ u in Set.Ioi U, freeResolventIntegrand s u‖
      ≤ ∫ u in Set.Ioi U, ‖freeResolventIntegrand s u‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ u in Set.Ioi U, C * ((1 : ℝ) + u ^ 2)⁻¹ :=
        setIntegral_mono_on hf2.norm hg measurableSet_Ioi
          (fun u _ => hmaj u)
    _ = C * ∫ u in Set.Ioi U, ((1 : ℝ) + u ^ 2)⁻¹ := by
        first
          | exact integral_const_mul C _
          | rw [integral_const_mul]
          | rw [MeasureTheory.integral_const_mul]
    _ = C * (Real.pi / 2 - Real.arctan U) := by
        first
          | rw [integral_Ioi_inv_one_add_sq]
          | rw [MeasureTheory.integral_Ioi_inv_one_add_sq]

/-- **BRICK 1 CLOSES: the free stages converge to `FHadmFree` on Ω-compacts**,
in the exact `DFHLimitData.h_F_stage_to_FH` eps-N shape. -/
theorem admissibleFreeStage_to_FHadmFree :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in Filter.atTop, ∀ s : ℂ, s ∈ K →
          dist (admissibleFreeStage n s) (FHadmFree s) < ε := by
  intro K hK hKO ε hε
  obtain ⟨δ, hδpos, hδ⟩ := exists_uniform_lower_bound_on_compact K hK hKO
  obtain ⟨C, hCpos, hC⟩ := freeResolvent_norm_le_on_compact K hK hKO
  have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ))
      Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 2))
      Filter.atTop Filter.atTop := by
    first
      | exact tendsto_atTop_add_const_right _ 2 hcast
      | exact Filter.tendsto_atTop_add_const_right _ 2 hcast
  have hA : Filter.Tendsto
      (fun n : ℕ => Real.pi ^ 2 / (2 * ((n : ℝ) + 2) * δ ^ 2))
      Filter.atTop (nhds 0) := by
    have hshape : (fun n : ℕ => Real.pi ^ 2 / (2 * ((n : ℝ) + 2) * δ ^ 2))
        = fun n : ℕ => (Real.pi ^ 2 / (2 * δ ^ 2)) * (((n : ℝ) + 2))⁻¹ := by
      funext n
      have hn : ((n : ℝ) + 2) ≠ 0 := by positivity
      have hδ' : δ ≠ 0 := hδpos.ne'
      first
        | (field_simp; ring)
        | field_simp
    rw [hshape]
    have hinv : Filter.Tendsto (fun n : ℕ => (((n : ℝ) + 2))⁻¹)
        Filter.atTop (nhds 0) := by
      first
        | exact h1.inv_tendsto_atTop
        | simpa using h1.inv_tendsto_atTop
    simpa using hinv.const_mul (Real.pi ^ 2 / (2 * δ ^ 2))
  have h2 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 2) * Real.pi)
      Filter.atTop Filter.atTop := h1.atTop_mul_const Real.pi_pos
  have harctan : Filter.Tendsto Real.arctan Filter.atTop
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) := by
    first
      | exact Real.tendsto_arctan_atTop
      | exact tendsto_arctan_atTop
  have harct : Filter.Tendsto
      (fun n : ℕ => Real.arctan (((n : ℝ) + 2) * Real.pi))
      Filter.atTop (nhds (Real.pi / 2)) := by
    first
      | exact tendsto_nhds_of_tendsto_nhdsWithin (harctan.comp h2)
      | simpa [Function.comp]
          using tendsto_nhds_of_tendsto_nhdsWithin (harctan.comp h2)
  have hB : Filter.Tendsto
      (fun n : ℕ => 1 / (2 * Real.pi) * C *
        (Real.pi / 2 - Real.arctan (((n : ℝ) + 2) * Real.pi)))
      Filter.atTop (nhds 0) := by
    have hsub : Filter.Tendsto
        (fun n : ℕ => Real.pi / 2 - Real.arctan (((n : ℝ) + 2) * Real.pi))
        Filter.atTop (nhds (Real.pi / 2 - Real.pi / 2)) :=
      Filter.Tendsto.sub tendsto_const_nhds harct
    have hsub0 : Filter.Tendsto
        (fun n : ℕ => Real.pi / 2 - Real.arctan (((n : ℝ) + 2) * Real.pi))
        Filter.atTop (nhds 0) := by simpa using hsub
    simpa using hsub0.const_mul (1 / (2 * Real.pi) * C)
  have htot : Filter.Tendsto
      (fun n : ℕ => Real.pi ^ 2 / (2 * ((n : ℝ) + 2) * δ ^ 2)
        + 1 / (2 * Real.pi) * C *
            (Real.pi / 2 - Real.arctan (((n : ℝ) + 2) * Real.pi)))
      Filter.atTop (nhds 0) := by
    simpa using hA.add hB
  have heps := htot.eventually (gt_mem_nhds hε)
  filter_upwards [heps] with n hn
  intro s hs
  have hsΩ : s ∈ Ω := hKO hs
  have hU0 : 0 ≤ freeGridPt (admL n) (admN n) :=
    freeGridPt_nonneg (admL n) (admL_pos n) (admN n)
  have hsplit := FHadmFree_split hsΩ (freeGridPt (admL n) (admN n)) hU0
  rw [dist_eq_norm, hsplit]
  have halg : admissibleFreeStage n s
      - (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (∫ u in Set.Ioc (0 : ℝ) (freeGridPt (admL n) (admN n)),
              freeResolventIntegrand s u)
          + ((1 / (2 * Real.pi) : ℝ) : ℂ) *
              (∫ u in Set.Ioi (freeGridPt (admL n) (admN n)),
                freeResolventIntegrand s u))
      = (admissibleFreeStage n s
          - ((1 / (2 * Real.pi) : ℝ) : ℂ) *
              (∫ u in Set.Ioc (0 : ℝ) (freeGridPt (admL n) (admN n)),
                freeResolventIntegrand s u))
        - ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (∫ u in Set.Ioi (freeGridPt (admL n) (admN n)),
              freeResolventIntegrand s u) := by
    ring
  rw [halg]
  refine lt_of_le_of_lt (le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)) hn
  · have hpart1 := admissibleFreeStage_finiteRange_diff_le hsΩ hδpos
      (fun lam hlam => hδ s hs lam hlam) n
    refine le_trans hpart1 ?_
    exact le_of_eq (admFiniteRangeBound_eq hδpos n)
  · rw [norm_mul]
    have hnc : ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (by positivity)
    rw [hnc]
    have htail := freeResolvent_tail_norm_le hsΩ
      (fun u => hC s hs u) hU0
    have hstep : 1 / (2 * Real.pi) *
        ‖∫ u in Set.Ioi (freeGridPt (admL n) (admN n)),
            freeResolventIntegrand s u‖
        ≤ 1 / (2 * Real.pi) *
            (C * (Real.pi / 2 - Real.arctan (freeGridPt (admL n) (admN n)))) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    refine le_trans hstep ?_
    exact le_of_eq (by rw [freeGridPt_adm_eq n]; ring)

#print axioms freeGridPt_adm_eq
#print axioms admFiniteRangeBound_eq
#print axioms FHadmFree_split
#print axioms freeResolvent_tail_norm_le
#print axioms admissibleFreeStage_to_FHadmFree

end

end RHFormalization
