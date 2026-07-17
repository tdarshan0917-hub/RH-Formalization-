import RHFormalization.LogDerivResidue

/-!
# RHFormalization.RemovableDiv
**Removable singularity (existence form).** If `F` is analytic at `s0` with `F s0 = 0`,
there is an analytic `G` at `s0` agreeing with `F w / (w - s0)` for `w ≠ s0` near `s0`.
No `sorry`.
-/

set_option autoImplicit false

namespace RHFormalization

open Complex Filter Topology

theorem removable_div_exists
    {F : ℂ → ℂ} {s0 : ℂ}
    (hF : AnalyticAt ℂ F s0) (hF0 : F s0 = 0) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G s0 ∧
      ∀ᶠ w in 𝓝 s0, w ≠ s0 → F w / (w - s0) = G w := by
  by_cases hev : ∀ᶠ w in 𝓝 s0, F w = 0
  · refine ⟨fun _ => 0, analyticAt_const, ?_⟩
    filter_upwards [hev] with w hw _
    simp [hw]
  · have hneTop : analyticOrderAt F s0 ≠ ⊤ := by
      rw [Ne, analyticOrderAt_eq_top]; exact hev
    set k := analyticOrderNatAt F s0 with hk_def
    have hk_cast : analyticOrderAt F s0 = (k : ℕ) := by
      rw [hk_def, Nat.cast_analyticOrderNatAt hneTop]
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · exfalso
        have hz : analyticOrderAt F s0 = 0 := by rw [hk_cast, h0]; simp
        rw [analyticOrderAt_eq_zero] at hz
        rcases hz with h | h
        · exact h hF
        · exact h hF0
      · exact hpos
    obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := analytic_factor_at_zero hF hk_cast
    refine ⟨fun w => (w - s0) ^ (k - 1) * g w,
      ((analyticAt_id.sub analyticAt_const).pow (k - 1)).mul hg_an, ?_⟩
    filter_upwards [hg_eq] with w hw hwne
    have hsub : w - s0 ≠ 0 := sub_ne_zero.mpr hwne
    rw [hw]
    have hk1 : (w - s0) ^ k = (w - s0) ^ (k - 1) * (w - s0) := by
      conv_lhs => rw [show k = (k - 1) + 1 from by omega]
      rw [pow_succ]
    rw [hk1]
    field_simp

#print axioms removable_div_exists

end RHFormalization
