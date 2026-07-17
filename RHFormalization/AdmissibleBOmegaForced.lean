import RHFormalization.AdmissibleBConvReduction

/-!
# The forced identity of `Bω` on the overlap

Any pair `(Bω, hBconv)` feeding `RH_from_admissible_B_conv` must satisfy
`Bω = galerkinBcanLimitData.Bcan` on `RightHalfPlane 1` — pointwise limits
are unique, and `admissible_hB` is banked.  This pins the target object of
the open frontier: `hBconv` is precisely the statement that the canonical
B-limit continues holomorphically to Ω along the admissible net.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped Topology

/-- **Bω is forced on the overlap**: any admissible B-side limit agrees with
the banked canonical limit on `RightHalfPlane 1`. -/
theorem admissible_Bomega_forced
    (Bω : ℂ → ℂ)
    (hBconv : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in Filter.atTop, ∀ s : ℂ, s ∈ K →
          dist (galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s)
            (Bω s) < ε) :
    ∀ s ∈ RightHalfPlane (1 : ℝ), Bω s = galerkinBcanLimitData.Bcan s := by
  intro s hs
  have hsΩ : s ∈ Ω := by
    first
      | exact rightHalfPlane_subset_Omega (1 : ℝ) (by norm_num) hs
      | exact rightHalfPlane_subset_Omega 1 (by norm_num) hs
  have h1 : Tendsto
      (fun n : ℕ =>
        galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s)
      atTop (𝓝 (Bω s)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have h := hBconv {s} isCompact_singleton
      (Set.singleton_subset_iff.mpr hsΩ) ε hε
    filter_upwards [h] with n hn
    first
      | exact hn s rfl
      | exact hn s (Set.mem_singleton s)
  exact tendsto_nhds_unique h1 (admissible_hB s hs)

#print axioms admissible_Bomega_forced

end

end RHFormalization
