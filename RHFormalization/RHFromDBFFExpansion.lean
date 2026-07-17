import RHFormalization.DBFFProfileExpansion

/-!
# RH from an instantiated D.BFF expansion

ROUTE CARD
1. Target: RiemannHypothesis via `RH_from_admissible_continuation` (live endpoint).
2. F: FHadmFree (banked O(Ω)).  B: Bshared, OVERLAP-ONLY.  R: the profile limit.
3. Raw B on Ω?  NO.   R = F − raw B forced on Ω?  NO.
4. Manuscript object: D.BFF.6 expansion + D.CAN-REM identification.
5. Remaining input after this brick: ONE concrete `DBFFProfileExpansionData`
   for the admissible net with (i) coefficient convergence, (ii) ε → 0,
   (iii) the overlap identity on RHP(1).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped BigOperators Topology

/-- **RH from an instantiated D.BFF profile expansion.** -/
theorem RH_from_DBFF_expansion
    (D : DBFFProfileExpansionData)
    (climit : Fin D.J → ℂ)
    (h_cconv : ∀ j : Fin D.J,
        Tendsto (fun n => D.coeff n j) atTop (𝓝 (climit j)))
    (h_eps0 : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ s ∈ K, ‖D.eps n s‖ ≤ ε)
    (h_overlap : ∀ s ∈ RightHalfPlane (1 : ℝ),
        Tendsto (fun n => D.Rbulk n s) atTop
          (𝓝 (FHadmFree s - (shiftedLaplacePrimePackageAt 1).Bshared s))) :
    RiemannHypothesis := by
  refine RH_from_admissible_continuation
    (fun s => ∑ j : Fin D.J, climit j * D.Phi j s)
    (D.profile_limit_holo climit) ?_
  intro s hs
  have hsΩ : s ∈ Ω := by
    first
      | exact rightHalfPlane_subset_Omega (1 : ℝ) (by norm_num) hs
      | exact rightHalfPlane_subset_Omega 1 one_pos hs
      | exact rightHalfPlane_subset_Omega _ (by norm_num) hs
  have h1 : Tendsto (fun n => D.Rbulk n s) atTop
      (𝓝 (∑ j : Fin D.J, climit j * D.Phi j s)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have h := D.tendsto_profile_limit climit h_cconv h_eps0 {s}
      isCompact_singleton (Set.singleton_subset_iff.mpr hsΩ) ε hε
    filter_upwards [h] with n hn
    first
      | exact hn s rfl
      | exact hn s (Set.mem_singleton s)
  have h2 := h_overlap s hs
  have heq : (∑ j : Fin D.J, climit j * D.Phi j s)
      = FHadmFree s - (shiftedLaplacePrimePackageAt 1).Bshared s :=
    tendsto_nhds_unique h1 h2
  have heq' :
      (fun z : ℂ => ∑ j : Fin D.J, climit j * D.Phi j z) s
        = FHadmFree s - (shiftedLaplacePrimePackageAt 1).Bshared s := by
    simpa using heq
  rw [heq']
  ring

#print axioms RH_from_DBFF_expansion

end

end RHFormalization
