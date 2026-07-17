import RHFormalization.ShiftedLaplaceRepWitnessExtensionViaOrder
import RHFormalization.ShiftedLaplaceHoloLocalReduction
import RHFormalization.HExplicitFormulaLocalCancellation
import RHFormalization.MeromorphyAwayFromPoles
import RHFormalization.PairPoleIsolation
import RHFormalization.ExplicitFormulaRegularBranch
import RHFormalization.HMeromorphicPackage
import Mathlib.Analysis.Meromorphic.Order

namespace RHFormalization
noncomputable section
open Complex Filter Topology Metric
open scoped Classical

/-- The raw prime+pole sum. -/
noncomputable def repRaw (sigma0 : ℝ) : ℂ → ℂ :=
  fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s
    + ZpoleRepSeries defaultZeroMultiplicityData s

/-- The corrected global function: raw sum patched at each pole point to its
removable-limit value. Honest holomorphic object; equals raw off the pole set. -/
noncomputable def repCorrectedGlobal (sigma0 : ℝ) : ℂ → ℂ :=
  fun s => if s ∈ ZeroPoleSet then limUnder (𝓝[≠] s) (repRaw sigma0) else repRaw sigma0 s

theorem repCorrectedGlobal_eq_raw_of_notMem
    (sigma0 : ℝ) {s : ℂ} (hs : s ∉ ZeroPoleSet) :
    repCorrectedGlobal sigma0 s = repRaw sigma0 s := by
  simp only [repCorrectedGlobal, if_neg hs]

theorem eventually_notMem_zeroPoleSet_of_notMem
    {z : ℂ} (hzΩ : z ∈ Ω) (hz : z ∉ ZeroPoleSet) :
    ∀ᶠ w in 𝓝 z, w ∉ ZeroPoleSet := by
  obtain ⟨r, hr, hiso⟩ := nonpole_isolated z hzΩ hz
  filter_upwards [Metric.ball_mem_nhds z hr] with w hw hmem
  obtain ⟨ρ, hρ, hwρ⟩ := hmem
  have hd := hiso ρ hρ
  rw [Metric.mem_ball] at hw
  rw [hwρ] at hw
  have := dist_comm w z
  rw [hwρ] at this
  linarith [hw, hd, this]

theorem eventually_ne_notMem_zeroPoleSet_at_witness (W : ZeroWitness) :
    ∀ᶠ w in 𝓝 W.s0, w ≠ W.s0 → w ∉ ZeroPoleSet := by
  obtain ⟨r, hr, hbound⟩ := pairPole_isolated W
  filter_upwards [Metric.ball_mem_nhds W.s0 hr] with w hw hne hmem
  obtain ⟨ρ', hρ', hwρ'⟩ := hmem
  by_cases hpair : ρ' = W.ρ ∨ ρ' = 1 - W.ρ
  · have hps0 : polePoint ρ' = W.s0 := by
      rcases hpair with hp | hp
      · rw [hp]; exact W.hs0_def.symm
      · rw [hp]
        have hrefl : polePoint (1 - W.ρ) = polePoint W.ρ := by
          unfold polePoint; ring
        rw [hrefl]; exact W.hs0_def.symm
    rw [hwρ', hps0] at hne
    exact hne rfl
  · push_neg at hpair
    have hd := hbound ρ' hρ' hpair.1 hpair.2
    rw [Metric.mem_ball] at hw
    have := dist_comm w W.s0
    rw [hwρ'] at hw this
    linarith [hw, hd, this]

theorem repCorrectedGlobal_holomorphicOn
    (sigma0 : ℝ) (ZF : ZetaZeroFacts)
    (hBpp : ∀ W : ZeroWitness,
      HasPrincipalPartAtC
        (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
        W.s0 (-(zetaZeroMult W.ρ : ℂ)))
    (hZpp_rep : ∀ W : ZeroWitness,
      HasPrincipalPartAtC (ZpoleRepSeries defaultZeroMultiplicityData)
        W.s0 ((zetaZeroMult W.ρ : ℂ)))
    (h_regular : ∀ z : ℂ, z ∈ Ω → (∀ W : ZeroWitness, z ≠ W.s0) →
      HolomorphicAtC (repRaw sigma0) z) :
    HolomorphicOnC (repCorrectedGlobal sigma0) Ω := by
  classical
  apply holomorphicOnC_from_local_extensions_Omega
  intro z hzΩ
  by_cases hw : ∃ W : ZeroWitness, z = W.s0
  · obtain ⟨W, rfl⟩ := hw
    obtain ⟨h, hh_holo, hh_punct, hh_val⟩ :=
      repWitness_extension_via_order sigma0 W (hBpp W) (hZpp_rep W)
    refine ⟨h, hh_holo, ?_⟩
    apply localEqAtC_of_punctured_eventuallyEq_and_point_eq
    · rw [eventually_nhdsWithin_iff] at hh_punct
      filter_upwards [eventually_ne_notMem_zeroPoleSet_at_witness W, hh_punct]
        with w hiso hhw hne
      rw [hhw hne, repCorrectedGlobal_eq_raw_of_notMem sigma0 (hiso hne)]
      rfl
    · have hWmem : W.s0 ∈ ZeroPoleSet := ⟨W.ρ, W.h_zero, W.hs0_def⟩
      rw [hh_val]
      simp only [repCorrectedGlobal, if_pos hWmem]
      rfl
  · push_neg at hw
    have hznp : z ∉ ZeroPoleSet := not_zeroPoleSet_of_not_zeroWitness ZF z hzΩ hw
    refine ⟨repRaw sigma0, h_regular z hzΩ hw, ?_⟩
    have hev : ∀ᶠ w in 𝓝 z, w ∉ ZeroPoleSet :=
      eventually_notMem_zeroPoleSet_of_notMem hzΩ hznp
    filter_upwards [hev] with w hw using (repCorrectedGlobal_eq_raw_of_notMem sigma0 hw).symm

#print axioms repCorrectedGlobal_holomorphicOn

end
end RHFormalization
