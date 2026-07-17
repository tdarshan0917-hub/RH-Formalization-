import RHFormalization.ShiftedLaplaceRepWitnessExtensionViaOrder
import RHFormalization.ShiftedLaplaceRepCorrectedHolo
import RHFormalization.PrincipalPartMeromorphic
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

theorem genRepSum_meromorphicOrderAt_nonneg
    (B : ℂ → ℂ) (W : ZeroWitness)
    (hBpp : HasPrincipalPartAtC B W.s0 (-(zetaZeroMult W.ρ : ℂ)))
    (hZpp_rep : HasPrincipalPartAtC (ZpoleRepSeries defaultZeroMultiplicityData)
      W.s0 ((zetaZeroMult W.ρ : ℂ))) :
    0 ≤ meromorphicOrderAt
          (fun s => B s + ZpoleRepSeries defaultZeroMultiplicityData s) W.s0 := by
  classical
  obtain ⟨hF, hF_an, hF_eq⟩ := hBpp
  obtain ⟨hG, hG_an, hG_eq⟩ := hZpp_rep
  have hpunct : (fun s => B s + ZpoleRepSeries defaultZeroMultiplicityData s)
      =ᶠ[𝓝[≠] W.s0] (fun s => hF s + hG s) := by
    rw [eventuallyEq_nhdsWithin_iff]
    filter_upwards [hF_eq, hG_eq] with w hFw hGw hwne
    rw [hFw hwne, hGw hwne]; ring
  have hAn : AnalyticAt ℂ (fun s => hF s + hG s) W.s0 := hF_an.add hG_an
  rw [meromorphicOrderAt_congr hpunct]
  exact hAn.meromorphicOrderAt_nonneg

theorem genRepWitness_extension_via_order
    (B : ℂ → ℂ) (W : ZeroWitness)
    (hBpp : HasPrincipalPartAtC B W.s0 (-(zetaZeroMult W.ρ : ℂ)))
    (hZpp_rep : HasPrincipalPartAtC (ZpoleRepSeries defaultZeroMultiplicityData)
      W.s0 ((zetaZeroMult W.ρ : ℂ))) :
    ∃ h : ℂ → ℂ,
      HolomorphicAtC h W.s0 ∧
        (∀ᶠ w in 𝓝[≠] W.s0,
          h w = B w + ZpoleRepSeries defaultZeroMultiplicityData w) ∧
        h W.s0 = limUnder (𝓝[≠] W.s0)
          (fun s => B s + ZpoleRepSeries defaultZeroMultiplicityData s) := by
  classical
  have hMerB : MeromorphicAt B W.s0 :=
    hasPrincipalPartAtC_meromorphicAt _ W.s0 _ hBpp
  have hMerZ : MeromorphicAt (ZpoleRepSeries defaultZeroMultiplicityData) W.s0 :=
    hasPrincipalPartAtC_meromorphicAt _ W.s0 _ hZpp_rep
  have hMer : MeromorphicAt
      (fun s => B s + ZpoleRepSeries defaultZeroMultiplicityData s) W.s0 :=
    hMerB.add hMerZ
  have hOrd := genRepSum_meromorphicOrderAt_nonneg B W hBpp hZpp_rep
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hMer hOrd
  have hlim : limUnder (𝓝[≠] W.s0)
      (fun s => B s + ZpoleRepSeries defaultZeroMultiplicityData s) = c := hc.limUnder_eq
  set g : ℂ → ℂ := Function.update
    (fun s => B s + ZpoleRepSeries defaultZeroMultiplicityData s) W.s0 c with hgdef
  have hpunct : (∀ᶠ w in 𝓝[≠] W.s0,
      g w = B w + ZpoleRepSeries defaultZeroMultiplicityData w) := by
    filter_upwards [self_mem_nhdsWithin] with w hwne
    have hne : w ≠ W.s0 := hwne
    simp only [hgdef, Function.update_of_ne hne]
  refine ⟨g, ?_, hpunct, ?_⟩
  · have hMerU : MeromorphicAt g W.s0 :=
      hMer.congr (Filter.EventuallyEq.symm hpunct)
    have hCont : ContinuousAt g W.s0 := by
      have hval : g W.s0 = c := by simp [hgdef]
      rw [continuousAt_iff_punctured_nhds, hval]
      refine hc.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with w hwne
      have hne : w ≠ W.s0 := hwne
      simp only [hgdef, Function.update_of_ne hne]
    exact hMerU.analyticAt hCont
  · have hval : g W.s0 = c := by simp [hgdef]
    rw [hval, hlim]

noncomputable def genRepRaw (B : ℂ → ℂ) : ℂ → ℂ :=
  fun s => B s + ZpoleRepSeries defaultZeroMultiplicityData s

noncomputable def genRepCorrectedGlobal (B : ℂ → ℂ) : ℂ → ℂ :=
  fun s => if s ∈ ZeroPoleSet then limUnder (𝓝[≠] s) (genRepRaw B) else genRepRaw B s

theorem genRepCorrectedGlobal_eq_raw_of_notMem
    (B : ℂ → ℂ) {s : ℂ} (hs : s ∉ ZeroPoleSet) :
    genRepCorrectedGlobal B s = genRepRaw B s := by
  simp only [genRepCorrectedGlobal, if_neg hs]

theorem genRepCorrectedGlobal_holomorphicOn
    (B : ℂ → ℂ) (ZF : ZetaZeroFacts)
    (hBpp : ∀ W : ZeroWitness,
      HasPrincipalPartAtC B W.s0 (-(zetaZeroMult W.ρ : ℂ)))
    (hZpp_rep : ∀ W : ZeroWitness,
      HasPrincipalPartAtC (ZpoleRepSeries defaultZeroMultiplicityData)
        W.s0 ((zetaZeroMult W.ρ : ℂ)))
    (h_regular : ∀ z : ℂ, z ∈ Ω → (∀ W : ZeroWitness, z ≠ W.s0) →
      HolomorphicAtC (genRepRaw B) z) :
    HolomorphicOnC (genRepCorrectedGlobal B) Ω := by
  classical
  apply holomorphicOnC_from_local_extensions_Omega
  intro z hzΩ
  by_cases hw : ∃ W : ZeroWitness, z = W.s0
  · obtain ⟨W, rfl⟩ := hw
    obtain ⟨h, hh_holo, hh_punct, hh_val⟩ :=
      genRepWitness_extension_via_order B W (hBpp W) (hZpp_rep W)
    refine ⟨h, hh_holo, ?_⟩
    apply localEqAtC_of_punctured_eventuallyEq_and_point_eq
    · rw [eventually_nhdsWithin_iff] at hh_punct
      filter_upwards [eventually_ne_notMem_zeroPoleSet_at_witness W, hh_punct]
        with w hiso hhw hne
      rw [hhw hne, genRepCorrectedGlobal_eq_raw_of_notMem B (hiso hne)]
      rfl
    · have hWmem : W.s0 ∈ ZeroPoleSet := ⟨W.ρ, W.h_zero, W.hs0_def⟩
      rw [hh_val]
      simp only [genRepCorrectedGlobal, if_pos hWmem]
      rfl
  · push_neg at hw
    have hznp : z ∉ ZeroPoleSet := not_zeroPoleSet_of_not_zeroWitness ZF z hzΩ hw
    refine ⟨genRepRaw B, h_regular z hzΩ hw, ?_⟩
    have hev : ∀ᶠ w in 𝓝 z, w ∉ ZeroPoleSet :=
      eventually_notMem_zeroPoleSet_of_notMem hzΩ hznp
    filter_upwards [hev] with w hw using (genRepCorrectedGlobal_eq_raw_of_notMem B hw).symm

#print axioms genRepCorrectedGlobal_holomorphicOn

end
end RHFormalization
