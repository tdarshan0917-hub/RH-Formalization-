import RHFormalization.AscoliLocBddBridge
import Mathlib

/-!
# MontelOnOpen — QR-6a: Montel extraction on any open `U ⊆ ℂ`

The banked Montel/Ascoli chain (AscoliBridgeLayer1–3, AscoliObligationDirect,
AscoliLocBddBridge) is stated on Ω but uses only that Ω is open. This file restates it
for an arbitrary open `U`: a locally bounded sequence of holomorphic functions on `U` has,
along any subsequence, a further subsequence converging locally uniformly on `U`-compacts
to a holomorphic limit. Proofs are the banked ones with `isOpen_Omega` replaced by `hU`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Filter Topology Complex Metric Set

open scoped NNReal

/-- Bundle a holomorphic-on-`U` function into `C(↥U, ℂ)`. -/
def bundleCU {U : Set ℂ} (hU : IsOpen U) (f : ℂ → ℂ) (hf : HolomorphicOnC f U) :
    C(U, ℂ) :=
  ⟨U.restrict f, by
    apply ContinuousOn.restrict
    exact ((hU.analyticOn_iff_analyticOnNhd).mp hf).continuousOn⟩

@[simp] theorem bundleCU_apply {U : Set ℂ} (hU : IsOpen U) (f : ℂ → ℂ)
    (hf : HolomorphicOnC f U) (s : ℂ) (hs : s ∈ U) :
    (bundleCU hU f hf) ⟨s, hs⟩ = f s := rfl

/-- Closed embedding of `C(↥U, ℂ)` into uniform convergence on compacts. -/
theorem isClosedEmbedding_toUOFC_open {U : Set ℂ} (hU : IsOpen U) :
    IsClosedEmbedding
      (ContinuousMap.toUniformOnFunIsCompact :
        C(U, ℂ) → UniformOnFun ↥U ℂ {K | IsCompact K}) := by
  have hemb := ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact
      (α := ↥U) (β := ℂ) |>.isEmbedding
  haveI : LocallyCompactSpace ↥U := hU.locallyCompactSpace
  have hclosed : IsClosed (Set.range
      (ContinuousMap.toUniformOnFunIsCompact :
        C(U, ℂ) → UniformOnFun ↥U ℂ {K | IsCompact K})) := by
    rw [ContinuousMap.range_toUniformOnFunIsCompact]
    exact UniformOnFun.isClosed_setOf_continuous CompactlyCoherentSpace.isCoherentWith
  exact ⟨hemb, hclosed⟩

/-- Arzelà–Ascoli on `C(↥U, ℂ)`: pointwise bounded + equicontinuous ⟹ compact closure. -/
theorem relCompact_open {U : Set ℂ} (hU : IsOpen U)
    (G : ℕ → C(U, ℂ)) (M : ↥U → ℝ)
    (hbd : ∀ x : ↥U, ∀ n, G n x ∈ closedBall (0 : ℂ) (M x))
    (hequi : Equicontinuous ((↑) : (Set.range G) → ↥U → ℂ)) :
    IsCompact (closure (Set.range G)) := by
  set Fcoe : C(U, ℂ) → (↥U → ℂ) := fun f => (f : ↥U → ℂ) with hFcoe
  have hScompact : ∀ K ∈ {K : Set ↥U | IsCompact K}, IsCompact K := fun K hK => hK
  have hclemb : IsClosedEmbedding
      (UniformOnFun.ofFun {K : Set ↥U | IsCompact K} ∘ Fcoe) :=
    isClosedEmbedding_toUOFC_open hU
  have heqcontOn : ∀ K ∈ {K : Set ↥U | IsCompact K},
      EquicontinuousOn (Fcoe ∘ ((↑) : (Set.range G) → C(U, ℂ))) K := by
    intro K _hK
    exact (hequi.equicontinuousOn K)
  have hptC : ∀ K ∈ {K : Set ↥U | IsCompact K}, ∀ x ∈ K,
      ∃ Q, IsCompact Q ∧ ∀ i ∈ (Set.range G), Fcoe i x ∈ Q := by
    intro K _hK x _hx
    refine ⟨closedBall (0 : ℂ) (M x), isCompact_closedBall _ _, ?_⟩
    rintro i ⟨n, rfl⟩
    exact hbd x n
  exact ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    hScompact hclemb heqcontOn hptC

/-- Subsequence extraction in `C(↥U, ℂ)` from a compact set. -/
theorem subseq_in_C_open {U : Set ℂ} (hU : IsOpen U)
    {G : ℕ → C(U, ℂ)} {S : Set C(U, ℂ)} (hS : IsCompact S) (hG : ∀ n, G n ∈ S)
    (φ : ℕ → ℕ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ gC : C(U, ℂ),
      Tendsto (fun n => G (φ (ψ n))) atTop (nhds gC) := by
  have hlc : LocallyCompactSpace ↥U := hU.locallyCompactSpace
  have hcg : IsCountablyGenerated (uniformity (C(U, ℂ))) := inferInstance
  have hfc : FirstCountableTopology (C(U, ℂ)) := UniformSpace.firstCountableTopology _
  obtain ⟨gC, _hgC, ψ, hψ, ht⟩ := hS.tendsto_subseq (fun n => hG (φ n))
  exact ⟨ψ, hψ, gC, ht⟩

/-- `C(↥U,ℂ)`-convergence gives the locally uniform dist bound on every compact `K ⊆ U`. -/
theorem C_tendsto_to_locunif_open {U : Set ℂ}
    {H : ℕ → C(U, ℂ)} {gC : C(U, ℂ)}
    (hconv : Tendsto H atTop (nhds gC))
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ s : ℂ, ∀ hs : s ∈ U, s ∈ K →
      dist ((H n) ⟨s, hs⟩) (gC ⟨s, hs⟩) < ε := by
  set K' : Set ↥U := Subtype.val ⁻¹' K with hK'def
  have hK'_compact : IsCompact K' := by
    rw [Subtype.isCompact_iff]
    have : Subtype.val '' K' = K := by
      rw [hK'def, Subtype.image_preimage_val]
      exact Set.inter_eq_right.mpr hKU
    rw [this]; exact hK
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn] at hconv
  have hunif := hconv K' hK'_compact
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  have hev := hunif ε hε
  filter_upwards [hev] with n hn
  intro s hs hsK
  have hmem : (⟨s, hs⟩ : ↥U) ∈ K' := hsK
  have := hn ⟨s, hs⟩ hmem
  rw [dist_comm] at this
  exact this

/-- Equicontinuity seed at a point of `U` from local boundedness. -/
theorem dist_lt_of_locbdd_holo_open {U : Set ℂ} (hU : IsOpen U)
    (F : ℕ → ℂ → ℂ)
    (hF : ∀ n, HolomorphicOnC (F n) U)
    (h_loc_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖F n s‖ ≤ C)
    (x₀ : ℂ) (hx₀ : x₀ ∈ U) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y : ℂ, dist y x₀ < δ → ∀ n : ℕ,
        dist (F n x₀) (F n y) < ε := by
  intro ε hε
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  have hr4 : (0 : ℝ) < r / 4 := by linarith
  have hsub : Metric.closedBall x₀ (r / 4 + r / 4) ⊆ U := by
    refine Set.Subset.trans ?_ hball
    apply Metric.closedBall_subset_ball
    linarith
  obtain ⟨C, hC⟩ := h_loc_bdd (Metric.closedBall x₀ (r / 4 + r / 4))
    (isCompact_closedBall _ _) hsub
  have hM0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have hbd : ∀ n : ℕ, ∀ w ∈ Metric.closedBall x₀ (r / 4 + r / 4),
      ‖F n w‖ ≤ max C 0 :=
    fun n w hw => le_trans (hC n w hw) (le_max_left _ _)
  have hdiff : ∀ n : ℕ, DifferentiableOn ℂ (F n) U := by
    intro n
    first
      | exact ((hU.analyticOn_iff_analyticOnNhd).mp (hF n)).differentiableOn
      | exact (hF n).differentiableOn
  have hlip := lipschitzOnWith_ball_of_bounded_holo F hU hr4 hM0 hsub hdiff hbd
  obtain ⟨K0, hlip'⟩ : ∃ K : ℝ≥0, ∀ n : ℕ,
      LipschitzOnWith K (F n) (Metric.ball x₀ (r / 4)) := ⟨_, hlip⟩
  have hK0 : (0 : ℝ) ≤ (K0 : ℝ) := K0.coe_nonneg
  have h1 : (0 : ℝ) < (K0 : ℝ) + 1 := by linarith
  have hApos : (0 : ℝ) < ε / ((K0 : ℝ) + 1) := div_pos hε h1
  refine ⟨min (ε / ((K0 : ℝ) + 1)) (r / 8), lt_min hApos (by linarith), ?_⟩
  intro y hy n
  have hyball : y ∈ Metric.ball x₀ (r / 4) := by
    rw [Metric.mem_ball]
    have h2 : dist y x₀ < r / 8 :=
      lt_of_lt_of_le hy (min_le_right _ _)
    linarith
  have hxball : x₀ ∈ Metric.ball x₀ (r / 4) := Metric.mem_ball_self hr4
  have hd := (hlip' n).dist_le_mul x₀ hxball y hyball
  have hA : (K0 : ℝ) * (ε / ((K0 : ℝ) + 1)) < ε := by
    rw [← mul_div_assoc]
    first
      | (rw [div_lt_iff₀ h1]; nlinarith)
      | (rw [div_lt_iff h1]; nlinarith)
  calc dist (F n x₀) (F n y)
      ≤ (K0 : ℝ) * dist x₀ y := hd
    _ ≤ (K0 : ℝ) * (ε / ((K0 : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hK0
        rw [dist_comm]
        exact le_of_lt (lt_of_lt_of_le hy (min_le_left _ _))
    _ < ε := hA

/-- **QR-6a — Montel on an open `U`.** Locally bounded holomorphic family ⟹ along any
subsequence, a further subsequence converging locally uniformly on `U`-compacts to a
holomorphic limit. -/
theorem montel_extraction_open {U : Set ℂ} (hU : IsOpen U)
    (F : ℕ → ℂ → ℂ)
    (hF : ∀ n, HolomorphicOnC (F n) U)
    (h_loc_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖F n s‖ ≤ C)
    (φ : ℕ → ℕ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ g : ℂ → ℂ, HolomorphicOnC g U ∧
      ∀ K : Set ℂ, IsCompact K → K ⊆ U → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ s : ℂ, s ∈ K → dist (F (φ (ψ n)) s) (g s) < ε := by
  classical
  set G : ℕ → C(U, ℂ) := fun n => bundleCU hU (F n) (hF n) with hG
  set M : ↥U → ℝ := fun x => Classical.choose (h_loc_bdd {(x : ℂ)}
      isCompact_singleton (Set.singleton_subset_iff.mpr x.property)) with hMdef
  have hbd : ∀ x : ↥U, ∀ n, G n x ∈ closedBall (0 : ℂ) (M x) := by
    intro x n
    have hspec := Classical.choose_spec (h_loc_bdd {(x : ℂ)} isCompact_singleton
      (Set.singleton_subset_iff.mpr x.property))
    have hb := hspec n (x : ℂ) (Set.mem_singleton _)
    rw [Metric.mem_closedBall, dist_zero_right]
    first
      | exact hb
      | simpa [hG, hMdef, bundleCU_apply] using hb
  have hequi : Equicontinuous ((↑) : (Set.range G) → ↥U → ℂ) := by
    intro x₀
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδpos, hspec⟩ := dist_lt_of_locbdd_holo_open hU F hF h_loc_bdd
      (x₀ : ℂ) x₀.property ε hε
    refine ⟨δ, hδpos, ?_⟩
    intro y hy i
    have hyd : dist ((y : ℂ)) ((x₀ : ℂ)) < δ := by
      first
        | exact hy
        | (rwa [Subtype.dist_eq] at hy)
    obtain ⟨n, hn⟩ := i.property
    have h1 := hspec (y : ℂ) hyd n
    first
      | (rw [← hn]; exact h1)
      | (simpa [← hn, hG, bundleCU_apply] using h1)
  have hcpt := relCompact_open hU G M hbd hequi
  obtain ⟨ψ, hψ_mono, gC, hψ_conv⟩ := subseq_in_C_open hU hcpt
    (fun n => subset_closure (Set.mem_range_self n)) φ
  set g : ℂ → ℂ := fun s => if hs : s ∈ U then gC ⟨s, hs⟩ else 0 with hgdef
  have hdist : ∀ K : Set ℂ, IsCompact K → K ⊆ U → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ s : ℂ, s ∈ K → dist (F (φ (ψ n)) s) (g s) < ε := by
    intro K hK hKU ε hε
    have hL2 := C_tendsto_to_locunif_open hψ_conv K hK hKU ε hε
    filter_upwards [hL2] with n hn
    intro s hsK
    have hsU : s ∈ U := hKU hsK
    have hb := hn s hsU hsK
    rw [hgdef]
    simp only [hsU, dif_pos]
    first
      | exact hb
      | simpa [hG, bundleCU_apply] using hb
  have hg_holo : HolomorphicOnC g U := by
    have hTLU : TendstoLocallyUniformlyOn (fun n => F (φ (ψ n))) g atTop U := by
      rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
      intro K hKU hK
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      have hd := hdist K hK hKU ε hε
      filter_upwards [hd] with n hn s hsK
      rw [dist_comm]; exact hn s hsK
    have hED : ∀ᶠ n in (atTop : Filter ℕ), DifferentiableOn ℂ (F (φ (ψ n))) U := by
      filter_upwards with n
      exact ((hU.analyticOn_iff_analyticOnNhd).mp (hF (φ (ψ n)))).differentiableOn
    have hdiff : DifferentiableOn ℂ g U := hTLU.differentiableOn hED hU
    rw [show HolomorphicOnC g U = AnalyticOn ℂ g U from rfl,
        hU.analyticOn_iff_analyticOnNhd]
    exact hdiff.analyticOnNhd hU
  exact ⟨ψ, hψ_mono, g, hg_holo, hdist⟩

#print axioms relCompact_open
#print axioms montel_extraction_open

end

end RHFormalization
