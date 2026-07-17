import RHFormalization.HMeromorphicPackage

/-!
# RHFormalization.DefaultZeroExhaustion

A PROVEN inhabitant of `ZeroExhaustion`: stage `n` collects the nontrivial
zeta zeros in the compact region (closed ball of radius n+2) ∩
(1/(n+2) ≤ re ≤ 1 − 1/(n+2)). Finiteness is the isolated-zeros argument:
an accumulation point would force ζ ≡ 0 on {re < 1} by the identity theorem,
then ≡ 0 on {im > 0} by a second application through the overlap, contradicting
ζ(2+i) ≠ 0. Eventual containment is archimedean.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped Classical

/-- Compact truncation region at stage n. -/
def zetaStripRegion (n : ℕ) : Set ℂ :=
  Metric.closedBall 0 ((n : ℝ) + 2) ∩
    {s : ℂ | 1 / ((n : ℝ) + 2) ≤ s.re ∧ s.re ≤ 1 - 1 / ((n : ℝ) + 2)}

theorem isCompact_zetaStripRegion (n : ℕ) :
    IsCompact (zetaStripRegion n) := by
  refine (isCompact_closedBall _ _).inter_right ?_
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_le Complex.continuous_re continuous_const)

/-- ζ is analytic on the open half-plane re < 1 (which omits 1). -/
theorem zeta_analyticOnNhd_re_lt_one :
    AnalyticOnNhd ℂ riemannZeta {s : ℂ | s.re < 1} := by
  refine DifferentiableOn.analyticOnNhd ?_ (isOpen_lt Complex.continuous_re continuous_const)
  intro s hs
  refine (differentiableAt_riemannZeta ?_).differentiableWithinAt
  intro h1
  rw [h1] at hs
  simp at hs

/-- ζ is analytic on the open half-plane im > 0 (which omits 1). -/
theorem zeta_analyticOnNhd_im_pos :
    AnalyticOnNhd ℂ riemannZeta {s : ℂ | 0 < s.im} := by
  refine DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const Complex.continuous_im)
  intro s hs
  refine (differentiableAt_riemannZeta ?_).differentiableWithinAt
  intro h1
  rw [h1] at hs
  simp at hs

/-- The zeros of ζ in each truncation region form a finite set. -/
theorem zetaZeros_region_finite (n : ℕ) :
    {ρ : ℂ | IsNontrivialZetaZero ρ ∧ ρ ∈ zetaStripRegion n}.Finite := by
  by_contra hfin
  have hinf : {ρ : ℂ | IsNontrivialZetaZero ρ ∧ ρ ∈ zetaStripRegion n}.Infinite :=
    Set.not_finite.mp hfin
  set S := {ρ : ℂ | IsNontrivialZetaZero ρ ∧ ρ ∈ zetaStripRegion n} with hS
  let f : ℕ ↪ S := hinf.natEmbedding
  have hxK : ∀ k : ℕ, (f k : ℂ) ∈ zetaStripRegion n := fun k => (f k).2.2
  obtain ⟨a, haK, φ, hφ, htend⟩ :=
    (isCompact_zetaStripRegion n).tendsto_subseq hxK
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  have haU1 : a ∈ {s : ℂ | s.re < 1} := by
    have h2 := haK.2.2
    simp only [Set.mem_setOf_eq]
    linarith
  have hAa : AnalyticAt ℂ riemannZeta a := zeta_analyticOnNhd_re_lt_one a haU1
  rcases hAa.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · -- identity theorem chain to the contradiction at 2 + i
    have hEq1 : Set.EqOn riemannZeta 0 {s : ℂ | s.re < 1} :=
      zeta_analyticOnNhd_re_lt_one.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (((convex_halfSpace_re_lt 1)).isPreconnected) haU1 hzero
    have hI_U1 : Complex.I ∈ {s : ℂ | s.re < 1} := by
      simp [Complex.I_re]
    have hcI : riemannZeta =ᶠ[nhds Complex.I] 0 := by
      filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hI_U1]
        with z hz
      exact hEq1 hz
    have hI_U2 : Complex.I ∈ {s : ℂ | 0 < s.im} := by
      simp [Complex.I_im]
    have hEq2 : Set.EqOn riemannZeta 0 {s : ℂ | 0 < s.im} :=
      zeta_analyticOnNhd_im_pos.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        ((convex_halfSpace_im_gt 0).isPreconnected) hI_U2 hcI
    have h2I : (2 + Complex.I) ∈ {s : ℂ | 0 < s.im} := by
      simp [Complex.add_im, Complex.I_im]
    have hz2I : riemannZeta (2 + Complex.I) = 0 := hEq2 h2I
    have hne2I : riemannZeta (2 + Complex.I) ≠ 0 := by
      refine riemannZeta_ne_zero_of_one_lt_re ?_
      simp [Complex.add_re, Complex.I_re]
    exact hne2I hz2I
  · -- eventual nonvanishing contradicts the accumulating zeros
    have hne' : ∀ᶠ z in nhds a, z ≠ a → riemannZeta z ≠ 0 := by
      simpa [eventually_nhdsWithin_iff] using hne
    have hk : ∀ᶠ k in Filter.atTop,
        ((f (φ k) : ℂ) ≠ a → riemannZeta (f (φ k) : ℂ) ≠ 0) :=
      htend.eventually hne'
    have hkeq : ∀ᶠ k in Filter.atTop, (f (φ k) : ℂ) = a := by
      filter_upwards [hk] with k hkk
      by_contra hne2
      exact hkk hne2 ((f (φ k)).2.1).1
    obtain ⟨k1, hk1⟩ := hkeq.exists
    obtain ⟨k2, hk2, hk2gt⟩ := (hkeq.and (Filter.eventually_gt_atTop k1)).exists
    have : φ k1 = φ k2 := by
      have hsub : f (φ k1) = f (φ k2) := Subtype.ext (by rw [hk1, hk2])
      exact f.injective hsub
    have : k1 = k2 := hφ.injective this
    omega

/-- A PROVEN inhabitant of the zero-exhaustion structure. -/
noncomputable def defaultZeroExhaustion : ZeroExhaustion :=
  { zeroSet := fun n => (zetaZeros_region_finite n).toFinset
    h_all_zeros := by
      intro n ρ h
      exact ((zetaZeros_region_finite n).mem_toFinset.mp h).1
    h_eventually_contains := by
      intro ρ hρ
      obtain ⟨hζ, h0, h1⟩ := hρ
      obtain ⟨n1, hn1⟩ := exists_nat_ge ‖ρ‖
      obtain ⟨n2, hn2⟩ := exists_nat_ge (1 / ρ.re)
      obtain ⟨n3, hn3⟩ := exists_nat_ge (1 / (1 - ρ.re))
      refine ⟨n1 + n2 + n3, ?_⟩
      rw [(zetaZeros_region_finite _).mem_toFinset]
      have hN : (n1 : ℝ) ≤ ((n1 + n2 + n3 : ℕ) : ℝ) := by exact_mod_cast by omega
      have hN2 : (n2 : ℝ) ≤ ((n1 + n2 + n3 : ℕ) : ℝ) := by exact_mod_cast by omega
      have hN3 : (n3 : ℝ) ≤ ((n1 + n2 + n3 : ℕ) : ℝ) := by exact_mod_cast by omega
      set N : ℝ := ((n1 + n2 + n3 : ℕ) : ℝ) with hNdef
      have hNpos : (0 : ℝ) < N + 2 := by positivity
      have h1re : 0 < 1 - ρ.re := by linarith
      refine ⟨⟨hζ, h0, h1⟩, ?_, ?_, ?_⟩
      · rw [mem_closedBall_zero_iff]
        linarith
      · have : 1 / ρ.re ≤ N + 2 := by linarith
        have h1le : 1 ≤ ρ.re * (N + 2) := by
          rw [div_le_iff₀ h0] at this
          linarith [this]
        rw [div_le_iff₀ hNpos]
        linarith
      · have : 1 / (1 - ρ.re) ≤ N + 2 := by linarith
        have h1le : 1 ≤ (1 - ρ.re) * (N + 2) := by
          rw [div_le_iff₀ h1re] at this
          linarith [this]
        have : 1 / (N + 2) ≤ 1 - ρ.re := by
          rw [div_le_iff₀ hNpos]
          linarith
        linarith }

#print axioms defaultZeroExhaustion

end

end RHFormalization
