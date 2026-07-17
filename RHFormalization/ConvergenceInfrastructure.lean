import RHFormalization.MeromorphyAssembly

/-!
# RHFormalization.ConvergenceInfrastructure

Campaign C, installment 1: (a) uniform pole-distance on compacts away from
poles; (b) the subtype-stage map tends to atTop in the Finset lattice; (c)
subtype sums match the stage sums.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped Classical

/-- (a) Uniform pole-distance on a compact away from the poles. -/
theorem compact_uniform_pole_distance (K : CompactAwayFromZeroPoles) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ρ : ℂ, IsNontrivialZetaZero ρ →
        ∀ s ∈ K.K, δ ≤ dist s (polePoint ρ) := by
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ k : ℕ, ∃ (ρ : ℂ) (s : ℂ),
      IsNontrivialZetaZero ρ ∧ s ∈ K.K ∧
        dist s (polePoint ρ) < 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨ρ, h1, s, h2, h3⟩ := hcon (1 / ((k : ℝ) + 1)) (by positivity)
    exact ⟨ρ, s, h1, h2, h3⟩
  choose z w hz_zero hw_mem hzw_dist using hseq
  obtain ⟨x, hxK, φ, hφ, htend⟩ := K.h_compact.tendsto_subseq hw_mem
  have hxΩ : x ∈ Ω := K.h_subset_Omega hxK
  have hxnp : x ∉ ZeroPoleSet := K.h_avoid x hxK
  obtain ⟨r, hr, hiso⟩ := nonpole_isolated x hxΩ hxnp
  have hclose : ∀ᶠ k in Filter.atTop, dist (w (φ k)) x < r / 2 :=
    (Metric.tendsto_nhds.mp htend) (r / 2) (by linarith)
  have hsmall : ∀ᶠ k in Filter.atTop,
      (1 : ℝ) / ((φ k : ℝ) + 1) < r / 2 := by
    have hb : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hc : Tendsto (fun k : ℕ => 1 / ((φ k : ℝ) + 1)) atTop (nhds 0) :=
      hb.comp (hφ.tendsto_atTop)
    refine (Metric.tendsto_nhds.mp hc (r / 2) (by linarith)).mono (fun k hk => ?_)
    have hpos : (0:ℝ) < 1 / ((φ k : ℝ) + 1) := by positivity
    rw [Real.dist_eq, sub_zero, abs_of_pos hpos] at hk
    exact hk
  obtain ⟨k, hk1, hk2⟩ := (hclose.and hsmall).exists
  have hd := hiso (z (φ k)) (hz_zero (φ k))
  have htri : dist x (polePoint (z (φ k))) ≤
      dist x (w (φ k)) + dist (w (φ k)) (polePoint (z (φ k))) :=
    dist_triangle _ _ _
  rw [dist_comm x (w (φ k))] at htri
  have hsm : dist (w (φ k)) (polePoint (z (φ k))) < r / 2 :=
    lt_trans (hzw_dist (φ k)) hk2
  rw [dist_comm (polePoint (z (φ k))) x] at hd
  linarith

/-- (b) The subtype-stage map. -/
def subtypeStage (n : ℕ) : Finset {ρ : ℂ // IsNontrivialZetaZero ρ} :=
  (defaultZeroExhaustion.zeroSet n).subtype IsNontrivialZetaZero

/-- The subtype stages tend to atTop in the Finset lattice. -/
theorem subtypeStage_tendsto :
    Tendsto subtypeStage atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  have hstage : ∀ ρ : {ρ : ℂ // IsNontrivialZetaZero ρ}, ρ ∈ b →
      ∃ N, ρ.1 ∈ defaultZeroExhaustion.zeroSet N := by
    intro ρ _
    exact defaultZeroExhaustion.h_eventually_contains ρ.1 ρ.2
  choose stage hstage using hstage
  classical
  refine ⟨b.attach.sup (fun ρ => stage ρ.1 ρ.2), fun a ha => ?_⟩
  rw [Finset.le_iff_subset]
  intro ρ hρb
  rw [subtypeStage, Finset.mem_subtype]
  refine defaultZeroExhaustion_mono ?_ (hstage ρ hρb)
  exact le_trans
    (Finset.le_sup (f := fun x : {x // x ∈ b} => stage x.1 x.2)
      (b.mem_attach ⟨ρ, hρb⟩))
    ha

/-- (c) Subtype sums match the stage sums. -/
theorem subtypeStage_sum_eq
    (M : ZeroMultiplicityData) (n : ℕ) (s : ℂ) :
    Finset.sum (subtypeStage n) (fun ρ => zeroPoleSummand M ρ.1 s) =
      zeroPolePartial M defaultZeroExhaustion n s := by
  unfold zeroPolePartial finiteZeroPoleSeries subtypeStage
  rw [Finset.sum_subtype_of_mem (fun ρ => zeroPoleSummand M ρ s)
    (fun x hx => defaultZeroExhaustion.h_all_zeros n x hx)]

#print axioms compact_uniform_pole_distance
#print axioms subtypeStage_tendsto
#print axioms subtypeStage_sum_eq

end

end RHFormalization
