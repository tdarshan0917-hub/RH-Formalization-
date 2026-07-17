import RHFormalization.BallCutDistance
import RHFormalization.GalerkinFHModel
import RHFormalization.GalerkinStageTraceBridge
import RHFormalization.EigenvalueGrowthSummable
import RHFormalization.GalerkinEigenvalueFloor

/-!
# RHFormalization.GalerkinFConvergence
Front F: compact-local eps-N convergence of the stage F-slots to galerkinFH.
Part 1: the three analytic legs on an arbitrary compact K ⊆ Ω.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric

/-- Compact-δ: uniform lower bound `δ ≤ ‖s+λ‖` on any compact `K ⊆ Ω`,
for all `λ ≥ 0`. Mirror of `exists_uniform_lower_bound_on_ball` with the
closed ball replaced by `K`; empty `K` handled trivially. -/
theorem exists_uniform_lower_bound_on_compact
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ K, ∀ lam : ℝ, 0 ≤ lam →
      δ ≤ ‖s + (lam : ℂ)‖ := by
  rcases K.eq_empty_or_nonempty with hemp | hne
  · exact ⟨1, one_pos, by simp [hemp]⟩
  · obtain ⟨x₀, hx₀mem, hx₀min⟩ :=
      hK.exists_isMinOn hne continuous_psiCut.continuousOn
    refine ⟨psiCut x₀, psiCut_pos_of_mem_Omega (hKO hx₀mem), ?_⟩
    intro s hsmem lam hlam
    have hmin : psiCut x₀ ≤ psiCut s := hx₀min hsmem
    exact hmin.trans (psiCut_le_norm_add s lam hlam)

/-- Compact norm bound: `∃ RK ≥ 0` with `‖s‖ ≤ RK` on `K`, via the
extreme value theorem on the norm (no IsBounded API needed). -/
theorem exists_norm_bound_on_compact
    (K : Set ℂ) (hK : IsCompact K) :
    ∃ RK : ℝ, 0 ≤ RK ∧ ∀ s ∈ K, ‖s‖ ≤ RK := by
  rcases K.eq_empty_or_nonempty with hemp | hne
  · exact ⟨0, le_refl 0, by simp [hemp]⟩
  · obtain ⟨x₀, hx₀mem, hx₀max⟩ :=
      hK.exists_isMaxOn hne (continuous_norm.continuousOn)
    exact ⟨‖x₀‖, norm_nonneg _, fun s hs => hx₀max hs⟩

/-- **The uniform term bound on K**: a single constant `C > 0` with
`‖(s+λ)⁻¹‖ ≤ C·(1+λ)⁻¹` for ALL `s ∈ K`, `λ ≥ 0`. Applies to both the
stage terms (λ = shifted stage eigenvalue) and the FH terms (λ = model
spectrum). Mirror of `exists_summable_bound_on_ball`'s core. -/
theorem inv_norm_le_on_compact
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ K, ∀ lam : ℝ, 0 ≤ lam →
      ‖(s + (lam : ℂ))⁻¹‖ ≤ C * (1 + lam)⁻¹ := by
  obtain ⟨delta, hdpos, hd⟩ := exists_uniform_lower_bound_on_compact K hK hKO
  obtain ⟨RK, hRnn, hRK⟩ := exists_norm_bound_on_compact K hK
  set C : ℝ := (1 + RK) / delta + 1 with hCdef
  have hCpos : 0 < C := by
    have h0 : 0 ≤ (1 + RK) / delta := by positivity
    rw [hCdef]; linarith
  refine ⟨C, hCpos, ?_⟩
  intro s hs lam hlam
  have hlow : delta ≤ ‖s + (lam : ℂ)‖ := hd s hs lam hlam
  have hpos : 0 < ‖s + (lam : ℂ)‖ := lt_of_lt_of_le hdpos hlow
  have hsR : ‖s‖ ≤ RK := hRK s hs
  have hnl : ‖(lam : ℂ)‖ = lam := by
    rw [Complex.norm_real]; exact abs_of_nonneg hlam
  have hgrow : lam - RK ≤ ‖s + (lam : ℂ)‖ := by
    have h1 : ‖(lam : ℂ)‖ - ‖(-s)‖ ≤ ‖(lam : ℂ) - (-s)‖ := norm_sub_norm_le _ _
    have hns : ‖(-s)‖ = ‖s‖ := norm_neg s
    have hsub : ‖(lam : ℂ) - (-s)‖ = ‖s + (lam : ℂ)‖ := by
      rw [sub_neg_eq_add, add_comm]
    rw [hns, hsub, hnl] at h1
    linarith
  have h1lpos : (0:ℝ) < 1 + lam := by linarith
  have hge1 : (1:ℝ) ≤ ‖s + (lam : ℂ)‖ / delta := by
    rw [le_div_iff₀ hdpos]; linarith
  have hcore : (1 + lam : ℝ) ≤ C * ‖s + (lam : ℂ)‖ := by
    have hA : (1 + RK : ℝ) ≤ (1 + RK) / delta * ‖s + (lam : ℂ)‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hdpos]
      nlinarith [hge1, hdpos, hRnn, hpos]
    have hsum2 : (1 + lam : ℝ) ≤
        (1 + RK) / delta * ‖s + (lam : ℂ)‖ + 1 * ‖s + (lam : ℂ)‖ := by
      have hB : (lam : ℝ) - RK ≤ 1 * ‖s + (lam : ℂ)‖ := by
        rw [one_mul]; exact hgrow
      linarith
    rw [hCdef]; nlinarith [hsum2]
  rw [norm_inv, inv_le_iff_one_le_mul₀ hpos]
  have hmul : (1 + lam : ℝ) * (1 + lam)⁻¹ = 1 := by field_simp
  calc (1:ℝ) = (1 + lam) * (1 + lam)⁻¹ := by rw [hmul]
    _ ≤ (C * ‖s + (lam : ℂ)‖) * (1 + lam)⁻¹ := by
        apply mul_le_mul_of_nonneg_right hcore; positivity
    _ = C * (1 + lam)⁻¹ * ‖s + (lam : ℂ)‖ := by ring

#print axioms exists_uniform_lower_bound_on_compact
#print axioms exists_norm_bound_on_compact
#print axioms inv_norm_le_on_compact

/-- Head leg: resolvent difference bound. If both denominators are
delta-bounded below, `‖(s+a)⁻¹ − (s+b)⁻¹‖ ≤ |a−b|/δ²`. -/
theorem resolvent_diff_norm_le (s : ℂ) (a b δ : ℝ) (hδ : 0 < δ)
    (ha : δ ≤ ‖s + (a : ℂ)‖) (hb : δ ≤ ‖s + (b : ℂ)‖) :
    ‖(s + (a : ℂ))⁻¹ - (s + (b : ℂ))⁻¹‖ ≤ |a - b| / δ ^ 2 := by
  have hpa : (0:ℝ) < ‖s + (a : ℂ)‖ := lt_of_lt_of_le hδ ha
  have hpb : (0:ℝ) < ‖s + (b : ℂ)‖ := lt_of_lt_of_le hδ hb
  have hane : (s + (a : ℂ)) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hpa; exact lt_irrefl 0 hpa
  have hbne : (s + (b : ℂ)) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hpb; exact lt_irrefl 0 hpb
  have hid : (s + (a : ℂ))⁻¹ - (s + (b : ℂ))⁻¹
      = (s + (a : ℂ))⁻¹ * (((b - a : ℝ) : ℂ)) * (s + (b : ℂ))⁻¹ := by
    have h := inv_sub_inv' hane hbne
    have harg : (s + (b : ℂ)) - (s + (a : ℂ)) = ((b - a : ℝ) : ℂ) := by
      push_cast; ring
    rw [h, harg]
  have hnorm : ‖(s + (a : ℂ))⁻¹ - (s + (b : ℂ))⁻¹‖
      = ‖s + (a : ℂ)‖⁻¹ * |b - a| * ‖s + (b : ℂ)‖⁻¹ := by
    rw [hid, norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_real,
      Real.norm_eq_abs]
  rw [hnorm, abs_sub_comm b a]
  have heq : ‖s + (a : ℂ)‖⁻¹ * |a - b| * ‖s + (b : ℂ)‖⁻¹
      = |a - b| / (‖s + (a : ℂ)‖ * ‖s + (b : ℂ)‖) := by
    rw [div_eq_mul_inv, mul_inv]; ring
  rw [heq]
  gcongr
  all_goals nlinarith [hδ, ha, hb, hpa, hpb, abs_nonneg (a - b)]

/-- Tail leg, summability: the majorant `C·(1+π²k²)⁻¹` is summable, by
comparison against the banked `summable_inv_nsq_add_one`. -/
theorem summable_pi_head_majorant (C : ℝ) :
    Summable (fun k : ℕ => C * (1 + Real.pi ^ 2 * (k : ℝ) ^ 2)⁻¹) := by
  have hpi2 : (1:ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hcomp : Summable (fun k : ℕ => (1 + Real.pi ^ 2 * (k : ℝ) ^ 2)⁻¹) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      summable_inv_nsq_add_one
    have hle : ((k : ℝ) ^ 2 + 1) ≤ 1 + Real.pi ^ 2 * (k : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((k : ℝ)), hpi2]
    have hposA : (0:ℝ) < (k : ℝ) ^ 2 + 1 := by positivity
    have hposB : (0:ℝ) < 1 + Real.pi ^ 2 * (k : ℝ) ^ 2 := by positivity
    first
      | exact inv_le_inv_of_le hposA hle
      | exact inv_anti₀ hposA hle
      | (rw [inv_le_inv₀ hposB hposA]; exact hle)
  exact hcomp.mul_left C

/-- Tail leg, cut: a summable nonneg sequence has tails below any `ε`. -/
theorem exists_tail_tsum_lt (u : ℕ → ℝ) (hu : ∀ k, 0 ≤ u k)
    (hsum : Summable u) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∑' k, u (k + M) < ε := by
  have hfun : ∀ M : ℕ, ∑' k, u (k + M)
      = (∑' k, u k) - ∑ i ∈ Finset.range M, u i := by
    intro M
    have h : (∑ i ∈ Finset.range M, u i) + ∑' k, u (k + M) = ∑' k, u k := by
      first
        | exact sum_add_tsum_nat_add M hsum
        | exact hsum.sum_add_tsum_nat_add M
        | exact Summable.sum_add_tsum_nat_add M hsum
        | exact hsum.sum_add_tsum_nat_add (k := M)
    linarith
  have hT : Tendsto (fun M : ℕ => ∑' k, u (k + M)) atTop (nhds 0) := by
    have h1 : Tendsto
        (fun M : ℕ => (∑' k, u k) - ∑ i ∈ Finset.range M, u i)
        atTop (nhds ((∑' k, u k) - ∑' k, u k)) :=
      tendsto_const_nhds.sub hsum.hasSum.tendsto_sum_nat
    rw [sub_self] at h1
    exact h1.congr (fun M => (hfun M).symm)
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp hT) ε hε
  refine ⟨M, ?_⟩
  have h := hM M (le_refl M)
  rw [Real.dist_eq, sub_zero] at h
  have habs : ∑' k, u (k + M) ≤ |∑' k, u (k + M)| := le_abs_self _
  linarith [abs_lt.mp h]

/-- Head leg, reindexed convergence: the stage-n eigenvalue slot
`diagLamAt k (n−1−k)` tends to `lamDiag k` as the STAGE index n → ∞. -/
theorem diagLamAt_reindex_tendsto (k : ℕ) :
    Tendsto (fun n : ℕ => diagLamAt k (n - 1 - k)) atTop
      (nhds (lamDiag k)) := by
  have hre : Tendsto (fun n : ℕ => n - 1 - k) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr
      (fun b => ⟨b + 1 + k, fun a ha => by omega⟩)
  exact (diagLamAt_tendsto_lamDiag k).comp hre

/-- Shifted version: the head-term input at stage index n. -/
theorem stage_eig_reindex_shifted_tendsto (k : ℕ) :
    Tendsto (fun n : ℕ => diagLamAt k (n - 1 - k) + SupVConst) atTop
      (nhds (lamDiag k + SupVConst)) :=
  (diagLamAt_reindex_tendsto k).add tendsto_const_nhds

#print axioms resolvent_diff_norm_le
#print axioms summable_pi_head_majorant
#print axioms exists_tail_tsum_lt
#print axioms diagLamAt_reindex_tendsto
#print axioms stage_eig_reindex_shifted_tendsto

/-- Range sums of a nonneg summable sequence are bounded by its tsum
(head/tail split plus tail nonnegativity; no sum_le_tsum name needed). -/
theorem sum_range_le_tsum_of_nonneg (v : ℕ → ℝ) (hv : ∀ j, 0 ≤ v j)
    (hsum : Summable v) (L : ℕ) :
    ∑ j ∈ Finset.range L, v j ≤ ∑' j, v j := by
  have hsplit : (∑ j ∈ Finset.range L, v j) + ∑' i, v (i + L) = ∑' j, v j := by
    first
      | exact sum_add_tsum_nat_add L hsum
      | exact hsum.sum_add_tsum_nat_add L
      | exact Summable.sum_add_tsum_nat_add L hsum
  have htail : 0 ≤ ∑' i, v (i + L) := tsum_nonneg (fun i => hv _)
  linarith

/-- **GENERIC THREE-EPSILON ESTIMATE**: a finite sum of `n+1` terms vs an
infinite sum, with a common summable majorant `u`, head terms within
`ε/(3(M+1))` of each other, and tail mass below `ε/3`. No galerkin content;
this is the pure assembly step of the F-front convergence. -/
theorem three_eps_sum_tsum_estimate (F g : ℕ → ℂ) (u : ℕ → ℝ) (n M : ℕ)
    (ε : ℝ) (hε : 0 < ε) (hMn : M ≤ n)
    (hu_nonneg : ∀ k, 0 ≤ u k) (hu_sum : Summable u)
    (hg_sum : Summable g)
    (hF_bd : ∀ k, k < n + 1 → ‖F k‖ ≤ u k)
    (hg_bd : ∀ k, ‖g k‖ ≤ u k)
    (hhead : ∀ k, k < M → ‖F k - g k‖ ≤ ε / (3 * ((M : ℝ) + 1)))
    (htail : ∑' j, u (j + M) < ε / 3) :
    ‖(∑ k ∈ Finset.range (n + 1), F k) - ∑' k, g k‖ < ε := by
  have hu_tail_sum : Summable (fun j => u (j + M)) :=
    (summable_nat_add_iff M).mpr hu_sum
  have hg_tail_norm_sum : Summable (fun j => ‖g (j + M)‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => hg_bd (j + M)) hu_tail_sum
  have hFHsplit : (∑ k ∈ Finset.range M, g k) + ∑' j, g (j + M) = ∑' k, g k := by
    first
      | exact sum_add_tsum_nat_add M hg_sum
      | exact hg_sum.sum_add_tsum_nat_add M
      | exact Summable.sum_add_tsum_nat_add M hg_sum
  have hrange : Finset.range (n + 1) = Finset.range (M + (n + 1 - M)) := by
    congr 1
    omega
  have hSsplit : ∑ k ∈ Finset.range (n + 1), F k
      = (∑ k ∈ Finset.range M, F k)
        + ∑ j ∈ Finset.range (n + 1 - M), F (M + j) := by
    rw [hrange]
    exact Finset.sum_range_add F M (n + 1 - M)
  have hdecomp : (∑ k ∈ Finset.range (n + 1), F k) - ∑' k, g k
      = ((∑ k ∈ Finset.range M, (F k - g k))
          + ∑ j ∈ Finset.range (n + 1 - M), F (M + j))
        - ∑' j, g (j + M) := by
    rw [hSsplit, ← hFHsplit, Finset.sum_sub_distrib]
    ring
  have hT1 : ∑ k ∈ Finset.range M, ‖F k - g k‖ < ε / 3 := by
    have hb : ∀ k ∈ Finset.range M,
        ‖F k - g k‖ ≤ ε / (3 * ((M : ℝ) + 1)) :=
      fun k hk => hhead k (Finset.mem_range.mp hk)
    have hs1 : ∑ k ∈ Finset.range M, ‖F k - g k‖
        ≤ (M : ℝ) * (ε / (3 * ((M : ℝ) + 1))) := by
      calc ∑ k ∈ Finset.range M, ‖F k - g k‖
          ≤ ∑ _k ∈ Finset.range M, (ε / (3 * ((M : ℝ) + 1))) :=
            Finset.sum_le_sum hb
        _ = (M : ℝ) * (ε / (3 * ((M : ℝ) + 1))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hs2 : (M : ℝ) * (ε / (3 * ((M : ℝ) + 1))) < ε / 3 := by
      have hD : (0:ℝ) < 3 * ((M : ℝ) + 1) := by positivity
      rw [← mul_div_assoc]
      first
        | (rw [div_lt_div_iff hD (by norm_num : (0:ℝ) < 3)]; nlinarith [hε])
        | (rw [div_lt_div_iff₀ hD (by norm_num : (0:ℝ) < 3)]; nlinarith [hε])
    linarith
  have hT2 : ∑ j ∈ Finset.range (n + 1 - M), ‖F (M + j)‖ < ε / 3 := by
    have hb : ∀ j ∈ Finset.range (n + 1 - M), ‖F (M + j)‖ ≤ u (j + M) := by
      intro j hj
      have hjn : M + j < n + 1 := by
        have hj' := Finset.mem_range.mp hj
        omega
      have h1 := hF_bd (M + j) hjn
      have h2 : u (M + j) = u (j + M) := by rw [Nat.add_comm]
      exact le_of_le_of_eq h1 h2
    calc ∑ j ∈ Finset.range (n + 1 - M), ‖F (M + j)‖
        ≤ ∑ j ∈ Finset.range (n + 1 - M), u (j + M) := Finset.sum_le_sum hb
      _ ≤ ∑' j, u (j + M) :=
          sum_range_le_tsum_of_nonneg (fun j => u (j + M))
            (fun j => hu_nonneg _) hu_tail_sum (n + 1 - M)
      _ < ε / 3 := htail
  have hT3 : ‖∑' j, g (j + M)‖ < ε / 3 := by
    have h1 : ‖∑' j, g (j + M)‖ ≤ ∑' j, ‖g (j + M)‖ :=
      norm_tsum_le_tsum_norm hg_tail_norm_sum
    have h2 : ∑' j, ‖g (j + M)‖ ≤ ∑' j, u (j + M) := by
      first
        | exact tsum_le_tsum (fun j => hg_bd (j + M)) hg_tail_norm_sum hu_tail_sum
        | exact tsum_mono hg_tail_norm_sum hu_tail_sum (fun j => hg_bd (j + M))
        | exact Summable.tsum_le_tsum (fun j => hg_bd (j + M))
            hg_tail_norm_sum hu_tail_sum
        | exact hg_tail_norm_sum.tsum_le_tsum (fun j => hg_bd (j + M))
            hu_tail_sum
    linarith
  rw [hdecomp]
  have hA : ‖((∑ k ∈ Finset.range M, (F k - g k))
      + ∑ j ∈ Finset.range (n + 1 - M), F (M + j))
      - ∑' j, g (j + M)‖
      ≤ ‖(∑ k ∈ Finset.range M, (F k - g k))
        + ∑ j ∈ Finset.range (n + 1 - M), F (M + j)‖
        + ‖∑' j, g (j + M)‖ := norm_sub_le _ _
  have hB : ‖(∑ k ∈ Finset.range M, (F k - g k))
      + ∑ j ∈ Finset.range (n + 1 - M), F (M + j)‖
      ≤ ‖∑ k ∈ Finset.range M, (F k - g k)‖
        + ‖∑ j ∈ Finset.range (n + 1 - M), F (M + j)‖ := norm_add_le _ _
  have hC1 : ‖∑ k ∈ Finset.range M, (F k - g k)‖
      ≤ ∑ k ∈ Finset.range M, ‖F k - g k‖ := norm_sum_le _ _
  have hC2 : ‖∑ j ∈ Finset.range (n + 1 - M), F (M + j)‖
      ≤ ∑ j ∈ Finset.range (n + 1 - M), ‖F (M + j)‖ := norm_sum_le _ _
  linarith

/-- The stage-n shifted eigenvalue family as a total ℕ-indexed function:
`stageLam n k` is the k-th SMALLEST shifted eigenvalue for `k ≤ n`, junk 0
beyond. This is the ℕ-form the generic estimate consumes. -/
noncomputable def stageLam (n k : ℕ) : ℝ :=
  if h : k < n + 1 then
    perturbedEigenvalues (galerkinFreeMu (n + 1) 1)
      (galerkinVC_isHermitian (N := n + 1) 1 (stageCodes n) ppWeightReal 1)
      (Fin.rev ⟨k, h⟩) + SupVConst
  else 0

theorem stageLam_floor (n k : ℕ) (hk : k < n + 1) :
    Real.pi ^ 2 * ((k : ℝ)) ^ 2 ≤ stageLam n k := by
  unfold stageLam
  rw [dif_pos hk]
  exact stage_shifted_eig_floor n ⟨k, hk⟩

theorem stageLam_nonneg (n k : ℕ) : 0 ≤ stageLam n k := by
  by_cases hk : k < n + 1
  · have h := stageLam_floor n k hk
    have hsq : (0:ℝ) ≤ Real.pi ^ 2 * ((k : ℝ)) ^ 2 := by positivity
    linarith
  · unfold stageLam
    rw [dif_neg hk]

theorem stageLam_head (n k : ℕ) (hk : k < n) :
    stageLam n k = diagLamAt k (n - 1 - k) + SupVConst := by
  unfold stageLam
  rw [dif_pos (by omega : k < n + 1)]
  first
    | exact congrArg (fun x : ℝ => x + SupVConst) (stage_eig_eq_diagLamAt n k hk)
    | rw [stage_eig_eq_diagLamAt n k hk]

/-- The package F-slot at stage n IS the bridge trace (defeq route). -/
theorem package_F_stage_eq_bridge (n : ℕ) (s : ℂ) :
    galerkinStagePackage.F_stage (galerkinStageSeq n) s
    = ∑ k : Fin (n + 1),
        (s + ((perturbedEigenvalues (galerkinFreeMu (n + 1) 1)
          (galerkinVC_isHermitian (N := n + 1) 1 (stageCodes n) ppWeightReal 1)
          (Fin.rev k) + SupVConst : ℝ) : ℂ))⁻¹ := by
  first
    | exact stage_shifted_trace_eq n s
    | (show galerkinPerturbedFStage (N := n + 1) (galerkinFreeMu (n + 1) 1) 1
          (stageCodes n) ppWeightReal 1 (s + (SupVConst : ℂ)) = _
       exact stage_shifted_trace_eq n s)

/-- **The stage trace as a range sum over stageLam** -- the exact LHS shape
for the generic three-epsilon estimate. -/
theorem stage_trace_range (n : ℕ) (s : ℂ) :
    galerkinStagePackage.F_stage (galerkinStageSeq n) s
    = ∑ k ∈ Finset.range (n + 1), (s + (stageLam n k : ℂ))⁻¹ := by
  rw [package_F_stage_eq_bridge n s,
    ← Fin.sum_univ_eq_sum_range (fun k => (s + (stageLam n k : ℂ))⁻¹) (n + 1)]
  apply Finset.sum_congr rfl
  intro k _
  have hval : stageLam n (k : ℕ)
      = perturbedEigenvalues (galerkinFreeMu (n + 1) 1)
          (galerkinVC_isHermitian (N := n + 1) 1 (stageCodes n) ppWeightReal 1)
          (Fin.rev k) + SupVConst := by
    unfold stageLam
    rw [dif_pos k.isLt]
  rw [hval]

#print axioms sum_range_le_tsum_of_nonneg
#print axioms three_eps_sum_tsum_estimate
#print axioms stageLam_floor
#print axioms stageLam_nonneg
#print axioms stageLam_head
#print axioms package_F_stage_eq_bridge
#print axioms stage_trace_range

/-- Majorant monotonicity: raise the eigenvalue, lower the bound. -/
theorem majorant_mono (C x lam : ℝ) (hC : 0 ≤ C) (hx : 0 ≤ x)
    (hfloor : x ≤ lam) : C * (1 + lam)⁻¹ ≤ C * (1 + x)⁻¹ := by
  have hposA : (0:ℝ) < 1 + x := by linarith
  have hle : (1 + x) ≤ 1 + lam := by linarith
  have hinv : (1 + lam)⁻¹ ≤ (1 + x)⁻¹ := by
    first
      | exact inv_le_inv_of_le hposA hle
      | exact inv_anti₀ hposA hle
      | (rw [inv_le_inv₀ (by linarith) hposA]; exact hle)
  exact mul_le_mul_of_nonneg_left hinv hC

/-- **FRONT F, MAIN THEOREM** (D.FH-LIMIT compact-local eps-N convergence):
on every compact `K ⊆ Ω`, the genuine-operator shifted stage traces converge
uniformly to `galerkinFH`. Exact shape of `DFHLimitData.h_F_stage_to_FH`. -/
theorem galerkinF_stage_to_FH :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in Filter.atTop, ∀ s : ℂ, s ∈ K →
          dist (galerkinStagePackage.F_stage (galerkinStageSeq n) s)
            (galerkinFH s) < ε := by
  intro K hK hKO ε hε
  obtain ⟨δ, hδpos, hδ⟩ := exists_uniform_lower_bound_on_compact K hK hKO
  obtain ⟨C, hCpos, hC⟩ := inv_norm_le_on_compact K hK hKO
  obtain ⟨M, hM⟩ := exists_tail_tsum_lt
    (fun k => C * (1 + Real.pi ^ 2 * (k : ℝ) ^ 2)⁻¹)
    (fun k => mul_nonneg hCpos.le (by positivity))
    (summable_pi_head_majorant C) (ε / 3) (by linarith)
  have hθpos : (0:ℝ) < ε / (3 * ((M : ℝ) + 1)) := by positivity
  have hηpos : (0:ℝ) < δ ^ 2 * (ε / (3 * ((M : ℝ) + 1))) :=
    mul_pos (pow_pos hδpos 2) hθpos
  have hevk : ∀ k : ℕ, ∀ᶠ n in Filter.atTop,
      dist (diagLamAt k (n - 1 - k) + SupVConst) (lamDiag k + SupVConst)
        < δ ^ 2 * (ε / (3 * ((M : ℝ) + 1))) := by
    intro k
    have ht := stage_eig_reindex_shifted_tendsto k
    rw [Metric.tendsto_atTop] at ht
    obtain ⟨N, hN⟩ := ht _ hηpos
    exact Filter.eventually_atTop.mpr ⟨N, hN⟩
  have hall : ∀ᶠ n in Filter.atTop, ∀ k ∈ Finset.range M,
      dist (diagLamAt k (n - 1 - k) + SupVConst) (lamDiag k + SupVConst)
        < δ ^ 2 * (ε / (3 * ((M : ℝ) + 1))) :=
    (Finset.range M).eventually_all.mpr (fun k _ => hevk k)
  filter_upwards [hall, Filter.eventually_ge_atTop M] with n hn hnM
  intro s hs
  rw [dist_eq_norm, stage_trace_range n s, galerkinFH_eq_tsum s]
  have hg_bd : ∀ k : ℕ,
      ‖(s + ((lamDiag k + SupVConst : ℝ) : ℂ))⁻¹‖
        ≤ C * (1 + Real.pi ^ 2 * (k : ℝ) ^ 2)⁻¹ := fun k =>
    (hC s hs (lamDiag k + SupVConst) (lamDiag_shifted_nonneg k)).trans
      (majorant_mono C (Real.pi ^ 2 * (k : ℝ) ^ 2) (lamDiag k + SupVConst)
        hCpos.le (by positivity) (lamDiag_shifted_growth k))
  have hF_bd : ∀ k : ℕ, k < n + 1 →
      ‖(s + (stageLam n k : ℂ))⁻¹‖
        ≤ C * (1 + Real.pi ^ 2 * (k : ℝ) ^ 2)⁻¹ := fun k hk =>
    (hC s hs (stageLam n k) (stageLam_nonneg n k)).trans
      (majorant_mono C (Real.pi ^ 2 * (k : ℝ) ^ 2) (stageLam n k)
        hCpos.le (by positivity) (stageLam_floor n k hk))
  have hg_sum :
      Summable (fun k : ℕ => (s + ((lamDiag k + SupVConst : ℝ) : ℂ))⁻¹) := by
    have hnorm : Summable
        (fun k : ℕ => ‖(s + ((lamDiag k + SupVConst : ℝ) : ℂ))⁻¹‖) :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) hg_bd
        (summable_pi_head_majorant C)
    first
      | exact Summable.of_norm hnorm
      | exact summable_of_summable_norm hnorm
  have hhead : ∀ k : ℕ, k < M →
      ‖(s + (stageLam n k : ℂ))⁻¹
        - (s + ((lamDiag k + SupVConst : ℝ) : ℂ))⁻¹‖
        ≤ ε / (3 * ((M : ℝ) + 1)) := by
    intro k hkM
    have hkn : k < n := lt_of_lt_of_le hkM hnM
    have hsl : stageLam n k = diagLamAt k (n - 1 - k) + SupVConst :=
      stageLam_head n k hkn
    have habs : |stageLam n k - (lamDiag k + SupVConst)|
        < δ ^ 2 * (ε / (3 * ((M : ℝ) + 1))) := by
      have h := hn k (Finset.mem_range.mpr hkM)
      rw [Real.dist_eq] at h
      rw [← hsl] at h
      exact h
    have hres := resolvent_diff_norm_le s (stageLam n k)
      (lamDiag k + SupVConst) δ hδpos
      (hδ s hs (stageLam n k) (stageLam_nonneg n k))
      (hδ s hs (lamDiag k + SupVConst) (lamDiag_shifted_nonneg k))
    have hd2 : (0:ℝ) < δ ^ 2 := pow_pos hδpos 2
    have hchain : |stageLam n k - (lamDiag k + SupVConst)| / δ ^ 2
        ≤ ε / (3 * ((M : ℝ) + 1)) := by
      first
        | rw [div_le_iff₀ hd2]
        | rw [div_le_iff hd2]
      calc |stageLam n k - (lamDiag k + SupVConst)|
          ≤ δ ^ 2 * (ε / (3 * ((M : ℝ) + 1))) := le_of_lt habs
        _ = ε / (3 * ((M : ℝ) + 1)) * δ ^ 2 := by ring
    exact hres.trans hchain
  exact three_eps_sum_tsum_estimate
    (fun k => (s + (stageLam n k : ℂ))⁻¹)
    (fun k => (s + ((lamDiag k + SupVConst : ℝ) : ℂ))⁻¹)
    (fun k => C * (1 + Real.pi ^ 2 * (k : ℝ) ^ 2)⁻¹)
    n M ε hε hnM
    (fun k => mul_nonneg hCpos.le (by positivity))
    (summable_pi_head_majorant C)
    hg_sum hF_bd hg_bd hhead hM

#print axioms majorant_mono
#print axioms galerkinF_stage_to_FH

end

end RHFormalization
