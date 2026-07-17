import RHFormalization.BSideHeatKernelLaplace
import RHFormalization.BSideHeatKernelLaplaceHolo
import RHFormalization.BSideHeatKernelLaplaceRealAxisM1
import RHFormalization.ShiftedLaplaceBRegularAtomic
import RHFormalization.ShiftedLaplaceSqrtBranch
import RHFormalization.ShiftedLaplaceSqrtNonzero
import Mathlib

namespace RHFormalization
open Complex MeasureTheory Set Filter Topology

lemma bLHS_analytic (a : ℝ) :
    AnalyticOnNhd ℂ (fun s : ℂ => shiftedLaplaceHeatKernelC a s) {s : ℂ | 0 < s.re} := by
  intro z hz
  have hzre : 0 < z.re := hz
  have hslit : (z + (1/4 : ℂ)) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp [Complex.add_re]
    linarith
  have hne : (z + (1/4 : ℂ)) ≠ 0 := by
    intro h
    rw [h] at hslit
    simp [Complex.mem_slitPlane_iff] at hslit
  have h_sqrt := shiftedLaplaceSqrt_holomorphicAt_of_shift_mem_slitPlane z hslit
  have h_sqrt_ne := shiftedLaplaceSqrt_ne_zero_of_shift_ne_zero z hne
  exact shiftedLaplaceHeatKernelC_holomorphicAt_of_shiftedSqrt a z h_sqrt h_sqrt_ne

lemma bRHS_analytic (a : ℝ) :
    AnalyticOnNhd ℂ (bRHS a) {s : ℂ | 0 < s.re} := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz
    exact (bRHS_differentiableAt a z hz).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re

lemma bConnector_frequently (a : ℝ) (ha : 0 ≤ a) :
    ∃ᶠ (z : ℂ) in nhdsWithin (1:ℂ) {(1:ℂ)}ᶜ,
      (fun s : ℂ => shiftedLaplaceHeatKernelC a s) z = bRHS a z := by
  have hseq_real : Filter.Tendsto (fun n : ℕ => (1 + 1/((n:ℝ)+1) : ℝ)) Filter.atTop (nhds (1:ℝ)) := by
    have h : Filter.Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) Filter.atTop (nhds (0:ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using (tendsto_const_nhds (x := (1:ℝ)) (f := Filter.atTop)).add h
  have hseq : Filter.Tendsto (fun n : ℕ => ((1 + 1/((n:ℝ)+1) : ℝ) : ℂ)) Filter.atTop (nhds (1:ℂ)) := by
    have hc := (Complex.continuous_ofReal.tendsto (1:ℝ)).comp hseq_real
    simpa [Function.comp_def] using hc
  have hne : ∀ᶠ (n : ℕ) in Filter.atTop, ((1 + 1/((n:ℝ)+1) : ℝ) : ℂ) ∈ ({(1:ℂ)}ᶜ : Set ℂ) := by
    filter_upwards with n
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcontra
    have heq1 : (1 + 1/((n:ℝ)+1) : ℝ) = 1 := by exact_mod_cast hcontra
    have hpos : 0 < 1/((n:ℝ)+1) := by positivity
    linarith
  have hseqW : Filter.Tendsto (fun n : ℕ => ((1 + 1/((n:ℝ)+1) : ℝ) : ℂ))
      Filter.atTop (nhdsWithin (1:ℂ) {(1:ℂ)}ᶜ) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hseq hne
  apply hseqW.frequently
  apply Filter.Frequently.of_forall
  intro n
  have hσ : 0 < (1 + 1/((n:ℝ)+1) : ℝ) := by positivity
  exact shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG_ofReal_M1 a (1 + 1/((n:ℝ)+1)) ha hσ

theorem shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG_halfplane (a : ℝ) (ha : 0 ≤ a) (s : ℂ) (hs : 0 < s.re) :
    shiftedLaplaceHeatKernelC a s
      = ∫ t in Set.Ioi (0:ℝ), shiftedHeatIntegrand a s t := by
  have hpre : IsPreconnected {s : ℂ | 0 < s.re} :=
    (convex_halfSpace_re_gt 0).isPreconnected
  have h1 : (1:ℂ) ∈ {s : ℂ | 0 < s.re} := by simp
  have heq := (bLHS_analytic a).eqOn_of_preconnected_of_frequently_eq
    (bRHS_analytic a) hpre h1 (bConnector_frequently a ha)
  exact heq hs

#print axioms shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG_halfplane

end RHFormalization
