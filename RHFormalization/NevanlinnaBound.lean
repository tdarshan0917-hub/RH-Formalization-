import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

open MeasureTheory Real Complex Metric ValueDistribution MeromorphicOn

namespace RHFormalization

/-- **Proximity of `Λ₀` is bounded by `log⁺` of its circle-supremum.** Since `Λ₀` is entire,
on the compact sphere `|z| = r` it attains a finite max `M`; then
`proximity Λ₀ ⊤ r = circleAverage (log⁺‖Λ₀‖) ≤ log⁺ M`. This feeds the growth bound into the
Nevanlinna machinery. -/
theorem proximity_completedRiemannZeta0_le {r : ℝ} (hr : 0 < r) :
    ∃ M : ℝ, 0 ≤ M ∧ ValueDistribution.proximity completedRiemannZeta₀ ⊤ r ≤ log⁺ M := by
  -- Λ₀ continuous (entire), sphere compact ⟹ ‖Λ₀‖ attains a max M on the sphere.
  have hcont : Continuous completedRiemannZeta₀ := differentiable_completedZeta₀.continuous
  have hcompact : IsCompact (sphere (0 : ℂ) |r|) := isCompact_sphere 0 |r|
  have hne : (sphere (0 : ℂ) |r|).Nonempty := by
    rw [abs_of_pos hr]; exact NormedSpace.sphere_nonempty.mpr hr.le
  obtain ⟨z₀, hz₀mem, hz₀max⟩ :=
    hcompact.exists_isMaxOn hne (hcont.norm.continuousOn)
  refine ⟨‖completedRiemannZeta₀ z₀‖, norm_nonneg _, ?_⟩
  rw [ValueDistribution.proximity_top]
  -- circleAverage of log⁺‖Λ₀‖ ≤ log⁺ M, since log⁺‖Λ₀ z‖ ≤ log⁺ M on the sphere
  apply circleAverage_mono_on_of_le_circle
  · exact MeromorphicOn.circleIntegrable_posLog_norm
      (fun x _ => (differentiable_completedZeta₀.analyticAt x).meromorphicAt)
  · intro x hx
    have hmax : ‖completedRiemannZeta₀ x‖ ≤ ‖completedRiemannZeta₀ z₀‖ := hz₀max hx
    exact posLog_le_posLog (norm_nonneg _) hmax
  
#print axioms proximity_completedRiemannZeta0_le

/-- **The zero-counting function is bounded by the characteristic.** Since
`characteristic = proximity + logCounting` and `proximity ≥ 0`, we have
`logCounting f 0 ≤ characteristic f 0` pointwise. (`logCounting f 0` is the Nevanlinna count of
the zeros of `f`.) -/
theorem logCounting_le_characteristic (f : ℂ → ℂ) (a : WithTop ℂ) (r : ℝ) :
    ValueDistribution.logCounting f a r ≤ ValueDistribution.characteristic f a r := by
  simp only [ValueDistribution.characteristic, Pi.add_apply]
  have hp : 0 ≤ ValueDistribution.proximity f a r := ValueDistribution.proximity_nonneg r
  linarith

#print axioms logCounting_le_characteristic

/-- **For the entire function `Λ₀`, the pole-counting term vanishes:** `logCounting Λ₀ ⊤ = 0`.
Since `Λ₀` is entire its divisor is nonnegative (no poles), so the negative part of the divisor —
which the `⊤`-counting function measures — is zero. -/
theorem logCounting_completedZeta0_top_eq_zero (r : ℝ) :
    ValueDistribution.logCounting completedRiemannZeta₀ ⊤ r = 0 := by
  rw [ValueDistribution.logCounting_top]
  have hana : AnalyticOnNhd ℂ completedRiemannZeta₀ Set.univ :=
    differentiable_completedZeta₀.differentiableOn.analyticOnNhd isOpen_univ
  have hnn : 0 ≤ MeromorphicOn.divisor completedRiemannZeta₀ Set.univ :=
    hana.divisor_nonneg
  rw [negPart_eq_zero.mpr hnn, map_zero]
  rfl

#print axioms logCounting_completedZeta0_top_eq_zero

/-- **The characteristic of `Λ₀` at `⊤` is bounded by `log⁺ M`.** Combines `logCounting Λ₀ ⊤ = 0`
(entire, no poles) with the proximity bound: `T(r,⊤) = m(r,⊤) + N(r,⊤) = m(r,⊤) ≤ log⁺ M`. -/
theorem characteristic_completedZeta0_top_le {r : ℝ} (hr : 0 < r) :
    ∃ M : ℝ, 0 ≤ M ∧ ValueDistribution.characteristic completedRiemannZeta₀ ⊤ r ≤ log⁺ M := by
  obtain ⟨M, hM0, hMle⟩ := proximity_completedRiemannZeta0_le hr
  refine ⟨M, hM0, ?_⟩
  have hchar : ValueDistribution.characteristic completedRiemannZeta₀ ⊤ r
      = ValueDistribution.proximity completedRiemannZeta₀ ⊤ r
        + ValueDistribution.logCounting completedRiemannZeta₀ ⊤ r := by
    simp only [ValueDistribution.characteristic, Pi.add_apply]
  rw [hchar, logCounting_completedZeta0_top_eq_zero, add_zero]
  exact hMle

#print axioms characteristic_completedZeta0_top_le

/-- **The characteristic at `0` equals the characteristic of the inverse at `⊤`.** Both unfold to
`proximity Λ₀ 0 + logCounting Λ₀ 0` via `proximity_inv` and `logCounting_inv`. This is the bridge
that lets the First Main Theorem (stated for `f` vs `f⁻¹` at `⊤`) bound the zero-count
`logCounting Λ₀ 0`. -/
theorem characteristic_completedZeta0_zero_eq_inv_top (r : ℝ) :
    ValueDistribution.characteristic completedRiemannZeta₀ 0 r
      = ValueDistribution.characteristic completedRiemannZeta₀⁻¹ ⊤ r := by
  simp only [ValueDistribution.characteristic, Pi.add_apply,
    ValueDistribution.proximity_inv, ValueDistribution.logCounting_inv]

#print axioms characteristic_completedZeta0_zero_eq_inv_top

/-- **The integrated zero-count of `Λ₀` is bounded by `log⁺ M + C`.** This is the key Segment-C
result: the Nevanlinna zero-counting function `N(r) = logCounting Λ₀ 0 r` is dominated by our
Mellin growth bound plus a First-Main-Theorem constant. Chain:
`N(r) ≤ characteristic Λ₀ 0 = characteristic Λ₀⁻¹ ⊤ ≤ characteristic Λ₀ ⊤ + C ≤ log⁺ M + C`. -/
theorem logCounting_completedZeta0_zero_le {r : ℝ} (hr : 0 < r) :
    ∃ M C : ℝ, 0 ≤ M ∧
      ValueDistribution.logCounting completedRiemannZeta₀ 0 r ≤ log⁺ M + C := by
  -- Meromorphic Λ₀ (entire)
  have hmero : Meromorphic completedRiemannZeta₀ :=
    fun x => (differentiable_completedZeta₀.analyticAt x).meromorphicAt
  -- the FMT constant
  set C : ℝ := max |Real.log ‖completedRiemannZeta₀ 0‖|
    |Real.log ‖meromorphicTrailingCoeffAt completedRiemannZeta₀ 0‖| with hC
  -- ⊤-characteristic bound (brick 26)
  obtain ⟨M, hM0, hMtop⟩ := characteristic_completedZeta0_top_le hr
  refine ⟨M, C, hM0, ?_⟩
  -- N(r) ≤ characteristic Λ₀ 0 r  (brick 24)
  have hNle : ValueDistribution.logCounting completedRiemannZeta₀ 0 r
      ≤ ValueDistribution.characteristic completedRiemannZeta₀ 0 r :=
    logCounting_le_characteristic completedRiemannZeta₀ 0 r
  -- characteristic Λ₀ 0 r = characteristic Λ₀⁻¹ ⊤ r  (brick 27)
  rw [characteristic_completedZeta0_zero_eq_inv_top] at hNle
  -- FMT: |characteristic Λ₀ ⊤ r - characteristic Λ₀⁻¹ ⊤ r| ≤ C
  have hFMT := ValueDistribution.characteristic_sub_characteristic_inv_le hmero (R := r)
  rw [← hC] at hFMT
  -- so characteristic Λ₀⁻¹ ⊤ r ≤ characteristic Λ₀ ⊤ r + C
  have hinv_le : ValueDistribution.characteristic completedRiemannZeta₀⁻¹ ⊤ r
      ≤ ValueDistribution.characteristic completedRiemannZeta₀ ⊤ r + C := by
    have := abs_le.mp hFMT
    linarith [this.1, this.2]
  -- chain everything
  calc ValueDistribution.logCounting completedRiemannZeta₀ 0 r
      ≤ ValueDistribution.characteristic completedRiemannZeta₀⁻¹ ⊤ r := hNle
    _ ≤ ValueDistribution.characteristic completedRiemannZeta₀ ⊤ r + C := hinv_le
    _ ≤ log⁺ M + C := by linarith [hMtop]

#print axioms logCounting_completedZeta0_zero_le

end RHFormalization
