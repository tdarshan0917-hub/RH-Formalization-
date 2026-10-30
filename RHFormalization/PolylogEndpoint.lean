import RHFormalization.PolylogSquareStageBridge
import Mathlib

/-!
# PolylogEndpoint — PL-5b-ii: RH from polylogarithmic growth of the prime discrepancy

If on every compact subset of the half-plane `Re ρ > ½` the von Mangoldt discrepancy
`vmDiscrepancy (m+1) ρ` grows at most like `C·(log(m+1))^A`, then RH.
Route: for an Ω-compact `K`, `Re √(s+¼) ≥ c > 0` on `K`; shift `ρ_s` left by `δ = c/2`
(or `c/4` at the single point where `ρ_s − c/2 = 1`), apply PL-5a, feed PL-5b-i.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

/-- The principal square root has positive real part on the slit plane. -/
theorem sqrt_re_pos_of_mem_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    0 < (Complex.sqrt z).re := by
  have harg : z.arg ≠ Real.pi := by
    first
      | exact Complex.slitPlane_arg_ne_pi hz
      | exact (Complex.mem_slitPlane_iff_arg.mp hz).1
  have hz0 : z ≠ 0 := by
    first
      | exact Complex.slitPlane_ne_zero hz
      | exact (Complex.mem_slitPlane_iff_arg.mp hz).2
  unfold Complex.sqrt
  have hcast : (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv]; norm_num
  rw [hcast, Complex.cpow_ofReal_re]
  apply mul_pos
  · first
      | exact Real.rpow_pos_of_pos (norm_pos_iff.mpr hz0) _
      | exact Real.rpow_pos_of_pos (Complex.abs.pos hz0) _
      | positivity
  · apply Real.cos_pos_of_mem_Ioo
    have h1 := Complex.neg_pi_lt_arg z
    have h2 : z.arg < Real.pi := lt_of_le_of_ne (Complex.arg_le_pi z) harg
    rw [Set.mem_Ioo]
    constructor <;> nlinarith [Real.pi_pos]

theorem sqrtShift_continuousOn (K : Set ℂ) (hKO : K ⊆ Ω) :
    ContinuousOn (fun s : ℂ => Complex.sqrt (s + (1/4:ℂ))) K := by
  intro s hs
  have hslit : (s + (1/4:ℂ)) ∈ Complex.slitPlane :=
    shiftedLaplaceShift_mem_slitPlane_of_mem_Omega s (hKO hs)
  have hd : DifferentiableAt ℂ (fun z : ℂ => Complex.sqrt (z + (1/4:ℂ))) s := by
    have hsh : DifferentiableAt ℂ (fun z : ℂ => z + (1/4:ℂ)) s := by fun_prop
    simpa using (Complex.differentiableAt_sqrt hslit).comp s hsh
  exact hd.continuousAt.continuousWithinAt

/-- Positive lower bound for `Re √(s+¼)` on an Ω-compact. -/
theorem sqrtRe_min (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∃ c : ℝ, 0 < c ∧ ∀ s ∈ K, c ≤ (Complex.sqrt (s + (1/4:ℂ))).re := by
  rcases K.eq_empty_or_nonempty with hemp | hne
  · exact ⟨1, one_pos, by simp [hemp]⟩
  · have hcont : ContinuousOn (fun s : ℂ => (Complex.sqrt (s + (1/4:ℂ))).re) K :=
      Complex.continuous_re.comp_continuousOn (sqrtShift_continuousOn K hKO)
    obtain ⟨s₀, hs₀K, hs₀min⟩ := hK.exists_isMinOn hne hcont
    exact ⟨(Complex.sqrt (s₀ + (1/4:ℂ))).re,
      sqrt_re_pos_of_mem_slitPlane
        (shiftedLaplaceShift_mem_slitPlane_of_mem_Omega s₀ (hKO hs₀K)),
      fun s hs => hs₀min hs⟩

/-- The point `ρ_s − δ`. -/
def shiftPt (δ : ℝ) (s : ℂ) : ℂ :=
  Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ) - (δ:ℂ)

theorem shiftPt_re (δ : ℝ) (s : ℂ) :
    (shiftPt δ s).re = (Complex.sqrt (s + (1/4:ℂ))).re + 1/2 - δ := by
  unfold shiftPt
  rw [Complex.sub_re, Complex.add_re, Complex.ofReal_re]
  have h12 : ((1/2:ℂ)).re = (1/2:ℝ) := by simp
  rw [h12]

/-- One shift: PL-5a at `ρ = ρ_s − δ` bounds the discrepancy at `ρ_s`. -/
theorem vmDiscrepancy_bound_via_shift {K : Set ℂ} (hKO : K ⊆ Ω) {c δ C Kδ : ℝ} {A : ℕ}
    (hcK : ∀ s ∈ K, c ≤ (Complex.sqrt (s + (1/4:ℂ))).re) (hδc : δ ≤ c) (hC : 0 ≤ C)
    (hKδ : ∀ ρ : ℂ, 0 ≤ ρ.re → ρ ≠ 1 → ρ + (δ:ℂ) ≠ 1 →
      (∀ m : ℕ, ‖vmDiscrepancy (m + 1) ρ‖ ≤ C * (Real.log ((m:ℝ) + 1)) ^ A) →
      ∀ M : ℕ, 1 ≤ M → ‖vmDiscrepancy M (ρ + (δ:ℂ))‖ ≤ Kδ)
    (hD : ∀ s ∈ K, shiftPt δ s ≠ 1 → ∀ m : ℕ,
      ‖vmDiscrepancy (m + 1) (shiftPt δ s)‖ ≤ C * (Real.log ((m:ℝ) + 1)) ^ A)
    {s : ℂ} (hs : s ∈ K) (hne : shiftPt δ s ≠ 1) {M : ℕ} (hM : 1 ≤ M) :
    ‖vmDiscrepancy M (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ))‖ ≤ Kδ := by
  have hsum : shiftPt δ s + (δ:ℂ) = Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ) := by
    unfold shiftPt; ring
  have hρs : Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ) ≠ 1 := by
    intro h
    exact sqrt_ne_half (hKO hs) (by linear_combination h)
  have hre : 0 ≤ (shiftPt δ s).re := by
    rw [shiftPt_re]
    have h1 := hcK s hs
    linarith
  have h := hKδ (shiftPt δ s) hre hne (by rw [hsum]; exact hρs) (hD s hs hne) M hM
  rwa [hsum] at h

/-- **PL-5b-ii — the polylog endpoint.** RH from polylogarithmic growth of the
von Mangoldt discrepancy on compact subsets of the half-plane `Re ρ > ½`. -/
theorem RH_from_vmDiscrepancy_polylog
    (hpoly : ∀ L : Set ℂ, IsCompact L → L ⊆ {ρ : ℂ | (1/2:ℝ) < ρ.re} →
      ∃ C : ℝ, ∃ A : ℕ, ∀ ρ ∈ L, ρ ≠ 1 → ∀ m : ℕ,
        ‖vmDiscrepancy (m + 1) ρ‖ ≤ C * (Real.log ((m:ℝ) + 1)) ^ A) :
    RiemannHypothesis := by
  apply RH_from_vmDiscrepancy_bdd
  intro K hK hKO
  obtain ⟨c, hc, hcK⟩ := sqrtRe_min K hK hKO
  have hsq := sqrtShift_continuousOn K hKO
  have hcont : ∀ δ : ℝ, ContinuousOn (shiftPt δ) K := fun δ => by
    unfold shiftPt
    exact (hsq.add continuousOn_const).sub continuousOn_const
  have hL : IsCompact (shiftPt (c/2) '' K ∪ shiftPt (c/4) '' K) :=
    (hK.image_of_continuousOn (hcont (c/2))).union (hK.image_of_continuousOn (hcont (c/4)))
  have hLsub : shiftPt (c/2) '' K ∪ shiftPt (c/4) '' K ⊆ {ρ : ℂ | (1/2:ℝ) < ρ.re} := by
    rintro x (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · show (1/2:ℝ) < (shiftPt (c/2) s).re
      rw [shiftPt_re]
      have h1 := hcK s hs
      linarith
    · show (1/2:ℝ) < (shiftPt (c/4) s).re
      rw [shiftPt_re]
      have h1 := hcK s hs
      linarith
  obtain ⟨C, A, hCA⟩ := hpoly _ hL hLsub
  have hC' : (0:ℝ) ≤ max C 0 := le_max_right _ _
  have hD : ∀ δ : ℝ, (δ = c/2 ∨ δ = c/4) → ∀ s ∈ K, shiftPt δ s ≠ 1 → ∀ m : ℕ,
      ‖vmDiscrepancy (m + 1) (shiftPt δ s)‖ ≤ max C 0 * (Real.log ((m:ℝ) + 1)) ^ A := by
    intro δ hδ s hs hne m
    have hmem : shiftPt δ s ∈ shiftPt (c/2) '' K ∪ shiftPt (c/4) '' K := by
      rcases hδ with rfl | rfl
      · exact Or.inl ⟨s, hs, rfl⟩
      · exact Or.inr ⟨s, hs, rfl⟩
    have hlog : 0 ≤ (Real.log ((m:ℝ) + 1)) ^ A :=
      pow_nonneg (Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg m))) A
    exact le_trans (hCA _ hmem hne m) (mul_le_mul_of_nonneg_right (le_max_left C 0) hlog)
  obtain ⟨K1, hK1⟩ :=
    shifted_vmDiscrepancy_uniform (div_pos hc (by norm_num : (0:ℝ) < 2)) A hC'
  obtain ⟨K2, hK2⟩ :=
    shifted_vmDiscrepancy_uniform (div_pos hc (by norm_num : (0:ℝ) < 4)) A hC'
  refine ⟨max K1 K2, fun M hM s hs => ?_⟩
  by_cases h1 : shiftPt (c/2) s = 1
  · have h2 : shiftPt (c/4) s ≠ 1 := by
      intro h2
      have hx : ((c/2:ℝ):ℂ) = ((c/4:ℝ):ℂ) := by
        unfold shiftPt at h1 h2
        linear_combination h2 - h1
      have hx' : c/2 = c/4 := Complex.ofReal_injective hx
      linarith
    exact le_trans (vmDiscrepancy_bound_via_shift hKO hcK (by linarith) hC' hK2
      (hD (c/4) (Or.inr rfl)) hs h2 (by omega)) (le_max_right _ _)
  · exact le_trans (vmDiscrepancy_bound_via_shift hKO hcK (by linarith) hC' hK1
      (hD (c/2) (Or.inl rfl)) hs h1 (by omega)) (le_max_left _ _)

#print axioms sqrt_re_pos_of_mem_slitPlane
#print axioms sqrtRe_min
#print axioms RH_from_vmDiscrepancy_polylog

end

end RHFormalization
