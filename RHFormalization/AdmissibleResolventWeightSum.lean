import RHFormalization.GalerkinStageSequence
import RHFormalization.GalerkinFConvergence
import RHFormalization.HeatSumSqrtBound
import RHFormalization.AdmissibleFreeTailAssembly

/-!
# RHFormalization.AdmissibleResolventWeightSum

**BRICK 4b-iii(a): the resolvent-weight sum bound.**

`Σ_{m<N} ‖(s + μₘ)⁻¹‖² ≤ C₀²·L` for the exact free spectrum
`μₘ = ((m+1)π/L)²` — LINEAR in the window `L`, via the Stone 7′
sum-vs-integral pattern against the arctan antiderivative. Linearity is
load-bearing: the crude `Σ 1/(m+1)²` route gives `L²` and the residual
assembly would diverge. Pointwise-with-hypothesis shape (applies at the
shifted point `w = s + SupVConst`), plus the K-uniform corollary via
`inv_norm_le_on_compact`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter MeasureTheory
open scoped BigOperators Classical

/-- **4b-iii(a), pointwise form**: given the single-point resolvent-weight
hypothesis, the free-spectrum squared resolvent weights sum linearly in `L`. -/
theorem freeMu_resolvent_sq_sum_le
    (N : ℕ) (L : ℝ) (hL : 0 < L) (s : ℂ) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hbound : ∀ lam : ℝ, 0 ≤ lam →
      ‖(s + (lam : ℂ))⁻¹‖ ≤ C₀ * (1 + lam)⁻¹) :
    ∑ m : Fin N, ‖(s + ((galerkinFreeMu N L m : ℝ) : ℂ))⁻¹‖ ^ 2
      ≤ C₀ ^ 2 * L := by
  -- per-term: ‖(s+μₘ)⁻¹‖² ≤ C₀²·(1 + (π(m+1)/L)²)⁻¹
  have hterm : ∀ m : Fin N,
      ‖(s + ((galerkinFreeMu N L m : ℝ) : ℂ))⁻¹‖ ^ 2
        ≤ C₀ ^ 2 * ((1 : ℝ) + (Real.pi * ((m : ℝ) + 1) / L) ^ 2)⁻¹ := by
    intro m
    have hμeq : galerkinFreeMu N L m = (Real.pi * ((m : ℝ) + 1) / L) ^ 2 := by
      unfold galerkinFreeMu; ring
    have hμ0 : (0 : ℝ) ≤ galerkinFreeMu N L m := by rw [hμeq]; positivity
    have hb := hbound (galerkinFreeMu N L m) hμ0
    have hn : (0 : ℝ) ≤ ‖(s + ((galerkinFreeMu N L m : ℝ) : ℂ))⁻¹‖ :=
      norm_nonneg _
    have hbnn : (0 : ℝ) ≤ C₀ * ((1 : ℝ) + galerkinFreeMu N L m)⁻¹ :=
      le_trans hn hb
    have hsq : ‖(s + ((galerkinFreeMu N L m : ℝ) : ℂ))⁻¹‖ ^ 2
        ≤ (C₀ * ((1 : ℝ) + galerkinFreeMu N L m)⁻¹) ^ 2 := by
      first
        | exact sq_le_sq' (by linarith) hb
        | nlinarith [hb, hn, hbnn]
    have hip : (0 : ℝ) ≤ ((1 : ℝ) + galerkinFreeMu N L m)⁻¹ := by positivity
    have hile : ((1 : ℝ) + galerkinFreeMu N L m)⁻¹ ≤ 1 := by
      first
        | exact inv_le_one_of_one_le₀ (by linarith)
        | exact inv_le_one (by linarith)
        | · have h1 : (0 : ℝ) < 1 + galerkinFreeMu N L m := by positivity
            have h2 := inv_le_inv_of_le one_pos
              (by linarith : (1 : ℝ) ≤ 1 + galerkinFreeMu N L m)
            simpa using h2
    have hdrop : (C₀ * ((1 : ℝ) + galerkinFreeMu N L m)⁻¹) ^ 2
        ≤ C₀ ^ 2 * ((1 : ℝ) + galerkinFreeMu N L m)⁻¹ := by
      have hexp : (C₀ * ((1 : ℝ) + galerkinFreeMu N L m)⁻¹) ^ 2
          = C₀ ^ 2 * (((1 : ℝ) + galerkinFreeMu N L m)⁻¹
              * ((1 : ℝ) + galerkinFreeMu N L m)⁻¹) := by ring
      rw [hexp]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg C₀)
      nlinarith [hip, hile]
    calc ‖(s + ((galerkinFreeMu N L m : ℝ) : ℂ))⁻¹‖ ^ 2
        ≤ (C₀ * ((1 : ℝ) + galerkinFreeMu N L m)⁻¹) ^ 2 := hsq
      _ ≤ C₀ ^ 2 * ((1 : ℝ) + galerkinFreeMu N L m)⁻¹ := hdrop
      _ = C₀ ^ 2 * ((1 : ℝ) + (Real.pi * ((m : ℝ) + 1) / L) ^ 2)⁻¹ := by
          rw [hμeq]
  -- antitone on [0, N]
  have hanti : AntitoneOn (fun x : ℝ => ((1 : ℝ) + (Real.pi * x / L) ^ 2)⁻¹)
      (Set.Icc (0 : ℝ) ((0 : ℝ) + (N : ℝ))) := by
    intro x hx y hy hxy
    have hπ : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
    have hx0 : (0 : ℝ) ≤ x := hx.1
    have h1 : Real.pi * x / L ≤ Real.pi * y / L := by
      have hnum : Real.pi * x ≤ Real.pi * y :=
        mul_le_mul_of_nonneg_left hxy hπ
      first
        | gcongr
        | exact (div_le_div_right hL).mpr hnum
        | exact (div_le_div_iff_of_pos_right hL).mpr hnum
    have h0 : (0 : ℝ) ≤ Real.pi * x / L :=
      div_nonneg (mul_nonneg hπ hx0) hL.le
    have h2 : (Real.pi * x / L) ^ 2 ≤ (Real.pi * y / L) ^ 2 := by
      nlinarith [h0, h1]
    have hposx : (0 : ℝ) < (1 : ℝ) + (Real.pi * x / L) ^ 2 := by positivity
    have hposy : (0 : ℝ) < (1 : ℝ) + (Real.pi * y / L) ^ 2 := by positivity
    first
      | exact inv_le_inv_of_le hposx (by linarith)
      | · rw [inv_le_inv₀ hposy hposx]
          linarith
      | · gcongr
          all_goals first | positivity | linarith
  -- sum ≤ integral (Stone 7' template)
  have key := AntitoneOn.sum_le_integral
      (f := fun x : ℝ => ((1 : ℝ) + (Real.pi * x / L) ^ 2)⁻¹)
      (x₀ := (0 : ℝ)) (a := N) hanti
  simp only [zero_add] at key
  -- integral evaluation via arctan antiderivative
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (N : ℝ),
      HasDerivAt (fun t : ℝ => (L / Real.pi) * Real.arctan (Real.pi * t / L))
        (((1 : ℝ) + (Real.pi * x / L) ^ 2)⁻¹) x := by
    intro x _
    have hd1 : HasDerivAt (fun t : ℝ => Real.pi * t / L) (Real.pi / L) x := by
      first
        | · have h := ((hasDerivAt_id x).const_mul Real.pi).div_const L
            simpa using h
        | · have h := (HasDerivAt.const_mul Real.pi (hasDerivAt_id x)).div_const L
            simpa using h
    have hd2 : HasDerivAt (fun t : ℝ => Real.arctan (Real.pi * t / L))
        (1 / ((1 : ℝ) + (Real.pi * x / L) ^ 2) * (Real.pi / L)) x := by
      first
        | exact hd1.arctan
        | exact HasDerivAt.arctan hd1
    have hd3 : HasDerivAt
        (fun t : ℝ => (L / Real.pi) * Real.arctan (Real.pi * t / L))
        ((L / Real.pi) * (1 / ((1 : ℝ) + (Real.pi * x / L) ^ 2) * (Real.pi / L)))
        x := by
      first
        | exact hd2.const_mul (L / Real.pi)
        | exact HasDerivAt.const_mul (L / Real.pi) hd2
    convert hd3 using 1
    have hπne : Real.pi ≠ 0 := Real.pi_ne_zero
    have hLne : L ≠ 0 := hL.ne'
    first
      | field_simp
      | · field_simp
          ring
  have hcont0 : Continuous fun x : ℝ => Real.pi * x / L := by
    first
      | exact (continuous_const.mul continuous_id).div_const L
      | continuity
  have hne : ∀ x : ℝ, ((1 : ℝ) + (Real.pi * x / L) ^ 2) ≠ 0 := by
    intro x; positivity
  have hcont : Continuous
      fun x : ℝ => ((1 : ℝ) + (Real.pi * x / L) ^ 2)⁻¹ := by
    first
      | exact (continuous_const.add (hcont0.pow 2)).inv₀ hne
      | exact Continuous.inv₀ (continuous_const.add (hcont0.pow 2)) hne
      | fun_prop
  have hint_eq : ∫ x in (0 : ℝ)..(N : ℝ), ((1 : ℝ) + (Real.pi * x / L) ^ 2)⁻¹
      = (L / Real.pi) * Real.arctan (Real.pi * (N : ℝ) / L)
        - (L / Real.pi) * Real.arctan (Real.pi * 0 / L) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.intervalIntegrable 0 (N : ℝ))
  have hzero : Real.arctan (Real.pi * 0 / L) = 0 := by
    first
      | simp
      | norm_num [Real.arctan_zero]
  have hint_le : (∫ x in (0 : ℝ)..(N : ℝ),
      ((1 : ℝ) + (Real.pi * x / L) ^ 2)⁻¹) ≤ L / 2 := by
    rw [hint_eq, hzero, mul_zero, sub_zero]
    have harc : Real.arctan (Real.pi * (N : ℝ) / L) ≤ Real.pi / 2 :=
      (Real.arctan_lt_pi_div_two _).le
    have hLπ : (0 : ℝ) ≤ L / Real.pi := by positivity
    have hπne : Real.pi ≠ 0 := Real.pi_ne_zero
    calc (L / Real.pi) * Real.arctan (Real.pi * (N : ℝ) / L)
        ≤ (L / Real.pi) * (Real.pi / 2) :=
          mul_le_mul_of_nonneg_left harc hLπ
      _ = L / 2 := by field_simp
  -- Fin → range conversion
  have hfin : (∑ m : Fin N, ((1 : ℝ) + (Real.pi * ((m : ℝ) + 1) / L) ^ 2)⁻¹)
      = ∑ i ∈ Finset.range N,
          ((1 : ℝ) + (Real.pi * ((i : ℝ) + 1) / L) ^ 2)⁻¹ := by
    first
      | exact Fin.sum_univ_eq_sum_range
          (fun i : ℕ => ((1 : ℝ) + (Real.pi * ((i : ℝ) + 1) / L) ^ 2)⁻¹) N
      | · rw [Fin.sum_univ_eq_sum_range
            (fun i : ℕ => ((1 : ℝ) + (Real.pi * ((i : ℝ) + 1) / L) ^ 2)⁻¹)]
  -- range sum ≤ integral
  have hrange_le : (∑ i ∈ Finset.range N,
      ((1 : ℝ) + (Real.pi * ((i : ℝ) + 1) / L) ^ 2)⁻¹)
      ≤ ∫ x in (0 : ℝ)..(N : ℝ), ((1 : ℝ) + (Real.pi * x / L) ^ 2)⁻¹ := by
    refine le_trans (le_of_eq ?_) key
    apply Finset.sum_congr rfl
    intro i _
    first
      | · simp only []
          push_cast
          ring_nf
      | · push_cast
          ring_nf
      | norm_num
      | rfl
  -- assemble
  calc ∑ m : Fin N, ‖(s + ((galerkinFreeMu N L m : ℝ) : ℂ))⁻¹‖ ^ 2
      ≤ ∑ m : Fin N,
          C₀ ^ 2 * ((1 : ℝ) + (Real.pi * ((m : ℝ) + 1) / L) ^ 2)⁻¹ :=
        Finset.sum_le_sum (fun m _ => hterm m)
    _ = C₀ ^ 2 * ∑ m : Fin N,
          ((1 : ℝ) + (Real.pi * ((m : ℝ) + 1) / L) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
    _ = C₀ ^ 2 * ∑ i ∈ Finset.range N,
          ((1 : ℝ) + (Real.pi * ((i : ℝ) + 1) / L) ^ 2)⁻¹ := by rw [hfin]
    _ ≤ C₀ ^ 2 * ∫ x in (0 : ℝ)..(N : ℝ),
          ((1 : ℝ) + (Real.pi * x / L) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hrange_le (sq_nonneg C₀)
    _ ≤ C₀ ^ 2 * (L / 2) :=
        mul_le_mul_of_nonneg_left hint_le (sq_nonneg C₀)
    _ ≤ C₀ ^ 2 * L :=
        mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg C₀)

/-- **4b-iii(a), K-uniform corollary**: a single constant works for all
`s ∈ K`, all dimensions `N`, all windows `L > 0`. -/
theorem exists_freeMu_resolvent_sq_sum_bound_on_compact
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ K, ∀ (N : ℕ) (L : ℝ), 0 < L →
      ∑ m : Fin N, ‖(s + ((galerkinFreeMu N L m : ℝ) : ℂ))⁻¹‖ ^ 2
        ≤ C * L := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := inv_norm_le_on_compact K hK hKO
  exact ⟨C₀ ^ 2, pow_pos hC₀pos 2,
    fun s hs N L hL =>
      freeMu_resolvent_sq_sum_le N L hL s C₀ hC₀pos.le
        (fun lam hlam => hC₀ s hs lam hlam)⟩

#print axioms freeMu_resolvent_sq_sum_le
#print axioms exists_freeMu_resolvent_sq_sum_bound_on_compact

end

end RHFormalization
