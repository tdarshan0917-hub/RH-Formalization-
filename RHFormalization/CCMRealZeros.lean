import Mathlib

/-!
# CCMRealZeros — CCM-1: the finite-λ real-zeros theorem (core of CCM Thm 5.10(iii))

Connes–Consani–Moscovici, *Zeta Spectral Triples* (arXiv:2511.22755): the minimal eigenvector `ξ`
of the truncated Weil form has `ξ̂(z) = 2L^{-1/2} sin(zL/2) Σ_j ξ_j/(z - d_j)`, `d_j = 2πj/L`
(Prop. 5.9), and all zeros of `ξ̂` are real (Thm. 5.10(iii)). The structural input is their
eq. (5.3): `TD - DT = |η⟩⟨β| - |β⟩⟨η|`, `η = (1,…,1)`, i.e. `T_ij (d_j - d_i) = β_j - β_i`.

`ccm_zeros_real`: if `T` is symmetric with `Tξ = 0`, satisfies (5.3), `Σ ξ_j = 1`, and the form
`Q(w) = Σ conj(w_i) T_ij w_j` is nonzero on nonzero `w ⊥ η` (true when `T = QW - ε_N` with simple
lowest eigenvalue, since `η·ξ = 1`), then every zero of `R(z) = Σ ξ_j/(z - d_j)` is real.
Elementary proof: `w_j = z ξ_j/(z - d_j)` has `Σ w = zR(z) = 0` and `(z - z̄) Q(w) = 0`.
-/

set_option autoImplicit false

namespace RHFormalization

open scoped BigOperators

/-- **CCM-1 — all zeros of `Σ ξ_j/(z - d_j)` are real.** -/
theorem ccm_zeros_real {n : Type*} [Fintype n] [DecidableEq n]
    (d ξ : n → ℝ) (T : n → n → ℂ) (β : n → ℂ)
    (hsymm : ∀ i j, T i j = T j i)
    (hker : ∀ i, ∑ j, T i j * (ξ j : ℂ) = 0)
    (hdisp : ∀ i j, T i j * ((d j : ℂ) - d i) = β j - β i)
    (hsum : ∑ j, (ξ j : ℂ) = 1)
    (hpos : ∀ w : n → ℂ, ∑ i, w i = 0 → w ≠ 0 →
      ∑ i, ∑ j, starRingEnd ℂ (w i) * T i j * w j ≠ 0)
    (z : ℂ) (hz : ∀ j, z ≠ (d j : ℂ)) (hR : ∑ j, (ξ j : ℂ) / (z - d j) = 0) :
    z.im = 0 := by
  by_cases hz0 : z = 0
  · simp [hz0]
  have hne : ∀ j, z - (d j : ℂ) ≠ 0 := fun j => sub_ne_zero.mpr (hz j)
  obtain ⟨w, hw⟩ : ∃ w : n → ℂ, w = fun j => z * (ξ j : ℂ) / (z - d j) := ⟨_, rfl⟩
  have hwz : ∀ j, w j * (z - d j) = z * (ξ j : ℂ) := by
    intro j
    first
      | (rw [hw]; exact div_mul_cancel₀ _ (hne j))
      | (simp only [hw]; field_simp)
  have hw_rel : ∀ j, (d j : ℂ) * w j = z * w j - z * (ξ j : ℂ) := by
    intro j
    linear_combination (-1 : ℂ) * hwz j
  have hwfac : ∀ j, w j = z * ((ξ j : ℂ) / (z - d j)) := fun j => by simp only [hw]; ring
  have hsumw : ∑ j, w j = 0 := by
    rw [Finset.sum_congr rfl (fun j _ => hwfac j), ← Finset.mul_sum, hR, mul_zero]
  have hwne : w ≠ 0 := by
    intro h0
    have hj : ∀ j, (ξ j : ℂ) = 0 := by
      intro j
      have h := congrFun h0 j
      rw [hwfac j, Pi.zero_apply] at h
      rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd h1 hz0
      · rcases div_eq_zero_iff.mp h1 with h2 | h2
        · exact h2
        · exact absurd h2 (hne j)
    have h0' : ∑ j, (ξ j : ℂ) = 0 := Finset.sum_eq_zero (fun j _ => hj j)
    rw [hsum] at h0'
    exact one_ne_zero h0'
  have hker' : ∀ j, ∑ i, (ξ i : ℂ) * T i j = 0 := by
    intro j
    rw [← hker j]
    exact Finset.sum_congr rfl (fun i _ => by rw [hsymm i j]; ring)
  have hrow : ∀ i, ∑ j, T i j * ((d j : ℂ) * w j) = z * ∑ j, T i j * w j := by
    intro i
    have h1 : ∑ j, T i j * ((d j : ℂ) * w j)
        = ∑ j, (z * (T i j * w j) - z * (T i j * (ξ j : ℂ))) :=
      Finset.sum_congr rfl (fun j _ => by rw [hw_rel j]; ring)
    rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hker i, mul_zero, sub_zero]
  have hcol : ∀ j, ∑ i, starRingEnd ℂ (w i) * (d i : ℂ) * T i j
      = starRingEnd ℂ z * ∑ i, starRingEnd ℂ (w i) * T i j := by
    intro j
    have hc : ∀ i, starRingEnd ℂ (w i) * (d i : ℂ)
        = starRingEnd ℂ z * starRingEnd ℂ (w i) - starRingEnd ℂ z * (ξ i : ℂ) := by
      intro i
      have h := congrArg (starRingEnd ℂ) (hw_rel i)
      simp only [map_mul, map_sub, Complex.conj_ofReal] at h
      linear_combination h
    have h1 : ∑ i, starRingEnd ℂ (w i) * (d i : ℂ) * T i j
        = ∑ i, (starRingEnd ℂ z * (starRingEnd ℂ (w i) * T i j)
            - starRingEnd ℂ z * ((ξ i : ℂ) * T i j)) :=
      Finset.sum_congr rfl (fun i _ => by rw [hc i]; ring)
    rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hker' j, mul_zero, sub_zero]
  -- A = w* T D w = z Q
  have hA : ∑ i, ∑ j, starRingEnd ℂ (w i) * (T i j * ((d j : ℂ) * w j))
      = z * ∑ i, ∑ j, starRingEnd ℂ (w i) * T i j * w j := by
    have hi : ∀ i, ∑ j, starRingEnd ℂ (w i) * (T i j * ((d j : ℂ) * w j))
        = z * ∑ j, starRingEnd ℂ (w i) * T i j * w j := by
      intro i
      have e1 : ∑ j, starRingEnd ℂ (w i) * (T i j * ((d j : ℂ) * w j))
          = starRingEnd ℂ (w i) * ∑ j, T i j * ((d j : ℂ) * w j) := (Finset.mul_sum _ _ _).symm
      have e2 : ∑ j, starRingEnd ℂ (w i) * T i j * w j
          = starRingEnd ℂ (w i) * ∑ j, T i j * w j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [e1, e2, hrow i]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hi i), ← Finset.mul_sum]
  -- B = w* D T w = conj z · Q
  have hB : ∑ i, ∑ j, starRingEnd ℂ (w i) * (d i : ℂ) * T i j * w j
      = starRingEnd ℂ z * ∑ i, ∑ j, starRingEnd ℂ (w i) * T i j * w j := by
    have hj : ∀ j, ∑ i, starRingEnd ℂ (w i) * (d i : ℂ) * T i j * w j
        = starRingEnd ℂ z * ∑ i, starRingEnd ℂ (w i) * T i j * w j := by
      intro j
      have e1 : ∑ i, starRingEnd ℂ (w i) * (d i : ℂ) * T i j * w j
          = (∑ i, starRingEnd ℂ (w i) * (d i : ℂ) * T i j) * w j := (Finset.sum_mul _ _ _).symm
      have e2 : ∑ i, starRingEnd ℂ (w i) * T i j * w j
          = (∑ i, starRingEnd ℂ (w i) * T i j) * w j := (Finset.sum_mul _ _ _).symm
      rw [e1, e2, hcol j]
      ring
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun j _ => hj j), ← Finset.mul_sum, Finset.sum_comm]
  -- A - B = w* (TD - DT) w = 0 by (5.3) and Σ w = 0
  have hsplit : ∑ i, ∑ j, starRingEnd ℂ (w i) * (T i j * ((d j : ℂ) - d i)) * w j
      = ∑ i, ∑ j, starRingEnd ℂ (w i) * (T i j * ((d j : ℂ) * w j))
        - ∑ i, ∑ j, starRingEnd ℂ (w i) * (d i : ℂ) * T i j * w j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have key : ∑ i, ∑ j, starRingEnd ℂ (w i) * (T i j * ((d j : ℂ) - d i)) * w j = 0 := by
    calc ∑ i, ∑ j, starRingEnd ℂ (w i) * (T i j * ((d j : ℂ) - d i)) * w j
        = ∑ i, ∑ j, (starRingEnd ℂ (w i) * (β j * w j) - starRingEnd ℂ (w i) * β i * w j) :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [hdisp i j]; ring))
      _ = ∑ i, (starRingEnd ℂ (w i) * ∑ j, β j * w j
            - starRingEnd ℂ (w i) * β i * ∑ j, w j) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = (∑ i, starRingEnd ℂ (w i)) * ∑ j, β j * w j := by
          rw [hsumw]
          simp only [mul_zero, sub_zero]
          rw [Finset.sum_mul]
      _ = 0 := by rw [← map_sum, hsumw, map_zero, zero_mul]
  have hzq : z * (∑ i, ∑ j, starRingEnd ℂ (w i) * T i j * w j)
      = starRingEnd ℂ z * (∑ i, ∑ j, starRingEnd ℂ (w i) * T i j * w j) := by
    have h := key
    rw [hsplit, hA, hB] at h
    exact sub_eq_zero.mp h
  have hQ := hpos w hsumw hwne
  have hconj : starRingEnd ℂ z = z := (mul_right_cancel₀ hQ hzq).symm
  exact Complex.conj_eq_iff_im.mp hconj

#print axioms ccm_zeros_real

end RHFormalization
