import RHFormalization.GreenBesselChainLink

/-!
# RHFormalization.DensityOscSinSqBridge
**P2 identification (real axis): the combined density−osc cosine sum is the
sin² mode sum, hence dominated by the half-line target + crushed box error.**
Per-mode: `1 − cos(2θ) = 2·sin²θ` with `θ = ((m+1)π/L)·a`, then the P2 chain
link at `κ = √t`, `κ² = t`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Real

/-- **Real-axis identification.** The `(1/L)·Σ (1−cos 2θ_m)/(t+λ_m)²`
combined object is exactly the Bessel mode sum, so the P2 chain link
dominates it. -/
theorem density_osc_cos_sum_le_halfLine (t L a : ℝ) (N : ℕ)
    (ht : 0 < t) (ha0 : 0 ≤ a) (haL : a ≤ L)
    (hkL : 1 ≤ Real.sqrt t * L) :
    (1 / L) * ∑ m ∈ Finset.range N,
        (1 - Real.cos (2 * ((((m : ℝ) + 1) * Real.pi / L) * a)))
          / (t + galerkinLam L m) ^ 2
      ≤ greenSqHalfLine (Real.sqrt t) a
        + 2 * (2 * L + 1 / (2 * Real.sqrt t))
            * Real.exp (-(2 * Real.sqrt t * (L - a))) / t := by
  set κ : ℝ := Real.sqrt t with hκdef
  have hκ : 0 < κ := Real.sqrt_pos.mpr ht
  have hκ2 : κ ^ 2 = t := Real.sq_sqrt ht.le
  have hCL := green_bessel_mode_sum_le_halfLine κ L a (Finset.range N)
    hκ ha0 haL hkL
  rw [hκ2] at hCL
  have hLHS : (1 / L) * ∑ m ∈ Finset.range N,
        (1 - Real.cos (2 * ((((m : ℝ) + 1) * Real.pi / L) * a)))
          / (t + galerkinLam L m) ^ 2
      = (2 / L) * ∑ m ∈ Finset.range N,
          Real.sin ((((m : ℝ) + 1) * Real.pi / L) * a) ^ 2
            / (t + galerkinLam L m) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have htrig := Real.sin_sq_eq_half_sub ((((m : ℝ) + 1) * Real.pi / L) * a)
    have hcos : 1 - Real.cos (2 * ((((m : ℝ) + 1) * Real.pi / L) * a))
        = 2 * Real.sin ((((m : ℝ) + 1) * Real.pi / L) * a) ^ 2 := by
      linarith
    rw [hcos]
    ring
  rw [hLHS]
  exact hCL

#print axioms density_osc_cos_sum_le_halfLine

end

end RHFormalization
