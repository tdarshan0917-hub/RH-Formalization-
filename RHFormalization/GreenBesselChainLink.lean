import RHFormalization.GreenBesselFinite
import RHFormalization.GreenSqHalfLineTarget
import RHFormalization.GreenSqRemainderBound

/-!
# RHFormalization.GreenBesselChainLink
**P2 chain link: mode sum ≤ half-line target + crushed box error.**
Composes P2-B3 (`green_bessel_finite`), P2-B2/target split
(`greenSq_diagonal_eq_halfLine_add_remainder`), and P2-C2b
(`greenSqRemainder_abs_le`) into the single statement the Gate-1
assembly consumes at `κ² = s + SupVConst`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Real

/-- **P2 chain link.** For any finite mode set, the sine mode sum is
dominated by the half-line target plus the superexponentially small
box error. -/
theorem green_bessel_mode_sum_le_halfLine (κ L a : ℝ) (S : Finset ℕ)
    (hκ : 0 < κ) (ha0 : 0 ≤ a) (haL : a ≤ L) (hkL : 1 ≤ κ * L) :
    (2 / L) * ∑ m ∈ S,
        Real.sin ((((m : ℝ) + 1) * Real.pi / L) * a) ^ 2
          / (κ ^ 2 + galerkinLam L m) ^ 2
      ≤ greenSqHalfLine κ a
        + 2 * (2 * L + 1 / (2 * κ)) * Real.exp (-(2 * κ * (L - a))) / κ ^ 2 := by
  have hL : 0 < L := by
    by_contra h
    push_neg at h
    nlinarith
  have hB := green_bessel_finite κ L a S hκ hL ha0 haL
  have hsplit := greenSq_diagonal_eq_halfLine_add_remainder κ L a hκ hL ha0 haL
  have hrem := greenSqRemainder_abs_le κ L a hκ ha0 haL hkL
  have habs : greenSqRemainder κ L a ≤ |greenSqRemainder κ L a| :=
    le_abs_self _
  rw [hsplit] at hB
  linarith

#print axioms green_bessel_mode_sum_le_halfLine

end

end RHFormalization
