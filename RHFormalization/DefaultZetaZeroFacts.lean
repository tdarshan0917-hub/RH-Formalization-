import Mathlib.NumberTheory.LSeries.RiemannZeta
import RHFormalization.Basic

/-!
# RHFormalization.DefaultZetaZeroFacts

Clean reduction of `ZetaZeroFacts` to one classical zeta fact:

  ζ(s) ≠ 0 for real s with 0 < Re(s) < 1.

This file does NOT claim that Mathlib already proves that fact.
It packages the exact remaining ZF obligation.
-/

namespace RHFormalization

noncomputable section

open Complex

/--
Parameterized constructor for `ZetaZeroFacts`.

If we have the classical fact that `riemannZeta s ≠ 0` for real
`s` in the open interval `(0,1)`, then `ZetaZeroFacts` follows.
-/
def defaultZetaZeroFacts_of_realZeroFree
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0) :
    ZetaZeroFacts where
  nontrivial_zero_im_ne_zero := by
    intro ρ hρ h_im
    obtain ⟨h_zero, h_pos, h_lt⟩ := hρ
    exact h_real_zero_free ρ h_im h_pos h_lt h_zero

end

end RHFormalization
