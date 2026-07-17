import RHFormalization.DBFFStarObject

/-!
# DBFFStarBoundSplit

ROUTE CARD
1. Target: first bound-splitting brick for the `hstar` / O3 slot.
2. Object: `starObject`, already banked in `DBFFStarObject`.
3. Raw B on Ω? NO.
4. R = F − raw B forced? NO.
5. True outright: this is only algebra/norm splitting.
6. Manuscript: D.OP-BOUND / D.OP.2 / O3; prepares off-parabola and parabola-depth bounds.
7. Consumer: `DBFFStarOffParabolaBound` and later the operator-side O1–O3 proof.

This file does not prove O3. It splits O3 into two named bound obligations:
the Dirichlet partial-sum part and the main-term part.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Finset ArithmeticFunction

open scoped BigOperators

/-- The Dirichlet partial-sum part of `starObject`. -/
def starDirichletPartial (n : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.Ioc 0 ⌊Real.exp (admR n)⌋₊,
    LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
      (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)) k

/-- The main-term plus fixed-term part subtracted in `starObject`. -/
def starMainPart (n : ℕ) (s : ℂ) : ℂ :=
  mainTermIntegral n s
    + 1 / ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ)))

/-- `starObject` is exactly Dirichlet partial sum minus main part. -/
theorem starObject_eq_dirichlet_sub_main (n : ℕ) (s : ℂ) :
    starObject n s = starDirichletPartial n s - starMainPart n s := by
  unfold starObject starDirichletPartial starMainPart
  ring

/-- Norm split for `starObject`. -/
theorem starObject_norm_le_parts (n : ℕ) (s : ℂ) :
    ‖starObject n s‖
      ≤ ‖starDirichletPartial n s‖ + ‖starMainPart n s‖ := by
  rw [starObject_eq_dirichlet_sub_main]
  exact norm_sub_le _ _

/--
If the Dirichlet partial part and main part are uniformly bounded on `K`,
then `starObject` is uniformly bounded on `K`.

This is the local bridge used by the off-parabola O3 brick.
-/
theorem starObject_bounded_of_parts_bounded
    (K : Set ℂ)
    (Cdir Cmain : ℝ)
    (hdir : ∀ n : ℕ, ∀ s ∈ K, ‖starDirichletPartial n s‖ ≤ Cdir)
    (hmain : ∀ n : ℕ, ∀ s ∈ K, ‖starMainPart n s‖ ≤ Cmain) :
    ∀ n : ℕ, ∀ s ∈ K, ‖starObject n s‖ ≤ Cdir + Cmain := by
  intro n s hs
  calc
    ‖starObject n s‖
        ≤ ‖starDirichletPartial n s‖ + ‖starMainPart n s‖ :=
          starObject_norm_le_parts n s
    _ ≤ Cdir + Cmain := add_le_add (hdir n s hs) (hmain n s hs)

#print axioms starDirichletPartial
#print axioms starMainPart
#print axioms starObject_eq_dirichlet_sub_main
#print axioms starObject_norm_le_parts
#print axioms starObject_bounded_of_parts_bounded

end

end RHFormalization
