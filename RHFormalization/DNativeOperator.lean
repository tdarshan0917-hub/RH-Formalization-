import Mathlib
import RHFormalization.Basic

/-!
# RHFormalization.DNativeOperator

Native Mathlib-facing operator layer for the D-side finite-stage package.

This file does not prove Appendix D.  It starts replacing the remaining abstract
D-stage predicates by Mathlib-native operator notions where Mathlib currently has
usable infrastructure.

The first targets are:
* self-adjointness via `IsSelfAdjoint`;
* lower semiboundedness as a quadratic-form inequality;
* nonnegativity as a quadratic-form inequality.
-/

namespace RHFormalization

noncomputable section

open Complex

/--
For a bounded complex Hilbert-space operator `H`, nonnegativity means

`Re ⟪x, H x⟫ ≥ 0`

for every vector `x`.

This is the bounded-operator analogue of the shifted nonnegative stage condition.
-/
def OperatorNonnegative
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (H : E →L[ℂ] E) : Prop :=
  ∀ x : E, 0 ≤ (inner ℂ x (H x)).re

/--
Lower semiboundedness as a quadratic-form inequality.

There exists a real lower-bound constant `M` such that

`Re ⟪x, H x⟫ ≥ - M * ‖x‖^2`.

This is a Mathlib-facing bounded-operator model of the lower-semiboundedness
condition used in the D-stage legality package.
-/
def OperatorLowerSemibounded
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (H : E →L[ℂ] E) : Prop :=
  ∃ M : ℝ, ∀ x : E, -M * ‖x‖ ^ 2 ≤ (inner ℂ x (H x)).re

/--
Native bounded finite-stage operator data.

This is not yet the full PWQO finite-stage operator.  It is the Mathlib-facing
operator core needed to begin discharging the first D-stage legality predicates.
-/
structure NativeBoundedDStage
    (E : Type*)
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  H : E →L[ℂ] E
  h_selfAdjoint : IsSelfAdjoint H
  h_lowerSemibounded : OperatorLowerSemibounded H
  h_shiftedNonnegative : OperatorNonnegative H

/--
The self-adjointness certificate is now a Mathlib-native `IsSelfAdjoint` proof.
-/
theorem NativeBoundedDStage.selfAdjoint
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (S : NativeBoundedDStage E) :
    IsSelfAdjoint S.H :=
  S.h_selfAdjoint

/--
The lower-semiboundedness certificate is a concrete quadratic-form inequality.
-/
theorem NativeBoundedDStage.lowerSemibounded
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (S : NativeBoundedDStage E) :
    OperatorLowerSemibounded S.H :=
  S.h_lowerSemibounded

/--
The shifted nonnegativity certificate is a concrete quadratic-form inequality.
-/
theorem NativeBoundedDStage.shiftedNonnegative
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (S : NativeBoundedDStage E) :
    OperatorNonnegative S.H :=
  S.h_shiftedNonnegative

end

end RHFormalization
