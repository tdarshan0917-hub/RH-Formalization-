import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import RHFormalization.Basic

/-!
# RHFormalization.DNativeUnboundedOperator

Native Mathlib-facing unbounded-operator layer for the D-side finite-stage package.

This file begins replacing the remaining abstract D-stage predicates by Mathlib-native
unbounded operator notions.

It provides:
* partial linear maps;
* self-adjointness;
* closedness and dense domain from self-adjointness;
* lower semiboundedness as a quadratic-form inequality;
* shifted nonnegativity as a quadratic-form inequality.
-/

namespace RHFormalization

noncomputable section

/--
Quadratic-form lower semiboundedness for a Mathlib partial linear map.

The quantifier ranges over the operator domain.
-/
def LinearPMapLowerSemibounded
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (H : E →ₗ.[ℂ] E) : Prop :=
  ∃ M : ℝ, ∀ x : H.domain,
    -M * ‖(x : E)‖ ^ 2 ≤ (inner ℂ (x : E) (H x : E)).re

/--
Quadratic-form nonnegativity for a Mathlib partial linear map.

This models the globally shifted nonnegative finite-stage operator condition.
-/
def LinearPMapNonnegative
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (H : E →ₗ.[ℂ] E) : Prop :=
  ∀ x : H.domain,
    0 ≤ (inner ℂ (x : E) (H x : E)).re

/--
Native unbounded D-stage operator core.

This is closer to the manuscript's Schrödinger/Friedrichs operator than the bounded
`ContinuousLinearMap` test layer. The operator is a Mathlib partial linear map
`E →ₗ.[ℂ] E`.
-/
structure NativeUnboundedDStage
    (E : Type*)
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  H : E →ₗ.[ℂ] E
  h_selfAdjoint :
    IsSelfAdjoint H
  h_lowerSemibounded :
    LinearPMapLowerSemibounded H
  h_shiftedNonnegative :
    LinearPMapNonnegative H

/--
A native unbounded D-stage operator is closed.
-/
theorem NativeUnboundedDStage.isClosed
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (S : NativeUnboundedDStage E) :
    S.H.IsClosed :=
  S.h_selfAdjoint.isClosed

/--
A native unbounded D-stage operator has dense domain.
-/
theorem NativeUnboundedDStage.dense_domain
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (S : NativeUnboundedDStage E) :
    Dense (S.H.domain : Set E) :=
  S.h_selfAdjoint.dense_domain

/--
Self-adjointness certificate extracted from the native unbounded D-stage object.
-/
theorem NativeUnboundedDStage.selfAdjoint
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (S : NativeUnboundedDStage E) :
    IsSelfAdjoint S.H :=
  S.h_selfAdjoint

/--
Lower-semiboundedness certificate extracted from the native unbounded D-stage object.
-/
theorem NativeUnboundedDStage.lowerSemibounded
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (S : NativeUnboundedDStage E) :
    LinearPMapLowerSemibounded S.H :=
  S.h_lowerSemibounded

/--
Shifted nonnegativity certificate extracted from the native unbounded D-stage object.
-/
theorem NativeUnboundedDStage.shiftedNonnegative
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (S : NativeUnboundedDStage E) :
    LinearPMapNonnegative S.H :=
  S.h_shiftedNonnegative

end

end RHFormalization
