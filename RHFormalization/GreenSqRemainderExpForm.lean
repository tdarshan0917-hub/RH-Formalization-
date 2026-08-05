import RHFormalization.GreenSqHalfLineTarget
import Mathlib

/-!
# GreenSqRemainderExpForm — P2-C2a: the remainder in exact exp/sinh form

ROUTE CARD
1. Target: `greenSqRemainder κ L a = e^{2κa}·M/(8κ²·sinh(κL)²)` with
   `M = a·y(1−y)(2−z(1+y)) − (L−a)(1−y)² − (1−y)²(1−yz)/(2κ)`,
   `y = e^{−2κa}, z = e^{−2κ(L−a)}` (numerically verified). Via the core
   cross-multiplied identity `N − 2κ²·F∞·sinh(κL)² = e^{2κa}·M/4`, which
   has ONLY monomial denominators (A, B, κ) — field_simp-safe.
   Since `e^{2κa}/sinh(κL)² ≈ 4e^{−2κ(L−a)}·(1+…)`, the C2b bound
   `|rem| ≤ C·L·e^{−2κ(L−a)}/κ²` follows from |M| ≤ 2L + 1/(2κ).
2. Raw B on Ω? NO. B−M bare Prop? NO — field identities.
3. Consumer: P2-C2b (the bound) → eps-class box remainder on the net.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace RHFormalization

open Real

/-- The bounded factor of the remainder. -/
noncomputable def greenSqRemainderM (κ L a : ℝ) : ℝ :=
  a * Real.exp (-(2*κ*a)) * (1 - Real.exp (-(2*κ*a)))
      * (2 - Real.exp (-(2*κ*(L-a))) * (1 + Real.exp (-(2*κ*a))))
    - (L - a) * (1 - Real.exp (-(2*κ*a)))^2
    - (1 - Real.exp (-(2*κ*a)))^2
        * (1 - Real.exp (-(2*κ*a)) * Real.exp (-(2*κ*(L-a)))) / (2*κ)

/-- **The core cross-multiplied identity** (monomial denominators only). -/
theorem greenSqCore (κ L a : ℝ) (hκ : 0 < κ) :
    Real.sinh (κ*(L-a))^2 * (Real.sinh (κ*a) * Real.cosh (κ*a) / κ - a)
      + Real.sinh (κ*a)^2
          * (Real.sinh (κ*(L-a)) * Real.cosh (κ*(L-a)) / κ - (L - a))
      - 2 * κ^2 * greenSqHalfLine κ a * Real.sinh (κ*L)^2
    = Real.exp (2*κ*a) * greenSqRemainderM κ L a / 4 := by
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  have hXa : Real.exp (-(2*κ*a)) = ((Real.exp (κ * a))⁻¹) ^ 2 := by
    rw [show -(2*κ*a) = (-(κ*a)) + (-(κ*a)) by ring, Real.exp_add,
      Real.exp_neg]
    ring
  have hYa : Real.exp (-(2*κ*(L-a))) = ((Real.exp (κ * (L-a)))⁻¹) ^ 2 := by
    rw [show -(2*κ*(L-a)) = (-(κ*(L-a))) + (-(κ*(L-a))) by ring,
      Real.exp_add, Real.exp_neg]
    ring
  have hX2 : Real.exp (2*κ*a) = (Real.exp (κ * a)) ^ 2 := by
    rw [show (2*κ*a) = κ*a + κ*a by ring, Real.exp_add]
    ring
  have hL_split : Real.exp (κ * L)
      = Real.exp (κ * a) * Real.exp (κ * (L - a)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsinh_a : Real.sinh (κ * a)
      = (Real.exp (κ * a) - (Real.exp (κ * a))⁻¹) / 2 := by
    rw [Real.sinh_eq, Real.exp_neg]
  have hsinh_u : Real.sinh (κ * (L - a))
      = (Real.exp (κ * (L-a)) - (Real.exp (κ * (L-a)))⁻¹) / 2 := by
    rw [Real.sinh_eq, Real.exp_neg]
  have hsinh_L : Real.sinh (κ * L)
      = (Real.exp (κ * a) * Real.exp (κ * (L-a))
          - (Real.exp (κ * a) * Real.exp (κ * (L-a)))⁻¹) / 2 := by
    rw [Real.sinh_eq, Real.exp_neg, hL_split]
  have hcosh_a : Real.cosh (κ * a)
      = (Real.exp (κ * a) + (Real.exp (κ * a))⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg]
  have hcosh_u : Real.cosh (κ * (L - a))
      = (Real.exp (κ * (L-a)) + (Real.exp (κ * (L-a)))⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg]
  have hX0 : Real.exp (κ * a) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hY0 : Real.exp (κ * (L - a)) ≠ 0 := ne_of_gt (Real.exp_pos _)
  unfold greenSqHalfLine greenSqRemainderM
  rw [hsinh_a, hsinh_u, hsinh_L, hcosh_a, hcosh_u, hXa, hYa, hX2]
  field_simp
  ring

/-- **P2-C2a: exact exp/sinh form of the box remainder.** -/
theorem greenSqRemainder_exp_form (κ L a : ℝ) (hκ : 0 < κ) (hL : 0 < L) :
    greenSqRemainder κ L a
      = Real.exp (2*κ*a) * greenSqRemainderM κ L a
          / (8 * κ^2 * Real.sinh (κ*L)^2) := by
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  have hkl : 0 < κ * L := by positivity
  have hS_pos : 0 < Real.sinh (κ * L) := by
    first
      | exact Real.sinh_pos_iff.mpr hkl
      | exact (Real.sinh_pos _).mpr hkl
      | exact Real.sinh_pos.mpr hkl
      | (rw [Real.sinh_eq]
         have hlt := Real.exp_lt_exp.mpr (neg_lt_self hkl)
         linarith)
  have hS0 : Real.sinh (κ * L) ≠ 0 := ne_of_gt hS_pos
  have hcore := greenSqCore κ L a hκ
  unfold greenSqRemainder
  set S := Real.sinh (κ * L) with hSdef
  field_simp at hcore ⊢
  first
    | linear_combination 4 * hcore
    | linear_combination 2 * hcore
    | linear_combination hcore
    | linear_combination 8 * hcore
    | linear_combination (4 : ℝ) * S ^ 2 * hcore
    | linear_combination 4 * κ * hcore
    | linear_combination 16 * hcore
    | nlinarith [hcore, sq_nonneg S, sq_nonneg κ]

#print axioms greenSqRemainderM
#print axioms greenSqCore
#print axioms greenSqRemainder_exp_form

end RHFormalization
