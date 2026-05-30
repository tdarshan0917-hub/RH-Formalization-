import RHFormalization.CanonicalPrimePowerCutoffMassEnumeration
import RHFormalization.DCanonicalWindowConcrete

/-!
# RHFormalization.CanonicalPrimePowerDWindowKernelEstimate

Connects D.CANONICAL-WINDOW compact-uniform convergence to the prime-power
kernel-window estimate.

This is not an RH endpoint.

The current D-side frontier contains the hard field

  h_kernel_window_error_le :
    ‖Kstage_n q.center s - Kshared q.center s‖ ≤ windowError s n.

This file proves the compact-epsilon version of that estimate from the
D.CANONICAL-WINDOW API, assuming the prime-power stage kernel and shared kernel
are identified with the finite-window kernel and its limit along a real
displacement coordinate.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Compact-epsilon kernel-window estimate from D.CANONICAL-WINDOW.

If the prime-power stage kernel is represented by `W.gbar_stage`, and the shared
kernel is represented by `W.G_limit`, then compact-uniform convergence of the
window kernel gives eventual uniform control of the prime-power kernel error on
active finite-stage indices whose displacement coordinates lie in a fixed compact
real set.
-/
theorem primePower_kernel_window_error_eventually_of_DCanonicalWindow
    (X : DFiniteStagePackageFromOperatorLayer)
    (W : DCanonicalWindowData)
    (Wapi : DCanonicalWindowAPI W)
    (alpha : ℕ → DFiniteStage)
    (h_alpha : ∀ n : ℕ, alpha n = Wapi.alpha n)
    (Kshared : CanonicalKernelC)
    (coord : PrimePowerPair → ℂ → ℝ)
    (s : ℂ)
    (A : Set ℝ)
    (hA : IsCompact A)
    (h_coord_mem :
      ∀ n : ℕ,
      ∀ q : PrimePowerPair,
        q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
          coord q s ∈ A)
    (h_stage_kernel_eq_window :
      ∀ n : ℕ,
      ∀ q : PrimePowerPair,
        q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
          X.toFiniteCanonicalPrimePowerFormula.kernel (alpha n) q.center s =
            W.gbar_stage (Wapi.alpha n) (coord q s))
    (h_shared_kernel_eq_limit :
      ∀ q : PrimePowerPair,
        Kshared q.center s =
          W.G_limit (coord q s)) :
    ∀ ε : ℝ,
      0 < ε →
        ∀ᶠ n in Filter.atTop,
          ∀ q : PrimePowerPair,
            q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
              ‖X.toFiniteCanonicalPrimePowerFormula.kernel (alpha n) q.center s -
                  Kshared q.center s‖ < ε := by
  intro ε hε

  have hwin :
      ∀ᶠ n in Filter.atTop,
        ∀ a : ℝ,
          a ∈ A →
            dist
              (W.gbar_stage (Wapi.alpha n) a)
              (W.G_limit a) < ε :=
    Wapi.local_uniform_to_G_limit A hA ε hε

  filter_upwards [hwin] with n hn q hq

  have hcoord : coord q s ∈ A :=
    h_coord_mem n q hq

  have hdist :
      dist
        (W.gbar_stage (Wapi.alpha n) (coord q s))
        (W.G_limit (coord q s)) < ε :=
    hn (coord q s) hcoord

  simpa
    [h_stage_kernel_eq_window n q hq,
     h_shared_kernel_eq_limit q,
     dist_eq_norm]
    using hdist

/--
Package-level bridge data for applying D.CANONICAL-WINDOW to prime-power kernels
at a fixed complex point `s`.

This is the local data needed to turn the compact-uniform window theorem into
the active-index prime-power kernel-window estimate.
-/
structure PrimePowerKernelWindowCompactBridgeData
    (X : DFiniteStagePackageFromOperatorLayer)
    (W : DCanonicalWindowData)
    (Wapi : DCanonicalWindowAPI W)
    (alpha : ℕ → DFiniteStage)
    (Kshared : CanonicalKernelC)
    (s : ℂ) where

  /-- The finite-stage sequence agrees with the canonical-window sequence. -/
  h_alpha :
    ∀ n : ℕ, alpha n = Wapi.alpha n

  /-- Real displacement coordinate for each prime-power pair at point `s`. -/
  coord :
    PrimePowerPair → ℝ

  /-- Compact displacement set containing all active finite-stage coordinates. -/
  A : Set ℝ

  /-- Compactness of the displacement set. -/
  hA :
    IsCompact A

  /-- Active finite-stage prime powers have coordinates in the compact set. -/
  h_coord_mem :
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
        coord q ∈ A

  /--
  The finite-stage prime-power kernel is represented by the D.CANONICAL-WINDOW
  stage kernel.
  -/
  h_stage_kernel_eq_window :
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
        X.toFiniteCanonicalPrimePowerFormula.kernel (alpha n) q.center s =
          W.gbar_stage (Wapi.alpha n) (coord q)

  /--
  The shared prime-power kernel is represented by the D.CANONICAL-WINDOW limit.
  -/
  h_shared_kernel_eq_limit :
    ∀ q : PrimePowerPair,
      Kshared q.center s =
        W.G_limit (coord q)

/--
Use compact bridge data to obtain the eventual compact-epsilon version of the
prime-power kernel-window estimate.
-/
theorem PrimePowerKernelWindowCompactBridgeData.eventual_kernel_window_error
    {X : DFiniteStagePackageFromOperatorLayer}
    {W : DCanonicalWindowData}
    {Wapi : DCanonicalWindowAPI W}
    {alpha : ℕ → DFiniteStage}
    {Kshared : CanonicalKernelC}
    {s : ℂ}
    (B : PrimePowerKernelWindowCompactBridgeData X W Wapi alpha Kshared s) :
    ∀ ε : ℝ,
      0 < ε →
        ∀ᶠ n in Filter.atTop,
          ∀ q : PrimePowerPair,
            q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
              ‖X.toFiniteCanonicalPrimePowerFormula.kernel (alpha n) q.center s -
                  Kshared q.center s‖ < ε := by
  intro ε hε
  exact
    primePower_kernel_window_error_eventually_of_DCanonicalWindow
      X
      W
      Wapi
      alpha
      B.h_alpha
      Kshared
      (fun q _s => B.coord q)
      s
      B.A
      B.hA
      (fun n q hq => B.h_coord_mem n q hq)
      (fun n q hq => B.h_stage_kernel_eq_window n q hq)
      (fun q => B.h_shared_kernel_eq_limit q)
      ε
      hε

end

end RHFormalization
