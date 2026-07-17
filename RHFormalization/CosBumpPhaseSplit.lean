import RHFormalization.CosBumpRecenter
import Mathlib

set_option autoImplicit false

namespace RHFormalization

open Real MeasureTheory intervalIntegral
open scoped Real BigOperators

/-!
# O3 brick 2 — phase split of the recentered Gaussian cosine transform.

cos(j*π*(u+log q)/L) = cos(A u + B) splits by angle-addition; the B-phases are
u-constant and pull out, leaving centered cosine and sine transforms.
-/

theorem cosBumpIntegral_phase_split (d : ℝ) (q : ℕ) (L : ℝ) (j : ℝ) :
    cosBumpIntegral d q L j
      = Real.cos (j * Real.pi * Real.log q / L)
          * (∫ u in (0 - Real.log q)..(L - Real.log q),
              Real.cos (j * Real.pi * u / L) * gaussBump d u)
        - Real.sin (j * Real.pi * Real.log q / L)
          * (∫ u in (0 - Real.log q)..(L - Real.log q),
              Real.sin (j * Real.pi * u / L) * gaussBump d u) := by
  rw [cosBumpIntegral_recenter]
  have hpt : ∀ u : ℝ,
      Real.cos (j * Real.pi * (u + Real.log q) / L) * gaussBump d u
        = Real.cos (j * Real.pi * Real.log q / L)
            * (Real.cos (j * Real.pi * u / L) * gaussBump d u)
          - Real.sin (j * Real.pi * Real.log q / L)
            * (Real.sin (j * Real.pi * u / L) * gaussBump d u) := by
    intro u
    have harg : j * Real.pi * (u + Real.log q) / L
        = j * Real.pi * u / L + j * Real.pi * Real.log q / L := by ring
    rw [harg, Real.cos_add]; ring
  rw [intervalIntegral.integral_congr (fun u _ => hpt u)]
  have hcC : Continuous (fun u : ℝ =>
      Real.cos (j * Real.pi * Real.log q / L)
        * (Real.cos (j * Real.pi * u / L) * gaussBump d u)) := by
    unfold gaussBump; fun_prop
  have hcS : Continuous (fun u : ℝ =>
      Real.sin (j * Real.pi * Real.log q / L)
        * (Real.sin (j * Real.pi * u / L) * gaussBump d u)) := by
    unfold gaussBump; fun_prop
  rw [intervalIntegral.integral_sub
        (hcC.intervalIntegrable _ _) (hcS.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]

#print axioms cosBumpIntegral_phase_split

end RHFormalization
