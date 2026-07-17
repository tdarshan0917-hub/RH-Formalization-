import RHFormalization.ShiftedLaplaceLogDerivModel
import RHFormalization.ShiftedLaplaceBsharedMeromorphic
import Mathlib.Analysis.Complex.SqrtDeriv

namespace RHFormalization

open Complex Filter Topology

/-- `φ(s) = √(s+1/4) + 1/2`. -/
noncomputable def shiftedPhi (s : ℂ) : ℂ := Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)

/-- `φ` has derivative `(s+1/4)^(-1/2)/2` at any `s ∈ Ω`. -/
theorem shiftedPhi_hasDerivAt_of_mem_Omega {s : ℂ} (hs : s ∈ Ω) :
    HasDerivAt shiftedPhi ((s + (1/4:ℂ)) ^ (-1/2 : ℂ) / 2) s := by
  have hslit : (s + (1/4:ℂ)) ∈ Complex.slitPlane := shift_mem_slitPlane_of_mem_Omega hs
  -- inner: s + 1/4 has deriv 1
  have hinner : HasDerivAt (fun z : ℂ => z + (1/4:ℂ)) 1 s :=
    (hasDerivAt_id s).add_const _
  -- sqrt has deriv (s+1/4)^(-1/2)/2 at (s+1/4)
  have hsqrt : HasDerivAt Complex.sqrt ((s + (1/4:ℂ)) ^ (-1/2 : ℂ) / 2) (s + (1/4:ℂ)) :=
    Complex.hasDerivAt_sqrt hslit
  -- chain: (sqrt ∘ (·+1/4)) has deriv [(s+1/4)^(-1/2)/2] * 1
  have hcomp0 : HasDerivAt (Complex.sqrt ∘ (fun z : ℂ => z + (1/4:ℂ)))
      ((s + (1/4:ℂ)) ^ (-1/2 : ℂ) / 2 * 1) s := hsqrt.comp s hinner
  have hcomp : HasDerivAt (fun z => Complex.sqrt (z + (1/4:ℂ)))
      ((s + (1/4:ℂ)) ^ (-1/2 : ℂ) / 2) s := by
    rw [mul_one] at hcomp0
    exact hcomp0
  -- add const 1/2
  exact hcomp.add_const _

/-- `deriv φ s0 = (s0+1/4)^(-1/2)/2`. -/
theorem shiftedPhi_deriv_of_mem_Omega {s : ℂ} (hs : s ∈ Ω) :
    deriv shiftedPhi s = (s + (1/4:ℂ)) ^ (-1/2 : ℂ) / 2 :=
  (shiftedPhi_hasDerivAt_of_mem_Omega hs).deriv

/-- `deriv φ s0 ≠ 0` for `s ∈ Ω`. -/
theorem shiftedPhi_deriv_ne_zero_of_mem_Omega {s : ℂ} (hs : s ∈ Ω) :
    deriv shiftedPhi s ≠ 0 := by
  rw [shiftedPhi_deriv_of_mem_Omega hs]
  have hne : (s + (1/4:ℂ)) ≠ 0 := shift_ne_zero_of_mem_Omega hs
  have hcpow : (s + (1/4:ℂ)) ^ (-1/2 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num) |>.mpr hne
  exact div_ne_zero hcpow (by norm_num)

end RHFormalization
