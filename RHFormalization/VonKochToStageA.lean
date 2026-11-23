import RHFormalization.VonKochDiscrepancyBound
import RHFormalization.RHConverseStageA
import RHFormalization.DBFFCompensatorMainTerm
import RHFormalization.DBFFCompensator
import RHFormalization.PolylogSquareStageBridge
import RHFormalization.AdmissibleGalerkinStage
import Mathlib

/-!
# VonKochToStageA — RHC-2c: von Koch bound ⇒ hP_dense

`starObject n s = D(Y; ρ) − 1/(½ − √(s+¼))` with `Y = e^{admR n}`, `ρ = √(s+¼) + ½`, where
`D(Y; ρ) = Σ_{0<k≤Y} Λ(k)k^{-ρ} − (Y^{1-ρ}−1)/(1−ρ)` (`starObject_eq_vmReal`).
On a compact `K ⊆ Ω`: `Re ρ ≥ ½+δ` (`sqrtRe_min`), `‖ρ‖ ≤ R`, `ρ ≠ 1` (`sqrt_ne_half`),
`‖1/(½ − √(s+¼))‖ ≤ 1/e` (`halfDenom_min`). RHC-2b bounds `D`; RHC-1 gives hP_dense.
`RH_of_vonKoch` closes the loop through the Stage A endpoint.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

theorem ofReal_exp_cpow (R : ℝ) (z : ℂ) :
    ((Real.exp R : ℝ) : ℂ) ^ z = Complex.exp (z * R) := by
  have hne : ((Real.exp R : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos R).ne'
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log (Real.exp_pos R).le, Real.log_exp]
  first
    | rw [mul_comm]
    | ring_nf

theorem starObject_eq_vmReal (n : ℕ) {s : ℂ} (hs : s ∈ Ω) :
    starObject n s
      = ((∑ k ∈ Finset.Ioc 0 ⌊Real.exp (admR n)⌋₊,
            LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)) k)
          - ((((Real.exp (admR n) : ℝ) : ℂ)) ^ (1 - (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ))) - 1)
              / (1 - (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ))))
        - 1 / ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) := by
  unfold starObject
  rw [mainTermIntegral_eval n hs, ofReal_exp_cpow,
    show (1:ℂ) - (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)) = (1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ)) by
      ring]
  try ring

/-- **RHC-2c(i)**: von Koch bound ⇒ the star object is uniformly bounded on Ω-compacts. -/
theorem starObject_locbdd_of_vonKoch
    (hVK : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
        ∀ t : ℝ, 1 ≤ t → |Chebyshev.psi t - t| ≤ C * t ^ (1/2 + δ/2)) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖starObject n s‖ ≤ C := by
  intro K hK hKΩ
  obtain ⟨δ, hδ, hre⟩ := sqrtRe_min K hK hKΩ
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn
    ((sqrtShift_continuousOn K hKΩ).add (continuousOn_const (c := (1/2:ℂ))))
  obtain ⟨e, he, hed⟩ := halfDenom_min K hK hKΩ
  obtain ⟨C, hC, hVKδ⟩ := hVK δ hδ
  obtain ⟨B, hB⟩ := vmDiscrepancyReal_bound δ R C hδ hC hVKδ
  refine ⟨B + 1 / e, fun n s hs => ?_⟩
  have hsΩ : s ∈ Ω := hKΩ hs
  rw [starObject_eq_vmReal n hsΩ]
  have h12 : ((1/2:ℂ)).re = 1/2 := by
    first
      | (norm_num; done)
      | (simp; done)
      | (rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by push_cast; ring, Complex.ofReal_re])
  have hρre : 1/2 + δ ≤ (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)).re := by
    rw [Complex.add_re, h12]
    linarith [hre s hs]
  have hρ1 : Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ) ≠ 1 := by
    intro h
    apply sqrt_ne_half hsΩ
    linear_combination h
  have hY : 1 ≤ Real.exp (admR n) := Real.one_le_exp (admR_pos n).le
  have hmain := hB _ hρre (hR s hs) hρ1 _ hY
  have hden : ‖1 / ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ)))‖ ≤ 1 / e := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le he (hed s hs)
  have t := norm_sub_le
    ((∑ k ∈ Finset.Ioc 0 ⌊Real.exp (admR n)⌋₊,
        LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)) k)
      - ((((Real.exp (admR n) : ℝ) : ℂ)) ^ (1 - (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ))) - 1)
          / (1 - (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ))))
    (1 / ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))))
  linarith

/-- **RHC-2c — von Koch bound ⇒ hP_dense.** -/
theorem hPdense_of_vonKoch
    (hVK : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
        ∀ t : ℝ, 1 ≤ t → |Chebyshev.psi t - t| ≤ C * t ^ (1/2 + δ/2)) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cp : ℝ, ∀ n, ∀ s ∈ K,
          ‖(2:ℂ) * denseFreePairedTransform n s - compensatorM n s‖ ≤ Cp :=
  hPdense_of_starObject_locbdd (starObject_locbdd_of_vonKoch hVK)

/-- Sanity loop: von Koch bound ⇒ RH through the Stage A endpoint. -/
theorem RH_of_vonKoch
    (hVK : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
        ∀ t : ℝ, 1 ≤ t → |Chebyshev.psi t - t| ≤ C * t ^ (1/2 + δ/2)) :
    RiemannHypothesis :=
  RH_from_pairedTransform_only_dense (hPdense_of_vonKoch hVK)

#print axioms starObject_eq_vmReal
#print axioms starObject_locbdd_of_vonKoch
#print axioms hPdense_of_vonKoch
#print axioms RH_of_vonKoch

end

end RHFormalization
