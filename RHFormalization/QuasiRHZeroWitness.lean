import RHFormalization.PolylogEndpoint
import RHFormalization.ShiftedLaplaceBranchIdentity
import RHFormalization.PoleGeometry
import RHFormalization.MontelUniqueLimit
import Mathlib

/-!
# QuasiRHZeroWitness — QR-1: the subregion Ω_θ and where far zeros put their poles

`Ω_θ := {s ∈ Ω : θ < Re √(s+¼)}`. A nontrivial zero ρ with `|Re ρ − ½| > θ` (θ ≥ 0)
has its pole `polePoint ρ = −ρ(1−ρ)` inside `Ω_θ`: `√(s₀+¼) = ρ − ½` (or `½ − ρ`), so
`Re √(s₀+¼) = |Re ρ − ½| > θ`. The quasi-RH target `QuasiRH θ` says every nontrivial
zero satisfies `|Re ρ − ½| ≤ θ`; `QuasiRH 0` is RH.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

/-- The subregion `Ω_θ` of the slit plane. -/
def OmegaTheta (θ : ℝ) : Set ℂ :=
  {s : ℂ | s ∈ Ω ∧ θ < (Complex.sqrt (s + (1/4:ℂ))).re}

/-- Quasi-RH at width θ: every nontrivial zero lies within θ of the critical line. -/
def QuasiRH (θ : ℝ) : Prop :=
  ∀ ρ : ℂ, IsNontrivialZetaZero ρ → |ρ.re - 1/2| ≤ θ

theorem OmegaTheta_subset_Omega (θ : ℝ) : OmegaTheta θ ⊆ Ω := fun _ h => h.1

theorem isOpen_OmegaTheta (θ : ℝ) : IsOpen (OmegaTheta θ) := by
  have hcont : ContinuousOn (fun s : ℂ => (Complex.sqrt (s + (1/4:ℂ))).re) Ω :=
    Complex.continuous_re.comp_continuousOn (sqrtShift_continuousOn Ω (fun _ h => h))
  have h := hcont.isOpen_inter_preimage isOpen_Omega (isOpen_Ioi (a := θ))
  first
    | exact h
    | (have he : OmegaTheta θ
          = Ω ∩ (fun s : ℂ => (Complex.sqrt (s + (1/4:ℂ))).re) ⁻¹' Set.Ioi θ := by
         ext s; rfl
       rw [he]; exact h)

/-- A zero to the right of `½ + θ` puts its pole in `Ω_θ`. -/
theorem polePoint_mem_OmegaTheta_of_gt (ZF : ZetaZeroFacts) {ρ : ℂ}
    (h_zero : IsNontrivialZetaZero ρ) {θ : ℝ} (hθ : 0 ≤ θ)
    (h : (1/2:ℝ) + θ < ρ.re) :
    polePoint ρ ∈ OmegaTheta θ := by
  have hgt : (1/2:ℝ) < ρ.re := by linarith
  refine ⟨?_, ?_⟩
  · exact offLine_zeroPolePoint_in_Omega ZF h_zero hgt.ne'
  · rw [sqrt_polePoint_eq_of_re_gt hgt, Complex.sub_re]
    have h12 : ((1/2:ℂ)).re = (1/2:ℝ) := by norm_num
    rw [h12]
    linarith

/-- A zero to the left of `½ − θ` puts its pole in `Ω_θ`. -/
theorem polePoint_mem_OmegaTheta_of_lt (ZF : ZetaZeroFacts) {ρ : ℂ}
    (h_zero : IsNontrivialZetaZero ρ) {θ : ℝ} (hθ : 0 ≤ θ)
    (h : ρ.re < (1/2:ℝ) - θ) :
    polePoint ρ ∈ OmegaTheta θ := by
  have hlt : ρ.re < (1/2:ℝ) := by linarith
  refine ⟨?_, ?_⟩
  · exact offLine_zeroPolePoint_in_Omega ZF h_zero hlt.ne
  · rw [sqrt_polePoint_eq_of_re_lt hlt, Complex.sub_re]
    have h12 : ((1/2:ℂ)).re = (1/2:ℝ) := by norm_num
    rw [h12]
    linarith

/-- **QR-1**: a zero off the strip `|Re ρ − ½| ≤ θ` puts its pole in `Ω_θ`. -/
theorem polePoint_mem_OmegaTheta_of_offStrip (ZF : ZetaZeroFacts) {ρ : ℂ}
    (h_zero : IsNontrivialZetaZero ρ) {θ : ℝ} (hθ : 0 ≤ θ)
    (h : θ < |ρ.re - 1/2|) :
    polePoint ρ ∈ OmegaTheta θ := by
  rcases lt_abs.mp h with h1 | h1
  · exact polePoint_mem_OmegaTheta_of_gt ZF h_zero hθ (by linarith)
  · exact polePoint_mem_OmegaTheta_of_lt ZF h_zero hθ (by linarith)

/-- `QuasiRH 0` is exactly RH. -/
theorem quasiRH_zero_iff : QuasiRH 0 ↔ RiemannHypothesis := by
  constructor
  · intro h ρ hρ
    have := h ρ hρ
    have h0 : |ρ.re - 1/2| = 0 := le_antisymm this (abs_nonneg _)
    have := abs_eq_zero.mp h0
    linarith
  · intro h ρ hρ
    rw [h ρ hρ]
    norm_num

#print axioms isOpen_OmegaTheta
#print axioms polePoint_mem_OmegaTheta_of_offStrip
#print axioms quasiRH_zero_iff

end

end RHFormalization
