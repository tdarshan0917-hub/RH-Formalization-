import RHFormalization.QuasiRHZeroWitness
import Mathlib

/-!
# QuasiRHConnected — QR-2: Ω_θ is preconnected

In the coordinate `w = √(s+¼)`, `Ω_θ` is the image under `w ↦ w² − ¼` of
`W_θ := {w : θ < Re w, w² − ¼ ∈ Ω}` = half-plane `Re w > θ` minus the real segment
`(θ, ½]`. `W_θ` is star-convex about any real point `p > max(½, θ)`: the segment from `p`
to a non-real `w` meets the real axis only at `p`, and from `p` to a real `w > ½` it stays
in `(½, ∞)`. Star-convex ⟹ preconnected; continuous image ⟹ `Ω_θ` preconnected.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

/-- The `w`-picture of `Ω_θ`. -/
def Wset (θ : ℝ) : Set ℂ :=
  {w : ℂ | θ < w.re ∧ w ^ 2 - (1/4:ℂ) ∈ Ω}

theorem sqQ_re (z : ℂ) : (z ^ 2 - (1/4:ℂ)).re = z.re ^ 2 - z.im ^ 2 - 1/4 := by
  have hq : ((1/4:ℂ)).re = 1/4 := by norm_num
  rw [Complex.sub_re, sq, Complex.mul_re, hq]
  ring

theorem sqQ_im (z : ℂ) : (z ^ 2 - (1/4:ℂ)).im = 2 * z.re * z.im := by
  have hq : ((1/4:ℂ)).im = 0 := by norm_num
  rw [Complex.sub_im, sq, Complex.mul_im, hq]
  ring

/-- `W_θ` is star-convex about any real `p` with `p > ½` and `p > θ`. -/
theorem starConvex_Wset {θ p : ℝ} (hθ : 0 ≤ θ) (hp : 1/2 < p) (hpθ : θ < p) :
    StarConvex ℝ (p : ℂ) (Wset θ) := by
  intro y hy a b ha hb hab
  obtain ⟨hyre, hyΩ⟩ := hy
  have hzre : (a • (p:ℂ) + b • y).re = a * p + b * y.re := by
    simp [Complex.add_re, Complex.smul_re, Complex.ofReal_re, smul_eq_mul]
  have hzim : (a • (p:ℂ) + b • y).im = b * y.im := by
    simp [Complex.add_im, Complex.smul_im, Complex.ofReal_im, smul_eq_mul]
  have hθab : θ = a * θ + b * θ := by rw [← add_mul, hab, one_mul]
  have hre_gt : θ < a * p + b * y.re := by
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · have hb1 : b = 1 := by linarith
      rw [← ha0, hb1]
      linarith
    · have h1 : 0 < a * (p - θ) := mul_pos ha0 (by linarith)
      have h2 : 0 ≤ b * (y.re - θ) := mul_nonneg hb (by linarith)
      linarith
  refine ⟨by rw [hzre]; exact hre_gt, ?_⟩
  rw [mem_Omega_iff]
  rintro ⟨him, hre⟩
  rw [sqQ_im, hzre, hzim] at him
  rw [sqQ_re, hzre, hzim] at hre
  have hzpos : 0 < a * p + b * y.re := by linarith
  have hbim : b * y.im = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · norm_num at h'
      · linarith
    · exact h
  rw [hbim] at hre
  have hX : a * p + b * y.re ≤ 1/2 := by nlinarith
  rcases mul_eq_zero.mp hbim with hb0 | hyim
  · have ha1 : a = 1 := by linarith
    rw [hb0, ha1] at hX
    linarith
  · have hyΩ' := hyΩ
    rw [mem_Omega_iff] at hyΩ'
    have hyre_half : 1/2 < y.re := by
      by_contra hcon
      push_neg at hcon
      apply hyΩ'
      constructor
      · rw [sqQ_im, hyim]; ring
      · rw [sqQ_re, hyim]; nlinarith
    have h1 : 0 ≤ a * (p - 1/2) := mul_nonneg ha (by linarith)
    have h2 : 0 ≤ b * (y.re - 1/2) := mul_nonneg hb (by linarith)
    have hhalf : (1/2:ℝ) = a * (1/2) + b * (1/2) := by rw [← add_mul, hab, one_mul]
    have ha0 : a * (p - 1/2) = 0 := by linarith
    have hb0' : b * (y.re - 1/2) = 0 := by linarith
    rcases mul_eq_zero.mp ha0 with ha' | hp'
    · have hb1 : b = 1 := by linarith
      rw [hb1] at hb0'
      linarith
    · linarith

theorem isPreconnected_Wset (θ : ℝ) (hθ : 0 ≤ θ) : IsPreconnected (Wset θ) := by
  have hp : (1/2:ℝ) < max 1 (θ + 1) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hpθ : θ < max 1 (θ + 1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hsc := starConvex_Wset hθ hp hpθ
  first
    | exact hsc.isPreconnected
    | (have hmem : ((max 1 (θ + 1) : ℝ) : ℂ) ∈ Wset θ := by
         refine ⟨by simpa using hpθ, ?_⟩
         rw [mem_Omega_iff]
         rintro ⟨_, hre⟩
         rw [sqQ_re] at hre
         simp only [Complex.ofReal_re, Complex.ofReal_im] at hre
         nlinarith
       exact (hsc.isPathConnected hmem).isConnected.isPreconnected)

/-- `Ω_θ` is the image of `W_θ` under `w ↦ w² − ¼`. -/
theorem OmegaTheta_eq_image (θ : ℝ) (hθ : 0 ≤ θ) :
    OmegaTheta θ = (fun w : ℂ => w ^ 2 - (1/4:ℂ)) '' Wset θ := by
  ext s
  constructor
  · rintro ⟨hsΩ, hsθ⟩
    have hsq : (Complex.sqrt (s + (1/4:ℂ))) ^ 2 = s + (1/4:ℂ) := by
      unfold Complex.sqrt
      exact Complex.cpow_nat_inv_pow _ (by norm_num)
    refine ⟨Complex.sqrt (s + (1/4:ℂ)), ⟨hsθ, ?_⟩, ?_⟩
    · rw [hsq, add_sub_cancel_right]; exact hsΩ
    · show (Complex.sqrt (s + (1/4:ℂ))) ^ 2 - (1/4:ℂ) = s
      rw [hsq]; ring
  · rintro ⟨w, ⟨hwθ, hwΩ⟩, rfl⟩
    show w ^ 2 - (1/4:ℂ) ∈ OmegaTheta θ
    refine ⟨hwΩ, ?_⟩
    have hw0 : 0 < w.re := by linarith
    have hsq : Complex.sqrt (w ^ 2 - (1/4:ℂ) + (1/4:ℂ)) = w := by
      rw [sub_add_cancel]
      unfold Complex.sqrt
      exact Complex.sq_cpow_two_inv hw0
    rw [hsq]
    exact hwθ

/-- **QR-2**: `Ω_θ` is preconnected for `θ ≥ 0`. -/
theorem isPreconnected_OmegaTheta (θ : ℝ) (hθ : 0 ≤ θ) : IsPreconnected (OmegaTheta θ) := by
  rw [OmegaTheta_eq_image θ hθ]
  exact (isPreconnected_Wset θ hθ).image _
    (by fun_prop : Continuous fun w : ℂ => w ^ 2 - (1/4:ℂ)).continuousOn

#print axioms starConvex_Wset
#print axioms OmegaTheta_eq_image
#print axioms isPreconnected_OmegaTheta

end

end RHFormalization
