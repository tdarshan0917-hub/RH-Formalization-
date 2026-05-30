import Mathlib
import RHFormalization.OmegaTopology
import RHFormalization.GlobalMeromorphicIdentity

/-!
# RHFormalization.OmegaConnected

Theorem-backed connectedness/preconnectedness of the manuscript slit plane `Ω`.

We prove `IsPreconnected Ω` by decomposing Ω into three convex pieces:

* right half-plane: `0 < re z`;
* upper half-plane: `0 < im z`;
* lower half-plane: `im z < 0`.

Then we use `IsPreconnected.union` twice with explicit intersection points.
-/

namespace RHFormalization

noncomputable section

open Complex Topology

def RePosOmega : Set ℂ :=
  {z : ℂ | 0 < z.re}

def ImPosOmega : Set ℂ :=
  {z : ℂ | 0 < z.im}

def ImNegOmega : Set ℂ :=
  {z : ℂ | z.im < 0}

/-- The open right half-plane is convex. -/
theorem convex_re_pos_omega :
    Convex ℝ RePosOmega := by
  intro x hx y hy a b ha hb hab
  dsimp [RePosOmega] at hx hy ⊢
  have hmin : 0 < min x.re y.re := lt_min hx hy
  have hxmin : min x.re y.re ≤ x.re := min_le_left _ _
  have hymin : min x.re y.re ≤ y.re := min_le_right _ _
  have hax : a * min x.re y.re ≤ a * x.re := by
    exact mul_le_mul_of_nonneg_left hxmin ha
  have hby : b * min x.re y.re ≤ b * y.re := by
    exact mul_le_mul_of_nonneg_left hymin hb
  have hle :
      (a + b) * min x.re y.re ≤ a * x.re + b * y.re := by
    nlinarith [hax, hby]
  have hle' :
      min x.re y.re ≤ a * x.re + b * y.re := by
    simpa [hab] using hle
  have htarget : 0 < a * x.re + b * y.re :=
    lt_of_lt_of_le hmin hle'
  simpa [Complex.add_re, Complex.smul_re] using htarget

/-- The open upper half-plane is convex. -/
theorem convex_im_pos_omega :
    Convex ℝ ImPosOmega := by
  intro x hx y hy a b ha hb hab
  dsimp [ImPosOmega] at hx hy ⊢
  have hmin : 0 < min x.im y.im := lt_min hx hy
  have hxmin : min x.im y.im ≤ x.im := min_le_left _ _
  have hymin : min x.im y.im ≤ y.im := min_le_right _ _
  have hax : a * min x.im y.im ≤ a * x.im := by
    exact mul_le_mul_of_nonneg_left hxmin ha
  have hby : b * min x.im y.im ≤ b * y.im := by
    exact mul_le_mul_of_nonneg_left hymin hb
  have hle :
      (a + b) * min x.im y.im ≤ a * x.im + b * y.im := by
    nlinarith [hax, hby]
  have hle' :
      min x.im y.im ≤ a * x.im + b * y.im := by
    simpa [hab] using hle
  have htarget : 0 < a * x.im + b * y.im :=
    lt_of_lt_of_le hmin hle'
  simpa [Complex.add_im, Complex.smul_im] using htarget

/-- The open lower half-plane is convex. -/
theorem convex_im_neg_omega :
    Convex ℝ ImNegOmega := by
  intro x hx y hy a b ha hb hab
  dsimp [ImNegOmega] at hx hy ⊢
  have hmax : max x.im y.im < 0 := max_lt hx hy
  have hxmax : x.im ≤ max x.im y.im := le_max_left _ _
  have hymax : y.im ≤ max x.im y.im := le_max_right _ _
  have hax : a * x.im ≤ a * max x.im y.im := by
    exact mul_le_mul_of_nonneg_left hxmax ha
  have hby : b * y.im ≤ b * max x.im y.im := by
    exact mul_le_mul_of_nonneg_left hymax hb
  have hle :
      a * x.im + b * y.im ≤ (a + b) * max x.im y.im := by
    nlinarith [hax, hby]
  have hle' :
      a * x.im + b * y.im ≤ max x.im y.im := by
    simpa [hab] using hle
  have htarget : a * x.im + b * y.im < 0 :=
    lt_of_le_of_lt hle' hmax
  simpa [Complex.add_im, Complex.smul_im] using htarget

theorem isPreconnected_re_pos_omega :
    IsPreconnected RePosOmega :=
  convex_re_pos_omega.isPreconnected

theorem isPreconnected_im_pos_omega :
    IsPreconnected ImPosOmega :=
  convex_im_pos_omega.isPreconnected

theorem isPreconnected_im_neg_omega :
    IsPreconnected ImNegOmega :=
  convex_im_neg_omega.isPreconnected

/--
The manuscript slit plane decomposes into three half-planes.
-/
theorem Omega_eq_three_halfplanes :
    Ω = (RePosOmega ∪ ImPosOmega) ∪ ImNegOmega := by
  rw [Omega_eq_re_pos_union_im_ne_zero]
  ext z
  constructor
  · intro hz
    rcases hz with hzre | hzim
    · exact Or.inl (Or.inl (by
        simpa [RePosOmega] using hzre))
    · by_cases hpos : 0 < z.im
      · exact Or.inl (Or.inr (by
          simpa [ImPosOmega] using hpos))
      · have hle : z.im ≤ 0 := le_of_not_gt hpos
        have hlt : z.im < 0 := lt_of_le_of_ne hle hzim
        exact Or.inr (by
          simpa [ImNegOmega] using hlt)
  · intro hz
    rcases hz with h12 | hneg
    · rcases h12 with hre | hpos
      · left
        simpa [RePosOmega] using hre
      · right
        have hpos' : 0 < z.im := by
          simpa [ImPosOmega] using hpos
        exact ne_of_gt hpos'
    · right
      have hneg' : z.im < 0 := by
        simpa [ImNegOmega] using hneg
      exact ne_of_lt hneg'

/--
The union of the right and upper half-planes is preconnected.
The intersection point is `1 + i`.
-/
theorem isPreconnected_re_pos_union_im_pos :
    IsPreconnected (RePosOmega ∪ ImPosOmega) := by
  refine
    @IsPreconnected.union
      ℂ _
      (⟨(1 : ℝ), (1 : ℝ)⟩ : ℂ)
      RePosOmega
      ImPosOmega
      ?_
      ?_
      isPreconnected_re_pos_omega
      isPreconnected_im_pos_omega
  · norm_num [RePosOmega]
  · norm_num [ImPosOmega]

/--
The three-piece half-plane decomposition is preconnected.
The second intersection point is `1 - i`.
-/
theorem isPreconnected_three_halfplanes :
    IsPreconnected ((RePosOmega ∪ ImPosOmega) ∪ ImNegOmega) := by
  refine
    @IsPreconnected.union
      ℂ _
      (⟨(1 : ℝ), (-1 : ℝ)⟩ : ℂ)
      (RePosOmega ∪ ImPosOmega)
      ImNegOmega
      ?_
      ?_
      isPreconnected_re_pos_union_im_pos
      isPreconnected_im_neg_omega
  · left
    norm_num [RePosOmega]
  · norm_num [ImNegOmega]

/--
Native theorem-backed preconnectedness of the manuscript slit plane `Ω`.
-/
theorem isPreconnected_Omega_native :
    IsPreconnected Ω := by
  rw [Omega_eq_three_halfplanes]
  exact isPreconnected_three_halfplanes

/--
Default theorem-backed connectedness/preconnectedness API for `Ω`.
-/
def defaultConnectedOmegaAPI : ConnectedOmegaAPI :=
  { h_preconnected_Omega := isPreconnected_Omega_native }

end

end RHFormalization
