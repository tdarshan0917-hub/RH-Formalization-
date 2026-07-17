/-
GalerkinDimMonotone.lean

DIMENSION MONOTONICITY AT FIXED POTENTIAL: the galerkin matrices are
principal minors of one infinite matrix (VmatrixElement and galerkinFreeMu
are N-independent), so zero-padding is an isometric compression and the
banked interlacing engine applies: each k-th SMALLEST eigenvalue moves
monotonically DOWN as the Galerkin dimension grows, at every fixed code
set. With the banked pi^2-SupVConst floor this gives per-index limits --
the N-limit half of Front F.
-/
import RHFormalization.EmbeddedInterlacing
import RHFormalization.GalerkinSpectrumGrowth

namespace RHFormalization

noncomputable section

open Complex

/-- Transport a sum over `Fin m` to a sum over `Fin n` along `Fin.castLE`
when the summand vanishes above `n`. -/
theorem sum_fin_castLE_of_vanish {M : Type*} [AddCommMonoid M] {n m : ℕ}
    (h : n ≤ m) (f : Fin m → M)
    (hf : ∀ j : Fin m, ¬ ((j : ℕ) < n) → f j = 0) :
    (∑ j : Fin m, f j) = ∑ i : Fin n, f (Fin.castLE h i) := by
  classical
  have hinj : ∀ x ∈ (Finset.univ : Finset (Fin n)), ∀ y ∈ Finset.univ,
      Fin.castLE h x = Fin.castLE h y → x = y := by
    intro x _ y _ hxy
    apply Fin.ext
    have hv := congrArg Fin.val hxy
    first
      | simpa [Fin.val_castLE] using hv
      | simpa using hv
  have himg : ∑ j ∈ Finset.univ.image (Fin.castLE h), f j
      = ∑ i : Fin n, f (Fin.castLE h i) := Finset.sum_image hinj
  rw [← himg]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro j _ hj
  apply hf
  intro hjn
  apply hj
  rw [Finset.mem_image]
  refine ⟨⟨(j : ℕ), hjn⟩, Finset.mem_univ _, ?_⟩
  first
    | rfl
    | exact Fin.ext (by simp [Fin.val_castLE])
    | (apply Fin.ext; simp [Fin.val_castLE])

variable {n m : ℕ}

/-- The padding function at the coordinate level. -/
def padFun (h : n ≤ m) (x : EuclideanSpace ℂ (Fin n)) : Fin m → ℂ :=
  fun j => if hj : (j : ℕ) < n then x ⟨(j : ℕ), hj⟩ else 0

/-- Zero-padding as a linear map between Euclidean spaces. -/
def padMap (h : n ≤ m) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) where
  toFun x := (WithLp.equiv 2 (Fin m → ℂ)).symm (padFun h x)
  map_add' x y := by
    apply (WithLp.equiv 2 (Fin m → ℂ)).injective
    funext j
    show padFun h (x + y) j = _
    by_cases hj : (j : ℕ) < n
    · first
        | simp [padFun, hj, PiLp.add_apply]
        | simp [padFun, hj]
    · first
        | simp [padFun, hj, PiLp.add_apply]
        | simp [padFun, hj]
  map_smul' c x := by
    apply (WithLp.equiv 2 (Fin m → ℂ)).injective
    funext j
    show padFun h (c • x) j = _
    by_cases hj : (j : ℕ) < n
    · first
        | simp [padFun, hj, PiLp.smul_apply, RingHom.id_apply]
        | simp [padFun, hj]
    · first
        | simp [padFun, hj, PiLp.smul_apply, RingHom.id_apply]
        | simp [padFun, hj]

theorem padMap_apply (h : n ≤ m) (x : EuclideanSpace ℂ (Fin n)) (j : Fin m) :
    padMap h x j = if hj : (j : ℕ) < n then x ⟨(j : ℕ), hj⟩ else 0 := by
  show padFun h x j = _
  rfl

theorem padMap_apply_castLE (h : n ≤ m) (x : EuclideanSpace ℂ (Fin n))
    (i : Fin n) :
    padMap h x (Fin.castLE h i) = x i := by
  rw [padMap_apply]
  have hi : ((Fin.castLE h i : Fin m) : ℕ) < n := by
    first
      | (rw [Fin.val_castLE]; exact i.2)
      | simpa [Fin.val_castLE] using i.2
      | exact i.2
  rw [dif_pos hi]
  have hidx : (⟨((Fin.castLE h i : Fin m) : ℕ), hi⟩ : Fin n) = i := by
    apply Fin.eq_of_val_eq
    first
      | simp [Fin.val_castLE]
      | rfl
  rw [hidx]

theorem padMap_apply_not_lt (h : n ≤ m) (x : EuclideanSpace ℂ (Fin n))
    {j : Fin m} (hj : ¬ ((j : ℕ) < n)) :
    padMap h x j = 0 := by
  rw [padMap_apply, dif_neg hj]

/-- Zero-padding preserves inner products. -/
theorem inner_padMap_padMap (h : n ≤ m) (x y : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (padMap h x) (padMap h y) = inner ℂ x y := by
  have hvan : ∀ j : Fin m, ¬ ((j : ℕ) < n) →
      inner ℂ (padMap h x j) (padMap h y j) = 0 := by
    intro j hj
    rw [padMap_apply_not_lt h x hj]
    first
      | exact inner_zero_left _
      | simp
  rw [PiLp.inner_apply, PiLp.inner_apply,
    sum_fin_castLE_of_vanish h
      (fun j => inner ℂ (padMap h x j) (padMap h y j)) hvan]
  apply Finset.sum_congr rfl
  intro i _
  rw [padMap_apply_castLE, padMap_apply_castLE]

/-- **Principal-minor compression identity.** If the small matrix is the
leading principal minor of the big one, the big quadratic form through the
zero-padding equals the small quadratic form. -/
theorem inner_padMap_toEuclideanLin (h : n ≤ m)
    (Am : Matrix (Fin m) (Fin m) ℂ) (An : Matrix (Fin n) (Fin n) ℂ)
    (hminor : ∀ i j : Fin n, Am (Fin.castLE h i) (Fin.castLE h j) = An i j)
    (x : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (padMap h x) (Matrix.toEuclideanLin Am (padMap h x))
      = inner ℂ x (Matrix.toEuclideanLin An x) := by
  have happm : ∀ j : Fin m,
      (Matrix.toEuclideanLin Am (padMap h x)) j
        = ∑ k : Fin m, Am j k * (padMap h x) k := by
    intro j
    show (Matrix.mulVec Am ((padMap h x) : Fin m → ℂ)) j
        = ∑ k : Fin m, Am j k * (padMap h x) k
    first
      | simp [Matrix.mulVec, dotProduct]
      | rfl
  have happn : ∀ i : Fin n,
      (Matrix.toEuclideanLin An x) i = ∑ k : Fin n, An i k * x k := by
    intro i
    show (Matrix.mulVec An (x : Fin n → ℂ)) i = ∑ k : Fin n, An i k * x k
    first
      | simp [Matrix.mulVec, dotProduct]
      | rfl
  have hvan : ∀ j : Fin m, ¬ ((j : ℕ) < n) →
      inner ℂ (padMap h x j)
        ((Matrix.toEuclideanLin Am (padMap h x)) j) = 0 := by
    intro j hj
    rw [padMap_apply_not_lt h x hj]
    first
      | exact inner_zero_left _
      | simp
  rw [PiLp.inner_apply, PiLp.inner_apply,
    sum_fin_castLE_of_vanish h
      (fun j => inner ℂ (padMap h x j)
        ((Matrix.toEuclideanLin Am (padMap h x)) j)) hvan]
  apply Finset.sum_congr rfl
  intro i _
  rw [padMap_apply_castLE, happm, happn]
  have hsum : (∑ k : Fin m, Am (Fin.castLE h i) k * (padMap h x) k)
      = ∑ k : Fin n, An i k * x k := by
    have hvank : ∀ k : Fin m, ¬ ((k : ℕ) < n) →
        Am (Fin.castLE h i) k * (padMap h x) k = 0 := by
      intro k hk
      rw [padMap_apply_not_lt h x hk, mul_zero]
    rw [sum_fin_castLE_of_vanish h
      (fun k => Am (Fin.castLE h i) k * (padMap h x) k) hvank]
    apply Finset.sum_congr rfl
    intro k _
    rw [padMap_apply_castLE, hminor]
  rw [hsum]

/-- The galerkin perturbed matrix at dimension m has the dimension-n one
as its leading principal minor (the entries are N-independent). -/
theorem galerkinPerturbedMatrix_minor (qs : Finset ℕ) (h : n ≤ m)
    (i j : Fin n) :
    perturbedMatrix (galerkinFreeMu m 1)
        (galerkinVC (N := m) 1 qs ppWeightReal 1)
        (Fin.castLE h i) (Fin.castLE h j)
      = perturbedMatrix (galerkinFreeMu n 1)
          (galerkinVC (N := n) 1 qs ppWeightReal 1) i j := by
  have hV : galerkinVC (N := m) 1 qs ppWeightReal 1
        (Fin.castLE h i) (Fin.castLE h j)
      = galerkinVC (N := n) 1 qs ppWeightReal 1 i j := by
    first
      | rfl
      | (unfold galerkinVC; rw [galerkinV_apply, galerkinV_apply];
         simp [Fin.val_castLE])
      | (unfold galerkinVC galerkinV; simp [Fin.val_castLE])
  have hD : freeDiag (galerkinFreeMu m 1) (Fin.castLE h i) (Fin.castLE h j)
      = freeDiag (galerkinFreeMu n 1) i j := by
    unfold freeDiag
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
      first
        | rfl
        | (unfold galerkinFreeMu; norm_num [Fin.val_castLE])
        | (norm_cast; unfold galerkinFreeMu; simp [Fin.val_castLE])
    · have hcast : Fin.castLE h i ≠ Fin.castLE h j := by
        intro hcc
        apply hij
        apply Fin.ext
        have hv := congrArg Fin.val hcc
        first
          | simpa [Fin.val_castLE] using hv
          | simpa using hv
      rw [Matrix.diagonal_apply_ne _ hcast, Matrix.diagonal_apply_ne _ hij]
  show (freeDiag (galerkinFreeMu m 1)
        + galerkinVC (N := m) 1 qs ppWeightReal 1)
        (Fin.castLE h i) (Fin.castLE h j)
      = (freeDiag (galerkinFreeMu n 1)
          + galerkinVC (N := n) 1 qs ppWeightReal 1) i j
  rw [Matrix.add_apply, Matrix.add_apply, hV, hD]

/-- **DIMENSION MONOTONICITY.** At fixed code set, the k-th smallest
genuine galerkin eigenvalue moves DOWN as the dimension grows
(smallest = Fin.rev in the sorted-decreasing enumeration). -/
theorem galerkinEigenvalues_dim_mono (qs : Finset ℕ) (h : n ≤ m) (k : Fin n) :
    perturbedEigenvalues (galerkinFreeMu m 1)
        (galerkinVC_isHermitian (N := m) 1 qs ppWeightReal 1)
        (Fin.rev (Fin.castLE h k))
      ≤ perturbedEigenvalues (galerkinFreeMu n 1)
          (galerkinVC_isHermitian (N := n) 1 qs ppWeightReal 1)
          (Fin.rev k) := by
  have hJform : ∀ x : EuclideanSpace ℂ (Fin n),
      RCLike.re (inner ℂ (padMap h x)
        (perturbedOp (galerkinFreeMu m 1)
          (galerkinVC (N := m) 1 qs ppWeightReal 1) (padMap h x)))
        = RCLike.re (inner ℂ x
            (perturbedOp (galerkinFreeMu n 1)
              (galerkinVC (N := n) 1 qs ppWeightReal 1) x)) := by
    intro x
    have hc := inner_padMap_toEuclideanLin h
      (perturbedMatrix (galerkinFreeMu m 1)
        (galerkinVC (N := m) 1 qs ppWeightReal 1))
      (perturbedMatrix (galerkinFreeMu n 1)
        (galerkinVC (N := n) 1 qs ppWeightReal 1))
      (galerkinPerturbedMatrix_minor qs h) x
    first
      | (unfold perturbedOp; rw [hc])
      | rw [show perturbedOp (galerkinFreeMu m 1)
              (galerkinVC (N := m) 1 qs ppWeightReal 1) (padMap h x)
            = Matrix.toEuclideanLin (perturbedMatrix (galerkinFreeMu m 1)
                (galerkinVC (N := m) 1 qs ppWeightReal 1)) (padMap h x)
            from rfl,
          show perturbedOp (galerkinFreeMu n 1)
              (galerkinVC (N := n) 1 qs ppWeightReal 1) x
            = Matrix.toEuclideanLin (perturbedMatrix (galerkinFreeMu n 1)
                (galerkinVC (N := n) 1 qs ppWeightReal 1)) x
            from rfl,
          hc]
  exact eigenvalues_rev_le_of_isometric_compression
    (perturbedOp_isSymmetric (galerkinFreeMu m 1)
      (galerkinVC_isHermitian (N := m) 1 qs ppWeightReal 1))
    (perturbedOp_isSymmetric (galerkinFreeMu n 1)
      (galerkinVC_isHermitian (N := n) 1 qs ppWeightReal 1))
    perturbedOp_finrank perturbedOp_finrank
    (padMap h) (inner_padMap_padMap h) hJform h k

#print axioms sum_fin_castLE_of_vanish
#print axioms padMap
#print axioms inner_padMap_padMap
#print axioms inner_padMap_toEuclideanLin
#print axioms galerkinPerturbedMatrix_minor
#print axioms galerkinEigenvalues_dim_mono

end

end RHFormalization
