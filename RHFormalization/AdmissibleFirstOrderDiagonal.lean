import RHFormalization.AdmissiblePrimeFirstOrderSplit

/-!
# RHFormalization.AdmissibleFirstOrderDiagonal

**Front F-adm, brick 4a.** Exact diagonal evaluation of the first-order term:

  `FirstOrderWindow n s = −admDensityC·Σₘ Vₘₘ·((s+SupV)+μₘ)⁻²`

via `R_D = toEuclideanLin (diagonal (w+μ)⁻¹)` and matrix-level trace algebra.
This is the concrete windowed prime object for the B_stage/WindowError
comparison (deferred) and for the residual bounds.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Module

variable {N : ℕ}

/-- `toEuclideanLin` of a diagonal matrix acts diagonally on the std basis. -/
theorem toEuclideanLin_diag_apply_stdBasis (d : Fin N → ℂ) (i : Fin N) :
    Matrix.toEuclideanLin (Matrix.diagonal d) (stdBasisE N i)
      = d i • stdBasisE N i := by
  unfold stdBasisE
  apply (EuclideanSpace.basisFun (Fin N) ℂ).toBasis.repr.injective
  ext j
  first
    | ((simp [Matrix.toEuclideanLin, Matrix.mulVec_diagonal,
          EuclideanSpace.basisFun, Pi.single_apply, mul_comm, mul_ite]
        by_cases h : j = i <;>
          simp_all [Pi.single_apply, EuclideanSpace.single_apply]); done)
    | ((simp [Matrix.toEuclideanLin, Matrix.mulVec_diagonal,
          Pi.single_apply, mul_comm]
        by_cases h : j = i <;> simp_all [EuclideanSpace.single_apply]); done)
    | ((simp [Matrix.toEuclideanLin_eq_toLin, Matrix.toLin'_apply,
          Matrix.mulVec_diagonal, Pi.single_apply, mul_comm]
        by_cases h : j = i <;> simp_all [EuclideanSpace.single_apply]); done)
    | (by_cases h : j = i <;>
        simp_all [Matrix.toEuclideanLin, Matrix.mulVec_diagonal,
          EuclideanSpace.basisFun, EuclideanSpace.single_apply,
          Pi.single_apply, mul_comm, mul_ite])

/-- **The free resolvent IS a diagonal matrix operator.** -/
theorem freeResolventOpE_eq_diag (μ : Fin N → ℝ) (s : ℂ) :
    freeResolventOpE μ s
      = Matrix.toEuclideanLin
          (Matrix.diagonal (fun i => (s + ((μ i : ℝ) : ℂ))⁻¹)) := by
  apply (stdBasisE N).ext
  intro i
  have h1 : freeResolventOpE μ s (stdBasisE N i)
      = (s + ((μ i : ℝ) : ℂ))⁻¹ • stdBasisE N i := by
    unfold freeResolventOpE
    exact Basis.constr_basis _ _ _ _
  rw [h1, toEuclideanLin_diag_apply_stdBasis]

/-- `toEuclideanLin` is multiplicative (matrix mul ↦ End mul). -/
theorem toEuclideanLin_mul_eq (A B : Matrix (Fin N) (Fin N) ℂ) :
    Matrix.toEuclideanLin (A * B)
      = Matrix.toEuclideanLin A * Matrix.toEuclideanLin B := by
  first
    | (simp only [Matrix.toEuclideanLin_eq_toLin]
       rw [Matrix.toLin_mul (PiLp.basisFun 2 ℂ (Fin N))
         (PiLp.basisFun 2 ℂ (Fin N)) (PiLp.basisFun 2 ℂ (Fin N))]
       rfl)
    | (simp [Matrix.toEuclideanLin_eq_toLin, Matrix.toLin_mul,
        LinearMap.mul_eq_comp])
    | exact map_mul _ A B

/-- Operator trace of a matrix operator = matrix trace (PerturbedEigenvalueSum
idiom). -/
theorem trace_toEuclideanLin (M : Matrix (Fin N) (Fin N) ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N)) (Matrix.toEuclideanLin M)
      = M.trace := by
  rw [Matrix.toEuclideanLin_eq_toLin]
  exact Matrix.trace_toLin_eq M (PiLp.basisFun 2 ℂ (Fin N))

/-- Trace of a diagonal conjugation: `Tr(D V D) = Σₘ Vₘₘ dₘ²`. -/
theorem diag_conj_trace (d : Fin N → ℂ) (V : Matrix (Fin N) (Fin N) ℂ) :
    (Matrix.diagonal d * V * Matrix.diagonal d).trace
      = ∑ m, V m m * (d m) ^ 2 := by
  have h : ∀ m, (Matrix.diagonal d * V * Matrix.diagonal d) m m
      = V m m * (d m) ^ 2 := by
    intro m
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    ring
  first
    | (unfold Matrix.trace Matrix.diag
       exact Finset.sum_congr rfl fun m _ => h m)
    | (rw [Matrix.trace]
       exact Finset.sum_congr rfl fun m _ => h m)
    | simp [Matrix.trace, Matrix.diag, h]

/-- Generic trace form: `Tr(R_D · V_op · R_D) = Σₘ Vₘₘ (s+μₘ)⁻²`. -/
theorem trace_RD_V_RD (μ : Fin N → ℝ) (V : Matrix (Fin N) (Fin N) ℂ) (s : ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
        (freeResolventOpE μ s * Matrix.toEuclideanLin V
          * freeResolventOpE μ s)
      = ∑ m, V m m * ((s + ((μ m : ℝ) : ℂ))⁻¹) ^ 2 := by
  rw [freeResolventOpE_eq_diag, ← toEuclideanLin_mul_eq, ← toEuclideanLin_mul_eq,
    trace_toEuclideanLin, diag_conj_trace]

/-- **BRICK 4a: exact diagonal form of the first-order window term.** -/
theorem FirstOrderWindow_eq_diag_sum (n : ℕ) (s : ℂ) :
    FirstOrderWindow n s
      = -(admDensityC n *
          ∑ m : Fin (admN n),
            (galerkinVC (N := admN n) 1
                (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
                (admL n)) m m
              * (((s + (SupVConst : ℂ))
                  + ((galerkinFreeMu (admN n) (admL n) m : ℝ) : ℂ))⁻¹) ^ 2) := by
  unfold FirstOrderWindow
  rw [trace_RD_V_RD]

#print axioms freeResolventOpE_eq_diag
#print axioms toEuclideanLin_mul_eq
#print axioms trace_toEuclideanLin
#print axioms diag_conj_trace
#print axioms trace_RD_V_RD
#print axioms FirstOrderWindow_eq_diag_sum

end

end RHFormalization
