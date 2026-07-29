import RHFormalization.PairPoleIsolation
open Complex RHFormalization
example (f : ℂ → ℕ → ℂ) (S : Finset ℕ) (U : Set ℂ)
    (h : ∀ i ∈ S, DifferentiableOn ℂ (fun z => f z i) U) :
    DifferentiableOn ℂ (fun z => Finset.sum S (fun i => f z i)) U := by
  first
    | exact DifferentiableOn.sum h
    | exact DifferentiableOn.fun_sum h
    | (classical
       induction S using Finset.induction_on with
       | empty => simpa using differentiableOn_const 0
       | insert a s ha ih =>
         simp only [Finset.sum_insert ha]
         exact (h a (Finset.mem_insert_self a s)).add
           (ih (fun i hi => h i (Finset.mem_insert_of_mem hi))))
