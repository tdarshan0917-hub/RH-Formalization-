import RHFormalization.CurrentFrontierEndpoint

namespace RHFormalization
noncomputable section

open Complex Set Topology Filter
open scoped BigOperators

-- Target shape we want to prove eventually:
example
    (h :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0) :
    True := by
  trivial

-- Existing zeta nonvanishing lemmas we have seen or may need:
#check riemannZeta_ne_zero_of_one_lt_re
#check riemannZeta_ne_zero_of_one_le_re
#check riemannZeta_one_sub

-- Possible real-line / interval names:
#check riemannZeta_ne_zero_of_real
#check riemannZeta_ne_zero_of_mem_Ioo
#check riemannZeta_ne_zero_of_Ioo
#check riemannZeta_neg_of_mem_Ioo
#check riemannZeta_lt_zero_of_mem_Ioo
#check riemannZeta_real_neg_of_mem_Ioo

-- Eta / alternating zeta possibilities:
#check dirichletEta
#check DirichletEta
#check riemannZeta_eq_dirichletEta
#check dirichletEta_ne_zero
#check dirichletEta_pos
#check dirichletEta_lt_zero

-- Existing project reduction, if present:
#check defaultZetaZeroFacts_of_realZeroFree

end
end RHFormalization
