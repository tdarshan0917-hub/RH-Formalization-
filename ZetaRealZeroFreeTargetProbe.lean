import RHFormalization.DefaultZetaZeroFacts

namespace RHFormalization

noncomputable section

open Complex

#check riemannZeta
#check defaultZetaZeroFacts_of_realZeroFree

/--
This is the exact theorem needed to close `ZF : ZetaZeroFacts`.
Do not prove it here yet; this probe records the target shape.
-/
example :
    (∀ s : ℂ,
      s.im = 0 →
      0 < s.re →
      s.re < 1 →
      riemannZeta s ≠ 0) →
    ZetaZeroFacts := by
  intro h_real_zero_free
  exact defaultZetaZeroFacts_of_realZeroFree h_real_zero_free

#print axioms defaultZetaZeroFacts_of_realZeroFree

end

end RHFormalization
