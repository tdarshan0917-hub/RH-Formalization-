import RHFormalization.DNativeUnboundedOperator

namespace RHFormalization
noncomputable section

-- full-domain zero operator as a LinearPMap
noncomputable def zeroFull : ℂ →ₗ.[ℂ] ℂ :=
  (0 : ℂ →L[ℂ] ℂ).toPMap ⊤

#check zeroFull

example : IsSelfAdjoint zeroFull := by
  rw [isSelfAdjoint_def]
  sorry

example : LinearPMapLowerSemibounded zeroFull := by
  sorry

example : LinearPMapNonnegative zeroFull := by
  sorry

end
end RHFormalization
