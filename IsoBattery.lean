import RHFormalization.ReflectionPairPoleClass
open Complex RHFormalization
#check @Complex.abs_re_le_abs
#check @Complex.abs_re_le_norm
#check @Complex.mul_re
#check @Complex.mul_im
#check @isCompact_Icc
#check @IsCompact.prod
example : Continuous polePoint := by
  unfold polePoint
  fun_prop
