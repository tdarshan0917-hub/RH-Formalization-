import RHFormalization.RemovableDiv

namespace RHFormalization

open Complex Filter Topology

theorem hasPrincipalPart_const_mul
    {f a : ℂ → ℂ} {z c : ℂ}
    (hf : HasPrincipalPartAtC f z c)
    (ha : AnalyticAt ℂ a z) :
    HasPrincipalPartAtC (fun w => a w * f w) z (a z * c) := by
  obtain ⟨h, hh_an, hh_eq⟩ := hf
  have hF_an : AnalyticAt ℂ (fun w => a w - a z) z := ha.sub analyticAt_const
  have hF0 : (fun w => a w - a z) z = 0 := by simp
  obtain ⟨G, hG_an, hG_eq⟩ := removable_div_exists hF_an hF0
  refine ⟨fun w => c * G w + a w * h w, ?_, ?_⟩
  · exact (analyticAt_const.mul hG_an).add (ha.mul hh_an)
  · filter_upwards [hh_eq, hG_eq] with w hhw hGw
    intro hwz
    have hsub_ne : (w - z) ≠ 0 := sub_ne_zero.mpr hwz
    have hGval : (a w - a z) / (w - z) = G w := hGw hwz
    have hGw' : G w = (a w - a z) / (w - z) := hGval.symm
    rw [hhw hwz, hGw']
    field_simp
    ring
end RHFormalization
