import ThetaTrial.GammaEnergy.Multiplier

/-! The convergent horizontal digamma difference used in the Cauchy mean. -/

open Set MeasureTheory

namespace ThetaTrial.RationalFourier
open ThetaTrial.GammaEnergy

noncomputable def horizontalKernel (H h : ℝ) : ℝ :=
  shiftKernel h * (1 - Real.exp (-H * h))

theorem differenceKernel_horizontal_rescale (H h : ℝ) :
    (differenceKernel (((1 / 4 + H / 2 : ℝ) : ℂ)) (1 / 4) (2 * h)).re =
      horizontalKernel H h := by
  unfold differenceKernel horizontalKernel shiftKernel
  have he1 : -(1 / 4 : ℂ) * ((2 * h : ℝ) : ℂ) = ((-h / 2 : ℝ) : ℂ) := by
    push_cast; ring
  have he2 : -(((1 / 4 + H / 2 : ℝ) : ℂ)) * ((2 * h : ℝ) : ℂ) =
      ((-h / 2 + (-H * h) : ℝ) : ℂ) := by push_cast; ring
  rw [he1, he2]
  simp only [← Complex.ofReal_exp, ← Complex.ofReal_neg, ← Complex.ofReal_sub,
    ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [Real.exp_add]
  ring_nf

theorem horizontalKernel_integrable {H : ℝ} (hH : 0 < H) :
    IntegrableOn (horizontalKernel H) (Ioi 0) := by
  have hz : 0 < (((1 / 4 + H / 2 : ℝ) : ℂ)).re := by simp only [Complex.ofReal_re]; positivity
  have hw : 0 < (1 / 4 : ℂ).re := by norm_num
  have hi : IntegrableOn (fun t => (differenceKernel (((1 / 4 + H / 2 : ℝ) : ℂ)) (1 / 4) t).re)
      (Ioi 0) := (differenceKernel_integrable hz hw).re
  have hs := (integrableOn_Ioi_comp_mul_left_iff
    (fun t => (differenceKernel (((1 / 4 + H / 2 : ℝ) : ℂ)) (1 / 4) t).re)
    0 (by norm_num : (0 : ℝ) < 2)).mpr (by simpa only [mul_zero] using hi)
  simpa only [differenceKernel_horizontal_rescale] using hs

end ThetaTrial.RationalFourier
