import ThetaTrial.GammaEnergy.Multiplier

/-! The exact constant in the compensated physical gamma kernel. -/
noncomputable section
open Complex MeasureTheory Set

namespace ThetaTrial.Paper
open ThetaTrial.GammaEnergy

def gammaCompensationKernel (x : ℝ) : ℝ :=
  shiftKernel x * (1 - Real.exp (-x / 2))

theorem differenceKernel_half_quarter_rescale (x : ℝ) :
    differenceKernel (1 / 2) (1 / 4) (2 * x) =
      (gammaCompensationKernel x : ℂ) := by
  have h1 : -(1 / 4 : ℂ) * ((2 * x : ℝ) : ℂ) = ((-x / 2 : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : -(1 / 2 : ℂ) * ((2 * x : ℝ) : ℂ) = ((-x : ℝ) : ℂ) := by
    push_cast; ring
  have h3 : -((2 * x : ℝ) : ℂ) = ((-2 * x : ℝ) : ℂ) := by push_cast; ring
  unfold differenceKernel gammaCompensationKernel shiftKernel
  rw [h1, h2, h3]
  simp only [← Complex.ofReal_exp, ← Complex.ofReal_sub, ← Complex.ofReal_div]
  push_cast
  rw [show -(x : ℂ) = -(x : ℂ) / 2 + -(x : ℂ) / 2 by ring, Complex.exp_add]
  ring

theorem gammaCompensationKernel_integrable :
    IntegrableOn gammaCompensationKernel (Ioi 0) := by
  have hi := Complex.reCLM.integrable_comp (differenceKernel_integrable
    (z := (1 / 2 : ℂ)) (w := (1 / 4 : ℂ)) (by norm_num) (by norm_num))
  simp only [Complex.reCLM_apply] at hi
  have hs := (integrableOn_Ioi_comp_mul_left_iff
    (fun t : ℝ => (differenceKernel (1 / 2) (1 / 4) t).re) 0
    (by norm_num : (0 : ℝ) < 2)).mpr (by
      change Integrable _ (volume.restrict _)
      convert hi using 1 <;> simp only [mul_zero])
  simpa only [differenceKernel_half_quarter_rescale, Complex.ofReal_re] using hs

theorem gammaBase_compensation_constant :
    gammaBase + 2 * (∫ x : ℝ in Ioi 0, gammaCompensationKernel x) =
      -(Real.log (4 * Real.pi) + Real.eulerMascheroniConstant) := by
  have hd := congrArg Complex.re (digamma_sub_eq_integral
    (z := (1 / 2 : ℂ)) (w := (1 / 4 : ℂ)) (by norm_num) (by norm_num))
  have hr := Complex.reCLM.integral_comp_comm
    (differenceKernel_integrable
      (z := (1 / 2 : ℂ)) (w := (1 / 4 : ℂ)) (by norm_num) (by norm_num))
  simp only [Complex.reCLM_apply] at hr
  rw [Complex.sub_re, ← hr] at hd
  have hs := integral_comp_mul_left_Ioi'
    (fun t : ℝ => (differenceKernel (1 / 2) (1 / 4) t).re) 0
    (by norm_num : (0 : ℝ) < 2)
  simp only [mul_zero, smul_eq_mul, differenceKernel_half_quarter_rescale,
    Complex.ofReal_re] at hs
  have hh : (Complex.digamma (1 / 2)).re =
      -2 * Real.log 2 - Real.eulerMascheroniConstant := by
    rw [Complex.digamma_one_half]
    norm_num [Complex.mul_re, Complex.log_re]
  have hl : Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num) Real.pi_ne_zero]
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [h4]
  unfold gammaBase
  rw [hl]
  rw [hh] at hd
  linarith

end ThetaTrial.Paper
