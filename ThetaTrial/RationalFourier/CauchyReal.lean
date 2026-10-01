import ThetaTrial.RationalFourier.Cauchy

/-! Real and cosine versions of the Cauchy integral. -/

open Set MeasureTheory

namespace ThetaTrial.RationalFourier

theorem cauchy_phase_re (H h x : ℝ) :
    (Complex.exp (Complex.I * (h : ℂ) * (x : ℂ)) /
      ((H : ℂ) ^ 2 + (x : ℂ) ^ 2)).re = Real.cos (h * x) / (H ^ 2 + x ^ 2) := by
  rw [show (H : ℂ) ^ 2 + (x : ℂ) ^ 2 = ((H ^ 2 + x ^ 2 : ℝ) : ℂ) by push_cast; rfl,
    Complex.div_ofReal_re, Complex.exp_re]
  simp

theorem cauchy_cosine_integrable {H : ℝ} (hH : 0 < H) (h : ℝ) :
    Integrable (fun x : ℝ => Real.cos (h * x) / (H ^ 2 + x ^ 2)) := by
  have hi : Integrable (fun x : ℝ =>
      (Complex.exp (Complex.I * (h : ℂ) * (x : ℂ)) /
        ((H : ℂ) ^ 2 + (x : ℂ) ^ 2)).re) := (cauchy_phase_integrable hH h).re
  simpa only [cauchy_phase_re] using hi

theorem integral_cauchy_cosine {H : ℝ} (hH : 0 < H) (h : ℝ) :
    (∫ x : ℝ, Real.cos (h * x) / (H ^ 2 + x ^ 2)) =
      Real.pi / H * Real.exp (-H * |h|) := by
  have he := congrArg Complex.re (integral_cauchy_phase hH h)
  have hr := Complex.reCLM.integral_comp_comm (cauchy_phase_integrable hH h)
  simp only [Complex.reCLM_apply] at hr
  rw [← hr] at he
  simpa only [cauchy_phase_re, Complex.mul_re, Complex.div_ofReal_re,
    Complex.ofReal_re, Complex.div_ofReal_im, Complex.ofReal_im, zero_div,
    mul_zero, sub_zero] using he

theorem integral_cauchy {H : ℝ} (hH : 0 < H) :
    (∫ x : ℝ, 1 / (H ^ 2 + x ^ 2)) = Real.pi / H := by
  simpa using integral_cauchy_cosine hH 0

theorem cauchy_one_sub_cosine_integrable {H : ℝ} (hH : 0 < H) (h : ℝ) :
    Integrable (fun x : ℝ => (1 - Real.cos (h * x)) / (H ^ 2 + x ^ 2)) := by
  apply ((cauchy_integrable hH).sub (cauchy_cosine_integrable hH h)).congr
  filter_upwards [] with x
  dsimp
  ring

theorem integral_cauchy_one_sub_cosine {H : ℝ} (hH : 0 < H) {h : ℝ} (hh : 0 ≤ h) :
    (∫ x : ℝ, (1 - Real.cos (h * x)) / (H ^ 2 + x ^ 2)) =
      Real.pi / H * (1 - Real.exp (-H * h)) := by
  simp_rw [sub_div]
  rw [integral_sub (cauchy_integrable hH) (cauchy_cosine_integrable hH h),
    integral_cauchy hH, integral_cauchy_cosine hH, abs_of_nonneg hh]
  ring

end ThetaTrial.RationalFourier
