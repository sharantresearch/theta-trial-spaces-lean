import ThetaTrial.FourierNormalization
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Function.L2Space

/-! # Parseval and translation for the unitary Fourier transform -/

open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace ThetaTrial.GammaEnergy

theorem norm_phase_sub_one_sq (r : ℝ) :
    ‖Complex.exp (Complex.I * (r : ℂ)) - 1‖ ^ 2 = 2 * (1 - Real.cos r) := by
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.exp_re,
    Complex.exp_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, one_mul, sub_zero,
    zero_add, Complex.one_re, Complex.one_im, Real.exp_zero]
  nlinarith [Real.sin_sq_add_cos_sq r]

end ThetaTrial.GammaEnergy
