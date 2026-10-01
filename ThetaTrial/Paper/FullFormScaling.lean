import ThetaTrial.Paper.TrialFourier

/-! Exact scalar homogeneity of the Weil form. -/
noncomputable section
open Complex MeasureTheory
open scoped ComplexConjugate

namespace ThetaTrial.Paper

theorem correlation_const_mul (c : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    correlation (fun u => c * f u) x = (Complex.normSq c : ℂ) * correlation f x := by
  unfold correlation
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  simp only [map_mul]
  rw [← Complex.mul_conj c]
  ring

theorem fullWeilForm_const_mul (c : ℂ) (f : ℝ → ℂ) :
    fullWeilForm (fun u => c * f u) = Complex.normSq c * fullWeilForm f := by
  have hp : (paperFourier (fun u => c * f u) (I / 2) *
      conj (paperFourier (fun u => c * f u) (-I / 2))).re =
      Complex.normSq c * (paperFourier f (I / 2) * conj (paperFourier f (-I / 2))).re := by
    simp only [paperFourier_const_mul, map_mul]
    have he : (c * paperFourier f (I / 2)) * (conj c * conj (paperFourier f (-I / 2))) =
        (Complex.normSq c : ℂ) * (paperFourier f (I / 2) * conj (paperFourier f (-I / 2))) := by
      rw [← Complex.mul_conj c]
      ring
    rw [he]
    simp
  have hg : (fun r : ℝ => gammaWeight r *
      Complex.normSq (paperFourier (fun u => c * f u) r)) =
      fun r : ℝ => Complex.normSq c * (gammaWeight r * Complex.normSq (paperFourier f r)) := by
    funext r
    rw [paperFourier_const_mul, Complex.normSq_mul]
    ring
  have hprime : (fun n : ℕ => (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
      (correlation (fun u => c * f u) (Real.log n)).re) =
      fun n : ℕ => Complex.normSq c * ((ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        (correlation f (Real.log n)).re) := by
    funext n
    rw [correlation_const_mul]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  unfold fullWeilForm
  rw [hp, hg, hprime, integral_const_mul, tsum_mul_left]
  ring

end ThetaTrial.Paper

#print axioms ThetaTrial.Paper.fullWeilForm_const_mul
