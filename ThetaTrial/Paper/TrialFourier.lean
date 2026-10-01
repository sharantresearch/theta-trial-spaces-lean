import ThetaTrial.Paper.BV
import ThetaTrial.Paper.ThetaModes
import ThetaTrial.Paper.ThetaAvgContour
import ThetaTrial.Paper.ShiftedAverageFourier
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-! Fourier multipliers for the operator `D = -i d/du`, under integrability
hypotheses. -/

noncomputable section
open Complex MeasureTheory Set Polynomial
open scoped FourierTransform

namespace ThetaTrial.Paper

theorem differentialOperator_iterate (j : ℕ) (f : ℝ → ℂ) :
    (differentialOperator^[j]) f = fun u => (-I)^j * iteratedDeriv j f u := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    funext u
    simp only [differentialOperator, deriv_const_mul_field, iteratedDeriv_succ,
      pow_succ]
    ring

theorem paperFourier_const_mul (c : ℂ) (f : ℝ → ℂ) (z : ℂ) :
    paperFourier (fun u => c * f u) z = c * paperFourier f z := by
  unfold paperFourier
  simp_rw [mul_assoc]
  exact integral_const_mul _ _

theorem paperFourier_integrable_real {f : ℝ → ℂ} (hf : Integrable f) (r : ℝ) :
    Integrable (fun u : ℝ => f u * exp (-I * (r : ℂ) * (u : ℂ))) := by
  apply hf.norm.mono'
    (hf.aestronglyMeasurable.mul ((by fun_prop :
      Continuous (fun u : ℝ => exp (-I * (r : ℂ) * (u : ℂ)))).aestronglyMeasurable))
  filter_upwards [] with u
  simp [norm_mul, norm_exp, mul_re, mul_im]

theorem paperFourier_iteratedDeriv {f : ℝ → ℂ}
    (hf : ContDiff ℝ ⊤ f) (hfi : ∀ j : ℕ, Integrable (iteratedDeriv j f))
    (j : ℕ) (r : ℝ) :
    paperFourier (iteratedDeriv j f) r = (I * (r : ℂ))^j * paperFourier f r := by
  rw [paperFourier_eq_mathlib,
    congrFun (Real.fourier_iteratedDeriv (N := (j : ℕ∞)) (hf.of_le (by simp))
      (fun j _ => hfi j) (n := j) (by simp))
      (r / (2 * Real.pi)), ← paperFourier_eq_mathlib]
  simp only [smul_eq_mul]
  congr 2
  push_cast
  field_simp

theorem paperFourier_differentialOperator_iterate {f : ℝ → ℂ}
    (hf : ContDiff ℝ ⊤ f) (hfi : ∀ j : ℕ, Integrable (iteratedDeriv j f))
    (j : ℕ) (r : ℝ) :
    paperFourier ((differentialOperator^[j]) f) r =
      (r : ℂ)^j * paperFourier f r := by
  rw [differentialOperator_iterate, paperFourier_const_mul,
    paperFourier_iteratedDeriv hf hfi]
  rw [← mul_assoc, ← mul_pow]
  have he : -I * (I * (r : ℂ)) = (r : ℂ) := by rw [← mul_assoc]; simp
  rw [he]

theorem polynomialDerivative_integrable {f : ℝ → ℂ}
    (hfi : ∀ j : ℕ, Integrable (iteratedDeriv j f)) (P : ℂ[X]) :
    Integrable (polynomialDerivative P f) := by
  unfold polynomialDerivative
  apply integrable_finsetSum
  intro j hj
  simp_rw [differentialOperator_iterate]
  exact ((hfi j).const_mul ((-I)^j)).const_mul (P.coeff j)

/-- All complex coefficients and the paper's exact polynomial differential operator. -/
theorem paperFourier_polynomialDerivative {f : ℝ → ℂ}
    (hf : ContDiff ℝ ⊤ f) (hfi : ∀ j : ℕ, Integrable (iteratedDeriv j f))
    (P : ℂ[X]) (r : ℝ) :
    paperFourier (polynomialDerivative P f) r =
      P.eval (r : ℂ) * paperFourier f r := by
  unfold polynomialDerivative paperFourier
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum]
  · change (∑ j ∈ P.support,
      paperFourier (fun u => P.coeff j * ((differentialOperator^[j]) f) u) r) = _
    simp_rw [paperFourier_const_mul, paperFourier_differentialOperator_iterate hf hfi,
      ← mul_assoc]
    rw [← Finset.sum_mul, Polynomial.eval_eq_sum]
    rfl
  · intro j hj
    apply paperFourier_integrable_real
    rw [differentialOperator_iterate]
    exact ((hfi j).const_mul ((-I)^j)).const_mul (P.coeff j)

end ThetaTrial.Paper
