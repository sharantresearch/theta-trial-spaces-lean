import ThetaTrial.Paper.TrialFourier
import ThetaTrial.Paper.FullForm

/-! Complex Fourier multipliers, with exponential integrability checked before
integration by parts. -/

noncomputable section
open Complex MeasureTheory Set Polynomial
open scoped FourierTransform

namespace ThetaTrial.Paper

theorem paperFourier_integrand_integrable_of_weight {f : ℝ → ℂ} (z : ℂ)
    (hm : AEStronglyMeasurable f)
    (hw : Integrable (fun u : ℝ => Real.exp (|z.im| * |u|) * ‖f u‖)) :
    Integrable (fun u : ℝ => f u * exp (-I * z * (u : ℂ))) := by
  apply hw.mono' (hm.mul (by fun_prop))
  filter_upwards [] with u
  change ‖f u * exp (-I*z*(u:ℂ))‖ ≤ _
  rw [norm_mul, norm_exp]
  have he : (-I * z * (u : ℂ)).re = z.im * u := by
    simp [mul_re, mul_im]
  rw [he, mul_comm ‖f u‖]
  exact mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (by simpa only [abs_mul] using le_abs_self (z.im*u))) (norm_nonneg _)

theorem paperFourier_deriv_complex {f : ℝ → ℂ}
    (hf : Differentiable ℝ f) (z : ℂ)
    (hw : Integrable (fun u : ℝ => Real.exp (|z.im| * |u|) * ‖f u‖))
    (hw' : Integrable (fun u : ℝ => Real.exp (|z.im| * |u|) * ‖deriv f u‖))
    (hm' : AEStronglyMeasurable (deriv f)) :
    paperFourier (deriv f) z = I * z * paperFourier f z := by
  let g : ℝ → ℂ := fun u => f u * exp (-I * z * (u : ℂ))
  have hi := paperFourier_integrand_integrable_of_weight z hf.continuous.aestronglyMeasurable hw
  have hi' := paperFourier_integrand_integrable_of_weight z hm' hw'
  have hd (u : ℝ) : HasDerivAt g
      (deriv f u * exp (-I * z * (u : ℂ)) +
        (-I * z) * (f u * exp (-I * z * (u : ℂ)))) u := by
    have he := ((Complex.ofRealCLM.hasDerivAt (x := u)).const_mul (-I * z)).cexp
    convert (hf u).hasDerivAt.mul he using 1 <;> first | rfl | (dsimp [g]; ring)
  have hdg : deriv g = fun u => deriv f u * exp (-I * z * (u : ℂ)) +
        (-I * z) * (f u * exp (-I * z * (u : ℂ))) := funext fun u => (hd u).deriv
  have hig : Integrable (deriv g) := by
    rw [hdg]
    exact hi'.add (hi.const_mul (-I * z))
  have hzero : (∫ u : ℝ, deriv g u) = 0 := by
    have h := congrFun (Real.fourier_deriv hi (fun u => (hd u).differentiableAt) hig) 0
    simpa [Real.fourier_eq', g] using h
  rw [hdg, integral_add hi' (hi.const_mul (-I * z)), integral_const_mul] at hzero
  change paperFourier (deriv f) z + (-I * z) * paperFourier f z = 0 at hzero
  linear_combination hzero

theorem paperFourier_iteratedDeriv_complex {f : ℝ → ℂ}
    (hf : ContDiff ℝ ⊤ f)
    (hw : ∀ j : ℕ, ∀ R : ℝ,
      Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖iteratedDeriv j f u‖))
    (j : ℕ) (z : ℂ) :
    paperFourier (iteratedDeriv j f) z = (I * z)^j * paperFourier f z := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    rw [paperFourier_deriv_complex (hf.differentiable_iteratedDeriv j (by simp)) z (hw j |z.im|)]
    · rw [ih, pow_succ]
      ring
    · simpa only [iteratedDeriv_succ] using hw (j+1) |z.im|
    · simpa only [iteratedDeriv_succ] using
        (hf.continuous_iteratedDeriv (j+1) (by simp)).aestronglyMeasurable

theorem paperFourier_polynomialDerivative_complex {f : ℝ → ℂ}
    (hf : ContDiff ℝ ⊤ f)
    (hw : ∀ j : ℕ, ∀ R : ℝ,
      Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖iteratedDeriv j f u‖))
    (P : ℂ[X]) (z : ℂ) :
    paperFourier (polynomialDerivative P f) z = P.eval z * paperFourier f z := by
  unfold polynomialDerivative paperFourier
  simp_rw [differentialOperator_iterate, Finset.sum_mul]
  rw [integral_finsetSum]
  · change (∑ j ∈ P.support, paperFourier
      (fun u => P.coeff j * ((-I)^j * iteratedDeriv j f u)) z) = _
    simp_rw [paperFourier_const_mul, paperFourier_iteratedDeriv_complex hf hw]
    have he (j : ℕ) : (-I)^j * ((I*z)^j * paperFourier f z) =
        z^j * paperFourier f z := by
      rw [← mul_assoc, ← mul_pow]
      congr 2
      rw [← mul_assoc]
      simp
    simp_rw [he, ← mul_assoc]
    rw [← Finset.sum_mul, Polynomial.eval_eq_sum]
    rfl
  · intro j hj
    have hm : AEStronglyMeasurable (iteratedDeriv j f) :=
      (hf.continuous_iteratedDeriv j (by simp)).aestronglyMeasurable
    have hi := paperFourier_integrand_integrable_of_weight z hm (hw j |z.im|)
    simpa only [mul_assoc] using (hi.const_mul ((-I)^j)).const_mul (P.coeff j)

end ThetaTrial.Paper
