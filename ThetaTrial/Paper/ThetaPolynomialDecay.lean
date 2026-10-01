import ThetaTrial.Paper.ThetaPolynomialRadical

/-! All derivatives of `P(D)Φ` decay double-exponentially. -/

noncomputable section
open Complex MeasureTheory Set Polynomial

namespace ThetaTrial.Paper
open RadicalApproximation

theorem polynomialDerivative_theta_iteratedDeriv (P : ℂ[X]) (r : ℕ) :
    iteratedDeriv r (polynomialDerivative P (fun u : ℝ => (thetaDensity u : ℂ))) =
      fun u : ℝ => ∑ j ∈ P.support, (P.coeff j * (-I) ^ j) *
        iteratedDeriv (j + r) complexThetaDensity (u : ℂ) := by
  induction r with
  | zero =>
    funext u
    simp only [iteratedDeriv_zero, polynomialDerivative, differentialOperator_iterate,
      theta_real_iteratedDeriv, Nat.add_zero, mul_assoc]
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    have hd := HasDerivAt.fun_sum (u := P.support) (fun j _hj =>
      ((analytic_iteratedTheta (j + r) (u : ℂ) (real_mem_thetaStrip u)).differentiableAt.hasDerivAt.comp_ofReal).const_mul
        (P.coeff j * (-I) ^ j))
    simpa only [← Nat.add_assoc, iteratedDeriv_succ] using hd.deriv

theorem polynomialDerivative_theta_all_derivatives_doubleExp_decay (P : ℂ[X]) :
    ∃ c > 0, ∀ r : ℕ, ∃ C > 0, ∀ u : ℝ,
      ‖iteratedDeriv r (polynomialDerivative P (fun v : ℝ => (thetaDensity v : ℂ))) u‖ ≤
        C * ThetaTrial.ThetaSeries.doubleExpEnvelope
          ((9 / 2 : ℝ) + 2 * ((P.natDegree + r : ℕ) : ℝ)) c |u| := by
  obtain ⟨c, hc, hder⟩ := complexThetaDensity_iteratedDeriv_closed_strip_decay
    (by norm_num : (0 : ℝ) ≤ 0) (by positivity : (0 : ℝ) < Real.pi / 4)
  choose C hC hbound using hder
  have hreal (j : ℕ) (u : ℝ) : ‖iteratedDeriv j complexThetaDensity (u : ℂ)‖ ≤
      C j * ThetaTrial.ThetaSeries.doubleExpEnvelope (9 / 2 + 2 * (j : ℝ)) c |u| := by
    simpa only [ThetaTrial.ThetaSeries.doubleExpEnvelope, Complex.ofReal_re, mul_assoc] using
      hbound j (u : ℂ) (by simp)
  refine ⟨c, hc, ?_⟩
  intro r
  let K := ∑ j ∈ P.support, ‖P.coeff j * (-I) ^ j‖ * C (j + r)
  have hK : 0 ≤ K := Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (hC _).le)
  refine ⟨K + 1, by positivity, ?_⟩
  intro u
  rw [polynomialDerivative_theta_iteratedDeriv P r]
  let E := ThetaTrial.ThetaSeries.doubleExpEnvelope
    ((9 / 2 : ℝ) + 2 * ((P.natDegree + r : ℕ) : ℝ)) c |u|
  have hE : 0 ≤ E := by unfold E ThetaTrial.ThetaSeries.doubleExpEnvelope; positivity
  have henv (j : ℕ) (hj : j ∈ P.support) :
      ThetaTrial.ThetaSeries.doubleExpEnvelope (9 / 2 + 2 * ((j + r : ℕ) : ℝ)) c |u| ≤ E := by
    have hjd : j ≤ P.natDegree := Polynomial.le_natDegree_of_mem_supp j hj
    unfold E ThetaTrial.ThetaSeries.doubleExpEnvelope
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg u)
    have hjr : ((j + r : ℕ) : ℝ) ≤ ((P.natDegree + r : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hjd r
    linarith
  calc
    _ ≤ ∑ j ∈ P.support, ‖(P.coeff j * (-I) ^ j) * iteratedDeriv (j + r) complexThetaDensity (u : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ P.support, (‖P.coeff j * (-I) ^ j‖ * C (j + r)) * E := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        ((hreal (j + r) u).trans (mul_le_mul_of_nonneg_left (henv j hj) (hC _).le))
        (norm_nonneg _)
    _ = K * E := (Finset.sum_mul ..).symm
    _ ≤ (K + 1) * E := mul_le_mul_of_nonneg_right (by linarith) hE

end ThetaTrial.Paper

#print axioms ThetaTrial.Paper.polynomialDerivative_theta_all_derivatives_doubleExp_decay
