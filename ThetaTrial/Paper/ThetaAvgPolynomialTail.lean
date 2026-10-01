import ThetaTrial.Paper.ThetaAvgTail
import ThetaTrial.Paper.TrialFourier

/-! Degree-uniform contour bounds for the polynomial theta-average trials. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set Polynomial

namespace ThetaTrial.Paper

def thetaAvgCoefficientSum (k : ℕ) (P : ℂ[X]) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), ‖P.coeff j‖

theorem thetaAvgCoefficientSum_nonneg (k : ℕ) (P : ℂ[X]) : 0 ≤ thetaAvgCoefficientSum k P := by
  unfold thetaAvgCoefficientSum
  positivity

def thetaAvgPolynomialJet (a : ℝ) (P : ℂ[X]) (ell : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ P.support, (P.coeff j * (-I) ^ j) * thetaAvgTrialDerivative a (j + ell) x

theorem thetaAvg_support_subset_range {k : ℕ} {P : ℂ[X]} (hP : P.natDegree ≤ k) :
    P.support ⊆ Finset.range (k + 1) := by
  intro j hj
  apply Finset.mem_range.mpr
  exact Nat.lt_succ_of_le ((Polynomial.le_natDegree_of_ne_zero
    (Polynomial.mem_support_iff.mp hj)).trans hP)

theorem thetaAvgCoefficientSum_support_le {k : ℕ} {P : ℂ[X]} (hP : P.natDegree ≤ k) :
    (∑ j ∈ P.support, ‖P.coeff j‖) ≤ thetaAvgCoefficientSum k P := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (thetaAvg_support_subset_range hP)
    (fun j _ _ => norm_nonneg _)

theorem thetaAvg_factorial_scale_mono {Z : ℝ} (hZ : 1 ≤ Z) {j m : ℕ} (hjm : j ≤ m) :
    (j.factorial : ℝ) * Z ^ (2 * j) ≤ m.factorial * Z ^ (2 * m) := by
  have hf : (j.factorial : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_le hjm
  have hp := pow_le_pow_right₀ hZ (Nat.mul_le_mul_left 2 hjm)
  exact mul_le_mul hf hp (by positivity) (by positivity)

/-- Every ordinary derivative order of the finite polynomial trial sum,
with one common factorial/power majorant for all coefficients. -/
theorem thetaAvgPolynomialJet_norm_le {a x : ℝ} (ha : 0 ≤ a) (hZ : 16 ≤ scaleZ a)
    (hx : a ≤ |x|) {k : ℕ} {P : ℂ[X]} (hP : P.natDegree ≤ k) (ell : ℕ) :
    ‖thetaAvgPolynomialJet a P ell x‖ ≤
      thetaAvgCoefficientSum k P * ((k + ell).factorial * (scaleZ a) ^ (2 * (k + ell))) *
        thetaAvgContourEnvelope a x := by
  have hterm (j : ℕ) (hj : j ∈ P.support) :
      ‖(P.coeff j * (-I) ^ j) * thetaAvgTrialDerivative a (j + ell) x‖ ≤
        ‖P.coeff j‖ * (((k + ell).factorial : ℝ) * (scaleZ a) ^ (2 * (k + ell))) *
          thetaAvgContourEnvelope a x := by
    have hjk : j ≤ k := (Polynomial.le_natDegree_of_ne_zero
      (Polynomial.mem_support_iff.mp hj)).trans hP
    have hb := thetaAvg_contour_derivative_bound ha hZ hx (j + ell)
    have hm := thetaAvg_factorial_scale_mono (by linarith : 1 ≤ scaleZ a)
      (Nat.add_le_add_right hjk ell)
    have hb' := hb.trans (mul_le_mul_of_nonneg_right hm (thetaAvgContourEnvelope_pos a x).le)
    simp only [norm_mul, norm_pow, norm_neg, norm_I, one_pow, mul_one]
    simpa only [thetaAvgTrialDerivative, mul_assoc] using
      mul_le_mul_of_nonneg_left hb' (norm_nonneg (P.coeff j))
  calc
    _ ≤ ∑ j ∈ P.support, ‖(P.coeff j * (-I) ^ j) * thetaAvgTrialDerivative a (j + ell) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ P.support,
        ‖P.coeff j‖ * (((k + ell).factorial : ℝ) * (scaleZ a) ^ (2 * (k + ell))) *
          thetaAvgContourEnvelope a x := Finset.sum_le_sum hterm
    _ = (∑ j ∈ P.support, ‖P.coeff j‖) *
        (((k + ell).factorial : ℝ) * (scaleZ a) ^ (2 * (k + ell))) *
          thetaAvgContourEnvelope a x := by rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (thetaAvgCoefficientSum_support_le hP) (by positivity))
      (thetaAvgContourEnvelope_pos a x).le

theorem thetaAvgPolynomialJet_continuous {a : ℝ} (hZ : 16 ≤ scaleZ a)
    (P : ℂ[X]) (ell : ℕ) : Continuous (thetaAvgPolynomialJet a P ell) := by
  unfold thetaAvgPolynomialJet
  exact continuous_finsetSum _ (fun j _ => continuous_const.mul
    (thetaAvgTrialDerivative_continuous hZ (j + ell)))

theorem thetaAvgPolynomialJet_hasDerivAt {a : ℝ} (hZ : 16 ≤ scaleZ a)
    (P : ℂ[X]) (ell : ℕ) (x : ℝ) :
    HasDerivAt (thetaAvgPolynomialJet a P ell) (thetaAvgPolynomialJet a P (ell + 1) x) x := by
  unfold thetaAvgPolynomialJet
  convert HasDerivAt.fun_sum (fun j (_ : j ∈ P.support) =>
    (thetaAvgTrialDerivative_hasDerivAt hZ (j + ell) x).const_mul (P.coeff j * (-I) ^ j)) using 1
  all_goals rfl

/-- Both F and its first derivative are bounded with the same degree scale. -/
theorem thetaAvgPolynomialJet_zero_one_norm_le {a x : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (hx : a ≤ |x|) {k : ℕ} {P : ℂ[X]}
    (hP : P.natDegree ≤ k) :
    ‖thetaAvgPolynomialJet a P 0 x‖ + ‖thetaAvgPolynomialJet a P 1 x‖ ≤
      (2 * thetaAvgCoefficientSum k P * ((k + 1).factorial * (scaleZ a) ^ (2 * (k + 1)))) *
        thetaAvgContourEnvelope a x := by
  have h0 := thetaAvgPolynomialJet_norm_le ha hZ hx hP 0
  have h1 := thetaAvgPolynomialJet_norm_le ha hZ hx hP 1
  simp only [Nat.add_zero] at h0
  have hm := thetaAvg_factorial_scale_mono (by linarith : 1 ≤ scaleZ a) (Nat.le_succ k)
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hm (thetaAvgCoefficientSum_nonneg k P))
    (thetaAvgContourEnvelope_pos a x).le
  simp only [Nat.succ_eq_add_one] at hh
  nlinarith [h0, h1, hh]

/-- Hard-tail derivative integral and both jumps, uniformly in the polynomial. -/
theorem thetaAvgPolynomialJet_hardTailBudget_le {a : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) {k : ℕ} {P : ℂ[X]} (hP : P.natDegree ≤ k) :
    hardTailBudget (thetaAvgPolynomialJet a P 0) (thetaAvgPolynomialJet a P 1) a ≤
      (2 * thetaAvgCoefficientSum k P * ((k + 1).factorial * (scaleZ a) ^ (2 * (k + 1)))) *
        thetaAvgWeightedScale a * thetaAvgTailConstant := by
  apply thetaAvg_hardTailBudget_of_bound ha
    (mul_nonneg (mul_nonneg (by norm_num) (thetaAvgCoefficientSum_nonneg k P)) (by positivity))
    (thetaAvgPolynomialJet_continuous hZ P 0) (thetaAvgPolynomialJet_continuous hZ P 1)
  exact fun x hx => thetaAvgPolynomialJet_zero_one_norm_le ha hZ hx hP

theorem thetaAvgPolynomialJet_zero_eq {a : ℝ} (hZ : 16 ≤ scaleZ a) (P : ℂ[X]) :
    thetaAvgPolynomialJet a P 0 = polynomialDerivative P (fun u : ℝ => shiftedAverage a (u : ℂ)) := by
  funext x
  unfold thetaAvgPolynomialJet polynomialDerivative
  simp only [Nat.add_zero, differentialOperator_iterate, shiftedAverage_real_iteratedDeriv hZ,
    thetaAvgTrialDerivative]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem thetaAvgPolynomialJet_one_eq_deriv {a : ℝ} (hZ : 16 ≤ scaleZ a) (P : ℂ[X]) :
    thetaAvgPolynomialJet a P 1 = deriv (polynomialDerivative P
      (fun u : ℝ => shiftedAverage a (u : ℂ))) := by
  funext x
  have h := thetaAvgPolynomialJet_hasDerivAt hZ P 0 x
  rw [thetaAvgPolynomialJet_zero_eq hZ] at h
  exact h.deriv.symm

/-- The paper's polynomial hard-tail estimate for its P(D)G_a,
with the degree coefficient sum left explicit for the independent interval norm bound. -/
theorem thetaAvg_polynomial_hardTailBudget_exp_bound {a : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) {k : ℕ} {P : ℂ[X]} (hP : P.natDegree ≤ k) :
    hardTailBudget (polynomialDerivative P (fun u : ℝ => shiftedAverage a (u : ℂ)))
      (deriv (polynomialDerivative P (fun u : ℝ => shiftedAverage a (u : ℂ)))) a ≤
        thetaAvgBudgetConstant * thetaAvgCoefficientSum k P * (k + 1).factorial *
          (scaleZ a) ^ (2 * k) * Real.exp (16 * a - scaleT a) := by
  rw [← thetaAvgPolynomialJet_one_eq_deriv hZ, ← thetaAvgPolynomialJet_zero_eq hZ]
  apply (thetaAvgPolynomialJet_hardTailBudget_le ha hZ hP).trans_eq
  rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
  calc
    _ = (thetaAvgCoefficientSum k P * ((k + 1).factorial : ℝ) * (scaleZ a) ^ (2 * k)) *
        (2 * (scaleZ a) ^ 2 * thetaAvgWeightedScale a * thetaAvgTailConstant) := by ring
    _ = _ := by rw [thetaAvg_budget_scale_identity]; ring

end ThetaTrial.Paper
