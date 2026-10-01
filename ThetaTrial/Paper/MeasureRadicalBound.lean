import ThetaTrial.Paper.ThetaPolynomialRadical
import ThetaTrial.Paper.TailDerivativeMeasure

/-! The truncation estimate in terms of the paper's weighted
derivative-measure norm, including the two endpoint atoms. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set Polynomial

namespace ThetaTrial.Paper
open RadicalSource RadicalCorrelation RadicalCutoff

theorem RadicalSource.RegularSource.exteriorTail_boundedVariation {F : ℝ → ℂ}
    (hF : RegularSource F) {a : ℝ} (ha : 0 ≤ a) :
    BoundedVariationOn (exteriorTail a F) univ :=
  ThetaTrial.Paper.exteriorTail_boundedVariation hF.smooth.continuous ha
    (fun u _ => (hF.smooth.differentiable (by norm_num) u).hasDerivAt)
    hF.deriv_integrable.integrableOn

theorem RadicalSource.RegularSource.exteriorTail_measureBudget_eq {F : ℝ → ℂ}
    (hF : RegularSource F) {a : ℝ} (ha : 0 < a)
    (hv : BoundedVariationOn (exteriorTail a F) univ) :
    weightedBVMeasureBudget (exteriorTail a F) hv = hardTailBudget F (deriv F) a :=
  exteriorTail_weightedBVMeasureBudget_eq hF.smooth.continuous ha
    (fun u _ => (hF.smooth.differentiable (by norm_num) u).hasDerivAt)
    (weightedProfile_integrable hF.smooth.continuous.aestronglyMeasurable (hF.weight0 1)).integrableOn
    (weightedProfile_integrable (hF.smooth.continuous_deriv (by norm_num)).aestronglyMeasurable
      (hF.weight1 1)).integrableOn hv

theorem RadicalSource.source_window_abs_measure_bound {F : ℝ → ℂ}
    (hF : RegularSource F) {m : ℂ → ℂ}
    (hfactor : ∀ z, paperFourier F z = xiFunction z * m z)
    {a : ℝ} (ha : 0 < a) :
    |fullWeilForm (windowCut a F)| ≤ tailFormConstant *
      (weightedBVMeasureBudget (exteriorTail a F) (hF.exteriorTail_boundedVariation ha.le)) ^ 2 := by
  rw [hF.exteriorTail_measureBudget_eq ha]
  exact source_window_abs_bound hF hfactor ha.le

theorem ComplexShiftMeasure.polynomial_window_abs_measure_bound (μ : ComplexMeasure ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) (P : ℂ[X]) {a : ℝ} (ha : 0 < a) :
    let F := polynomialDerivative P (fun u : ℝ => ComplexShiftMeasure.source μ b (u : ℂ))
    let hv : BoundedVariationOn (exteriorTail a F) univ :=
      RegularSource.exteriorTail_boundedVariation (F := F)
        (ComplexShiftMeasure.polynomial_regularSource μ hb hbpi P) ha.le
    |fullWeilForm (windowCut a F)| ≤ tailFormConstant *
      (weightedBVMeasureBudget (exteriorTail a F) hv) ^ 2 :=
  source_window_abs_measure_bound (ComplexShiftMeasure.polynomial_regularSource μ hb hbpi P)
    (ComplexShiftMeasure.polynomial_fourier μ hb hbpi P) ha

theorem polynomialDerivative_theta_window_abs_measure_bound (P : ℂ[X]) {a : ℝ} (ha : 0 < a) :
    let F := polynomialDerivative P (fun u : ℝ => (thetaDensity u : ℂ))
    let hv : BoundedVariationOn (exteriorTail a F) univ :=
      RegularSource.exteriorTail_boundedVariation (F := F)
        (polynomialDerivative_theta_regularSource P) ha.le
    |fullWeilForm (windowCut a F)| ≤ tailFormConstant *
      (weightedBVMeasureBudget (exteriorTail a F) hv) ^ 2 :=
  source_window_abs_measure_bound (polynomialDerivative_theta_regularSource P)
    (polynomialDerivative_theta_fourier P) ha

end ThetaTrial.Paper

#print axioms ThetaTrial.Paper.ComplexShiftMeasure.polynomial_window_abs_measure_bound
#print axioms ThetaTrial.Paper.polynomialDerivative_theta_window_abs_measure_bound
