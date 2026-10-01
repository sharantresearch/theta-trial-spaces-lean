import ThetaTrial.Paper.ComplexShiftPolynomial
import ThetaTrial.Paper.ComplexShiftDecay

/-! The radical, admissibility and sharp-cutoff statements for `P(D)Φ`. -/

noncomputable section
open Complex MeasureTheory Set Polynomial
open scoped ComplexConjugate

namespace ThetaTrial.Paper
open RadicalSource RadicalApproximation ShiftMeasure

theorem theta_iteratedDeriv_regularSource (j : ℕ) :
    RegularSource (iteratedDeriv j (fun u : ℝ => (thetaDensity u : ℂ))) := by
  have h := shiftJet_regularSource (Measure.dirac (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ 0)
    (by positivity : (0 : ℝ) < Real.pi / 4) j
  have he : (fun u : ℝ => shiftJet (Measure.dirac (0 : ℝ)) 0 j (u : ℂ)) =
      iteratedDeriv j (fun u : ℝ => (thetaDensity u : ℂ)) := by
    funext u
    simp [shiftJet, theta_real_iteratedDeriv]
  rwa [he] at h

theorem polynomialDerivative_theta_regularSource (P : ℂ[X]) :
    RegularSource (polynomialDerivative P (fun u : ℝ => (thetaDensity u : ℂ))) :=
  regularSource_polynomialDerivative theta_iteratedDeriv_regularSource P

theorem polynomialDerivative_theta_fourier (P : ℂ[X]) (z : ℂ) :
    paperFourier (polynomialDerivative P (fun u : ℝ => (thetaDensity u : ℂ))) z =
      xiFunction z * P.eval z := by
  rw [paperFourier_polynomialDerivative_complex thetaDensity_contDiff
    theta_iteratedDeriv_weighted_integrable P z, paperFourier_theta]
  exact mul_comm _ _

theorem polynomialDerivative_theta_radical (P : ℂ[X]) {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h)
    (hi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖h u‖)) :
    Radical.fullPairing (polynomialDerivative P (fun u : ℝ => (thetaDensity u : ℂ))) h = 0 :=
  source_fullPairing_eq_zero (polynomialDerivative_theta_regularSource P)
    (polynomialDerivative_theta_fourier P) hm hi

theorem polynomialDerivative_theta_fullWeilForm_zero (P : ℂ[X]) :
    fullWeilForm (polynomialDerivative P (fun u : ℝ => (thetaDensity u : ℂ))) = 0 :=
  source_fullWeilForm_zero (polynomialDerivative_theta_regularSource P)
    (polynomialDerivative_theta_fourier P)

theorem polynomialDerivative_theta_tail_pairing_zero (P : ℂ[X]) (a : ℝ) :
    let F := polynomialDerivative P (fun u : ℝ => (thetaDensity u : ℂ))
    Radical.fullPairing F (exteriorTail a F) = 0 ∧
      Radical.fullPairing (exteriorTail a F) F = 0 :=
  source_tail_pairing_zero (polynomialDerivative_theta_regularSource P)
    (polynomialDerivative_theta_fourier P) a

theorem polynomialDerivative_theta_hardCutoff (P : ℂ[X]) {a : ℝ} (ha : 0 ≤ a) :
    let F := polynomialDerivative P (fun u : ℝ => (thetaDensity u : ℂ))
    fullWeilForm (windowCut a F) = fullWeilForm (exteriorTail a F) :=
  source_hardCutoff (polynomialDerivative_theta_regularSource P)
    (polynomialDerivative_theta_fourier P) ha

theorem polynomialDerivative_theta_window_inDomain (P : ℂ[X]) {a : ℝ} (ha : 0 ≤ a) :
    InWindowFormDomain a (windowCut a
      (polynomialDerivative P (fun u : ℝ => (thetaDensity u : ℂ)))) :=
  (polynomialDerivative_theta_regularSource P).window_inDomain ha

theorem polynomialDerivative_theta_window_abs_bound (P : ℂ[X]) {a : ℝ} (ha : 0 ≤ a) :
    let F := polynomialDerivative P (fun u : ℝ => (thetaDensity u : ℂ))
    |fullWeilForm (windowCut a F)| ≤ tailFormConstant * (hardTailBudget F (deriv F) a) ^ 2 :=
  source_window_abs_bound (polynomialDerivative_theta_regularSource P)
    (polynomialDerivative_theta_fourier P) ha

end ThetaTrial.Paper

#print axioms ThetaTrial.Paper.polynomialDerivative_theta_hardCutoff
#print axioms ThetaTrial.Paper.polynomialDerivative_theta_window_abs_bound
