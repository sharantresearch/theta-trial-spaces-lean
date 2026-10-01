import ThetaTrial.Paper.ThetaAvgPolynomialRegularity
import ThetaTrial.Paper.TrialFourierComplex

/-! The radical and sharp-cutoff identities for polynomial derivatives of the
shifted average. -/

noncomputable section
open Complex MeasureTheory Set Polynomial
open scoped ComplexConjugate

namespace ThetaTrial.Paper

theorem polynomialDerivative_shiftedAverage_fourier {a : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (P : ℂ[X]) (z : ℂ) :
    paperFourier (polynomialDerivative P (fun u : ℝ => shiftedAverage a (u : ℂ))) z =
      xiFunction z * (P.eval z * shiftMultiplier a z) := by
  have hw : ∀ j : ℕ, ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) *
      ‖iteratedDeriv j (fun v : ℝ => shiftedAverage a (v : ℂ)) u‖) := by
    intro j R
    simpa only [ThetaTrial.PrimeContinuity.weightedProfile_norm] using
      (shiftedAverage_real_iteratedDeriv_all_weights_integrable ha hZ j R).norm
  rw [paperFourier_polynomialDerivative_complex (shiftedAverage_real_contDiff hZ) hw P z,
    paperFourier_shiftedAverage (ContourArcIdentity.shiftWidth_arc_bounds hZ).1]
  ring

theorem polynomialDerivative_shiftedAverage_hardCutoff {a r : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (P : ℂ[X]) (hr : 0 ≤ r) :
    fullWeilForm (windowCut r (polynomialDerivative P
      (fun u : ℝ => shiftedAverage a (u : ℂ)))) =
    fullWeilForm (exteriorTail r (polynomialDerivative P
      (fun u : ℝ => shiftedAverage a (u : ℂ)))) :=
  RadicalSource.source_hardCutoff (polynomialDerivative_shiftedAverage_regularSource ha hZ P)
    (polynomialDerivative_shiftedAverage_fourier ha hZ P) hr

theorem polynomialDerivative_shiftedAverage_radical {a : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (P : ℂ[X]) {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h)
    (hi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖h u‖)) :
    Radical.fullPairing (polynomialDerivative P
      (fun u : ℝ => shiftedAverage a (u : ℂ))) h = 0 :=
  RadicalSource.source_fullPairing_eq_zero (polynomialDerivative_shiftedAverage_regularSource ha hZ P)
    (polynomialDerivative_shiftedAverage_fourier ha hZ P) hm hi

theorem polynomialDerivative_shiftedAverage_fullWeilForm_zero {a : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (P : ℂ[X]) :
    fullWeilForm (polynomialDerivative P (fun u : ℝ => shiftedAverage a (u : ℂ))) = 0 := by
  let F := polynomialDerivative P (fun u : ℝ => shiftedAverage a (u : ℂ))
  have hF : RadicalSource.RegularSource F := polynomialDerivative_shiftedAverage_regularSource ha hZ P
  have hq : Radical.fullQuadratic F = 0 :=
    polynomialDerivative_shiftedAverage_radical ha hZ P hF.smooth.continuous.aestronglyMeasurable hF.weight0
  rw [Radical.fullQuadratic_eq_paperForm (RadicalSource.source_fourier_integrable hF)] at hq
  exact_mod_cast hq

end ThetaTrial.Paper

#print axioms ThetaTrial.Paper.polynomialDerivative_shiftedAverage_hardCutoff
#print axioms ThetaTrial.Paper.polynomialDerivative_shiftedAverage_fullWeilForm_zero
