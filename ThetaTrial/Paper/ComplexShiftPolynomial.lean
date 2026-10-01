import ThetaTrial.Paper.ComplexShiftMeasure
import ThetaTrial.Paper.RadicalSourceAlgebra
import ThetaTrial.Paper.RadicalConsequences

/-! The radical and sharp-cutoff identities for arbitrary finite complex
measures of imaginary theta shifts and arbitrary complex polynomials. -/

noncomputable section
open Complex MeasureTheory Set Polynomial
open scoped ComplexConjugate

namespace ThetaTrial.Paper.ComplexShiftMeasure
open RadicalSource

theorem polynomial_regularSource (μ : ComplexMeasure ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) (P : ℂ[X]) :
    RegularSource (polynomialDerivative P (fun u : ℝ => source μ b (u : ℂ))) := by
  apply regularSource_polynomialDerivative
  intro j
  rw [source_real_iteratedDeriv μ hbpi j]
  exact jet_regularSource μ hb hbpi j

theorem polynomial_fourier (μ : ComplexMeasure ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) (P : ℂ[X]) (z : ℂ) :
    paperFourier (polynomialDerivative P (fun u : ℝ => source μ b (u : ℂ))) z =
      xiFunction z * (P.eval z * multiplier μ b z) := by
  have hw : ∀ j : ℕ, ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) *
      ‖iteratedDeriv j (fun v : ℝ => source μ b (v : ℂ)) u‖) := by
    intro j R
    rw [source_real_iteratedDeriv μ hbpi j]
    exact jet_weighted_integrable μ hb hbpi j R
  have hs : ContDiff ℝ ⊤ (fun u : ℝ => source μ b (u : ℂ)) := jet_real_contDiff μ hbpi 0
  rw [paperFourier_polynomialDerivative_complex hs hw P z,
    source_fourier μ hb hbpi z]
  ring

theorem polynomial_radical (μ : ComplexMeasure ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) (P : ℂ[X]) {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h)
    (hi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖h u‖)) :
    Radical.fullPairing (polynomialDerivative P (fun u : ℝ => source μ b (u : ℂ))) h = 0 :=
  source_fullPairing_eq_zero (polynomial_regularSource μ hb hbpi P)
    (polynomial_fourier μ hb hbpi P) hm hi

theorem polynomial_fullWeilForm_zero (μ : ComplexMeasure ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) (P : ℂ[X]) :
    fullWeilForm (polynomialDerivative P (fun u : ℝ => source μ b (u : ℂ))) = 0 :=
  source_fullWeilForm_zero (polynomial_regularSource μ hb hbpi P)
    (polynomial_fourier μ hb hbpi P)

theorem polynomial_tail_pairing_zero (μ : ComplexMeasure ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) (P : ℂ[X]) (a : ℝ) :
    let F := polynomialDerivative P (fun u : ℝ => source μ b (u : ℂ))
    Radical.fullPairing F (exteriorTail a F) = 0 ∧
      Radical.fullPairing (exteriorTail a F) F = 0 :=
  source_tail_pairing_zero (polynomial_regularSource μ hb hbpi P)
    (polynomial_fourier μ hb hbpi P) a

theorem polynomial_hardCutoff (μ : ComplexMeasure ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) (P : ℂ[X]) {a : ℝ} (ha : 0 ≤ a) :
    let F := polynomialDerivative P (fun u : ℝ => source μ b (u : ℂ))
    fullWeilForm (windowCut a F) = fullWeilForm (exteriorTail a F) :=
  RadicalSource.source_hardCutoff (polynomial_regularSource μ hb hbpi P)
    (polynomial_fourier μ hb hbpi P) ha

theorem polynomial_window_inDomain (μ : ComplexMeasure ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) (P : ℂ[X]) {a : ℝ} (ha : 0 ≤ a) :
    InWindowFormDomain a
      (windowCut a (polynomialDerivative P (fun u : ℝ => source μ b (u : ℂ)))) :=
  (polynomial_regularSource μ hb hbpi P).window_inDomain ha

theorem polynomial_window_abs_bound (μ : ComplexMeasure ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) (P : ℂ[X]) {a : ℝ} (ha : 0 ≤ a) :
    let F := polynomialDerivative P (fun u : ℝ => source μ b (u : ℂ))
    |fullWeilForm (windowCut a F)| ≤ tailFormConstant * (hardTailBudget F (deriv F) a) ^ 2 :=
  source_window_abs_bound (polynomial_regularSource μ hb hbpi P)
    (polynomial_fourier μ hb hbpi P) ha

end ThetaTrial.Paper.ComplexShiftMeasure

#print axioms ThetaTrial.Paper.ComplexShiftMeasure.polynomial_hardCutoff
#print axioms ThetaTrial.Paper.ComplexShiftMeasure.polynomial_window_abs_bound
