import ThetaTrial.Paper.Radical
import ThetaTrial.Paper.WeightedBVMeasure

/-! The geometric side of the form only needs the real line and the two
polar frequencies; for BV tests, exponential weight one suffices. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set
open scoped ComplexConjugate

namespace ThetaTrial.Paper.RadicalBV
open Radical

theorem paperFT_weilTest_strip {f : ℝ → ℂ}
    (hf : ∀ z : ℂ, |z.im| ≤ 1 → FourierIntegrableAt f z)
    {z : ℂ} (hz : |z.im| ≤ 1) :
    Zeta23.paperFT (Zeta23.EF.weilTest f f) z =
      Radical.paperFourier f (-z) * conj (Radical.paperFourier f (-conj z)) := by
  have h := Radical.paperFourier_weilTest_of_integrable
    (hf (-z) (by simpa only [Complex.neg_im, abs_neg] using hz))
    (hf (conj (-z)) (by simpa only [Complex.conj_im, Complex.neg_im, neg_neg] using hz))
  simpa only [Radical.paperFourier, neg_neg, map_neg] using h

theorem pole_pair_of_strip {f : ℝ → ℂ}
    (hf : ∀ z : ℂ, |z.im| ≤ 1 → FourierIntegrableAt f z) :
    Zeta23.paperFT (Zeta23.EF.weilTest f f) (I / 2) +
      Zeta23.paperFT (Zeta23.EF.weilTest f f) (-I / 2) =
      (2 : ℂ) * ((ThetaTrial.Paper.paperFourier f (I / 2) *
        conj (ThetaTrial.Paper.paperFourier f (-I / 2))).re : ℂ) := by
  rw [paperFT_weilTest_strip hf (by norm_num), paperFT_weilTest_strip hf (by norm_num)]
  simp only [map_div₀, conj_I, map_ofNat, map_neg, neg_neg, neg_div,
    paperFourier_eq_paper]
  have h := Complex.add_conj (ThetaTrial.Paper.paperFourier f (I / 2) *
    conj (ThetaTrial.Paper.paperFourier f (-I / 2)))
  simpa only [map_mul, conj_conj, add_comm, mul_comm, Complex.ofReal_mul,
    Complex.ofReal_ofNat, neg_div] using h

theorem gamma_integral_of_strip {f : ℝ → ℂ}
    (hf : ∀ z : ℂ, |z.im| ≤ 1 → FourierIntegrableAt f z) :
    (∫ r : ℝ, Zeta23.paperFT (Zeta23.EF.weilTest f f) r *
      (Zeta23.EF.gammaBracket r : ℂ)) =
      ((∫ r : ℝ, ThetaTrial.Paper.gammaWeight r *
        Complex.normSq (ThetaTrial.Paper.paperFourier f r)) : ℝ) := by
  calc
    _ = ∫ r : ℝ, (Complex.normSq (paperFourier f (-r)) : ℂ) *
        (Zeta23.EF.gammaBracket r : ℂ) := by
      apply integral_congr_ae
      filter_upwards with r
      rw [paperFT_weilTest_strip hf (by simp)]
      simp only [conj_ofReal, Complex.mul_conj, paperFourier_eq_paper]
    _ = ∫ r : ℝ, (Complex.normSq (paperFourier f (-(-r : ℝ))) : ℂ) *
        (Zeta23.EF.gammaBracket (-r) : ℂ) :=
      (integral_neg_eq_self _ volume).symm
    _ = _ := by
      simp only [Complex.ofReal_neg, neg_neg, ThetaTrial.WeilFormula.gammaBracket_neg,
        paperFourier_eq_paper]
      have he : (fun r : ℝ => (Complex.normSq (ThetaTrial.Paper.paperFourier f r) : ℂ) *
          (Zeta23.EF.gammaBracket r : ℂ)) = fun r : ℝ =>
          ((ThetaTrial.Paper.gammaWeight r *
            Complex.normSq (ThetaTrial.Paper.paperFourier f r) : ℝ) : ℂ) := by
        funext r
        simp only [Zeta23.EF.gammaBracket, ThetaTrial.Paper.gammaWeight,
          Complex.ofReal_mul, mul_comm]
      rw [he]
      exact integral_complex_ofReal

/-- Dictionary to the paper's real form, valid also for noncompact
or discontinuous inputs with exponential moments on the unit strip. The identity itself
does not assert convergence of the prime sum or gamma integral; that is
separately supplied by the dominated-approximation results below. -/
theorem fullQuadratic_eq_paperForm_of_strip {f : ℝ → ℂ}
    (hf : ∀ z : ℂ, |z.im| ≤ 1 → FourierIntegrableAt f z) :
    fullQuadratic f = (ThetaTrial.Paper.fullWeilForm f : ℂ) := by
  have hp : (∑' n : ℕ,
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (Zeta23.EF.weilTest f f (Real.log n) +
          Zeta23.EF.weilTest f f (-Real.log n))) =
      (2 : ℂ) * ((∑' n : ℕ,
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          (ThetaTrial.Paper.correlation f (Real.log n)).re : ℝ) : ℂ) := by
    simp_rw [ThetaTrial.WeilFormula.weilTest_add_neg, weilFormulaCorrelation_eq_paper]
    rw [Complex.ofReal_tsum, ← tsum_mul_left]
    apply tsum_congr
    intro n
    push_cast
    ring
  unfold fullQuadratic fullPairing fullWeil Zeta23.EF.literatureRHS
  rw [pole_pair_of_strip hf, hp, gamma_integral_of_strip hf]
  unfold ThetaTrial.Paper.fullWeilForm
  push_cast
  ring


theorem weightedBV_fullQuadratic_eq_paperForm {f : ℝ → ℂ}
    (hv : BoundedVariationOn f univ)
    (hw : Integrable (ThetaTrial.PrimeContinuity.weightedProfile 1 f))
    (hm : Integrable (fun x : ℝ => Real.exp |x|) hv.vectorMeasure.variation) :
    Radical.fullQuadratic f = (fullWeilForm f : ℂ) :=
  fullQuadratic_eq_paperForm_of_strip
    (weightedBVMeasure_fullForm_converges hv hw hm).2.2.1

end ThetaTrial.Paper.RadicalBV

#print axioms ThetaTrial.Paper.RadicalBV.weightedBV_fullQuadratic_eq_paperForm

