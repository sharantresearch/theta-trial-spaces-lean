import ThetaTrial.Paper.Definitions
import ThetaTrial.PrimeContinuity.FullForm
import ThetaTrial.RationalFourier.GammaMoment

/-! Convergence of the arithmetic terms of the form under weighted `L2` and
Fourier-decay hypotheses. -/

noncomputable section
open Complex MeasureTheory Set
open scoped ComplexConjugate

namespace ThetaTrial.Paper

theorem correlation_eq_weilFormula (f : ℝ → ℂ) (x : ℝ) :
    correlation f x = ThetaTrial.WeilFormula.correlation f x := by
  unfold correlation ThetaTrial.WeilFormula.correlation
  rw [← integral_add_right_eq_self
    (fun u : ℝ => f u * conj (f (u - x))) x]
  simp only [add_sub_cancel_right]

theorem gammaWeight_eq_weilFormula (r : ℝ) :
    gammaWeight r = ThetaTrial.GammaEnergy.gammaMultiplier r := by
  unfold gammaWeight ThetaTrial.GammaEnergy.gammaMultiplier
  push_cast
  ring_nf

theorem fullPrime_absolutely_summable {a : ℝ} (ha : 1 / 2 < a)
    {f : ℝ → ℂ} (hf : ThetaTrial.PrimeContinuity.WeightedL2 a f) :
    Summable (fun n : ℕ => |(ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
      (correlation f (Real.log n)).re|) := by
  simpa only [ThetaTrial.PrimeContinuity.primeTerm, correlation_eq_weilFormula] using
    ThetaTrial.PrimeContinuity.primeTerm_absolutely_summable ha hf

theorem fullPrime_continuous_bound {a : ℝ} (ha : 1 / 2 < a)
    {f g : ℝ → ℂ} (hf : ThetaTrial.PrimeContinuity.WeightedL2 a f)
    (hg : ThetaTrial.PrimeContinuity.WeightedL2 a g) :
    |(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        (correlation f (Real.log n)).re) -
      (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        (correlation g (Real.log n)).re)| ≤
      ThetaTrial.PrimeContinuity.logMajorantSum a *
        ThetaTrial.PrimeContinuity.weightedNorm a (f - g) *
        (ThetaTrial.PrimeContinuity.weightedNorm a f + ThetaTrial.PrimeContinuity.weightedNorm a g) := by
  simpa only [ThetaTrial.PrimeContinuity.fullPrimeForm, ThetaTrial.PrimeContinuity.primeTerm,
    correlation_eq_weilFormula] using ThetaTrial.PrimeContinuity.fullPrimeForm_lipschitz ha hf hg

theorem gamma_cauchy_integrable :
    Integrable (fun r : ℝ => |gammaWeight r| / (1 + r ^ 2)) := by
  have h := (ThetaTrial.RationalFourier.gamma_cauchy_integrable (H := 1) (by norm_num)).norm
  apply h.congr
  filter_upwards [] with r
  simp [gammaWeight_eq_weilFormula, abs_of_pos (by positivity : 0 < 1 + r ^ 2)]

/-- The gamma term is absolutely integrable under the stated
ordinary Fourier-square envelope, including functions with jumps. -/
theorem gamma_term_integrable_of_fourier_decay {f : ℝ → ℂ} {M : ℝ}
    (hm : AEStronglyMeasurable (fun r : ℝ => paperFourier f r))
    (hb : ∀ r : ℝ, ‖paperFourier f r‖ ^ 2 ≤ M ^ 2 / (1 + r ^ 2)) :
    Integrable (fun r : ℝ => gammaWeight r * Complex.normSq (paperFourier f r)) := by
  have hg : AEStronglyMeasurable gammaWeight := by
    have he : gammaWeight = ThetaTrial.GammaEnergy.gammaMultiplier :=
      funext gammaWeight_eq_weilFormula
    rw [he]
    exact ThetaTrial.RationalFourier.gammaMultiplier_aestronglyMeasurable
  apply Integrable.mono' (gamma_cauchy_integrable.const_mul (M ^ 2))
    (hg.mul (Complex.continuous_normSq.comp_aestronglyMeasurable hm))
  filter_upwards [] with r
  change ‖gammaWeight r * Complex.normSq (paperFourier f r)‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Complex.normSq_nonneg _),
    ← Complex.sq_norm]
  calc
    |gammaWeight r| * ‖paperFourier f r‖ ^ 2 ≤
        |gammaWeight r| * (M ^ 2 / (1 + r ^ 2)) :=
      mul_le_mul_of_nonneg_left (hb r) (abs_nonneg _)
    _ = _ := by ring

end ThetaTrial.Paper
