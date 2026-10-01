import ThetaTrial.WeilFormula.Arithmetic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Group.Integral

/-!
The exponentially weighted `L2` norm and translation correlations used for
continuity of the prime form. Membership is the ordinary `MemLp` predicate.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped ComplexConjugate ENNReal Topology

namespace ThetaTrial.PrimeContinuity

def weightedProfile (a : ℝ) (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  (Real.exp (a * |y|) : ℂ) * f y

abbrev WeightedL2 (a : ℝ) (f : ℝ → ℂ) : Prop :=
  MemLp (weightedProfile a f) 2 (volume : Measure ℝ)

/-- L2 norm of exp(a|y|)f, expressed by its squared integral. -/
def weightedNorm (a : ℝ) (f : ℝ → ℂ) : ℝ :=
  Real.sqrt (∫ y : ℝ, ‖weightedProfile a f y‖ ^ 2)

/-- The mixed correlation, linear in the first argument. Taking the real part
removes the dependence on the order of the pair. -/
def mixedCorrelation (f g : ℝ → ℂ) (h : ℝ) : ℂ :=
  ∫ y : ℝ, f (y + h) * conj (g y)

theorem weightedProfile_norm (a : ℝ) (f : ℝ → ℂ) (y : ℝ) :
    ‖weightedProfile a f y‖ = Real.exp (a * |y|) * ‖f y‖ := by
  rw [weightedProfile, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem weightedNorm_nonneg (a : ℝ) (f : ℝ → ℂ) : 0 ≤ weightedNorm a f :=
  Real.sqrt_nonneg _

theorem weighted_square_integrable {a : ℝ} {f : ℝ → ℂ}
    (hf : WeightedL2 a f) : Integrable (fun y : ℝ => ‖weightedProfile a f y‖ ^ 2) :=
  hf.norm.integrable_sq

theorem weightedProfile_cancel (a : ℝ) (f : ℝ → ℂ) (y : ℝ) :
    (Real.exp (-(a * |y|)) : ℂ) * weightedProfile a f y = f y := by
  rw [weightedProfile, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
    neg_add_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]

theorem WeightedL2.aestronglyMeasurable {a : ℝ} {f : ℝ → ℂ}
    (hf : WeightedL2 a f) : AEStronglyMeasurable f := by
  have hc : Continuous (fun y : ℝ => (Real.exp (-(a * |y|)) : ℂ)) := by fun_prop
  have hh : AEStronglyMeasurable (fun y : ℝ =>
      (Real.exp (-(a * |y|)) : ℂ) * weightedProfile a f y) :=
    hc.aestronglyMeasurable.mul hf.1
  simpa only [weightedProfile_cancel] using hh

theorem WeightedL2.memLp {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : WeightedL2 a f) : MemLp f 2 := by
  apply MemLp.of_le hf (WeightedL2.aestronglyMeasurable hf)
  filter_upwards [] with y
  rw [weightedProfile_norm]
  exact le_mul_of_one_le_left (norm_nonneg _)
    (Real.one_le_exp_iff.mpr (mul_nonneg ha (abs_nonneg _)))

theorem WeightedL2.sub {a : ℝ} {f g : ℝ → ℂ}
    (hf : WeightedL2 a f) (hg : WeightedL2 a g) : WeightedL2 a (f - g) := by
  have he : weightedProfile a (f - g) = weightedProfile a f - weightedProfile a g := by
    funext y
    simp only [weightedProfile, Pi.sub_apply, mul_sub]
  rw [WeightedL2, he]
  exact MemLp.sub hf hg

theorem memLp_translate {f : ℝ → ℂ} (hf : MemLp f 2) (h : ℝ) :
    MemLp (fun y : ℝ => f (y + h)) 2 :=
  hf.comp_measurePreserving (measurePreserving_add_right volume h)

theorem weighted_product_integrable {a : ℝ} {f g : ℝ → ℂ}
    (hf : WeightedL2 a f) (hg : WeightedL2 a g) (h : ℝ) :
    Integrable (fun y : ℝ => ‖weightedProfile a f (y + h)‖ *
      ‖weightedProfile a g y‖) := by
  exact (memLp_translate hf h).norm.integrable_mul hg.norm

theorem integral_weighted_product_le {a : ℝ} {f g : ℝ → ℂ}
    (hf : WeightedL2 a f) (hg : WeightedL2 a g) (h : ℝ) :
    (∫ y : ℝ, ‖weightedProfile a f (y + h)‖ * ‖weightedProfile a g y‖) ≤
      weightedNorm a f * weightedNorm a g := by
  have hcs := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp (fun y : ℝ => weightedProfile a f (y + h)) (ENNReal.ofReal 2) by
      simpa using memLp_translate hf h)
    (show MemLp (weightedProfile a g) (ENNReal.ofReal 2) by simpa using hg)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hcs
  rw [integral_add_right_eq_self (fun y : ℝ => ‖weightedProfile a f y‖ ^ 2) h] at hcs
  simpa only [weightedNorm] using hcs

theorem correlation_integrable {a : ℝ} (ha : 0 ≤ a) {f g : ℝ → ℂ}
    (hf : WeightedL2 a f) (hg : WeightedL2 a g) (h : ℝ) :
    Integrable (fun y : ℝ => f (y + h) * conj (g y)) := by
  have hh := (memLp_translate (hf.memLp ha) h).integrable_mul (hg.memLp ha).star
  change Integrable (fun y : ℝ => f (y + h) * star (g y)) at hh
  exact hh

/-- Pointwise exponential comparison, from the triangle inequality. -/
theorem correlation_integrand_norm_le {a : ℝ} (ha : 0 ≤ a)
    (f g : ℝ → ℂ) (h y : ℝ) :
    ‖f (y + h) * conj (g y)‖ ≤ Real.exp (-a * |h|) *
      (‖weightedProfile a f (y + h)‖ * ‖weightedProfile a g y‖) := by
  have habs : |h| ≤ |y + h| + |y| := by
    calc
      |h| = |(y + h) - y| := by congr 1; ring
      _ ≤ |y + h| + |y| := abs_sub _ _
  have he : 1 ≤ Real.exp (-a * |h|) * Real.exp (a * |y + h|) *
      Real.exp (a * |y|) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left habs ha])
  rw [norm_mul, norm_conj]
  calc
    ‖f (y + h)‖ * ‖g y‖ ≤
        (Real.exp (-a * |h|) * Real.exp (a * |y + h|) * Real.exp (a * |y|)) *
          (‖f (y + h)‖ * ‖g y‖) :=
      le_mul_of_one_le_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) he
    _ = _ := by rw [weightedProfile_norm, weightedProfile_norm]; ring

theorem mixedCorrelation_norm_le {a : ℝ} (ha : 0 ≤ a) {f g : ℝ → ℂ}
    (hf : WeightedL2 a f) (hg : WeightedL2 a g) (h : ℝ) :
    ‖mixedCorrelation f g h‖ ≤
      Real.exp (-a * |h|) * (weightedNorm a f * weightedNorm a g) := by
  calc
    ‖mixedCorrelation f g h‖ ≤ ∫ y : ℝ, ‖f (y + h) * conj (g y)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ, Real.exp (-a * |h|) *
        (‖weightedProfile a f (y + h)‖ * ‖weightedProfile a g y‖) :=
      integral_mono (correlation_integrable ha hf hg h).norm
        ((weighted_product_integrable hf hg h).const_mul _)
        (correlation_integrand_norm_le ha f g h)
    _ = Real.exp (-a * |h|) *
        ∫ y : ℝ, ‖weightedProfile a f (y + h)‖ * ‖weightedProfile a g y‖ :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_weighted_product_le hf hg h)
      (Real.exp_pos _).le

theorem mixedCorrelation_self (f : ℝ → ℂ) (h : ℝ) :
    mixedCorrelation f f h = ThetaTrial.WeilFormula.correlation f h := rfl

theorem correlation_sub_eq_mixed {a : ℝ} (ha : 0 ≤ a) {f g : ℝ → ℂ}
    (hf : WeightedL2 a f) (hg : WeightedL2 a g) (h : ℝ) :
    ThetaTrial.WeilFormula.correlation f h - ThetaTrial.WeilFormula.correlation g h =
      mixedCorrelation (f - g) f h + mixedCorrelation g (f - g) h := by
  rw [ThetaTrial.WeilFormula.correlation, ThetaTrial.WeilFormula.correlation,
    ← integral_sub (correlation_integrable ha hf hf h) (correlation_integrable ha hg hg h),
    mixedCorrelation, mixedCorrelation,
    ← integral_add (correlation_integrable ha (hf.sub hg) hf h)
      (correlation_integrable ha hg (hf.sub hg) h)]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [Pi.sub_apply, map_sub]
  ring

theorem correlation_difference_norm_le {a : ℝ} (ha : 0 ≤ a) {f g : ℝ → ℂ}
    (hf : WeightedL2 a f) (hg : WeightedL2 a g) (h : ℝ) :
    ‖ThetaTrial.WeilFormula.correlation f h - ThetaTrial.WeilFormula.correlation g h‖ ≤
      Real.exp (-a * |h|) * weightedNorm a (f - g) *
        (weightedNorm a f + weightedNorm a g) := by
  rw [correlation_sub_eq_mixed ha hf hg h]
  calc
    _ ≤ ‖mixedCorrelation (f - g) f h‖ + ‖mixedCorrelation g (f - g) h‖ := norm_add_le _ _
    _ ≤ Real.exp (-a * |h|) * (weightedNorm a (f - g) * weightedNorm a f) +
        Real.exp (-a * |h|) * (weightedNorm a g * weightedNorm a (f - g)) :=
      add_le_add (mixedCorrelation_norm_le ha (hf.sub hg) hf h)
        (mixedCorrelation_norm_le ha hg (hf.sub hg) h)
    _ = _ := by ring

theorem correlation_real_part_difference_le {a : ℝ} (ha : 0 ≤ a) {f g : ℝ → ℂ}
    (hf : WeightedL2 a f) (hg : WeightedL2 a g) (h : ℝ) :
    |(ThetaTrial.WeilFormula.correlation f h).re -
      (ThetaTrial.WeilFormula.correlation g h).re| ≤
      Real.exp (-a * |h|) * weightedNorm a (f - g) *
        (weightedNorm a f + weightedNorm a g) := by
  simpa only [Complex.sub_re] using
    (Complex.abs_re_le_norm (ThetaTrial.WeilFormula.correlation f h -
      ThetaTrial.WeilFormula.correlation g h)).trans (correlation_difference_norm_le ha hf hg h)

end ThetaTrial.PrimeContinuity
