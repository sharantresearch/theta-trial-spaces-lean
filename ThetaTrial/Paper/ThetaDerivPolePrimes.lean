import ThetaTrial.Paper.GammaCross
import ThetaTrial.Paper.ThetaDerivPrimeSums
import ThetaTrial.Paper.ThetaDerivPrimeAssembly
import ThetaTrial.Paper.ThetaDerivPrimeFactor
import ThetaTrial.PrimeContinuity.Weighted
import ThetaTrial.PrimeContinuity.LogSeries
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Pole and prime estimates for two noncompact tails

The hypotheses are integral and localization bounds on the two tails. The
prime sum includes every prime power, and the crossover point `exp (2*a)`
need not be an integer.
-/

noncomputable section
open MeasureTheory Set Complex
open scoped ComplexConjugate

namespace ThetaTrial.Paper

def poleContribution (f : ℝ → ℂ) : ℝ :=
  2 * (paperFourier f (I / 2) * conj (paperFourier f (-I / 2))).re

def primeContribution (f : ℝ → ℂ) : ℝ :=
  2 * ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
    (correlation f (Real.log n)).re

def halfWeightedL1 (f : ℝ → ℂ) : ℝ :=
  ∫ u : ℝ, Real.exp (|u| / 2) * ‖f u‖

lemma halfWeightedL1_nonneg (f : ℝ → ℂ) : 0 ≤ halfWeightedL1 f :=
  integral_nonneg (fun _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))

lemma paperFourier_norm_le_halfWeightedL1 {f : ℝ → ℂ}
    (hf : Integrable (fun u : ℝ => Real.exp (|u| / 2) * ‖f u‖))
    {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖paperFourier f z‖ ≤ halfWeightedL1 f := by
  unfold paperFourier halfWeightedL1
  apply norm_integral_le_of_norm_le hf
  filter_upwards [] with u
  have he : (-I * z * (u : ℂ)).re = z.im * u := by
    simp [Complex.mul_re, Complex.mul_im]
  have hex : z.im * u ≤ |u| / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hz (abs_nonneg u)
    have hab := le_abs_self (z.im * u)
    rw [abs_mul] at hab
    nlinarith
  rw [norm_mul, Complex.norm_exp, he]
  calc
    ‖f u‖ * Real.exp (z.im * u) ≤ ‖f u‖ * Real.exp (|u| / 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hex) (norm_nonneg _)
    _ = _ := mul_comm _ _

theorem poleContribution_abs_le {f : ℝ → ℂ}
    (hf : Integrable (fun u : ℝ => Real.exp (|u| / 2) * ‖f u‖)) :
    |poleContribution f| ≤ 2 * halfWeightedL1 f ^ 2 := by
  have hp := paperFourier_norm_le_halfWeightedL1 hf
    (z := I / 2) (by norm_num)
  have hn := paperFourier_norm_le_halfWeightedL1 hf
    (z := -I / 2) (by norm_num)
  have hr := Complex.abs_re_le_norm
    (paperFourier f (I / 2) * conj (paperFourier f (-I / 2)))
  rw [norm_mul, norm_conj] at hr
  have hm := mul_le_mul hp hn (norm_nonneg _) (halfWeightedL1_nonneg f)
  unfold poleContribution
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith

theorem poleContribution_abs_le_of_concentration {f : ℝ → ℂ} {B : ℝ}
    (hf : Integrable (fun u : ℝ => Real.exp (|u| / 2) * ‖f u‖))
    (hcon : halfWeightedL1 f ^ 2 ≤ B * squaredNorm f) :
    |poleContribution f| ≤ 2 * B * squaredNorm f := by
  have h := poleContribution_abs_le hf
  nlinarith

def sourceL2Norm (f : ℝ → ℂ) : ℝ := Real.sqrt (squaredNorm f)

def rightTailL2Norm (f : ℝ → ℂ) (b : ℝ) : ℝ :=
  Real.sqrt (∫ u : ℝ in Ici b, ‖f u‖ ^ 2)

def leftTailL2Norm (f : ℝ → ℂ) (b : ℝ) : ℝ :=
  Real.sqrt (∫ u : ℝ in Iic b, ‖f u‖ ^ 2)

lemma sourceL2Norm_nonneg (f : ℝ → ℂ) : 0 ≤ sourceL2Norm f := Real.sqrt_nonneg _

lemma sourceL2Norm_sq (f : ℝ → ℂ) : sourceL2Norm f ^ 2 = squaredNorm f :=
  Real.sq_sqrt (integral_nonneg (fun u => sq_nonneg ‖f u‖))

lemma sourceL2Norm_indicator (f : ℝ → ℂ) {s : Set ℝ} (hs : MeasurableSet s) :
    sourceL2Norm (s.indicator f) = Real.sqrt (∫ u : ℝ in s, ‖f u‖ ^ 2) := by
  unfold sourceL2Norm squaredNorm
  congr 1
  have heq (u : ℝ) : ‖s.indicator f u‖ ^ 2 = s.indicator (fun u => ‖f u‖ ^ 2) u := by
    by_cases hu : u ∈ s <;> simp [hu]
  simp_rw [heq]
  exact integral_indicator hs

lemma mixedCorrelation_integrable_l2 {f g : ℝ → ℂ}
    (hf2 : MemLp f 2) (hg2 : MemLp g 2) (h : ℝ) :
    Integrable (fun u : ℝ => f (u + h) * conj (g u)) := by
  exact (hf2.comp_measurePreserving (measurePreserving_add_right volume h)).integrable_mul
    hg2.star

lemma mixedCorrelation_norm_le_l2 {f g : ℝ → ℂ}
    (hf2 : MemLp f 2) (hg2 : MemLp g 2) (h : ℝ) :
    ‖ThetaTrial.PrimeContinuity.mixedCorrelation f g h‖ ≤ sourceL2Norm f * sourceL2Norm g := by
  have hcs := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp (fun u : ℝ => f (u + h)) (ENNReal.ofReal 2) by
      simpa using ThetaTrial.PrimeContinuity.memLp_translate hf2 h)
    (show MemLp g (ENNReal.ofReal 2) by simpa using hg2)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hcs
  rw [integral_add_right_eq_self (fun u : ℝ => ‖f u‖ ^ 2) h] at hcs
  calc
    _ ≤ ∫ u : ℝ, ‖f (u + h) * conj (g u)‖ := norm_integral_le_integral_norm _
    _ = ∫ u : ℝ, ‖f (u + h)‖ * ‖g u‖ := by simp only [norm_mul, norm_conj]
    _ ≤ _ := hcs

lemma same_right_correlation_le {f : ℝ → ℂ} {a x : ℝ}
    (hf2 : MemLp f 2) (hfr : ∀ u, u ≤ a → f u = 0) :
    ‖ThetaTrial.PrimeContinuity.mixedCorrelation f f x‖ ≤
      rightTailL2Norm f (a + x) * sourceL2Norm f := by
  have heq : ThetaTrial.PrimeContinuity.mixedCorrelation f f x =
      ThetaTrial.PrimeContinuity.mixedCorrelation ((Ici (a + x)).indicator f) f x := by
    unfold ThetaTrial.PrimeContinuity.mixedCorrelation
    apply integral_congr_ae
    filter_upwards [] with u
    by_cases hu : u ≤ a
    · simp [hfr u hu]
    · have hx : u + x ∈ Ici (a + x) := by simp only [mem_Ici]; linarith
      simp [hx]
  rw [heq]
  have hb := mixedCorrelation_norm_le_l2
    (hf2.indicator (s := Ici (a + x)) measurableSet_Ici) hf2 x
  rw [sourceL2Norm_indicator f measurableSet_Ici] at hb
  exact hb

lemma same_left_correlation_le {g : ℝ → ℂ} {a x : ℝ}
    (hg2 : MemLp g 2) (hgl : ∀ u, -a ≤ u → g u = 0) :
    ‖ThetaTrial.PrimeContinuity.mixedCorrelation g g x‖ ≤
      sourceL2Norm g * leftTailL2Norm g (-a - x) := by
  have heq : ThetaTrial.PrimeContinuity.mixedCorrelation g g x =
      ThetaTrial.PrimeContinuity.mixedCorrelation g ((Iic (-a - x)).indicator g) x := by
    unfold ThetaTrial.PrimeContinuity.mixedCorrelation
    apply integral_congr_ae
    filter_upwards [] with u
    by_cases hu : -a ≤ u + x
    · simp [hgl (u + x) hu]
    · have hx : u ∈ Iic (-a - x) := by simp only [mem_Iic]; linarith
      simp [hx]
  rw [heq]
  have hb := mixedCorrelation_norm_le_l2 hg2
    (hg2.indicator (s := Iic (-a - x)) measurableSet_Iic) x
  rw [sourceL2Norm_indicator g measurableSet_Iic] at hb
  exact hb

lemma crossMagnitude_le_l2 {f g : ℝ → ℂ}
    (hf2 : MemLp f 2) (hg2 : MemLp g 2) (h : ℝ) :
    crossMagnitude f g h ≤ sourceL2Norm f * sourceL2Norm g := by
  have hcs := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp (fun u : ℝ => f (u + h)) (ENNReal.ofReal 2) by
      simpa using ThetaTrial.PrimeContinuity.memLp_translate hf2 h)
    (show MemLp g (ENNReal.ofReal 2) by simpa using hg2)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hcs
  rw [integral_add_right_eq_self (fun u : ℝ => ‖f u‖ ^ 2) h] at hcs
  exact hcs

/-- Splitting at the midpoint of the two offsets costs precisely
the two ordinary tail L2 norms. No sign or coefficient restriction occurs. -/
lemma cross_correlation_le_tail_norms {f g : ℝ → ℂ} (hf2 : MemLp f 2) (hg2 : MemLp g 2)
    (a s : ℝ) :
    ‖ThetaTrial.PrimeContinuity.mixedCorrelation f g (2 * a + s)‖ ≤
      sourceL2Norm f * leftTailL2Norm g (-a - s / 2) +
        rightTailL2Norm f (a + s / 2) * sourceL2Norm g := by
  let fr : ℝ → ℂ := (Ici (a + s / 2)).indicator f
  let gl : ℝ → ℂ := (Iic (-a - s / 2)).indicator g
  have hfr2 : MemLp fr 2 := hf2.indicator measurableSet_Ici
  have hgl2 : MemLp gl 2 := hg2.indicator measurableSet_Iic
  have hsum : Integrable (fun u : ℝ =>
      ‖f (u + (2 * a + s))‖ * ‖gl u‖ + ‖fr (u + (2 * a + s))‖ * ‖g u‖) :=
    (crossMagnitude_integrand_integrable hf2 hgl2 _).add
      (crossMagnitude_integrand_integrable hfr2 hg2 _)
  have hcmp : crossMagnitude f g (2 * a + s) ≤
      crossMagnitude f gl (2 * a + s) + crossMagnitude fr g (2 * a + s) := by
    unfold crossMagnitude
    rw [← integral_add (crossMagnitude_integrand_integrable hf2 hgl2 _)
      (crossMagnitude_integrand_integrable hfr2 hg2 _)]
    apply integral_mono (crossMagnitude_integrand_integrable hf2 hg2 _) hsum
    intro u
    dsimp only
    by_cases hu : u ≤ -a - s / 2
    · have heq : gl u = g u := by simp [gl, hu]
      rw [heq]
      exact le_add_of_nonneg_right (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    · have hv : a + s / 2 ≤ u + (2 * a + s) := by linarith
      have heq : fr (u + (2 * a + s)) = f (u + (2 * a + s)) := by simp [fr, hv]
      rw [heq]
      exact le_add_of_nonneg_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hb1 := crossMagnitude_le_l2 hf2 hgl2 (2 * a + s)
  have hb2 := crossMagnitude_le_l2 hfr2 hg2 (2 * a + s)
  have hglNorm : sourceL2Norm gl = leftTailL2Norm g (-a - s / 2) :=
    sourceL2Norm_indicator g measurableSet_Iic
  have hfrNorm : sourceL2Norm fr = rightTailL2Norm f (a + s / 2) :=
    sourceL2Norm_indicator f measurableSet_Ici
  rw [hglNorm] at hb1
  rw [hfrNorm] at hb2
  calc
    _ ≤ crossMagnitude f g (2 * a + s) := by
      simpa only [ThetaTrial.PrimeContinuity.mixedCorrelation, crossMagnitude, norm_mul, norm_conj]
        using norm_integral_le_integral_norm (fun u : ℝ => f (u + (2 * a + s)) * conj (g u))
    _ ≤ _ := hcmp.trans (add_le_add hb1 hb2)

lemma cross_correlation_zero_before_gap {f g : ℝ → ℂ} {a x : ℝ}
    (hfr : ∀ u, u ≤ a → f u = 0) (hgl : ∀ u, -a ≤ u → g u = 0)
    (hx : x ≤ 2 * a) : ThetaTrial.PrimeContinuity.mixedCorrelation f g x = 0 := by
  unfold ThetaTrial.PrimeContinuity.mixedCorrelation
  simp_rw [separated_cross_zero hfr hgl hx]
  exact integral_zero _ _

lemma reverse_cross_correlation_zero {f g : ℝ → ℂ} {a x : ℝ}
    (ha : 0 ≤ a) (hfr : ∀ u, u ≤ a → f u = 0)
    (hgl : ∀ u, -a ≤ u → g u = 0) (hx : 0 ≤ x) :
    ThetaTrial.PrimeContinuity.mixedCorrelation g f x = 0 := by
  unfold ThetaTrial.PrimeContinuity.mixedCorrelation
  have heq (u : ℝ) : g (u + x) * conj (f u) = 0 := by
    by_cases hu : u ≤ a
    · simp [hfr u hu]
    · simp [hgl (u + x) (by linarith)]
  simp_rw [heq]
  exact integral_zero _ _

def survivalDecay (T s : ℝ) : ℝ := Real.exp (-(T / 8) * (Real.exp (2 * s) - 1))

/-- Ordinary tail L2 localization, in norm rather than squared-norm form. -/
def TwoTailSurvival (f g : ℝ → ℂ) (a T s₀ : ℝ) : Prop :=
  ∀ s : ℝ, s₀ ≤ s →
    rightTailL2Norm f (a + s) ≤ sourceL2Norm f * survivalDecay T s ∧
    leftTailL2Norm g (-a - s) ≤ sourceL2Norm g * survivalDecay T s

lemma sqrt_le_survivalDecay {A B T s : ℝ} (hA : 0 ≤ A)
    (hB : B ≤ A * Real.exp (-(T / 4) * (Real.exp (2 * s) - 1))) :
    Real.sqrt B ≤ Real.sqrt A * survivalDecay T s := by
  apply (Real.sqrt_le_left (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)).mpr
  have hs : survivalDecay T s ^ 2 = Real.exp (-(T / 4) * (Real.exp (2 * s) - 1)) := by
    unfold survivalDecay
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, Real.sq_sqrt hA]
  change B ≤ A * survivalDecay T s ^ 2
  rw [hs]
  exact hB

/-- Converts the squared survival estimates of the tails into the form used
here; open and closed endpoints differ by a null set. -/
theorem twoTailSurvival_of_squared {f g : ℝ → ℂ} {a T s₀ : ℝ}
    (hF : ∀ s : ℝ, s₀ ≤ s → (∫ u : ℝ in Ioi (a + s), ‖f u‖ ^ 2) ≤
      squaredNorm f * Real.exp (-(T / 4) * (Real.exp (2 * s) - 1)))
    (hG : ∀ s : ℝ, s₀ ≤ s → (∫ u : ℝ in Iio (-a - s), ‖g u‖ ^ 2) ≤
      squaredNorm g * Real.exp (-(T / 4) * (Real.exp (2 * s) - 1))) :
    TwoTailSurvival f g a T s₀ := by
  intro s hs
  constructor
  · unfold rightTailL2Norm sourceL2Norm
    rw [integral_Ici_eq_integral_Ioi]
    exact sqrt_le_survivalDecay (integral_nonneg (fun u => sq_nonneg ‖f u‖)) (hF s hs)
  · unfold leftTailL2Norm sourceL2Norm
    rw [integral_Iic_eq_integral_Iio]
    exact sqrt_le_survivalDecay (integral_nonneg (fun u => sq_nonneg ‖g u‖)) (hG s hs)

lemma same_correlations_le_survival {f g : ℝ → ℂ} {a T s₀ x : ℝ}
    (hf2 : MemLp f 2) (hg2 : MemLp g 2)
    (hfr : ∀ u, u ≤ a → f u = 0) (hgl : ∀ u, -a ≤ u → g u = 0)
    (hs : TwoTailSurvival f g a T s₀) (hx : s₀ ≤ x) :
    ‖ThetaTrial.PrimeContinuity.mixedCorrelation f f x‖ +
      ‖ThetaTrial.PrimeContinuity.mixedCorrelation g g x‖ ≤
        (squaredNorm f + squaredNorm g) * survivalDecay T x := by
  have hloc := hs x hx
  have hF := (same_right_correlation_le hf2 hfr).trans
    (mul_le_mul_of_nonneg_right hloc.1 (sourceL2Norm_nonneg f))
  have hG := (same_left_correlation_le hg2 hgl).trans
    (mul_le_mul_of_nonneg_left hloc.2 (sourceL2Norm_nonneg g))
  calc
    _ ≤ sourceL2Norm f * survivalDecay T x * sourceL2Norm f +
        sourceL2Norm g * (sourceL2Norm g * survivalDecay T x) := add_le_add hF hG
    _ = (sourceL2Norm f ^ 2 + sourceL2Norm g ^ 2) * survivalDecay T x := by ring
    _ = _ := by rw [sourceL2Norm_sq, sourceL2Norm_sq]

lemma cross_correlation_le_survival {f g : ℝ → ℂ} {a T s₀ s : ℝ}
    (hf2 : MemLp f 2) (hg2 : MemLp g 2)
    (hs : TwoTailSurvival f g a T s₀) (hs₀ : 2 * s₀ ≤ s) :
    ‖ThetaTrial.PrimeContinuity.mixedCorrelation f g (2 * a + s)‖ ≤
      2 * (sourceL2Norm f * sourceL2Norm g) *
        Real.exp (-(T / 8) * (Real.exp s - 1)) := by
  have hloc := hs (s / 2) (by linarith)
  have hF := mul_le_mul_of_nonneg_right hloc.1 (sourceL2Norm_nonneg g)
  have hG := mul_le_mul_of_nonneg_left hloc.2 (sourceL2Norm_nonneg f)
  have hc := cross_correlation_le_tail_norms hf2 hg2 a s
  unfold survivalDecay at hF hG
  have heq : 2 * (s / 2) = s := by ring
  rw [heq] at hF hG
  nlinarith

lemma correlation_add_four {f g : ℝ → ℂ} (hf2 : MemLp f 2) (hg2 : MemLp g 2) (x : ℝ) :
    correlation (fun u => f u + g u) x =
      (ThetaTrial.PrimeContinuity.mixedCorrelation f f x + ThetaTrial.PrimeContinuity.mixedCorrelation g g x) +
      (ThetaTrial.PrimeContinuity.mixedCorrelation f g x + ThetaTrial.PrimeContinuity.mixedCorrelation g f x) := by
  rw [correlation_eq_weilFormula]
  change ThetaTrial.PrimeContinuity.mixedCorrelation (fun u => f u + g u) (fun u => f u + g u) x = _
  unfold ThetaTrial.PrimeContinuity.mixedCorrelation
  have heq (u : ℝ) : (f (u + x) + g (u + x)) * conj (f u + g u) =
      (f (u + x) * conj (f u) + g (u + x) * conj (g u)) +
      (f (u + x) * conj (g u) + g (u + x) * conj (f u)) := by
    rw [map_add]
    ring
  simp_rw [heq]
  have hsame : Integrable (fun u => f (u + x) * conj (f u) + g (u + x) * conj (g u)) :=
    (mixedCorrelation_integrable_l2 hf2 hf2 x).add (mixedCorrelation_integrable_l2 hg2 hg2 x)
  have hcross : Integrable (fun u => f (u + x) * conj (g u) + g (u + x) * conj (f u)) :=
    (mixedCorrelation_integrable_l2 hf2 hg2 x).add (mixedCorrelation_integrable_l2 hg2 hf2 x)
  rw [integral_add hsame hcross,
    integral_add (mixedCorrelation_integrable_l2 hf2 hf2 x) (mixedCorrelation_integrable_l2 hg2 hg2 x),
    integral_add (mixedCorrelation_integrable_l2 hf2 hg2 x) (mixedCorrelation_integrable_l2 hg2 hf2 x)]

def mangoldtWeight (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n / Real.sqrt n

lemma mangoldtWeight_nonneg (n : ℕ) : 0 ≤ mangoldtWeight n :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

lemma mangoldtWeight_le_log (n : ℕ) : mangoldtWeight n ≤ Real.log n / Real.sqrt n :=
  div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (Real.sqrt_nonneg _)

lemma mangoldtWeight_eq_zero_of_lt_two {n : ℕ} (hn : n < 2) : mangoldtWeight n = 0 := by
  interval_cases n <;> simp [mangoldtWeight]

lemma mangoldtWeight_le_exp_log {a : ℝ} {n : ℕ} (_hn : 2 ≤ n)
    (hN : Real.exp (2 * a) ≤ (n : ℝ)) :
    mangoldtWeight n ≤ Real.exp (-a) * Real.log n := by
  have hs : Real.exp a ≤ Real.sqrt (n : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    have he : Real.exp a ^ 2 = Real.exp (2 * a) := by
      rw [show 2 * a = a + a by ring, Real.exp_add]
      ring
    rw [he]
    exact hN
  calc
    _ ≤ Real.log n / Real.sqrt n := mangoldtWeight_le_log n
    _ ≤ Real.log n / Real.exp a :=
      div_le_div_of_nonneg_left (Real.log_natCast_nonneg n) (Real.exp_pos a) hs
    _ = _ := by rw [Real.exp_neg]; ring

lemma log_le_crossover_offset {a : ℝ} (ha : 0 ≤ a) {n : ℕ}
    (hN : Real.exp (2 * a) ≤ (n : ℝ)) :
    Real.log n ≤ 2 * a + ((n : ℝ) - Real.exp (2 * a)) := by
  have hNp : 0 < Real.exp (2 * a) := Real.exp_pos _
  have hn : 0 < (n : ℝ) := lt_of_lt_of_le hNp hN
  have hN1 : 1 ≤ Real.exp (2 * a) := Real.one_le_exp_iff.mpr (by linarith)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hn hNp)
  rw [Real.log_div hn.ne' hNp.ne', Real.log_exp] at hlog
  have hdiv : (n : ℝ) / Real.exp (2 * a) - 1 ≤ (n : ℝ) - Real.exp (2 * a) := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hNp).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hN) (sub_nonneg.mpr hN1)]
  linarith

lemma mangoldtWeight_le_outer {a : ℝ} (ha : 0 ≤ a) {n : ℕ} (hn : 2 ≤ n)
    (hN : Real.exp (2 * a) ≤ (n : ℝ)) :
    mangoldtWeight n ≤ Real.exp (-a) * (2 * a + ((n : ℝ) - Real.exp (2 * a))) :=
  (mangoldtWeight_le_exp_log hn hN).trans
    (mul_le_mul_of_nonneg_left (log_le_crossover_offset ha hN) (Real.exp_pos _).le)

lemma mangoldtWeight_le_central {a s : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hN : Real.exp (2 * a) ≤ (n : ℝ))
    (hB : (n : ℝ) ≤ Real.exp (2 * a) * Real.exp (2 * s)) :
    mangoldtWeight n ≤ Real.exp (-a) * (2 * a + 2 * s) := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hn)
  have hl := Real.log_le_log hnp hB
  rw [Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp] at hl
  exact (mangoldtWeight_le_exp_log hn hN).trans
    (mul_le_mul_of_nonneg_left hl (Real.exp_pos _).le)

lemma crossover_decay_exact (a : ℝ) {n : ℕ} (hn : 0 < n) :
    (scaleT a / 8) * (Real.exp (Real.log n - 2 * a) - 1) =
      (Real.pi / 4) * ((n : ℝ) - Real.exp (2 * a)) := by
  have hnp : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [Real.exp_sub, Real.exp_log hnp]
  unfold scaleT scaleZ
  field_simp
  ring

lemma survivalDecay_log_bound {T : ℝ} (hT : 1 ≤ T) {n : ℕ} (hn : 2 ≤ n) :
    survivalDecay T (Real.log n) ≤ Real.exp (-3 * T / 8) *
      Real.exp (-(((n : ℝ) ^ 2 - 4) / 8)) := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hn)
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have he : Real.exp (2 * Real.log (n : ℝ)) = (n : ℝ) ^ 2 := by
    rw [show 2 * Real.log (n : ℝ) = Real.log n + Real.log n by ring,
      Real.exp_add, Real.exp_log hnp]
    ring
  unfold survivalDecay
  rw [he, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hn4 : 0 ≤ (n : ℝ) ^ 2 - 4 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hT) hn4]

lemma same_prime_correlations_bound {f g : ℝ → ℂ} {a T s₀ : ℝ}
    (hf2 : MemLp f 2) (hg2 : MemLp g 2)
    (hfr : ∀ u, u ≤ a → f u = 0) (hgl : ∀ u, -a ≤ u → g u = 0)
    (hs : TwoTailSurvival f g a T s₀) (hs₀ : s₀ ≤ Real.log 2)
    (hT : 1 ≤ T) {n : ℕ} (hn : 2 ≤ n) :
    mangoldtWeight n * (‖ThetaTrial.PrimeContinuity.mixedCorrelation f f (Real.log n)‖ +
      ‖ThetaTrial.PrimeContinuity.mixedCorrelation g g (Real.log n)‖) ≤
      ((squaredNorm f + squaredNorm g) * Real.exp (-3 * T / 8)) *
        ThetaDerivPrimeSums.diagonalKernel n := by
  have hlog : s₀ ≤ Real.log (n : ℝ) := hs₀.trans
    (Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hn))
  have hcorr := same_correlations_le_survival hf2 hg2 hfr hgl hs hlog
  have hA : 0 ≤ squaredNorm f + squaredNorm g :=
    add_nonneg (integral_nonneg (fun u => sq_nonneg ‖f u‖))
      (integral_nonneg (fun u => sq_nonneg ‖g u‖))
  have hw : 0 ≤ Real.log (n : ℝ) / Real.sqrt n :=
    div_nonneg (Real.log_natCast_nonneg n) (Real.sqrt_nonneg _)
  have hfirst := mul_le_mul (mangoldtWeight_le_log n) hcorr
    (add_nonneg (norm_nonneg _) (norm_nonneg _)) hw
  have hsecond := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (survivalDecay_log_bound hT hn) hA) hw
  unfold ThetaDerivPrimeSums.diagonalKernel
  rw [if_pos hn]
  nlinarith [hfirst, hsecond]

lemma cross_prime_before_crossover {f g : ℝ → ℂ} {a : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hfr : ∀ u, u ≤ a → f u = 0) (hgl : ∀ u, -a ≤ u → g u = 0)
    (hN : (n : ℝ) ≤ Real.exp (2 * a)) :
    ThetaTrial.PrimeContinuity.mixedCorrelation f g (Real.log n) = 0 := by
  apply cross_correlation_zero_before_gap hfr hgl
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hn)
  have hl := Real.log_le_log hnp hN
  rwa [Real.log_exp] at hl

lemma cross_prime_outer_bound {f g : ℝ → ℂ} {a s₀ : ℝ}
    (hf2 : MemLp f 2) (hg2 : MemLp g 2) (ha : 0 ≤ a) (hs₀ : 0 ≤ s₀)
    (hs : TwoTailSurvival f g a (scaleT a) s₀) {n : ℕ} (hn : 2 ≤ n)
    (hB : Real.exp (2 * a) * Real.exp (2 * s₀) < (n : ℝ)) :
    mangoldtWeight n * ‖ThetaTrial.PrimeContinuity.mixedCorrelation f g (Real.log n)‖ ≤
      (2 * (sourceL2Norm f * sourceL2Norm g) * Real.exp (-a)) *
        ThetaDerivPrimeSums.integerCrossoverTerm (Real.exp (2 * a)) (Real.pi / 4) (2 * a) n := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hn)
  have hE : 1 ≤ Real.exp (2 * s₀) := Real.one_le_exp_iff.mpr (by linarith)
  have hN : Real.exp (2 * a) < (n : ℝ) :=
    lt_of_le_of_lt (le_mul_of_one_le_right (Real.exp_pos _).le hE) hB
  have hlog := Real.log_lt_log (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hB
  rw [Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp] at hlog
  have hc := cross_correlation_le_survival hf2 hg2 hs
    (s := Real.log n - 2 * a) (by linarith)
  have he : 2 * a + (Real.log (n : ℝ) - 2 * a) = Real.log n := by ring
  rw [he, neg_mul, crossover_decay_exact a (lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hn)] at hc
  have hw := mangoldtWeight_le_outer ha hn hN.le
  have hw0 : 0 ≤ Real.exp (-a) * (2 * a + ((n : ℝ) - Real.exp (2 * a))) := by
    apply mul_nonneg (Real.exp_pos _).le
    linarith
  have hb := mul_le_mul hw hc (norm_nonneg _) hw0
  unfold ThetaDerivPrimeSums.integerCrossoverTerm
  rw [if_pos hN, neg_mul]
  nlinarith [hb]

lemma crossoverTerm_nonneg {N c B : ℝ} (hB : 0 ≤ B) (n : ℕ) :
    0 ≤ ThetaDerivPrimeSums.integerCrossoverTerm N c B n := by
  unfold ThetaDerivPrimeSums.integerCrossoverTerm
  split_ifs with hn
  · exact mul_nonneg (by linarith) (Real.exp_pos _).le
  · rfl

lemma cross_prime_complete_envelope {f g : ℝ → ℂ} {a s₀ : ℝ}
    (hf2 : MemLp f 2) (hg2 : MemLp g 2) (ha : 0 ≤ a) (hs₀ : 0 ≤ s₀)
    (hfr : ∀ u, u ≤ a → f u = 0) (hgl : ∀ u, -a ≤ u → g u = 0)
    (hs : TwoTailSurvival f g a (scaleT a) s₀) {n : ℕ} (hn : 2 ≤ n) :
    mangoldtWeight n * ‖ThetaTrial.PrimeContinuity.mixedCorrelation f g (Real.log n)‖ ≤
      ((sourceL2Norm f * sourceL2Norm g) * Real.exp (-a) * (2 * a + 2 * s₀)) *
        (if n ∈ ThetaDerivPrimeSums.centralBand (Real.exp (2 * a))
          (Real.exp (2 * a) * Real.exp (2 * s₀)) then 1 else 0) +
      (2 * (sourceL2Norm f * sourceL2Norm g) * Real.exp (-a)) *
        ThetaDerivPrimeSums.integerCrossoverTerm (Real.exp (2 * a)) (Real.pi / 4) (2 * a) n := by
  have hA : 0 ≤ sourceL2Norm f * sourceL2Norm g :=
    mul_nonneg (sourceL2Norm_nonneg f) (sourceL2Norm_nonneg g)
  have hcentral : 0 ≤ ((sourceL2Norm f * sourceL2Norm g) * Real.exp (-a) * (2 * a + 2 * s₀)) *
      (if n ∈ ThetaDerivPrimeSums.centralBand (Real.exp (2 * a))
        (Real.exp (2 * a) * Real.exp (2 * s₀)) then 1 else 0) := by
    positivity
  have houter : 0 ≤ (2 * (sourceL2Norm f * sourceL2Norm g) * Real.exp (-a)) *
      ThetaDerivPrimeSums.integerCrossoverTerm (Real.exp (2 * a)) (Real.pi / 4) (2 * a) n := by
    exact mul_nonneg (by positivity) (crossoverTerm_nonneg (by linarith) n)
  by_cases hN : (n : ℝ) ≤ Real.exp (2 * a)
  · rw [cross_prime_before_crossover hn hfr hgl hN, norm_zero, mul_zero]
    exact add_nonneg hcentral houter
  by_cases hB : (n : ℝ) ≤ Real.exp (2 * a) * Real.exp (2 * s₀)
  · have hmem : n ∈ ThetaDerivPrimeSums.centralBand (Real.exp (2 * a))
        (Real.exp (2 * a) * Real.exp (2 * s₀)) := by
      apply (ThetaDerivPrimeSums.mem_centralBand (by positivity) n).mpr
      exact ⟨le_of_not_ge hN, hB⟩
    rw [if_pos hmem, mul_one]
    have hw := mangoldtWeight_le_central hn (le_of_not_ge hN) hB
    have hc := mixedCorrelation_norm_le_l2 hf2 hg2 (Real.log n)
    have hp := mul_le_mul hw hc (norm_nonneg _)
      (mul_nonneg (Real.exp_pos _).le (by linarith))
    nlinarith [hp]
  · have hb := cross_prime_outer_bound hf2 hg2 ha hs₀ hs hn (lt_of_not_ge hB)
    exact hb.trans (le_add_of_nonneg_left hcentral)

lemma scaleT_ge_one {a : ℝ} (ha : 0 ≤ a) : 1 ≤ scaleT a := by
  have he : 1 ≤ Real.exp (2 * a) := Real.one_le_exp_iff.mpr (by linarith)
  unfold scaleT scaleZ
  nlinarith [Real.pi_gt_three]

lemma full_prime_term_envelope {f g : ℝ → ℂ} {a s₀ : ℝ}
    (hf2 : MemLp f 2) (hg2 : MemLp g 2) (ha : 0 ≤ a) (hs₀ : 0 ≤ s₀)
    (hslog : s₀ ≤ Real.log 2)
    (hfr : ∀ u, u ≤ a → f u = 0) (hgl : ∀ u, -a ≤ u → g u = 0)
    (hs : TwoTailSurvival f g a (scaleT a) s₀) (n : ℕ) :
    |mangoldtWeight n * (correlation (fun u => f u + g u) (Real.log n)).re| ≤
      ((squaredNorm f + squaredNorm g) * Real.exp (-3 * scaleT a / 8)) *
        ThetaDerivPrimeSums.diagonalKernel n +
      ((sourceL2Norm f * sourceL2Norm g) * Real.exp (-a) * (2 * a + 2 * s₀)) *
        (if n ∈ ThetaDerivPrimeSums.centralBand (Real.exp (2 * a))
          (Real.exp (2 * a) * Real.exp (2 * s₀)) then 1 else 0) +
      (2 * (sourceL2Norm f * sourceL2Norm g) * Real.exp (-a)) *
        ThetaDerivPrimeSums.integerCrossoverTerm (Real.exp (2 * a)) (Real.pi / 4) (2 * a) n := by
  by_cases hn : 2 ≤ n
  · have hsame := same_prime_correlations_bound hf2 hg2 hfr hgl hs hslog (scaleT_ge_one ha) hn
    have hcross := cross_prime_complete_envelope hf2 hg2 ha hs₀ hfr hgl hs hn
    have hnorm : ‖correlation (fun u => f u + g u) (Real.log n)‖ ≤
        ‖ThetaTrial.PrimeContinuity.mixedCorrelation f f (Real.log n)‖ +
        ‖ThetaTrial.PrimeContinuity.mixedCorrelation g g (Real.log n)‖ +
        ‖ThetaTrial.PrimeContinuity.mixedCorrelation f g (Real.log n)‖ := by
      rw [correlation_add_four hf2 hg2,
        reverse_cross_correlation_zero ha hfr hgl (Real.log_natCast_nonneg n), add_zero]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    have habs := (Complex.abs_re_le_norm
      (correlation (fun u => f u + g u) (Real.log n))).trans hnorm
    rw [abs_mul, abs_of_nonneg (mangoldtWeight_nonneg n)]
    have hm := mul_le_mul_of_nonneg_left habs (mangoldtWeight_nonneg n)
    nlinarith [hsame, hcross, hm]
  · rw [mangoldtWeight_eq_zero_of_lt_two (lt_of_not_ge hn), zero_mul, abs_zero]
    have hD := ThetaDerivPrimeSums.diagonalKernel_nonneg n
    have hA : 0 ≤ squaredNorm f + squaredNorm g :=
      add_nonneg (integral_nonneg (fun u => sq_nonneg ‖f u‖))
        (integral_nonneg (fun u => sq_nonneg ‖g u‖))
    have hc := crossoverTerm_nonneg (N := Real.exp (2 * a)) (c := Real.pi / 4)
      (show 0 ≤ 2 * a by linarith) n
    have hF := sourceL2Norm_nonneg f
    have hG := sourceL2Norm_nonneg g
    positivity

/-- Absolute convergence of the prime sum, from the survival estimate. -/
theorem fullPrime_absolutely_summable_of_twoTail {f g : ℝ → ℂ} {a s₀ : ℝ}
    (hf2 : MemLp f 2) (hg2 : MemLp g 2) (ha : 0 ≤ a) (hs₀ : 0 ≤ s₀)
    (hslog : s₀ ≤ Real.log 2)
    (hfr : ∀ u, u ≤ a → f u = 0) (hgl : ∀ u, -a ≤ u → g u = 0)
    (hs : TwoTailSurvival f g a (scaleT a) s₀) :
    Summable (fun n : ℕ => |(ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
      (correlation (fun u => f u + g u) (Real.log n)).re|) := by
  exact ThetaDerivPrimeAssembly.prime_absolutely_summable_of_envelope
    (by positivity) (by positivity) (show 0 ≤ 2 * a by linarith)
    (full_prime_term_envelope hf2 hg2 ha hs₀ hslog hfr hgl hs)

/-- The arithmetic bound before harmless constant
simplifications. Its three terms are the two same-edge correlations, the
finite crossover band, and the entire infinite range above that band. -/
theorem primeContribution_abs_le_twoTail_explicit {f g : ℝ → ℂ} {a s₀ : ℝ}
    (hf2 : MemLp f 2) (hg2 : MemLp g 2) (ha : 0 ≤ a) (hs₀ : 0 ≤ s₀)
    (hslog : s₀ ≤ Real.log 2)
    (hfr : ∀ u, u ≤ a → f u = 0) (hgl : ∀ u, -a ≤ u → g u = 0)
    (hs : TwoTailSurvival f g a (scaleT a) s₀) :
    |primeContribution (fun u => f u + g u)| ≤
      2 * (((squaredNorm f + squaredNorm g) * Real.exp (-3 * scaleT a / 8)) *
        ThetaDerivPrimeSums.diagonalKernelSum +
      ((sourceL2Norm f * sourceL2Norm g) * Real.exp (-a) * (2 * a + 2 * s₀)) *
        (Real.exp (2 * a) * Real.exp (2 * s₀) - Real.exp (2 * a) + 1) +
      (2 * (sourceL2Norm f * sourceL2Norm g) * Real.exp (-a)) *
        ThetaDerivPrimeSums.exponentialTailBound (Real.pi / 4) (2 * a)) := by
  have hN : Real.exp (2 * a) ≤ Real.exp (2 * a) * Real.exp (2 * s₀) :=
    le_mul_of_one_le_right (Real.exp_pos _).le
      (Real.one_le_exp_iff.mpr (by linarith))
  have hF := sourceL2Norm_nonneg f
  have hG := sourceL2Norm_nonneg g
  exact ThetaDerivPrimeAssembly.prime_sum_bound_interval_of_envelope
    (by positivity) hN (by positivity) (show 0 ≤ 2 * a by linarith)
    (by positivity) (by positivity)
    (full_prime_term_envelope hf2 hg2 ha hs₀ hslog hfr hgl hs)

theorem primeContribution_abs_le_factor {f g : ℝ → ℂ} {a s₀ : ℝ}
    (hf2 : MemLp f 2) (hg2 : MemLp g 2) (ha : 0 ≤ a) (hs₀ : 0 ≤ s₀)
    (hslog : s₀ ≤ Real.log 2)
    (hfr : ∀ u, u ≤ a → f u = 0) (hgl : ∀ u, -a ≤ u → g u = 0)
    (hs : TwoTailSurvival f g a (scaleT a) s₀) :
    |primeContribution (fun u => f u + g u)| ≤
      primeTailFactor a s₀ * squaredNorm (fun u => f u + g u) := by
  have hp := primeContribution_abs_le_twoTail_explicit hf2 hg2 ha hs₀ hslog hfr hgl hs
  have hmass : 2 * (sourceL2Norm f * sourceL2Norm g) ≤ squaredNorm f + squaredNorm g := by
    nlinarith [sq_nonneg (sourceL2Norm f - sourceL2Norm g), sourceL2Norm_sq f, sourceL2Norm_sq g]
  have hwidth : 0 ≤ Real.exp (2 * a) * Real.exp (2 * s₀) - Real.exp (2 * a) + 1 := by
    have hN : Real.exp (2 * a) ≤ Real.exp (2 * a) * Real.exp (2 * s₀) :=
      le_mul_of_one_le_right (Real.exp_pos _).le
        (Real.one_le_exp_iff.mpr (by linarith))
    linarith
  have hgeo := prime_exponentialTailBound_nonneg (show 0 < Real.pi / 4 by positivity)
    (show 0 ≤ 2 * a by linarith)
  have hb := mul_le_mul_of_nonneg_right hmass
    (show 0 ≤ Real.exp (-a) * (2 * a + 2 * s₀) *
      (Real.exp (2 * a) * Real.exp (2 * s₀) - Real.exp (2 * a) + 1) by positivity)
  have ho := mul_le_mul_of_nonneg_right hmass
    (show 0 ≤ 2 * Real.exp (-a) * ThetaDerivPrimeSums.exponentialTailBound (Real.pi / 4) (2 * a) by positivity)
  rw [separated_squaredNorm hf2 hg2 ha hfr hgl]
  unfold primeTailFactor
  nlinarith [hp, hb, ho]

theorem primeContribution_abs_le_of_width {f g : ℝ → ℂ} {a s₀ M K : ℝ}
    (hf2 : MemLp f 2) (hg2 : MemLp g 2) (ha : 1 ≤ a) (hs₀ : 0 ≤ s₀)
    (hslog : s₀ ≤ Real.log 2) (hM : 1 ≤ M) (hK : 0 ≤ K)
    (hwidth : Real.exp (2 * a) * s₀ ≤ K * M)
    (hfr : ∀ u, u ≤ a → f u = 0) (hgl : ∀ u, -a ≤ u → g u = 0)
    (hs : TwoTailSurvival f g a (scaleT a) s₀) :
    |primeContribution (fun u => f u + g u)| ≤
      primeTailConstant * (1 + K) * M * a * Real.exp (-a) *
        squaredNorm (fun u => f u + g u) := by
  have ha0 : 0 ≤ a := by linarith
  have hs1 : s₀ ≤ 1 := by
    have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hS : 0 ≤ squaredNorm (fun u => f u + g u) :=
    integral_nonneg (fun u => sq_nonneg ‖f u + g u‖)
  have hfac := mul_le_mul_of_nonneg_right (primeTailFactor_le ha hs₀ hs1) hS
  have hw : 1 + Real.exp (2 * a) * s₀ ≤ (1 + K) * M := by nlinarith
  have hC := primeTailConstant_nonneg
  have hmul := mul_le_mul_of_nonneg_right hw
    (show 0 ≤ primeTailConstant * a * Real.exp (-a) *
      squaredNorm (fun u => f u + g u) by positivity)
  have hp := primeContribution_abs_le_factor hf2 hg2 ha0 hs₀ hslog hfr hgl hs
  nlinarith [hp, hfac, hmul]

/-- The pole and prime estimate of Lemma `deriv:pole-primes`, from weighted L1
concentration and localization of the two tails. The crossover `exp (2*a)`
need not be an integer. -/
theorem pole_prime_bound_of_twoTail {f g : ℝ → ℂ} {a s₀ M K B : ℝ}
    (hf2 : MemLp f 2) (hg2 : MemLp g 2) (ha : 1 ≤ a) (hs₀ : 0 ≤ s₀)
    (hslog : s₀ ≤ Real.log 2) (hM : 1 ≤ M) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hwidth : Real.exp (2 * a) * s₀ ≤ K * M)
    (hfr : ∀ u, u ≤ a → f u = 0) (hgl : ∀ u, -a ≤ u → g u = 0)
    (hs : TwoTailSurvival f g a (scaleT a) s₀)
    (hwi : Integrable (fun u : ℝ => Real.exp (|u| / 2) * ‖f u + g u‖))
    (hw : halfWeightedL1 (fun u => f u + g u) ^ 2 ≤
      B * M * Real.exp (-a) * squaredNorm (fun u => f u + g u)) :
    |poleContribution (fun u => f u + g u)| + |primeContribution (fun u => f u + g u)| ≤
      (2 * B + primeTailConstant * (1 + K)) * M * a * Real.exp (-a) *
        squaredNorm (fun u => f u + g u) := by
  have hr := primeContribution_abs_le_of_width hf2 hg2 ha hs₀ hslog hM hK hwidth hfr hgl hs
  have hp := poleContribution_abs_le hwi
  have hS : 0 ≤ squaredNorm (fun u => f u + g u) :=
    integral_nonneg (fun u => sq_nonneg ‖f u + g u‖)
  have hbase : 0 ≤ B * M * Real.exp (-a) * squaredNorm (fun u => f u + g u) := by positivity
  have hmul := le_mul_of_one_le_right hbase ha
  nlinarith [hr, hp, hw, hmul]

#print axioms twoTailSurvival_of_squared
#print axioms full_prime_term_envelope
#print axioms fullPrime_absolutely_summable_of_twoTail
#print axioms primeContribution_abs_le_twoTail_explicit
#print axioms primeContribution_abs_le_factor
#print axioms primeContribution_abs_le_of_width
#print axioms pole_prime_bound_of_twoTail

end ThetaTrial.Paper
