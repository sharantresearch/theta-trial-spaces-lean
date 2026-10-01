import ThetaTrial.Paper.WeightedBVMeasure
import ThetaTrial.Paper.ThetaDerivPolynomialRegularity
import ThetaTrial.Paper.ThetaDerivSourceLocalization
import ThetaTrial.Paper.WindowFormBounds

/-! Absolute convergence of the complex prime series in the paper. The
interchange of real part and `tsum` uses summability of the complex norms. -/

noncomputable section
open Complex MeasureTheory Set Filter Polynomial
open ThetaTrial.PrimeContinuity
open scoped ComplexConjugate

namespace ThetaTrial.Paper

def complexPrimeTerm (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
    correlation f (Real.log n)

@[simp] theorem complexPrimeTerm_zero (f : ℝ → ℂ) : complexPrimeTerm f 0 = 0 := by
  simp [complexPrimeTerm]

@[simp] theorem complexPrimeTerm_one (f : ℝ → ℂ) : complexPrimeTerm f 1 = 0 := by
  simp [complexPrimeTerm]

theorem complexPrime_tsum_eq_from_two (f : ℝ → ℂ) :
    (∑' n : ℕ, complexPrimeTerm f n) =
      ∑' n : {n : ℕ // 2 ≤ n}, complexPrimeTerm f n := by
  symm
  apply tsum_subtype_eq_of_support_subset
  intro n hn
  by_contra h
  change ¬ 2 ≤ n at h
  change complexPrimeTerm f n ≠ 0 at hn
  have hn01 : n = 0 ∨ n = 1 := by omega
  rcases hn01 with rfl | rfl <;> simp at hn

theorem complexPrimeTerm_norm (f : ℝ → ℂ) (n : ℕ) :
    ‖complexPrimeTerm f n‖ = (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
      ‖correlation f (Real.log n)‖ := by
  have hc : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  simp only [complexPrimeTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hc]

theorem complexPrimeTerm_norm_le {a : ℝ} (ha : 1 / 2 < a) {f : ℝ → ℂ}
    (hf : WeightedL2 a f) (n : {n : ℕ // 2 ≤ n}) :
    ‖complexPrimeTerm f n‖ ≤ logMajorant a n * (weightedNorm a f * weightedNorm a f) := by
  have ha0 : 0 ≤ a := by linarith
  have hc : 0 ≤ ArithmeticFunction.vonMangoldt (n : ℕ) / Real.sqrt (n : ℝ) :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have hh : ‖correlation f (Real.log (n : ℝ))‖ ≤
      Real.exp (-a * Real.log (n : ℝ)) * (weightedNorm a f * weightedNorm a f) := by
    simpa only [mixedCorrelation_self, correlation_eq_weilFormula,
      abs_of_nonneg (Real.log_natCast_nonneg (n : ℕ))] using
      mixedCorrelation_norm_le ha0 hf hf (Real.log (n : ℝ))
  rw [complexPrimeTerm_norm]
  calc
    _ ≤ (ArithmeticFunction.vonMangoldt (n : ℕ) / Real.sqrt (n : ℝ)) *
        (Real.exp (-a * Real.log (n : ℝ)) * (weightedNorm a f * weightedNorm a f)) :=
      mul_le_mul_of_nonneg_left hh hc
    _ = primeCoeff a n * (weightedNorm a f * weightedNorm a f) := by
      unfold primeCoeff
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (primeCoeff_le_logMajorant a n)
      (mul_nonneg (weightedNorm_nonneg a f) (weightedNorm_nonneg a f))

theorem complexPrime_norm_summable {a : ℝ} (ha : 1 / 2 < a)
    {f : ℝ → ℂ} (hf : WeightedL2 a f) :
    Summable (fun n : ℕ => ‖complexPrimeTerm f n‖) := by
  apply (summable_subtype_and_compl (s := {n : ℕ | 2 ≤ n})).mp
  constructor
  · exact ((logMajorant_summable ha).mul_right
      (weightedNorm a f * weightedNorm a f)).of_nonneg_of_le
      (fun n => norm_nonneg _) (complexPrimeTerm_norm_le ha hf)
  · have hz (n : ↥({n : ℕ | 2 ≤ n}ᶜ)) : complexPrimeTerm f n = 0 := by
      have hn : ¬ 2 ≤ (n : ℕ) := n.property
      have hn01 : (n : ℕ) = 0 ∨ (n : ℕ) = 1 := by omega
      rcases hn01 with hn0 | hn1
      · simp [hn0]
      · simp [hn1]
    simpa only [hz, norm_zero] using
      (summable_zero : Summable (fun _ : ↥({n : ℕ | 2 ≤ n}ᶜ) => (0 : ℝ)))

theorem complexPrime_summable {a : ℝ} (ha : 1 / 2 < a)
    {f : ℝ → ℂ} (hf : WeightedL2 a f) : Summable (complexPrimeTerm f) :=
  (complexPrime_norm_summable ha hf).of_norm

/-- The paper's real part of the complex sum equals the
real-valued prime series used by `fullWeilForm`. -/
theorem complexPrime_re_tsum {f : ℝ → ℂ} (hs : Summable (complexPrimeTerm f)) :
    (∑' n : ℕ, complexPrimeTerm f n).re =
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        (correlation f (Real.log n)).re := by
  rw [Complex.re_tsum hs]
  simp only [complexPrimeTerm, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

theorem fullWeilForm_eq_complexPrime {f : ℝ → ℂ}
    (hs : Summable (complexPrimeTerm f)) :
    fullWeilForm f =
      (1 / (2 * Real.pi)) * (∫ r : ℝ, gammaWeight r * Complex.normSq (paperFourier f r))
      + 2 * (paperFourier f (I / 2) * conj (paperFourier f (-I / 2))).re
      - 2 * (∑' n : ℕ, complexPrimeTerm f n).re := by
  rw [complexPrime_re_tsum hs]
  rfl

theorem weightedBVMeasure_complexPrime {f : ℝ → ℂ} (hv : BoundedVariationOn f univ)
    (hw : Integrable (weightedProfile 1 f))
    (hm : Integrable (fun x : ℝ => Real.exp |x|) hv.vectorMeasure.variation) :
    Summable (fun n : ℕ => ‖complexPrimeTerm f n‖) ∧
      (∑' n : ℕ, complexPrimeTerm f n).re =
        ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          (correlation f (Real.log n)).re := by
  have hs := complexPrime_norm_summable (by norm_num : (1 / 2 : ℝ) < 1)
    (weightedBVMeasure_weightedL2 hv hw hm)
  exact ⟨hs, complexPrime_re_tsum hs.of_norm⟩

theorem exteriorTail_complexPrime {F F' : ℝ → ℂ} (hc : Continuous F)
    {a : ℝ} (ha : 0 ≤ a)
    (hd : ∀ x ∈ (Icc (-a) a)ᶜ, HasDerivAt F (F' x) x)
    (hi : IntegrableOn (weightedProfile 1 F) (Icc (-a) a)ᶜ)
    (hi' : IntegrableOn (weightedProfile 1 F') (Icc (-a) a)ᶜ) :
    Summable (fun n : ℕ => ‖complexPrimeTerm (exteriorTail a F) n‖) ∧
      (∑' n : ℕ, complexPrimeTerm (exteriorTail a F) n).re =
        ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          (correlation (exteriorTail a F) (Real.log n)).re := by
  have hs := complexPrime_norm_summable (by norm_num : (1 / 2 : ℝ) < 1)
    (exteriorTail_weightedL2 hc ha hd hi hi')
  exact ⟨hs, complexPrime_re_tsum hs.of_norm⟩

theorem thetaDeriv_exteriorTail_complexPrime (P : ℂ[X]) {a : ℝ} (ha : 0 ≤ a) :
    Summable (fun n : ℕ => ‖complexPrimeTerm
      (exteriorTail a (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))) n‖) ∧
      (∑' n : ℕ, complexPrimeTerm
        (exteriorTail a (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))) n).re =
        ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          (correlation (exteriorTail a (polynomialDerivative P
            (fun u => (thetaDensity u : ℂ)))) (Real.log n)).re := by
  have hd := (polynomialDerivative_thetaDensity_contDiff P).differentiable (by simp)
  exact exteriorTail_complexPrime (polynomialDerivative_thetaDensity_contDiff P).continuous ha
    (fun x _ => (hd x).hasDerivAt)
    (polynomialDerivative_thetaDensity_all_weights_integrable P 1).integrableOn
    (by simpa only [iteratedDeriv_one] using
      (polynomialDerivative_thetaDensity_iteratedDeriv_all_weights_integrable P 1 1).integrableOn)

/-- The theta-derivative majorant bounds the complex norm, including both
same-edge correlations and the cross-edge term. -/
theorem complexPrimeTerm_norm_le_twoTail {f g : ℝ → ℂ} {a s₀ : ℝ}
    (hf2 : MemLp f 2) (hg2 : MemLp g 2) (ha : 0 ≤ a) (hs₀ : 0 ≤ s₀)
    (hslog : s₀ ≤ Real.log 2)
    (hfr : ∀ u, u ≤ a → f u = 0) (hgl : ∀ u, -a ≤ u → g u = 0)
    (hs : TwoTailSurvival f g a (scaleT a) s₀) (n : ℕ) :
    ‖complexPrimeTerm (fun u => f u + g u) n‖ ≤
      ThetaDerivPrimeAssembly.threePartEnvelope
        ((squaredNorm f + squaredNorm g) * Real.exp (-3 * scaleT a / 8))
        ((sourceL2Norm f * sourceL2Norm g) * Real.exp (-a) * (2 * a + 2 * s₀))
        (2 * (sourceL2Norm f * sourceL2Norm g) * Real.exp (-a))
        (Real.exp (2 * a)) (Real.exp (2 * a) * Real.exp (2 * s₀))
        (Real.pi / 4) (2 * a) n := by
  unfold ThetaDerivPrimeAssembly.threePartEnvelope
  by_cases hn : 2 ≤ n
  · have hsame := same_prime_correlations_bound hf2 hg2 hfr hgl hs hslog (scaleT_ge_one ha) hn
    have hcross := cross_prime_complete_envelope hf2 hg2 ha hs₀ hfr hgl hs hn
    have hnorm : ‖correlation (fun u => f u + g u) (Real.log n)‖ ≤
        ‖mixedCorrelation f f (Real.log n)‖ + ‖mixedCorrelation g g (Real.log n)‖ +
        ‖mixedCorrelation f g (Real.log n)‖ := by
      rw [correlation_add_four hf2 hg2,
        reverse_cross_correlation_zero ha hfr hgl (Real.log_natCast_nonneg n), add_zero]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    rw [complexPrimeTerm_norm]
    change mangoldtWeight n * _ ≤ _
    have hm := mul_le_mul_of_nonneg_left hnorm (mangoldtWeight_nonneg n)
    nlinarith [hsame, hcross, hm]
  · have hzero : complexPrimeTerm (fun u => f u + g u) n = 0 := by
      have hn01 : n = 0 ∨ n = 1 := by omega
      rcases hn01 with rfl | rfl <;> simp
    rw [hzero, norm_zero]
    have hD := ThetaDerivPrimeSums.diagonalKernel_nonneg n
    have hA : 0 ≤ squaredNorm f + squaredNorm g :=
      add_nonneg (integral_nonneg (fun u => sq_nonneg ‖f u‖))
        (integral_nonneg (fun u => sq_nonneg ‖g u‖))
    have hc := crossoverTerm_nonneg (N := Real.exp (2 * a)) (c := Real.pi / 4)
      (show 0 ≤ 2 * a by linarith) n
    have hF := sourceL2Norm_nonneg f
    have hG := sourceL2Norm_nonneg g
    positivity

theorem complexPrime_norm_summable_of_twoTail {f g : ℝ → ℂ} {a s₀ : ℝ}
    (hf2 : MemLp f 2) (hg2 : MemLp g 2) (ha : 0 ≤ a) (hs₀ : 0 ≤ s₀)
    (hslog : s₀ ≤ Real.log 2)
    (hfr : ∀ u, u ≤ a → f u = 0) (hgl : ∀ u, -a ≤ u → g u = 0)
    (hs : TwoTailSurvival f g a (scaleT a) s₀) :
    Summable (fun n : ℕ => ‖complexPrimeTerm (fun u => f u + g u) n‖) :=
  (ThetaDerivPrimeAssembly.threePartEnvelope_summable _ _ _ _
    (by positivity) (by positivity) (show 0 ≤ 2 * a by linarith)).of_nonneg_of_le
    (fun n => norm_nonneg _) (complexPrimeTerm_norm_le_twoTail hf2 hg2 ha hs₀ hslog hfr hgl hs)

theorem primeContribution_eq_complex_of_twoTail {f g : ℝ → ℂ} {a s₀ : ℝ}
    (hf2 : MemLp f 2) (hg2 : MemLp g 2) (ha : 0 ≤ a) (hs₀ : 0 ≤ s₀)
    (hslog : s₀ ≤ Real.log 2)
    (hfr : ∀ u, u ≤ a → f u = 0) (hgl : ∀ u, -a ≤ u → g u = 0)
    (hs : TwoTailSurvival f g a (scaleT a) s₀) :
    primeContribution (fun u => f u + g u) =
      2 * (∑' n : ℕ, complexPrimeTerm (fun u => f u + g u) n).re := by
  rw [complexPrime_re_tsum
    (complexPrime_norm_summable_of_twoTail hf2 hg2 ha hs₀ hslog hfr hgl hs).of_norm]
  rfl

theorem thetaDerivTails_pole_complexPrime_bound (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a : ℝ) (ha1 : 1 ≤ a)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hslog : 40 * thetaDerivTailWidth d a ≤ Real.log 2) :
    |poleContribution (fun u => thetaDerivRightTail P a u + thetaDerivLeftTail P a u)| +
      |2 * (∑' n : ℕ, complexPrimeTerm
        (fun u => thetaDerivRightTail P a u + thetaDerivLeftTail P a u) n).re| ≤
      thetaDerivArithmeticConstant * ((d : ℝ) + 2) * a * Real.exp (-a) *
        squaredNorm (fun u => thetaDerivRightTail P a u + thetaDerivLeftTail P a u) := by
  have hsum : Summable (complexPrimeTerm
      (fun u => thetaDerivRightTail P a u + thetaDerivLeftTail P a u)) := by
    rw [← thetaDeriv_exteriorTail_eq_sum P a (by linarith)]
    exact (thetaDeriv_exteriorTail_complexPrime P (by linarith)).1.of_norm
  rw [complexPrime_re_tsum hsum]
  exact thetaDerivTails_pole_prime_bound d P hP hdegree a ha1 ha hsize hslog

theorem window_complexPrimeTerm_zero_outside {a : ℝ} {f : ℝ → ℂ}
    (hf : Function.support f ⊆ Icc (-a) a) {n : ℕ}
    (hn : n ∉ WindowFormBounds.primeWindow a) : complexPrimeTerm f n = 0 := by
  have hnf : Nat.floor (Real.exp (2 * |a|)) < n := by
    simpa only [WindowFormBounds.primeWindow, Finset.mem_range, not_lt,
      Nat.add_one_le_iff] using hn
  have hnR : Real.exp (2 * |a|) < (n : ℝ) := (Nat.floor_lt (Real.exp_pos _).le).mp hnf
  have hn0 : (0 : ℝ) < n := lt_trans (Real.exp_pos _) hnR
  have hl : 2 * |a| < |Real.log (n : ℝ)| :=
    ((Real.lt_log_iff_exp_lt hn0).mpr hnR).trans_le (le_abs_self _)
  have hc : correlation f (Real.log n) = 0 := by
    simpa only [RadicalCorrelation.weilTest_eq_integral, correlation] using
      WindowFormBounds.mixed_correlation_zero hf hf hl
  simp only [complexPrimeTerm, hc, mul_zero]

theorem window_complexPrime_norm_summable {a : ℝ} {f : ℝ → ℂ}
    (hf : Function.support f ⊆ Icc (-a) a) :
    Summable (fun n : ℕ => ‖complexPrimeTerm f n‖) := by
  apply summable_of_ne_finset_zero (s := WindowFormBounds.primeWindow a)
  intro _n hn
  rw [window_complexPrimeTerm_zero_outside hf hn, norm_zero]

theorem window_complexPrime_tsum_eq {a : ℝ} {f : ℝ → ℂ}
    (hf : Function.support f ⊆ Icc (-a) a) :
    (∑' n : ℕ, complexPrimeTerm f n) =
      ∑ n ∈ WindowFormBounds.primeWindow a, complexPrimeTerm f n :=
  tsum_eq_sum (fun _n hn => window_complexPrimeTerm_zero_outside hf hn)

theorem window_complexPrime_re_tsum {a : ℝ} {f : ℝ → ℂ}
    (hf : Function.support f ⊆ Icc (-a) a) :
    (∑' n : ℕ, complexPrimeTerm f n).re =
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        (correlation f (Real.log n)).re :=
  complexPrime_re_tsum (window_complexPrime_norm_summable hf).of_norm

theorem windowCut_complexPrime (a : ℝ) (f : ℝ → ℂ) :
    Summable (fun n : ℕ => ‖complexPrimeTerm (windowCut a f) n‖) ∧
      (∑' n : ℕ, complexPrimeTerm (windowCut a f) n).re =
        ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          (correlation (windowCut a f) (Real.log n)).re := by
  have hs : Function.support (windowCut a f) ⊆ Icc (-a) a :=
    support_indicator_subset
  exact ⟨window_complexPrime_norm_summable hs, window_complexPrime_re_tsum hs⟩

theorem windowCut_complexPrime_tsum_eq (a : ℝ) (f : ℝ → ℂ) :
    (∑' n : ℕ, complexPrimeTerm (windowCut a f) n) =
      ∑ n ∈ WindowFormBounds.primeWindow a, complexPrimeTerm (windowCut a f) n :=
  window_complexPrime_tsum_eq support_indicator_subset

end ThetaTrial.Paper
