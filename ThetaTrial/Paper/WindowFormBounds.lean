import ThetaTrial.Paper.FormDomain
import ThetaTrial.Paper.RadicalCutoff
import ThetaTrial.Paper.ThetaDerivPolePrimes

/-! Estimates for the Weil form on the supported logarithmic Fourier domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set Filter
open scoped ComplexConjugate

namespace ThetaTrial.Paper.WindowFormBounds
open Radical RadicalApproximation RadicalCorrelation RadicalCutoff

lemma zero_outside {a : ℝ} {f : ℝ → ℂ}
    (hf : Function.support f ⊆ Icc (-a) a) {u : ℝ} (hu : u ∉ Icc (-a) a) : f u = 0 :=
  Function.notMem_support.mp (fun h => hu (hf h))

lemma abs_le_window {a u : ℝ} (hu : u ∈ Icc (-a) a) : |u| ≤ |a| :=
  (abs_le.mpr hu).trans (le_abs_self a)

theorem weighted_integrable {a : ℝ} {f : ℝ → ℂ}
    (hf : InWindowFormDomain a f) (R : ℝ) :
    Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖f u‖) := by
  apply (hf.integrable.norm.const_mul (Real.exp (|R| * |a|))).mono'
    ((by fun_prop : Continuous (fun u : ℝ => Real.exp (R * |u|))).aestronglyMeasurable.mul
      hf.2.1.1.norm)
  filter_upwards with u
  change ‖Real.exp (R * |u|) * ‖f u‖‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
  by_cases hu : u ∈ Icc (-a) a
  · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_right (le_abs_self R) (abs_nonneg u)).trans
      (mul_le_mul_of_nonneg_left (abs_le_window hu) (abs_nonneg R))
  · simp [zero_outside hf.1 hu]

theorem fourier_integrable {a : ℝ} {f : ℝ → ℂ}
    (hf : InWindowFormDomain a f) (z : ℂ) : FourierIntegrableAt f z :=
  weighted_fourierIntegrable hf.2.1.1 (weighted_integrable hf) z

theorem mixed_correlation_zero {a : ℝ} {f h : ℝ → ℂ}
    (hf : Function.support f ⊆ Icc (-a) a)
    (hh : Function.support h ⊆ Icc (-a) a) {x : ℝ} (hx : 2 * |a| < |x|) :
    Zeta23.EF.weilTest f h x = 0 := by
  rw [weilTest_eq_integral]
  apply integral_eq_zero_of_ae
  filter_upwards with u
  by_cases hu : u ∈ Icc (-a) a
  · have huv : u - x ∉ Icc (-a) a := by
      intro hv
      have htri : |x| ≤ |u| + |u - x| := by
        calc
          |x| = |u - (u - x)| := by congr 1; ring
          _ ≤ |u| + |u - x| := abs_sub _ _
      linarith [abs_le_window hu, abs_le_window hv]
    simp [zero_outside hh huv]
  · simp [zero_outside hf hu]

def primeWindow (a : ℝ) : Finset ℕ := Finset.range (Nat.floor (Real.exp (2 * |a|)) + 1)

theorem primeTerm_zero_outside {a : ℝ} {f h : ℝ → ℂ}
    (hf : Function.support f ⊆ Icc (-a) a)
    (hh : Function.support h ⊆ Icc (-a) a) {n : ℕ} (hn : n ∉ primeWindow a) :
    primeTerm (Zeta23.EF.weilTest f h) n = 0 := by
  have hnf : Nat.floor (Real.exp (2 * |a|)) < n := by
    simpa only [primeWindow, Finset.mem_range, not_lt, Nat.add_one_le_iff] using hn
  have hnR : Real.exp (2 * |a|) < (n : ℝ) := (Nat.floor_lt (Real.exp_pos _).le).mp hnf
  have hn0 : (0 : ℝ) < n := lt_trans (Real.exp_pos _) hnR
  have hl : 2 * |a| < Real.log (n : ℝ) := (Real.lt_log_iff_exp_lt hn0).mpr hnR
  have hl' : 2 * |a| < |Real.log (n : ℝ)| := hl.trans_le (le_abs_self _)
  have hlneg : 2 * |a| < |-Real.log (n : ℝ)| := by simpa only [abs_neg] using hl'
  rw [primeTerm, mixed_correlation_zero hf hh hl', mixed_correlation_zero hf hh hlneg]
  simp

theorem prime_summable {a : ℝ} {f h : ℝ → ℂ}
    (hf : Function.support f ⊆ Icc (-a) a)
    (hh : Function.support h ⊆ Icc (-a) a) :
    Summable (primeTerm (Zeta23.EF.weilTest f h)) := by
  apply summable_of_ne_finset_zero (s := primeWindow a)
  exact fun n hn => primeTerm_zero_outside hf hh hn

theorem prime_tsum_eq {a : ℝ} {f h : ℝ → ℂ}
    (hf : Function.support f ⊆ Icc (-a) a)
    (hh : Function.support h ⊆ Icc (-a) a) :
    (∑' n, primeTerm (Zeta23.EF.weilTest f h) n) =
      ∑ n ∈ primeWindow a, primeTerm (Zeta23.EF.weilTest f h) n :=
  tsum_eq_sum (fun n hn => primeTerm_zero_outside hf hh hn)

lemma gammaWeight_measurable : AEStronglyMeasurable gammaWeight := by
  rw [show gammaWeight = ThetaTrial.GammaEnergy.gammaMultiplier from funext gammaWeight_eq_weilFormula]
  exact ThetaTrial.RationalFourier.gammaMultiplier_aestronglyMeasurable

lemma fourier_measurable {a : ℝ} {f : ℝ → ℂ} (hf : InWindowFormDomain a f) :
    AEStronglyMeasurable (fun r : ℝ => ThetaTrial.Paper.paperFourier f r) := by
  simp_rw [paperFourier_eq_logUncertainty]
  exact (LogUncertainty.paperFourier_continuous hf.integrable).aestronglyMeasurable

theorem gamma_mixed_integrable {a : ℝ} {f h : ℝ → ℂ}
    (hf : InWindowFormDomain a f) (hh : InWindowFormDomain a h) :
    Integrable (fun r : ℝ => (gammaWeight r : ℂ) *
      ThetaTrial.Paper.paperFourier f r * conj (ThetaTrial.Paper.paperFourier h r)) := by
  apply ((hf.gamma_integrable.norm.add hh.gamma_integrable.norm).div_const 2).mono'
    (((Complex.ofRealCLM.continuous.comp_aestronglyMeasurable gammaWeight_measurable).mul
      (fourier_measurable hf)).mul (Complex.continuous_conj.comp_aestronglyMeasurable
        (fourier_measurable hh)))
  filter_upwards with r
  change ‖(gammaWeight r : ℂ) * ThetaTrial.Paper.paperFourier f r *
    conj (ThetaTrial.Paper.paperFourier h r)‖ ≤
    (‖gammaWeight r * ‖ThetaTrial.Paper.paperFourier f r‖ ^ 2‖ +
     ‖gammaWeight r * ‖ThetaTrial.Paper.paperFourier h r‖ ^ 2‖) / 2
  simp only [norm_mul, norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_pow, abs_norm]
  nlinarith [sq_nonneg (‖ThetaTrial.Paper.paperFourier f r‖ -
    ‖ThetaTrial.Paper.paperFourier h r‖), abs_nonneg (gammaWeight r)]

theorem mixed_domain {a : ℝ} {f h : ℝ → ℂ}
    (hf : InWindowFormDomain a f) (hh : InWindowFormDomain a h) :
    Domain (Zeta23.EF.weilTest f h) := by
  refine ⟨fun z => FourierIntegrableAt.weilTest (fourier_integrable hf z)
    (fourier_integrable hh (conj z)), ?_, prime_summable hf.1 hh.1⟩
  apply (gamma_mixed_integrable hf hh).comp_neg.congr
  filter_upwards with r
  rw [gammaTerm, paperFT_weilTest hf.2.1.1 hh.2.1.1
    (weighted_integrable hf) (weighted_integrable hh)]
  simp only [conj_ofReal, ThetaTrial.Paper.paperFourier_eq_source,
    Complex.ofReal_neg, neg_neg,
    show gammaWeight (-r) = gammaWeight r from ThetaTrial.WeilFormula.gammaBracket_neg r]
  change (gammaWeight r : ℂ) * Zeta23.paperFT f r * conj (Zeta23.paperFT h r) =
    Zeta23.paperFT f r * conj (Zeta23.paperFT h r) * (gammaWeight r : ℂ)
  ring

theorem fullPairing_self_eq {a : ℝ} {f : ℝ → ℂ} (hf : InWindowFormDomain a f) :
    fullPairing f f = (fullWeilForm f : ℂ) :=
  fullQuadratic_eq_paperForm (fourier_integrable hf)

def windowVolume (a : ℝ) : ℝ := (volume (Icc (-a) a)).toReal

lemma windowVolume_nonneg (a : ℝ) : 0 ≤ windowVolume a := ENNReal.toReal_nonneg

theorem l1_le_l2 {a : ℝ} {f : ℝ → ℂ} (hf : InWindowFormDomain a f) :
    (∫ u : ℝ, ‖f u‖) ≤ (windowVolume a + 1) * sourceL2Norm f := by
  let k := FormDomain.windowExponential a 0
  have hk := FormDomain.windowExponential_memLp a 0
  have hb := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp f (ENNReal.ofReal 2) from by simpa using hf.2.1)
    (show MemLp k (ENNReal.ofReal 2) from by simpa [k] using hk)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hb
  have hprod : (∫ u : ℝ, ‖f u‖ * ‖k u‖) = ∫ u : ℝ, ‖f u‖ := by
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu : u ∈ Icc (-a) a
    · simp [k, FormDomain.windowExponential, hu]
    · simp [zero_outside hf.1 hu]
  have hki : (∫ u : ℝ, ‖k u‖ ^ 2) = windowVolume a := by
    change _ = (volume (Icc (-a) a)).toReal
    rw [← FormDomain.windowExponential_norm_sq a 0,
      ← FormDomain.integral_norm_sq_L2]
    apply integral_congr_ae
    filter_upwards [hk.coeFn_toLp] with u hu
    simp only [hu, k]
  rw [hprod, hki] at hb
  have hv : Real.sqrt (windowVolume a) ≤ windowVolume a + 1 := by
    have hs := Real.sq_sqrt (windowVolume_nonneg a)
    nlinarith [Real.sqrt_nonneg (windowVolume a), windowVolume_nonneg a]
  calc
    _ ≤ sourceL2Norm f * Real.sqrt (windowVolume a) := hb
    _ ≤ sourceL2Norm f * (windowVolume a + 1) :=
      mul_le_mul_of_nonneg_left hv (sourceL2Norm_nonneg f)
    _ = _ := mul_comm _ _

theorem halfWeightedL1_le {a : ℝ} {f : ℝ → ℂ} (hf : InWindowFormDomain a f) :
    halfWeightedL1 f ≤ Real.exp (|a| / 2) * (windowVolume a + 1) * sourceL2Norm f := by
  have hi : Integrable (fun u : ℝ => Real.exp (|u| / 2) * ‖f u‖) := by
    simpa only [one_div, ← div_eq_mul_inv, mul_comm (2 : ℝ)⁻¹] using weighted_integrable hf (1 / 2)
  have hb : halfWeightedL1 f ≤ Real.exp (|a| / 2) * ∫ u : ℝ, ‖f u‖ := by
    rw [← integral_const_mul]
    apply integral_mono hi (hf.integrable.norm.const_mul _)
    intro u
    by_cases hu : u ∈ Icc (-a) a
    · exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by
        linarith [abs_le_window hu])) (norm_nonneg _)
    · simp [zero_outside hf.1 hu]
  calc
    _ ≤ Real.exp (|a| / 2) * ∫ u : ℝ, ‖f u‖ := hb
    _ ≤ Real.exp (|a| / 2) * ((windowVolume a + 1) * sourceL2Norm f) :=
      mul_le_mul_of_nonneg_left (l1_le_l2 hf) (Real.exp_pos _).le
    _ = _ := by ring

def poleWindowBound (a : ℝ) : ℝ :=
  2 * (Real.exp (|a| / 2) * (windowVolume a + 1)) ^ 2

theorem pole_bound {a : ℝ} {f : ℝ → ℂ} (hf : InWindowFormDomain a f) :
    |poleContribution f| ≤ poleWindowBound a * squaredNorm f := by
  have hi : Integrable (fun u : ℝ => Real.exp (|u| / 2) * ‖f u‖) := by
    simpa only [one_div, ← div_eq_mul_inv, mul_comm (2 : ℝ)⁻¹] using weighted_integrable hf (1 / 2)
  have hb := halfWeightedL1_le hf
  have hs : halfWeightedL1 f ^ 2 ≤
      (Real.exp (|a| / 2) * (windowVolume a + 1)) ^ 2 * squaredNorm f := by
    calc
      _ ≤ (Real.exp (|a| / 2) * (windowVolume a + 1) * sourceL2Norm f) ^ 2 :=
        pow_le_pow_left₀ (halfWeightedL1_nonneg f) hb 2
      _ = _ := by rw [mul_pow, sourceL2Norm_sq]
  have hp := poleContribution_abs_le hi
  dsimp [poleWindowBound]
  nlinarith

def primeWindowBound (a : ℝ) : ℝ :=
  2 * ∑ n ∈ primeWindow a, ArithmeticFunction.vonMangoldt n / Real.sqrt n

theorem primeWindowBound_nonneg (a : ℝ) : 0 ≤ primeWindowBound a := by
  unfold primeWindowBound
  positivity

theorem prime_bound {a : ℝ} {f : ℝ → ℂ} (hf : InWindowFormDomain a f) :
    |primeContribution f| ≤ primeWindowBound a * squaredNorm f := by
  have hcorr (x : ℝ) : ‖correlation f x‖ ≤ squaredNorm f := by
    have h := mixedCorrelation_norm_le_l2 hf.2.1 hf.2.1 x
    rw [ThetaTrial.PrimeContinuity.mixedCorrelation_self, ← correlation_eq_weilFormula,
      ← pow_two, sourceL2Norm_sq] at h
    exact h
  have hzero (n : ℕ) (hn : n ∉ primeWindow a) :
      ArithmeticFunction.vonMangoldt n / Real.sqrt n * (correlation f (Real.log n)).re = 0 := by
    have hz := primeTerm_zero_outside hf.1 hf.1 hn
    have he := ThetaTrial.WeilFormula.weilTest_add_neg f (Real.log n)
    simp only [primeTerm, he, Radical.weilFormulaCorrelation_eq_paper] at hz
    have hr : (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        (2 * (correlation f (Real.log n)).re) = 0 := by exact_mod_cast hz
    nlinarith
  unfold primeContribution
  rw [tsum_eq_sum hzero, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2 * ∑ n ∈ primeWindow a,
        |ArithmeticFunction.vonMangoldt n / Real.sqrt n * (correlation f (Real.log n)).re| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ 2 * ∑ n ∈ primeWindow a,
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * squaredNorm f := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro n hn
      have hc : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n :=
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
      rw [abs_mul, abs_of_nonneg hc]
      exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (hcorr _)) hc
    _ = primeWindowBound a * squaredNorm f := by rw [← Finset.sum_mul]; unfold primeWindowBound; ring

theorem fullForm_log_bounded_perturbation : ∃ C : ℝ, 0 < C ∧
    ∀ (a : ℝ) (f : ℝ → ℂ), InWindowFormDomain a f →
      |fullWeilForm f - (1 / (2 * Real.pi)) *
        (∫ r : ℝ, Real.log (2 + |r|) * ‖ThetaTrial.Paper.paperFourier f r‖ ^ 2)| ≤
      (C + poleWindowBound a + primeWindowBound a) * squaredNorm f := by
  obtain ⟨C, hC, hg⟩ := archimedean_log_bounded_perturbation
  refine ⟨C, hC, fun a f hf => ?_⟩
  have he : fullWeilForm f = archimedeanEnergy f + poleContribution f - primeContribution f := rfl
  rw [he]
  have ha := hg a f hf
  have hp := pole_bound hf
  have hq := prime_bound hf
  calc
    _ = |(archimedeanEnergy f - (1 / (2 * Real.pi)) *
          (∫ r : ℝ, Real.log (2 + |r|) * ‖ThetaTrial.Paper.paperFourier f r‖ ^ 2)) +
          poleContribution f - primeContribution f| := by congr 1; ring
    _ ≤ |archimedeanEnergy f - (1 / (2 * Real.pi)) *
          (∫ r : ℝ, Real.log (2 + |r|) * ‖ThetaTrial.Paper.paperFourier f r‖ ^ 2)| +
          |poleContribution f| + |primeContribution f| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (C + poleWindowBound a + primeWindowBound a) * squaredNorm f := by linarith

#print axioms mixed_domain
#print axioms fullForm_log_bounded_perturbation

end ThetaTrial.Paper.WindowFormBounds
