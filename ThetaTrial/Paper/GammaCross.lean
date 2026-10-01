import ThetaTrial.Paper.Archimedean
import ThetaTrial.GammaEnergy
import ThetaTrial.Paper.ShiftParseval
import ThetaTrial.Paper.GammaCrossMagnitude
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod

/-!
# Gamma energy on nonsmooth noncompact sources

The cosine-difference formula is extended to the full finite-energy
L1/L2 domain by a proved product-integrability argument. The normalization
here is the paper's unnormalized Fourier transform and factor `1/(2*pi)`.
-/

noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate

namespace ThetaTrial.Paper

def gammaJoint (f : ℝ → ℂ) (h r : ℝ) : ℝ :=
  ThetaTrial.GammaEnergy.shiftKernel h * (1 - Real.cos (h * r)) *
    ‖LogUncertainty.paperFourier f r‖ ^ 2

lemma gammaJoint_measurable {f : ℝ → ℂ} (hf : Integrable f) :
    Measurable (Function.uncurry (gammaJoint f)) := by
  have hv : Measurable (fun r => ‖LogUncertainty.paperFourier f r‖ ^ 2) :=
    (LogUncertainty.paperFourier_continuous hf).measurable.norm.pow_const 2
  exact ((ThetaTrial.GammaEnergy.shiftKernel_measurable.comp measurable_fst).mul
    (measurable_const.sub ((measurable_fst.mul measurable_snd).cos))).mul
      (hv.comp measurable_snd)

lemma gammaJoint_nonneg (f : ℝ → ℂ) {h : ℝ} (hh : 0 < h) (r : ℝ) :
    0 ≤ gammaJoint f h r :=
  mul_nonneg (mul_nonneg (ThetaTrial.GammaEnergy.shiftKernel_pos hh).le
    (sub_nonneg.mpr (Real.cos_le_one _))) (sq_nonneg _)

lemma gammaJoint_frequency_integral (f : ℝ → ℂ) (r : ℝ) :
    (gammaWeight r - ThetaTrial.GammaEnergy.gammaBase) *
      ‖LogUncertainty.paperFourier f r‖ ^ 2 =
      2 * ∫ h : ℝ in Ioi 0, gammaJoint f h r := by
  rw [gammaWeight_eq_weilFormula, ThetaTrial.GammaEnergy.gammaMultiplier_sub_base]
  unfold gammaJoint
  rw [integral_mul_const]
  ring

lemma gammaJoint_integrable {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2)
    (hg : Integrable (fun r : ℝ => gammaWeight r *
      Complex.normSq (paperFourier f r))) :
    Integrable (Function.uncurry (gammaJoint f))
      ((volume.restrict (Ioi 0)).prod volume) := by
  have hv := uncertainty_fourier_sq_integrable hf hf2
  have hgv : Integrable (fun r : ℝ => gammaWeight r *
      ‖LogUncertainty.paperFourier f r‖ ^ 2) := by
    simpa only [← Complex.sq_norm, paperFourier_real_eq_uncertainty] using hg
  have hd : Integrable (fun r : ℝ => (gammaWeight r - ThetaTrial.GammaEnergy.gammaBase) *
      ‖LogUncertainty.paperFourier f r‖ ^ 2) := by
    apply (hgv.sub (hv.const_mul ThetaTrial.GammaEnergy.gammaBase)).congr
    filter_upwards [] with r
    change gammaWeight r * ‖LogUncertainty.paperFourier f r‖ ^ 2 -
      ThetaTrial.GammaEnergy.gammaBase * ‖LogUncertainty.paperFourier f r‖ ^ 2 = _
    ring
  apply (integrable_prod_iff' (gammaJoint_measurable hf).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [] with r
    exact (ThetaTrial.GammaEnergy.shiftKernel_cosine_integrable r).mul_const
      (‖LogUncertainty.paperFourier f r‖ ^ 2)
  · apply (hd.div_const 2).congr
    filter_upwards [] with r
    dsimp only [Function.uncurry]
    have heq : (∫ h : ℝ in Ioi 0, ‖gammaJoint f h r‖) =
        ∫ h : ℝ in Ioi 0, gammaJoint f h r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro h hh
      exact Real.norm_of_nonneg (gammaJoint_nonneg f hh r)
    rw [heq]
    have hx := gammaJoint_frequency_integral f r
    linarith

lemma gammaJoint_shift_integral {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2) (h : ℝ) :
    ThetaTrial.GammaEnergy.shiftKernel h * ThetaTrial.GammaEnergy.physicalShiftSq f h =
      (1 / Real.pi) * ∫ r : ℝ, gammaJoint f h r := by
  unfold ThetaTrial.GammaEnergy.physicalShiftSq
  rw [ShiftParseval.shift_parseval hf hf2]
  unfold gammaJoint
  simp only [mul_assoc, integral_const_mul]
  ring

theorem physical_shift_energy_integrable {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2)
    (hg : Integrable (fun r : ℝ => gammaWeight r *
      Complex.normSq (paperFourier f r))) :
    IntegrableOn (fun h => ThetaTrial.GammaEnergy.shiftKernel h *
      ThetaTrial.GammaEnergy.physicalShiftSq f h) (Ioi 0) := by
  apply ((gammaJoint_integrable hf hf2 hg).integral_prod_left.const_mul
    (1 / Real.pi)).congr
  filter_upwards [] with h
  exact (gammaJoint_shift_integral hf hf2 h).symm

/-- The gamma shift-energy identity on the full finite-energy L1/L2
domain. It therefore includes sharp noncompact BV tails. -/
theorem archimedeanEnergy_eq_shift {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2)
    (hg : Integrable (fun r : ℝ => gammaWeight r *
      Complex.normSq (paperFourier f r))) :
    archimedeanEnergy f = ThetaTrial.GammaEnergy.gammaBase * squaredNorm f +
      ThetaTrial.GammaEnergy.shiftEnergy f := by
  have hv := uncertainty_fourier_sq_integrable hf hf2
  have hgv : Integrable (fun r : ℝ => gammaWeight r *
      ‖LogUncertainty.paperFourier f r‖ ^ 2) := by
    simpa only [← Complex.sq_norm, paperFourier_real_eq_uncertainty] using hg
  have hd : Integrable (fun r : ℝ => (gammaWeight r - ThetaTrial.GammaEnergy.gammaBase) *
      ‖LogUncertainty.paperFourier f r‖ ^ 2) := by
    apply (hgv.sub (hv.const_mul ThetaTrial.GammaEnergy.gammaBase)).congr
    filter_upwards [] with r
    change gammaWeight r * ‖LogUncertainty.paperFourier f r‖ ^ 2 -
      ThetaTrial.GammaEnergy.gammaBase * ‖LogUncertainty.paperFourier f r‖ ^ 2 = _
    ring
  have heq : (∫ r : ℝ, (gammaWeight r - ThetaTrial.GammaEnergy.gammaBase) *
      ‖LogUncertainty.paperFourier f r‖ ^ 2) =
      (2 * Real.pi) * ThetaTrial.GammaEnergy.shiftEnergy f := by
    simp_rw [gammaJoint_frequency_integral]
    rw [integral_const_mul, ← integral_integral_swap (gammaJoint_integrable hf hf2 hg)]
    unfold ThetaTrial.GammaEnergy.shiftEnergy
    simp_rw [gammaJoint_shift_integral hf hf2]
    rw [integral_const_mul]
    field_simp
  have hsplit (r : ℝ) : gammaWeight r * ‖LogUncertainty.paperFourier f r‖ ^ 2 =
      (gammaWeight r - ThetaTrial.GammaEnergy.gammaBase) * ‖LogUncertainty.paperFourier f r‖ ^ 2 +
        ThetaTrial.GammaEnergy.gammaBase * ‖LogUncertainty.paperFourier f r‖ ^ 2 := by ring
  unfold archimedeanEnergy
  simp only [← Complex.sq_norm, paperFourier_real_eq_uncertainty]
  simp_rw [hsplit]
  rw [integral_add hd (hv.const_mul ThetaTrial.GammaEnergy.gammaBase), integral_const_mul,
    heq, LogUncertainty.paperFourier_mass hf hf2]
  unfold squaredNorm
  field_simp
  ring

lemma complex_separated_shift_sq (a b c d : ℂ)
    (hac : a * conj c = 0) (hbd : b * conj d = 0) (hcb : c * conj b = 0) :
    ‖(a + c) - (b + d)‖ ^ 2 =
      ‖a - b‖ ^ 2 + ‖c - d‖ ^ 2 - 2 * (a * conj d).re := by
  simp only [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_add,
    map_add, mul_add, add_mul, Complex.add_re, hac, hbd, hcb, Complex.zero_re]
  ring

lemma separated_product_zero {f g : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hfr : ∀ u, u ≤ a → f u = 0) (hgl : ∀ u, -a ≤ u → g u = 0) (u : ℝ) :
    f u * conj (g u) = 0 := by
  by_cases hu : u ≤ a
  · simp [hfr u hu]
  · have hg : g u = 0 := hgl u (by linarith)
    simp [hg]

lemma separated_shift_sq {f g : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hfr : ∀ u, u ≤ a → f u = 0) (hgl : ∀ u, -a ≤ u → g u = 0)
    {h : ℝ} (hh : 0 ≤ h) (u : ℝ) :
    ‖(f (u + h) + g (u + h)) - (f u + g u)‖ ^ 2 =
      ‖f (u + h) - f u‖ ^ 2 + ‖g (u + h) - g u‖ ^ 2 -
        2 * (f (u + h) * conj (g u)).re := by
  apply complex_separated_shift_sq
  · exact separated_product_zero ha hfr hgl (u + h)
  · exact separated_product_zero ha hfr hgl u
  · by_cases hu : u ≤ a
    · simp [hfr u hu]
    · simp [hgl (u + h) (by linarith)]

lemma separated_cross_zero {f g : ℝ → ℂ} {a h : ℝ}
    (hfr : ∀ u, u ≤ a → f u = 0) (hgl : ∀ u, -a ≤ u → g u = 0)
    (hh : h ≤ 2 * a) (u : ℝ) : f (u + h) * conj (g u) = 0 := by
  by_cases hu : -a ≤ u
  · simp [hgl u hu]
  · simp [hfr (u + h) (by linarith)]

/-- The physical-space gamma kernel decreases at every positive separation. -/
lemma shiftKernel_antitone {d h : ℝ} (hd : 0 < d) (hdh : d ≤ h) :
    ThetaTrial.GammaEnergy.shiftKernel h ≤ ThetaTrial.GammaEnergy.shiftKernel d := by
  have he : Real.exp (-h / 2) ≤ Real.exp (-d / 2) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hden : 1 - Real.exp (-2 * d) ≤ 1 - Real.exp (-2 * h) := by
    have := Real.exp_le_exp.mpr (show -2 * h ≤ -2 * d by linarith)
    linarith
  have hdp : 0 < 1 - Real.exp (-2 * d) := by
    have := Real.exp_lt_one_iff.mpr (show -2 * d < 0 by linarith)
    linarith
  unfold ThetaTrial.GammaEnergy.shiftKernel
  exact div_le_div₀ (Real.exp_pos _).le he hdp hden

lemma separated_squaredNorm {f g : ℝ → ℂ} {a : ℝ}
    (hf2 : MemLp f 2) (hg2 : MemLp g 2) (ha : 0 ≤ a)
    (hfr : ∀ u, u ≤ a → f u = 0) (hgl : ∀ u, -a ≤ u → g u = 0) :
    squaredNorm (fun u => f u + g u) = squaredNorm f + squaredNorm g := by
  unfold squaredNorm
  have heq (u : ℝ) : ‖f u + g u‖ ^ 2 = ‖f u‖ ^ 2 + ‖g u‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_add,
      separated_product_zero ha hfr hgl u, Complex.zero_re, mul_zero, add_zero]
  simp_rw [heq]
  exact integral_add (hf2.integrable_norm_pow (by norm_num))
    (hg2.integrable_norm_pow (by norm_num))

lemma separated_physicalShiftSq {f g : ℝ → ℂ} {a : ℝ}
    (hf2 : MemLp f 2) (hg2 : MemLp g 2) (ha : 0 ≤ a)
    (hfr : ∀ u, u ≤ a → f u = 0) (hgl : ∀ u, -a ≤ u → g u = 0)
    {h : ℝ} (hh : 0 ≤ h) :
    ThetaTrial.GammaEnergy.physicalShiftSq (fun u => f u + g u) h =
      ThetaTrial.GammaEnergy.physicalShiftSq f h + ThetaTrial.GammaEnergy.physicalShiftSq g h -
        2 * crossCorrelationReal f g h := by
  unfold ThetaTrial.GammaEnergy.physicalShiftSq crossCorrelationReal
  simp_rw [separated_shift_sq ha hfr hgl hh]
  have hiSum : Integrable (fun u => ‖f (u + h) - f u‖ ^ 2 +
      ‖g (u + h) - g u‖ ^ 2) :=
    (ShiftParseval.shift_sq_integrable hf2 h).add
      (ShiftParseval.shift_sq_integrable hg2 h)
  rw [integral_sub hiSum
      ((crossCorrelationReal_integrand_integrable hf2 hg2 h).const_mul 2),
    integral_add (ShiftParseval.shift_sq_integrable hf2 h)
      (ShiftParseval.shift_sq_integrable hg2 h), integral_const_mul]

def gammaCrossIntegral (f g : ℝ → ℂ) : ℝ :=
  ∫ h : ℝ in Ioi 0, ThetaTrial.GammaEnergy.shiftKernel h * crossCorrelationReal f g h

lemma boundedVariationOn_add {f g : ℝ → ℂ}
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ) :
    BoundedVariationOn (fun u => f u + g u) univ := by
  have hle : eVariationOn (fun u => f u + g u) univ ≤
      eVariationOn f univ + eVariationOn g univ := by
    apply iSup_le
    rintro ⟨n, ⟨u, hum, hus⟩⟩
    calc
      _ ≤ (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
          (∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i))) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro i hi
        exact edist_add_add_le _ _ _ _
      _ ≤ _ := add_le_add (eVariationOn.sum_le hum hus) (eVariationOn.sum_le hum hus)
  exact ne_of_lt (lt_of_le_of_lt hle (ENNReal.add_lt_top.mpr ⟨hf.lt_top, hg.lt_top⟩))

lemma gammaCross_integrable_of_separated_bv {f g : ℝ → ℂ} {a : ℝ}
    (hf : Integrable f) (hg : Integrable g)
    (hfv : BoundedVariationOn f univ) (hgv : BoundedVariationOn g univ)
    (ha : 0 ≤ a) (hfr : ∀ u, u ≤ a → f u = 0)
    (hgl : ∀ u, -a ≤ u → g u = 0) :
    IntegrableOn (fun h => ThetaTrial.GammaEnergy.shiftKernel h *
      crossCorrelationReal f g h) (Ioi 0) := by
  have hf2 := memLp_two_of_integrable_bv hf hfv
  have hg2 := memLp_two_of_integrable_bv hg hgv
  have hsF := physical_shift_energy_integrable hf hf2 (gamma_term_integrable_of_bv hf hfv)
  have hsG := physical_shift_energy_integrable hg hg2 (gamma_term_integrable_of_bv hg hgv)
  have hsFG := physical_shift_energy_integrable (hf.add hg) (hf2.add hg2)
    (gamma_term_integrable_of_bv (hf.add hg) (boundedVariationOn_add hfv hgv))
  apply (((hsF.add hsG).sub hsFG).div_const 2).congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with h hh
  change (ThetaTrial.GammaEnergy.shiftKernel h * ThetaTrial.GammaEnergy.physicalShiftSq f h +
    ThetaTrial.GammaEnergy.shiftKernel h * ThetaTrial.GammaEnergy.physicalShiftSq g h -
    ThetaTrial.GammaEnergy.shiftKernel h * ThetaTrial.GammaEnergy.physicalShiftSq (fun u => f u + g u) h) / 2 = _
  rw [separated_physicalShiftSq hf2 hg2 ha hfr hgl hh.le]
  ring

/-- The interaction of two separated complex BV sources, as an identity
involving the gamma kernel. -/
theorem archimedeanEnergy_add_separated {f g : ℝ → ℂ} {a : ℝ}
    (hf : Integrable f) (hg : Integrable g)
    (hfv : BoundedVariationOn f univ) (hgv : BoundedVariationOn g univ)
    (ha : 0 ≤ a) (hfr : ∀ u, u ≤ a → f u = 0)
    (hgl : ∀ u, -a ≤ u → g u = 0) :
    archimedeanEnergy (fun u => f u + g u) =
      archimedeanEnergy f + archimedeanEnergy g - 2 * gammaCrossIntegral f g := by
  have hf2 := memLp_two_of_integrable_bv hf hfv
  have hg2 := memLp_two_of_integrable_bv hg hgv
  have hsF := physical_shift_energy_integrable hf hf2 (gamma_term_integrable_of_bv hf hfv)
  have hsG := physical_shift_energy_integrable hg hg2 (gamma_term_integrable_of_bv hg hgv)
  have hsCross := gammaCross_integrable_of_separated_bv hf hg hfv hgv ha hfr hgl
  have hshift : ThetaTrial.GammaEnergy.shiftEnergy (fun u => f u + g u) =
      ThetaTrial.GammaEnergy.shiftEnergy f + ThetaTrial.GammaEnergy.shiftEnergy g -
        2 * gammaCrossIntegral f g := by
    unfold ThetaTrial.GammaEnergy.shiftEnergy gammaCrossIntegral
    have heq : (∫ h : ℝ in Ioi 0, ThetaTrial.GammaEnergy.shiftKernel h *
        ThetaTrial.GammaEnergy.physicalShiftSq (fun u => f u + g u) h) =
        ∫ h : ℝ in Ioi 0, (ThetaTrial.GammaEnergy.shiftKernel h * ThetaTrial.GammaEnergy.physicalShiftSq f h +
          ThetaTrial.GammaEnergy.shiftKernel h * ThetaTrial.GammaEnergy.physicalShiftSq g h) -
          2 * (ThetaTrial.GammaEnergy.shiftKernel h * crossCorrelationReal f g h) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro h hh
      dsimp only
      rw [separated_physicalShiftSq hf2 hg2 ha hfr hgl hh.le]
      ring
    have hsSum : IntegrableOn (fun h => ThetaTrial.GammaEnergy.shiftKernel h *
        ThetaTrial.GammaEnergy.physicalShiftSq f h + ThetaTrial.GammaEnergy.shiftKernel h *
          ThetaTrial.GammaEnergy.physicalShiftSq g h) (Ioi 0) := hsF.add hsG
    rw [heq, integral_sub hsSum (hsCross.const_mul 2),
      integral_add hsF hsG, integral_const_mul]
  rw [archimedeanEnergy_eq_shift (f := fun u => f u + g u) (hf.add hg) (hf2.add hg2)
      (gamma_term_integrable_of_bv (hf.add hg) (boundedVariationOn_add hfv hgv)),
    archimedeanEnergy_eq_shift hf hf2 (gamma_term_integrable_of_bv hf hfv),
    archimedeanEnergy_eq_shift hg hg2 (gamma_term_integrable_of_bv hg hgv),
    separated_squaredNorm hf2 hg2 ha hfr hgl, hshift]
  ring

lemma gammaCross_abs_le_of_separated_bv {f g : ℝ → ℂ} {a : ℝ}
    (hf : Integrable f) (hg : Integrable g)
    (hfv : BoundedVariationOn f univ) (hgv : BoundedVariationOn g univ)
    (ha : 0 < a) (hfr : ∀ u, u ≤ a → f u = 0)
    (hgl : ∀ u, -a ≤ u → g u = 0) :
    |gammaCrossIntegral f g| ≤ ThetaTrial.GammaEnergy.shiftKernel (2 * a) *
      ((∫ u : ℝ, ‖f u‖) * ∫ u : ℝ, ‖g u‖) := by
  have hf2 := memLp_two_of_integrable_bv hf hfv
  have hg2 := memLp_two_of_integrable_bv hg hgv
  have hcross := gammaCross_integrable_of_separated_bv hf hg hfv hgv ha.le hfr hgl
  have hm := crossMagnitude_integrable hf hg
  have hk : 0 ≤ ThetaTrial.GammaEnergy.shiftKernel (2 * a) :=
    (ThetaTrial.GammaEnergy.shiftKernel_pos (by linarith)).le
  have hb : ∀ h : ℝ, 0 < h →
      ‖ThetaTrial.GammaEnergy.shiftKernel h * crossCorrelationReal f g h‖ ≤
        ThetaTrial.GammaEnergy.shiftKernel (2 * a) * crossMagnitude f g h := by
    intro h hh
    by_cases hd : h ≤ 2 * a
    · have hz : crossCorrelationReal f g h = 0 := by
        unfold crossCorrelationReal
        simp_rw [separated_cross_zero hfr hgl hd, Complex.zero_re]
        exact integral_zero _ _
      rw [hz, mul_zero, norm_zero]
      exact mul_nonneg hk (crossMagnitude_nonneg f g h)
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ThetaTrial.GammaEnergy.shiftKernel_pos hh).le]
      exact mul_le_mul (shiftKernel_antitone (by linarith) (le_of_not_ge hd))
        (crossCorrelationReal_abs_le hf2 hg2 h) (abs_nonneg _) hk
  unfold gammaCrossIntegral
  calc
    |∫ h : ℝ in Ioi 0, ThetaTrial.GammaEnergy.shiftKernel h * crossCorrelationReal f g h| =
        ‖∫ h : ℝ in Ioi 0, ThetaTrial.GammaEnergy.shiftKernel h * crossCorrelationReal f g h‖ :=
      (Real.norm_eq_abs _).symm
    _ ≤ ∫ h : ℝ in Ioi 0, ‖ThetaTrial.GammaEnergy.shiftKernel h * crossCorrelationReal f g h‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ h : ℝ in Ioi 0, ThetaTrial.GammaEnergy.shiftKernel (2 * a) * crossMagnitude f g h := by
      apply integral_mono_ae hcross.norm (hm.const_mul _).integrableOn
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with h hh
      exact hb h hh
    _ ≤ ∫ h : ℝ, ThetaTrial.GammaEnergy.shiftKernel (2 * a) * crossMagnitude f g h :=
      setIntegral_le_integral (hm.const_mul _) (ae_of_all _ (fun h =>
        mul_nonneg hk (crossMagnitude_nonneg f g h)))
    _ = _ := by rw [integral_const_mul, integral_crossMagnitude hf hg]

/-- The gamma interaction is exponentially small in the tail
separation. The sources may be complex, nonsmooth, and noncompact. -/
theorem archimedeanEnergy_add_separated_lower {f g : ℝ → ℂ} {a : ℝ}
    (hf : Integrable f) (hg : Integrable g)
    (hfv : BoundedVariationOn f univ) (hgv : BoundedVariationOn g univ)
    (ha : 0 < a) (hfr : ∀ u, u ≤ a → f u = 0)
    (hgl : ∀ u, -a ≤ u → g u = 0) :
    archimedeanEnergy f + archimedeanEnergy g -
      2 * ThetaTrial.GammaEnergy.shiftKernel (2 * a) *
        ((∫ u : ℝ, ‖f u‖) * ∫ u : ℝ, ‖g u‖) ≤
      archimedeanEnergy (fun u => f u + g u) := by
  rw [archimedeanEnergy_add_separated hf hg hfv hgv ha.le hfr hgl]
  have hb := gammaCross_abs_le_of_separated_bv hf hg hfv hgv ha hfr hgl
  linarith [le_abs_self (gammaCrossIntegral f g)]

/-- The diagonal logarithmic gain and the cross-tail term, under
one ordinary concentration scale. Zero edges are allowed. -/
theorem archimedeanEnergy_two_tail_concentration {f g : ℝ → ℂ} {a ρ : ℝ}
    (hf : Integrable f) (hg : Integrable g)
    (hfv : BoundedVariationOn f univ) (hgv : BoundedVariationOn g univ)
    (ha : 0 < a) (hρ : 0 < ρ)
    (hfr : ∀ u, u ≤ a → f u = 0) (hgl : ∀ u, -a ≤ u → g u = 0)
    (hconF : (∫ u : ℝ, ‖f u‖) ^ 2 ≤ ρ * squaredNorm f)
    (hconG : (∫ u : ℝ, ‖g u‖) ^ 2 ≤ ρ * squaredNorm g) :
    (Real.log (Real.pi / ρ) - 1 - archimedeanConstant -
      ρ * ThetaTrial.GammaEnergy.shiftKernel (2 * a)) *
        squaredNorm (fun u => f u + g u) ≤
      archimedeanEnergy (fun u => f u + g u) := by
  have hf2 := memLp_two_of_integrable_bv hf hfv
  have hg2 := memLp_two_of_integrable_bv hg hgv
  have hdiagF := archimedeanEnergy_lower_of_concentration hf hfv hρ hconF
  have hdiagG := archimedeanEnergy_lower_of_concentration hg hgv hρ hconG
  have hcross := archimedeanEnergy_add_separated_lower hf hg hfv hgv ha hfr hgl
  have hmass : 2 * ((∫ u : ℝ, ‖f u‖) * ∫ u : ℝ, ‖g u‖) ≤
      ρ * (squaredNorm f + squaredNorm g) := by
    nlinarith [sq_nonneg ((∫ u : ℝ, ‖f u‖) - ∫ u : ℝ, ‖g u‖)]
  have herr := mul_le_mul_of_nonneg_left hmass
    (ThetaTrial.GammaEnergy.shiftKernel_pos (show 0 < 2 * a by linarith)).le
  rw [separated_squaredNorm hf2 hg2 ha.le hfr hgl]
  nlinarith

lemma shiftKernel_two_mul_le_exp {a : ℝ} (ha : 1 ≤ a) :
    ThetaTrial.GammaEnergy.shiftKernel (2 * a) ≤
      Real.exp (-a) / (1 - Real.exp (-4)) := by
  have hden : 1 - Real.exp (-4) ≤ 1 - Real.exp (-2 * (2 * a)) := by
    have := Real.exp_le_exp.mpr (show -2 * (2 * a) ≤ (-4 : ℝ) by linarith)
    linarith
  have hdp : 0 < 1 - Real.exp (-4) := by
    have := Real.exp_lt_one_iff.mpr (show (-4 : ℝ) < 0 by norm_num)
    linarith
  unfold ThetaTrial.GammaEnergy.shiftKernel
  have he : -(2 * a) / 2 = -a := by ring
  rw [he]
  exact div_le_div₀ (Real.exp_pos _).le le_rfl hdp hden

/-- The explicit exponentially small interaction version used in the
paper after its theta-tail L1 concentration estimate. -/
theorem archimedeanEnergy_two_tail_concentration_exp {f g : ℝ → ℂ} {a ρ : ℝ}
    (hf : Integrable f) (hg : Integrable g)
    (hfv : BoundedVariationOn f univ) (hgv : BoundedVariationOn g univ)
    (ha : 1 ≤ a) (hρ : 0 < ρ)
    (hfr : ∀ u, u ≤ a → f u = 0) (hgl : ∀ u, -a ≤ u → g u = 0)
    (hconF : (∫ u : ℝ, ‖f u‖) ^ 2 ≤ ρ * squaredNorm f)
    (hconG : (∫ u : ℝ, ‖g u‖) ^ 2 ≤ ρ * squaredNorm g) :
    (Real.log (Real.pi / ρ) - 1 - archimedeanConstant -
      ρ * (Real.exp (-a) / (1 - Real.exp (-4)))) *
        squaredNorm (fun u => f u + g u) ≤
      archimedeanEnergy (fun u => f u + g u) := by
  have hlo := archimedeanEnergy_two_tail_concentration hf hg hfv hgv
    (show 0 < a by linarith) hρ hfr hgl hconF hconG
  have hN : 0 ≤ squaredNorm (fun u => f u + g u) :=
    integral_nonneg (fun u => sq_nonneg ‖f u + g u‖)
  have hcmp := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (shiftKernel_two_mul_le_exp ha) hρ.le) hN
  nlinarith

#print axioms archimedeanEnergy_eq_shift
#print axioms archimedeanEnergy_add_separated
#print axioms archimedeanEnergy_add_separated_lower
#print axioms archimedeanEnergy_two_tail_concentration
#print axioms archimedeanEnergy_two_tail_concentration_exp

end ThetaTrial.Paper
