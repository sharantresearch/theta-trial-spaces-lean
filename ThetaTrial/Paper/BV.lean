import ThetaTrial.Paper.Definitions
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Slope
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.MeasureTheory.Function.L2Space

/-!
Bounded-variation estimates. Jumps are included in the total variation, and
the translation estimate uses the variation rather than a derivative.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal FourierTransform RealInnerProductSpace

namespace ThetaTrial.Paper

private lemma variation_increment_norm {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf : BoundedVariationOn f univ) {x y : ℝ} (hxy : x ≤ y) :
    ‖f y - f x‖ ≤ variationOnFromTo f univ 0 y - variationOnFromTo f univ 0 x := by
  rw [variationOnFromTo.sub_right hf.locallyBoundedVariationOn
    (mem_univ 0) (mem_univ y) (mem_univ x)]
  rw [variationOnFromTo.eq_of_le _ _ hxy]
  simpa only [univ_inter, dist_eq_norm] using
    (hf.mono (subset_univ (Icc x y))).dist_le
      (show y ∈ Icc x y from ⟨hxy, le_rfl⟩)
      (show x ∈ Icc x y from ⟨le_rfl, hxy⟩)

/-- A translation estimate for BV functions. No differentiability is needed,
so jumps at the endpoints and in the interior are allowed. -/
theorem integral_norm_translate_sub_le_of_nonneg {f : ℝ → ℂ}
    (hfi : Integrable f) (hfv : BoundedVariationOn f univ) {h : ℝ} (hh : 0 ≤ h) :
    (∫ x : ℝ, ‖f (x + h) - f x‖) ≤ h * (eVariationOn f univ).toReal := by
  let v : ℝ → ℝ := variationOnFromTo f univ 0
  have hv : Monotone v := by
    exact monotoneOn_univ.mp (variationOnFromTo.monotoneOn
      hfv.locallyBoundedVariationOn (mem_univ 0))
  have hint : Integrable (fun x : ℝ => ‖f (x + h) - f x‖) :=
    ((hfi.comp_add_right h).sub hfi).norm
  have hb : ∀ R : ℝ, 0 ≤ R →
      (∫ x in (-R)..R, ‖f (x + h) - f x‖) ≤ h * (eVariationOn f univ).toReal := by
    intro R hR
    have hab : -R ≤ R := by linarith
    have hmono : MonotoneOn v (Icc (-R) (R + h)) := hv.monotoneOn _
    have hs := hmono.intervalIntegral_slope_le hab hh
    have hvi : IntervalIntegrable v volume (-R) (R + h) := hv.intervalIntegrable
    have hvdi : IntervalIntegrable (fun x => v (x + h) - v x) volume (-R) R := by
      exact ((hvi.comp_add_right h).mono_set (by grind [uIcc])).sub
        (hvi.mono_set (by grind [uIcc]))
    have hbound : (∫ x in (-R)..R, v (x + h) - v x) ≤
        h * (v (R + h) - v (-R)) := by
      by_cases hz : h = 0
      · simp [hz]
      · have hp : 0 < h := lt_of_le_of_ne hh (Ne.symm hz)
        simp only [slope, add_sub_cancel_left, vsub_eq_sub, smul_eq_mul,
          intervalIntegral.integral_const_mul] at hs
        have hs' := mul_le_mul_of_nonneg_left hs hh
        simpa [← mul_assoc, mul_inv_cancel₀ hz] using hs'
    have hvbound : v (R + h) - v (-R) ≤ (eVariationOn f univ).toReal := by
      change variationOnFromTo f univ 0 (R + h) -
        variationOnFromTo f univ 0 (-R) ≤ _
      rw [variationOnFromTo.sub_right hfv.locallyBoundedVariationOn
        (mem_univ 0) (mem_univ (R + h)) (mem_univ (-R))]
      exact (le_abs_self _).trans (variationOnFromTo.abs_le_eVariationOn hfv)
    calc
      _ ≤ ∫ x in (-R)..R, v (x + h) - v x :=
        intervalIntegral.integral_mono_on hab hint.intervalIntegrable hvdi
          (fun x _ => variation_increment_norm hfv (by linarith))
      _ ≤ h * (v (R + h) - v (-R)) := hbound
      _ ≤ _ := mul_le_mul_of_nonneg_left hvbound hh
  exact le_of_tendsto (intervalIntegral_tendsto_integral hint
    tendsto_neg_atTop_atBot tendsto_id) (eventually_atTop.2 ⟨0, hb⟩)

/-- The translation estimate for both signs of the shift. -/
theorem integral_norm_translate_sub_le {f : ℝ → ℂ}
    (hfi : Integrable f) (hfv : BoundedVariationOn f univ) (h : ℝ) :
    (∫ x : ℝ, ‖f (x + h) - f x‖) ≤ |h| * (eVariationOn f univ).toReal := by
  rcases le_total 0 h with hh | hh
  · simpa only [abs_of_nonneg hh] using
      integral_norm_translate_sub_le_of_nonneg hfi hfv hh
  · have heq : (∫ x : ℝ, ‖f (x + h) - f x‖) =
        ∫ x : ℝ, ‖f (x + -h) - f x‖ := by
      convert integral_add_right_eq_self (μ := (volume : Measure ℝ))
        (fun x : ℝ => ‖f (x + -h) - f x‖) h using 1
      congr 1
      ext x
      simp only [add_neg_cancel_right, norm_sub_rev]
    rw [heq, abs_of_nonpos hh]
    exact integral_norm_translate_sub_le_of_nonneg hfi hfv (neg_nonneg.mpr hh)

/-- BV decay for mathlib's Fourier convention, proved by a half-period shift. -/
theorem norm_fourier_le_variation {f : ℝ → ℂ}
    (hfi : Integrable f) (hfv : BoundedVariationOn f univ) {w : ℝ} (hw : w ≠ 0) :
    ‖𝓕 f w‖ ≤ (eVariationOn f univ).toReal / (4 * |w|) := by
  rw [Real.fourier_eq, fourierIntegral_eq_half_sub_half_period_translate hw hfi]
  rw [norm_smul]
  have hn : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hn]
  have hshift : |(1 / (2 * ‖w‖ ^ 2) : ℝ) • w| = 1 / (2 * |w|) := by
    simp only [smul_eq_mul, abs_mul, abs_div, abs_one,
      abs_pow, Real.norm_eq_abs, abs_abs]
    norm_num
    field_simp
    exact sq_abs w
  calc
    _ ≤ (1 / 2 : ℝ) * (∫ v : ℝ, ‖f v - f (v + (1 / (2 * ‖w‖ ^ 2) : ℝ) • w)‖) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [Circle.norm_smul] using
        norm_integral_le_integral_norm
          (fun v : ℝ => Real.fourierChar (-⟪v, w⟫) •
            (f v - f (v + (1 / (2 * ‖w‖ ^ 2) : ℝ) • w)))
    _ ≤ (1 / 2 : ℝ) * (|(1 / (2 * ‖w‖ ^ 2) : ℝ) • w| *
        (eVariationOn f univ).toReal) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [norm_sub_rev] using integral_norm_translate_sub_le hfi hfv
        ((1 / (2 * ‖w‖ ^ 2) : ℝ) • w)
    _ = _ := by rw [hshift]; ring

/-- Exact conversion to the paper's unnormalized Fourier transform. -/
theorem paperFourier_eq_mathlib (f : ℝ → ℂ) (r : ℝ) :
    paperFourier f r = 𝓕 f (r / (2 * Real.pi)) := by
  rw [paperFourier, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
  have he : ((-2 * Real.pi * (r / (2 * Real.pi) * u) : ℝ) : ℂ) *
      Complex.I = -Complex.I * (r : ℂ) * (u : ℂ) := by
    push_cast
    field_simp
  rw [he]
  ring

/-- The BV Fourier estimate includes all jumps in `eVariationOn`. -/
theorem paperFourier_norm_le_variation {f : ℝ → ℂ}
    (hfi : Integrable f) (hfv : BoundedVariationOn f univ) {r : ℝ} (hr : r ≠ 0) :
    ‖paperFourier f r‖ ≤ Real.pi * (eVariationOn f univ).toReal / (2 * |r|) := by
  rw [paperFourier_eq_mathlib]
  have h := norm_fourier_le_variation hfi hfv
    (show r / (2 * Real.pi) ≠ 0 from
      div_ne_zero hr (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  convert h using 1
  rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
  norm_num
  field_simp
  ring

/-- The low-frequency estimate uses only ordinary integrability. -/
theorem paperFourier_norm_le_l1 (f : ℝ → ℂ) (r : ℝ) :
    ‖paperFourier f r‖ ≤ ∫ x : ℝ, ‖f x‖ := by
  rw [paperFourier_eq_mathlib]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (innerₗ ℝ) f (r / (2 * Real.pi))

/-- L1 plus BV data yield the full low/high-frequency envelope. -/
theorem paperFourier_norm_mul_one_add_abs_le {f : ℝ → ℂ}
    (hfi : Integrable f) (hfv : BoundedVariationOn f univ) (r : ℝ) :
    ‖paperFourier f r‖ * (1 + |r|) ≤
      (∫ x : ℝ, ‖f x‖) + Real.pi * (eVariationOn f univ).toReal / 2 := by
  have hlo := paperFourier_norm_le_l1 f r
  have hhi : ‖paperFourier f r‖ * |r| ≤
      Real.pi * (eVariationOn f univ).toReal / 2 := by
    by_cases hr : r = 0
    · simp only [hr, abs_zero, mul_zero]
      positivity
    · have h := (le_div_iff₀ (mul_pos (by norm_num) (abs_pos.mpr hr))).mp
        (paperFourier_norm_le_variation hfi hfv hr)
      nlinarith
  nlinarith

/-- The exact shape required for the gamma-Cauchy integrability bridge. -/
theorem paperFourier_sq_le_cauchy_of_bv {f : ℝ → ℂ}
    (hfi : Integrable f) (hfv : BoundedVariationOn f univ) (r : ℝ) :
    ‖paperFourier f r‖ ^ 2 ≤
      ((∫ x : ℝ, ‖f x‖) + Real.pi * (eVariationOn f univ).toReal / 2) ^ 2 /
        (1 + r ^ 2) := by
  have h := paperFourier_norm_mul_one_add_abs_le hfi hfv r
  have hm : 0 ≤ (∫ x : ℝ, ‖f x‖) + Real.pi * (eVariationOn f univ).toReal / 2 :=
    add_nonneg (integral_nonneg (fun x => norm_nonneg (f x))) (by positivity)
  have hs := (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (by positivity)) hm).2 h
  have hr : 1 + r ^ 2 ≤ (1 + |r|) ^ 2 := by nlinarith [sq_abs r, abs_nonneg r]
  have hprod := mul_le_mul_of_nonneg_left hr (sq_nonneg ‖paperFourier f r‖)
  rw [mul_pow] at hs
  exact (le_div_iff₀ (by positivity : 0 < 1 + r ^ 2)).2 (hprod.trans hs)

/-- Continuity is obtained from L1 integrability. -/
theorem paperFourier_continuous_real {f : ℝ → ℂ} (hfi : Integrable f) :
    Continuous (fun r : ℝ => paperFourier f r) := by
  have hc : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hfi
  simpa only [paperFourier_eq_mathlib, Function.comp_def, id_eq] using
    hc.comp (continuous_id.div_const (2 * Real.pi))

/-- Integrability forces the BV limit at positive infinity to vanish. -/
theorem tendsto_zero_of_integrable_bv {f : ℝ → ℂ}
    (hfi : Integrable f) (hfv : BoundedVariationOn f univ) :
    Tendsto f atTop (𝓝 0) := by
  have ht := hfv.tendsto_atTop_limUnder
  have hz : limUnder atTop f = 0 := by
    apply (hfi.integrableAtFilter atTop).eq_zero_of_tendsto ?_ ht
    intro s hs
    rcases mem_atTop_sets.1 hs with ⟨b, hb⟩
    rw [← top_le_iff, ← Real.volume_Ici (a := b)]
    exact measure_mono hb
  rwa [hz] at ht

/-- A pointwise bound from the total variation. -/
theorem norm_le_variation {f : ℝ → ℂ}
    (hfi : Integrable f) (hfv : BoundedVariationOn f univ) (x : ℝ) :
    ‖f x‖ ≤ (eVariationOn f univ).toReal := by
  have ht := ((tendsto_const_nhds : Tendsto (fun _ : ℝ => f x) atTop (𝓝 (f x))).sub
    (tendsto_zero_of_integrable_bv hfi hfv)).norm
  simp only [sub_zero] at ht
  exact le_of_tendsto ht (Eventually.of_forall fun y =>
    by simpa only [← dist_eq_norm] using hfv.dist_le (mem_univ x) (mem_univ y))

/-- Integrable BV functions belong to L2; singular derivative parts need not vanish. -/
theorem memLp_two_of_integrable_bv {f : ℝ → ℂ}
    (hfi : Integrable f) (hfv : BoundedVariationOn f univ) : MemLp f 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm hfi.aestronglyMeasurable).2
  apply (hfi.norm.const_mul (eVariationOn f univ).toReal).mono'
    (hfi.aestronglyMeasurable.norm.pow 2)
  filter_upwards [] with x
  rw [sq]
  simpa only [Pi.mul_apply, norm_mul, norm_norm] using
    mul_le_mul_of_nonneg_right (norm_le_variation hfi hfv x) (norm_nonneg (f x))

end ThetaTrial.Paper
