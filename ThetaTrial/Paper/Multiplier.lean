import ThetaTrial.Paper.Definitions
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The von Mises multiplier of Lemma `avg:factorization`. -/

noncomputable section
open Complex MeasureTheory Set Filter Metric
open scoped Topology

namespace ThetaTrial.Paper

def shiftMultiplier (a : ℝ) (z : ℂ) : ℂ :=
  ∫ y : ℝ in Icc (-shiftWidth a) (shiftWidth a),
    (shiftWeight a y : ℂ) * Complex.exp (z * (y : ℂ))

theorem shiftWeight_pos (a y : ℝ) : 0 < shiftWeight a y := Real.exp_pos _

theorem shiftWeight_le_one (a y : ℝ) : shiftWeight a y ≤ 1 := by
  unfold shiftWeight
  apply Real.exp_le_one_iff.mpr
  have hz : 0 < scaleZ a := mul_pos Real.pi_pos (Real.exp_pos _)
  have hc := Real.cos_le_one (2 * y)
  nlinarith

@[simp] theorem shiftWeight_neg (a y : ℝ) : shiftWeight a (-y) = shiftWeight a y := by
  simp [shiftWeight]

theorem shiftMultiplier_integrable (a : ℝ) (z : ℂ) :
    IntegrableOn (fun y : ℝ => (shiftWeight a y : ℂ) * Complex.exp (z * (y : ℂ)))
      (Icc (-shiftWidth a) (shiftWidth a)) := by
  apply ContinuousOn.integrableOn_Icc
  exact (by unfold shiftWeight; fun_prop : Continuous _).continuousOn

theorem shiftMultiplier_integrand_bound (a : ℝ) (z : ℂ) {y : ℝ}
    (hy : y ∈ Icc (-shiftWidth a) (shiftWidth a)) :
    ‖(shiftWeight a y : ℂ) * Complex.exp (z * (y : ℂ))‖ ≤
      Real.exp (shiftWidth a * |z.re|) := by
  have hyabs : |y| ≤ shiftWidth a := abs_le.mpr hy
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (shiftWeight_pos a y), Complex.norm_exp]
  calc
    shiftWeight a y * Real.exp (z * (y : ℂ)).re ≤
        Real.exp (z * (y : ℂ)).re :=
      mul_le_of_le_one_left (Real.exp_pos _).le (shiftWeight_le_one a y)
    _ ≤ Real.exp (shiftWidth a * |z.re|) := by
      apply Real.exp_le_exp.mpr
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
      calc
        z.re * y ≤ |z.re * y| := le_abs_self _
        _ = |z.re| * |y| := abs_mul _ _
        _ ≤ |z.re| * shiftWidth a := mul_le_mul_of_nonneg_left hyabs (abs_nonneg _)
        _ = _ := mul_comm _ _

theorem shiftMultiplier_norm_le {a : ℝ} (hb : 0 ≤ shiftWidth a) (z : ℂ) :
    ‖shiftMultiplier a z‖ ≤ 2 * shiftWidth a * Real.exp (shiftWidth a * |z.re|) := by
  have h := norm_setIntegral_le_of_norm_le_const
    (f := fun y : ℝ => (shiftWeight a y : ℂ) * Complex.exp (z * (y : ℂ)))
    (μ := volume) (isCompact_Icc.measure_lt_top)
    (fun y hy => shiftMultiplier_integrand_bound a z hy)
  simpa [shiftMultiplier, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith :
    0 ≤ shiftWidth a - -shiftWidth a), mul_comm, two_mul,
    max_eq_left (by linarith : 0 ≤ shiftWidth a + shiftWidth a)] using h

theorem shiftMultiplier_hasDerivAt {a : ℝ} (hb : 0 ≤ shiftWidth a) (z : ℂ) :
    HasDerivAt (shiftMultiplier a)
      (∫ y : ℝ in Icc (-shiftWidth a) (shiftWidth a),
        (shiftWeight a y : ℂ) * ((y : ℂ) * Complex.exp (z * (y : ℂ)))) z := by
  let b := shiftWidth a
  let μ : Measure ℝ := volume.restrict (Icc (-b) b)
  let F : ℂ → ℝ → ℂ := fun w y =>
    (shiftWeight a y : ℂ) * Complex.exp (w * (y : ℂ))
  let F' : ℂ → ℝ → ℂ := fun w y =>
    (shiftWeight a y : ℂ) * ((y : ℂ) * Complex.exp (w * (y : ℂ)))
  let B : ℝ := b * Real.exp (b * (‖z‖ + 1))
  have hmeas : ∀ w, AEStronglyMeasurable (F w) μ := by
    intro w
    exact (by dsimp [F, shiftWeight]; fun_prop : Continuous _).aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable (F' z) μ := by
    exact (by dsimp [F', shiftWeight]; fun_prop : Continuous _).aestronglyMeasurable
  have hbound : ∀ᵐ y ∂μ, ∀ w ∈ ball z 1, ‖F' w y‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    intro w hw
    have hyabs : |y| ≤ b := abs_le.mpr hy
    have hwN : ‖w‖ ≤ ‖z‖ + 1 := by
      have ht := norm_le_norm_add_norm_sub z w
      rw [norm_sub_rev z w] at ht
      have hd : ‖w - z‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hw
      linarith
    have hwr : |w.re| ≤ ‖z‖ + 1 := (Complex.abs_re_le_norm w).trans hwN
    have he := shiftMultiplier_integrand_bound a w hy
    have he' : ‖(shiftWeight a y : ℂ) * Complex.exp (w * (y : ℂ))‖ ≤
        Real.exp (b * (‖z‖ + 1)) := he.trans (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hwr hb))
    have hident : F' w y = (y : ℂ) * F w y := by dsimp [F', F]; ring
    rw [hident, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hyabs he' (norm_nonneg _) (by dsimp [b]; exact hb)
  have hint : Integrable (fun _ : ℝ => B) μ := integrableOn_const isCompact_Icc.measure_ne_top
  have hdiff : ∀ᵐ y ∂μ, ∀ w ∈ ball z 1, HasDerivAt (F · y) (F' w y) w := by
    filter_upwards [] with y
    intro w hw
    have hd := (((hasDerivAt_id w).mul_const (y : ℂ)).cexp).const_mul
      (shiftWeight a y : ℂ)
    simpa [F, F', mul_comm] using hd
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds z (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall hmeas) (shiftMultiplier_integrable a z)
    hdmeas hbound hint hdiff).2

theorem shiftMultiplier_entire {a : ℝ} (hb : 0 ≤ shiftWidth a) :
    Differentiable ℂ (shiftMultiplier a) := fun z =>
  (shiftMultiplier_hasDerivAt hb z).differentiableAt

theorem integral_neg_symmetric_interval (f : ℝ → ℂ) (b : ℝ) :
    (∫ y : ℝ in Icc (-b) b, f (-y)) = ∫ y : ℝ in Icc (-b) b, f y := by
  let m : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).measurableEmbedding
  have h := m.setIntegral_map (μ := volume) f (Icc (-b) b)
  rw [Measure.map_neg_eq_self (volume : Measure ℝ)] at h
  simpa only [neg_preimage, neg_Icc, neg_neg] using h.symm

@[simp] theorem shiftMultiplier_neg (a : ℝ) (z : ℂ) :
    shiftMultiplier a (-z) = shiftMultiplier a z := by
  have h := integral_neg_symmetric_interval
    (fun y : ℝ => (shiftWeight a y : ℂ) * Complex.exp (z * (y : ℂ))) (shiftWidth a)
  simpa only [shiftMultiplier, shiftWeight_neg, Complex.ofReal_neg, mul_neg, neg_mul] using h

theorem shiftMultiplier_eq_cosh (a : ℝ) (z : ℂ) :
    shiftMultiplier a z =
      ∫ y : ℝ in Icc (-shiftWidth a) (shiftWidth a),
        (shiftWeight a y : ℂ) * Complex.cosh (z * (y : ℂ)) := by
  have h := integral_add (shiftMultiplier_integrable a z)
    (shiftMultiplier_integrable a (-z))
  have he : (fun y : ℝ => (shiftWeight a y : ℂ) * Complex.exp (z * (y : ℂ)) +
      (shiftWeight a y : ℂ) * Complex.exp (-z * (y : ℂ))) =
      (fun y : ℝ => (2 : ℂ) * ((shiftWeight a y : ℂ) *
        Complex.cosh (z * (y : ℂ)))) := by
    funext y
    simp only [Complex.cosh, neg_mul]
    ring
  rw [he, integral_const_mul] at h
  change _ = shiftMultiplier a z + shiftMultiplier a (-z) at h
  rw [shiftMultiplier_neg] at h
  linear_combination -h / 2

theorem shiftMultiplier_real (a r : ℝ) :
    shiftMultiplier a (r : ℂ) =
      ((∫ y : ℝ in Icc (-shiftWidth a) (shiftWidth a),
        shiftWeight a y * Real.cosh (r * y) : ℝ) : ℂ) := by
  rw [shiftMultiplier_eq_cosh, ← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Icc
  intro y hy
  push_cast
  rfl

theorem shiftMultiplier_real_ge_zero_value (a r : ℝ) :
    (shiftMultiplier a 0).re ≤ (shiftMultiplier a (r : ℂ)).re := by
  rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by rfl,
    shiftMultiplier_real, shiftMultiplier_real]
  simp only [Complex.ofReal_re, zero_mul, Real.cosh_zero, mul_one]
  apply setIntegral_mono_on
    (ContinuousOn.integrableOn_Icc (by unfold shiftWeight; fun_prop))
    (ContinuousOn.integrableOn_Icc (by unfold shiftWeight; fun_prop)) measurableSet_Icc
  intro y hy
  exact le_mul_of_one_le_right (shiftWeight_pos a y).le (Real.one_le_cosh _)

theorem shiftWeight_gaussian_lower (a y : ℝ) :
    Real.exp (-4 * scaleZ a * y ^ 2) ≤ shiftWeight a y := by
  have hz : 0 < scaleZ a := mul_pos Real.pi_pos (Real.exp_pos _)
  have hc : 1 - Real.cos (2 * y) ≤ 2 * y ^ 2 := by
    nlinarith [Real.cos_two_mul y, Real.sin_sq_add_cos_sq y, Real.sin_sq_le_sq (x := y)]
  unfold shiftWeight
  exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hc hz.le])

/-- A lower bound for the mass of the multiplier; the small interval can be
chosen on the scale `Z^(-1/2)`. -/
theorem shiftMultiplier_zero_lower {a d : ℝ} (hd : 0 ≤ d)
    (hdb : d ≤ shiftWidth a) (hs : 4 * scaleZ a * d ^ 2 ≤ 1) :
    2 * d * Real.exp (-1) ≤ (shiftMultiplier a 0).re := by
  have hz : 0 < scaleZ a := mul_pos Real.pi_pos (Real.exp_pos _)
  have hint : IntegrableOn (shiftWeight a) (Icc (-shiftWidth a) (shiftWidth a)) := by
    apply ContinuousOn.integrableOn_Icc
    unfold shiftWeight
    fun_prop
  have hsub : Icc (-d) d ⊆ Icc (-shiftWidth a) (shiftWidth a) := by
    intro y hy
    exact ⟨by linarith [hy.1], hy.2.trans hdb⟩
  have hl : (∫ y : ℝ in Icc (-d) d, Real.exp (-1)) ≤
      ∫ y : ℝ in Icc (-d) d, shiftWeight a y := by
    apply setIntegral_mono_on (integrableOn_const isCompact_Icc.measure_ne_top)
      (hint.mono_set hsub) measurableSet_Icc
    intro y hy
    have hy2 : y ^ 2 ≤ d ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg y) hd).mpr (abs_le.mpr hy)
    have hym := mul_le_mul_of_nonneg_left hy2 (show 0 ≤ 4 * scaleZ a by positivity)
    calc
      Real.exp (-1) ≤ Real.exp (-4 * scaleZ a * y ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith [hym])
      _ ≤ _ := shiftWeight_gaussian_lower a y
  have hu := setIntegral_mono_set hint
    (ae_of_all _ (fun y => (shiftWeight_pos a y).le))
    (ae_of_all _ (fun y hy => hsub hy))
  have hvol : (∫ y : ℝ in Icc (-d) d, Real.exp (-1)) =
      2 * d * Real.exp (-1) := by
    simp only [integral_const, measureReal_def, Measure.restrict_apply_univ,
      Real.volume_Icc, smul_eq_mul]
    rw [ENNReal.toReal_ofReal (show 0 ≤ d - -d by linarith)]
    ring
  rw [hvol] at hl
  have h0 := shiftMultiplier_real a 0
  simp only [Complex.ofReal_zero, zero_mul, Real.cosh_zero, mul_one] at h0
  rw [h0, Complex.ofReal_re]
  exact hl.trans hu

/-- Uniform nonzero mass at the natural scale, with a concrete constant. -/
theorem shiftMultiplier_zero_lower_sqrt {a : ℝ} (hZ : 16 ≤ scaleZ a) :
    Real.exp (-1) / Real.sqrt (scaleZ a) ≤ (shiftMultiplier a 0).re := by
  have hz : 0 < scaleZ a := by linarith
  have hroot : 0 < Real.sqrt (scaleZ a) := Real.sqrt_pos.mpr hz
  have hsq : (Real.sqrt (scaleZ a)) ^ 2 = scaleZ a := Real.sq_sqrt hz.le
  have hroot4 : 4 ≤ Real.sqrt (scaleZ a) := by nlinarith
  let d : ℝ := 1 / (2 * Real.sqrt (scaleZ a))
  have hd : 0 < d := by dsimp [d]; positivity
  have hd8 : d ≤ 1 / 8 := by
    dsimp [d]
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (scaleZ a))).mpr
    linarith
  have hinv : (scaleZ a)⁻¹ ≤ 1 / 16 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 16) hZ
  have hdb : d ≤ shiftWidth a := by
    unfold shiftWidth
    linarith [Real.pi_gt_three]
  have hsmall : 4 * scaleZ a * d ^ 2 = 1 := by
    dsimp [d]
    field_simp
    nlinarith
  have h := shiftMultiplier_zero_lower hd.le hdb hsmall.le
  convert h using 1 <;> dsimp [d] <;> ring

end ThetaTrial.Paper
