import ThetaTrial.Paper.ThetaStripDecay
import ThetaTrial.Paper.ThetaFourier
import ThetaTrial.Paper.Multiplier
import ThetaTrial.Paper.RadicalApproximation
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Tactic

/-!
# Horizontal shifts and the Fourier transform of the theta average

The paper uses the negative Fourier sign. Thus an upward shift by `iy`
contributes `exp (-z*y)`. The finite even weight makes the averaged
multiplier equal to `shiftMultiplier a z`.
-/

noncomputable section
open Complex MeasureTheory Set Filter Metric
open scoped Topology

namespace ThetaTrial.Paper

private theorem abs_le_of_uIcc_zero {v y : ℝ} (hv : v ∈ uIcc 0 y) : |v| ≤ |y| := by
  have h0 : (0 : ℝ) ∈ Icc (-|y|) |y| := ⟨by linarith [abs_nonneg y], abs_nonneg y⟩
  have hy : y ∈ Icc (-|y|) |y| := ⟨neg_abs_le y, le_abs_self y⟩
  exact abs_le.mpr ((uIcc_subset_Icc h0 hy) hv)

private theorem horizontal_integral_eq_of_vertical_decay
    (F : ℂ → ℂ) (y : ℝ)
    (hF : DifferentiableOn ℂ F {w | |w.im| ≤ |y|})
    (hI₀ : Integrable (fun u : ℝ => F (u : ℂ)))
    (hIy : Integrable (fun u : ℝ => F ((u : ℂ) + (y : ℂ) * I)))
    (g : ℝ → ℝ) (hg : Tendsto g atTop (𝓝 0))
    (hr : ∀ (R : ℝ), R ≥ 0 → ∀ v ∈ uIcc 0 y, ‖F ((R : ℂ) + (v : ℂ) * I)‖ ≤ g R)
    (hl : ∀ (R : ℝ), R ≥ 0 → ∀ v ∈ uIcc 0 y, ‖F ((-R : ℂ) + (v : ℂ) * I)‖ ≤ g R) :
    (∫ u : ℝ, F ((u : ℂ) + (y : ℂ) * I)) = ∫ u : ℝ, F (u : ℂ) := by
  have hrect (R : ℝ) :
      (∫ u : ℝ in -R..R, F (u : ℂ)) -
        (∫ u : ℝ in -R..R, F ((u : ℂ) + (y : ℂ) * I)) +
        I * (∫ v : ℝ in 0..y, F ((R : ℂ) + (v : ℂ) * I)) -
        I * (∫ v : ℝ in 0..y, F ((-R : ℂ) + (v : ℂ) * I)) = 0 := by
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      F ((-R : ℝ) : ℂ) ((R : ℂ) + (y : ℂ) * I) ?_
    · simpa using h
    · apply hF.mono
      intro w hw
      have him : w.im ∈ uIcc 0 y := by simpa using hw.2
      exact abs_le_of_uIcc_zero him
  have hgb : Tendsto (fun R : ℝ => g R * |y|) atTop (𝓝 0) := by
    simpa using hg.mul_const |y|
  have hright : Tendsto (fun R : ℝ => ∫ v : ℝ in 0..y,
      F ((R : ℂ) + (v : ℂ) * I)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hgb
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const
      (fun v hv => hr R hR v (uIoc_subset_uIcc hv))
  have hleft : Tendsto (fun R : ℝ => ∫ v : ℝ in 0..y,
      F ((-R : ℂ) + (v : ℂ) * I)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hgb
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const
      (fun v hv => hl R hR v (uIoc_subset_uIcc hv))
  have hbottom := intervalIntegral_tendsto_integral hI₀ tendsto_neg_atTop_atBot tendsto_id
  have htop := intervalIntegral_tendsto_integral hIy tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((hbottom.sub htop).add (hright.const_mul I)).sub (hleft.const_mul I)
  have hzlim : Tendsto (fun R : ℝ =>
      (∫ u : ℝ in -R..R, F (u : ℂ)) -
        (∫ u : ℝ in -R..R, F ((u : ℂ) + (y : ℂ) * I)) +
        I * (∫ v : ℝ in 0..y, F ((R : ℂ) + (v : ℂ) * I)) -
        I * (∫ v : ℝ in 0..y, F ((-R : ℂ) + (v : ℂ) * I))) atTop (𝓝 0) := by
    simp_rw [hrect]
    exact tendsto_const_nhds
  have heq := tendsto_nhds_unique hlim hzlim
  simpa using (sub_eq_zero.mp (by simpa using heq)).symm

def thetaFourierKernel (ξ w : ℂ) : ℂ :=
  complexThetaDensity w * Complex.exp (-I * ξ * w)

theorem thetaFourierKernel_differentiableOn (ξ : ℂ) :
    DifferentiableOn ℂ (thetaFourierKernel ξ) thetaStrip := by
  exact complexThetaDensity_differentiableOn_strip.mul (by fun_prop)

theorem norm_fourier_complex_exp_le (ξ w : ℂ) :
    ‖Complex.exp (-I * ξ * w)‖ ≤
      Real.exp (|ξ.im| * |w.re| + |ξ.re| * |w.im|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have h₁ := le_abs_self (ξ.im * w.re)
  have h₂ := le_abs_self (ξ.re * w.im)
  simp only [abs_mul] at h₁ h₂
  norm_num [Complex.mul_re, Complex.mul_im]
  linarith

/-- The theta Fourier kernel has a common superexponential bound
throughout every closed substrip, including both vertical ends. -/
theorem thetaFourierKernel_closed_strip_bound (ξ : ℂ) {b : ℝ}
    (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) :
    ∃ C > 0, ∃ c > 0, ∀ w : ℂ, |w.im| ≤ b →
      ‖thetaFourierKernel ξ w‖ ≤ C * ThetaTrial.ThetaSeries.doubleExpEnvelope
        ((9 / 2 : ℝ) + |ξ.im|) c |w.re| := by
  obtain ⟨C, hC, c, hc, htheta⟩ := complexThetaDensity_closed_strip_decay hb hbpi
  refine ⟨C * Real.exp (|ξ.re| * b), by positivity, c, hc, ?_⟩
  intro w hw
  have he : ‖Complex.exp (-I * ξ * w)‖ ≤
      Real.exp (|ξ.im| * |w.re| + |ξ.re| * b) :=
    (norm_fourier_complex_exp_le ξ w).trans (Real.exp_le_exp.mpr
      (by nlinarith [mul_le_mul_of_nonneg_left hw (abs_nonneg ξ.re)]))
  rw [thetaFourierKernel, norm_mul]
  calc
    _ ≤ (C * Real.exp (9 * |w.re| / 2) * Real.exp (-c * Real.exp (2 * |w.re|))) *
        Real.exp (|ξ.im| * |w.re| + |ξ.re| * b) :=
      mul_le_mul (htheta w hw) he (norm_nonneg _) (by positivity)
    _ = _ := by
      unfold ThetaTrial.ThetaSeries.doubleExpEnvelope
      rw [Real.exp_add, add_mul, Real.exp_add]
      have h : 9 * |w.re| / 2 = (9 / 2 : ℝ) * |w.re| := by ring
      rw [h]
      ring


theorem thetaFourierKernel_horizontal_integrable (ξ : ℂ) {y : ℝ}
    (hy : |y| < Real.pi / 4) :
    Integrable (fun u : ℝ => thetaFourierKernel ξ ((u : ℂ) + (y : ℂ) * I)) := by
  obtain ⟨C, hC, c, hc, hb⟩ :=
    thetaFourierKernel_closed_strip_bound ξ (abs_nonneg y) hy
  have hcont : Continuous (fun u : ℝ =>
      thetaFourierKernel ξ ((u : ℂ) + (y : ℂ) * I)) := by
    unfold thetaFourierKernel
    apply Continuous.mul
    · simpa only [iteratedDeriv_zero, mul_comm I] using
        RadicalApproximation.shiftedTheta_iteratedDeriv_continuous 0 hy
    · fun_prop
  apply ((RadicalApproximation.doubleExpEnvelope_abs_integrable _ hc).const_mul C).mono'
    hcont.aestronglyMeasurable
  filter_upwards with u
  simpa [Complex.mul_re, Complex.mul_im] using hb ((u : ℂ) + (y : ℂ) * I) (by simp)

/-- Cauchy's theorem on expanding rectangles for the theta kernel.
The two vertical sides are controlled by the closed-strip bound. -/
theorem thetaFourierKernel_integral_shift (ξ : ℂ) {y : ℝ}
    (hy : |y| < Real.pi / 4) :
    (∫ u : ℝ, thetaFourierKernel ξ ((u : ℂ) + (y : ℂ) * I)) =
      ∫ u : ℝ, thetaFourierKernel ξ (u : ℂ) := by
  obtain ⟨C, hC, c, hc, hb⟩ :=
    thetaFourierKernel_closed_strip_bound ξ (abs_nonneg y) hy
  apply horizontal_integral_eq_of_vertical_decay (thetaFourierKernel ξ) y
    ((thetaFourierKernel_differentiableOn ξ).mono (by
      intro w hw
      exact lt_of_le_of_lt hw hy))
    (by simpa using (thetaFourierKernel_horizontal_integrable ξ
      (y := 0) (by simpa using (show (0 : ℝ) < Real.pi / 4 by positivity))))
    (thetaFourierKernel_horizontal_integrable ξ hy)
    (fun R => C * ThetaTrial.ThetaSeries.doubleExpEnvelope ((9 / 2 : ℝ) + |ξ.im|) c R)
    (by simpa using (ThetaTrial.ThetaSeries.doubleExpEnvelope_tendsto
      ((9 / 2 : ℝ) + |ξ.im|) hc).const_mul C)
  · intro R hR v hv
    simpa [Complex.mul_re, Complex.mul_im, abs_of_nonneg hR] using
      hb ((R : ℂ) + (v : ℂ) * I) (by simpa using abs_le_of_uIcc_zero hv)
  · intro R hR v hv
    simpa [Complex.mul_re, Complex.mul_im, abs_of_nonneg hR] using
      hb ((-R : ℂ) + (v : ℂ) * I) (by simpa using abs_le_of_uIcc_zero hv)

theorem thetaFourierKernel_integral_real (ξ : ℂ) :
    (∫ u : ℝ, thetaFourierKernel ξ (u : ℂ)) = xiFunction ξ := by
  simpa only [thetaFourierKernel, complexThetaDensity_ofReal, paperFourier] using
    paperFourier_theta ξ

private theorem shifted_theta_fourier_integrand (ξ : ℂ) (u y : ℝ) :
    complexThetaDensity ((u : ℂ) + I * (y : ℂ)) *
      Complex.exp (-I * ξ * (u : ℂ)) =
    Complex.exp (-ξ * (y : ℂ)) *
      thetaFourierKernel ξ ((u : ℂ) + (y : ℂ) * I) := by
  have he : -ξ * (y : ℂ) + -I * ξ * ((u : ℂ) + (y : ℂ) * I) =
      -I * ξ * (u : ℂ) := by
    ring_nf
    simp [Complex.I_sq]
  unfold thetaFourierKernel
  rw [mul_left_comm, mul_assoc, ← Complex.exp_add, he, mul_comm I]
  simp only [mul_assoc]

/-- Fourier transform of an arbitrary fixed theta shift in the open
strip. The sign follows the paper's negative Fourier convention. -/
theorem paperFourier_theta_shifted (ξ : ℂ) {y : ℝ}
    (hy : |y| < Real.pi / 4) :
    paperFourier (fun u : ℝ => complexThetaDensity ((u : ℂ) + I * (y : ℂ))) ξ =
      Complex.exp (-ξ * (y : ℂ)) * xiFunction ξ := by
  unfold paperFourier
  simp_rw [shifted_theta_fourier_integrand]
  rw [integral_const_mul, thetaFourierKernel_integral_shift ξ hy,
    thetaFourierKernel_integral_real]

theorem paperFourier_theta_shifted_integrable (ξ : ℂ) {y : ℝ}
    (hy : |y| < Real.pi / 4) :
    Integrable (fun u : ℝ => complexThetaDensity ((u : ℂ) + I * (y : ℂ)) *
      Complex.exp (-I * ξ * (u : ℂ))) := by
  simp_rw [shifted_theta_fourier_integrand]
  exact (thetaFourierKernel_horizontal_integrable ξ hy).const_mul _


/-- Global measurability of the series definition; its analytic convergence
is separately established on the theta strip. -/
theorem complexThetaDensity_measurable : Measurable complexThetaDensity := by
  exact Measurable.tsum (fun n => (complexThetaMode_differentiable n).continuous.measurable)

def shiftedAverageFourierIntegrand (a : ℝ) (ξ : ℂ) (u y : ℝ) : ℂ :=
  (shiftWeight a y : ℂ) * complexThetaDensity ((u : ℂ) + I * (y : ℂ)) *
    Complex.exp (-I * ξ * (u : ℂ))

/-- The two-variable averaging/Fourier integrand is integrable. -/
theorem shiftedAverageFourierIntegrand_integrable {a : ℝ}
    (hb : 0 ≤ shiftWidth a) (ξ : ℂ) :
    Integrable (Function.uncurry (shiftedAverageFourierIntegrand a ξ))
      (volume.prod (volume.restrict (Icc (-shiftWidth a) (shiftWidth a)))) := by
  let J := Icc (-shiftWidth a) (shiftWidth a)
  let ν : Measure ℝ := volume.restrict J
  have hbpi : shiftWidth a < Real.pi / 4 := by
    have hZ : 0 < scaleZ a := mul_pos Real.pi_pos (Real.exp_pos _)
    unfold shiftWidth
    linarith [inv_pos.mpr hZ]
  obtain ⟨g, hg, hbound⟩ := RadicalApproximation.shiftedTheta_weighted_majorant
    0 |ξ.im| hb hbpi
  have hmeas : Measurable (Function.uncurry (shiftedAverageFourierIntegrand a ξ)) := by
    unfold shiftedAverageFourierIntegrand Function.uncurry
    exact ((by unfold shiftWeight; fun_prop : Measurable (fun p : ℝ × ℝ =>
      (shiftWeight a p.2 : ℂ))).mul
      (complexThetaDensity_measurable.comp (by fun_prop))).mul (by fun_prop)
  have hy : ∀ᵐ p : ℝ × ℝ ∂volume.prod ν, p.2 ∈ J := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_snd)).mpr
    exact Eventually.of_forall (fun _ => ae_restrict_mem measurableSet_Icc)
  apply (hg.comp_fst ν).mono' hmeas.aestronglyMeasurable
  filter_upwards [hy] with p hp
  have he : ‖Complex.exp (-I * ξ * (p.1 : ℂ))‖ ≤ Real.exp (|ξ.im| * |p.1|) := by
    simpa using norm_fourier_complex_exp_le ξ (p.1 : ℂ)
  have hw : ‖(shiftWeight a p.2 : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (shiftWeight_pos a p.2)]
    exact shiftWeight_le_one a p.2
  change ‖(shiftWeight a p.2 : ℂ) *
    complexThetaDensity ((p.1 : ℂ) + I * (p.2 : ℂ)) *
      Complex.exp (-I * ξ * (p.1 : ℂ))‖ ≤ g p.1
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ‖complexThetaDensity ((p.1 : ℂ) + I * (p.2 : ℂ))‖ *
        Real.exp (|ξ.im| * |p.1|) :=
      mul_le_mul (by simpa using mul_le_mul_of_nonneg_right hw (norm_nonneg _)) he
        (norm_nonneg _) (norm_nonneg _)
    _ ≤ g p.1 := by
      simpa only [iteratedDeriv_zero, mul_comm] using hbound p.1 p.2 (abs_le.mpr hp)

/-- Fourier integrability of the von Mises shifted theta average. -/
theorem paperFourier_shiftedAverage_integrable {a : ℝ}
    (hb : 0 ≤ shiftWidth a) (ξ : ℂ) :
    Integrable (fun u : ℝ => shiftedAverage a (u : ℂ) *
      Complex.exp (-I * ξ * (u : ℂ))) := by
  have h := (shiftedAverageFourierIntegrand_integrable hb ξ).integral_prod_left
  simpa only [Function.uncurry, shiftedAverageFourierIntegrand, integral_mul_const,
    shiftedAverage] using h

/-- The factorization in avg:factorization. Both contour shifting
and the exchange of integrations are proved from the theta decay. -/
theorem paperFourier_shiftedAverage {a : ℝ}
    (hb : 0 ≤ shiftWidth a) (ξ : ℂ) :
    paperFourier (fun u : ℝ => shiftedAverage a (u : ℂ)) ξ =
      xiFunction ξ * shiftMultiplier a ξ := by
  have hbpi : shiftWidth a < Real.pi / 4 := by
    have hZ : 0 < scaleZ a := mul_pos Real.pi_pos (Real.exp_pos _)
    unfold shiftWidth
    linarith [inv_pos.mpr hZ]
  calc
    _ = ∫ u : ℝ, ∫ y : ℝ in Icc (-shiftWidth a) (shiftWidth a),
        shiftedAverageFourierIntegrand a ξ u y := by
      simp only [paperFourier, shiftedAverage, shiftedAverageFourierIntegrand,
        integral_mul_const]
    _ = ∫ y : ℝ in Icc (-shiftWidth a) (shiftWidth a),
        ∫ u : ℝ, shiftedAverageFourierIntegrand a ξ u y :=
      integral_integral_swap (shiftedAverageFourierIntegrand_integrable hb ξ)
    _ = ∫ y : ℝ in Icc (-shiftWidth a) (shiftWidth a),
        (shiftWeight a y : ℂ) * (Complex.exp (-ξ * (y : ℂ)) * xiFunction ξ) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro y hy
      have hshift := paperFourier_theta_shifted ξ ((abs_le.mpr hy).trans_lt hbpi)
      simpa only [shiftedAverageFourierIntegrand, mul_assoc, integral_const_mul,
        paperFourier] using congrArg (fun q : ℂ => (shiftWeight a y : ℂ) * q) hshift
    _ = shiftMultiplier a (-ξ) * xiFunction ξ := by
      simp only [shiftMultiplier, ← mul_assoc, integral_mul_const]
    _ = _ := by rw [shiftMultiplier_neg, mul_comm]

end ThetaTrial.Paper
