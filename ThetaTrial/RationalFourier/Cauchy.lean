import ThetaTrial.FourierNormalization
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! # The base Cauchy Fourier integral -/

open Set MeasureTheory Complex
open scoped FourierTransform

namespace ThetaTrial.RationalFourier

noncomputable def laplace (H u : ℝ) : ℂ := (Real.exp (-H * |u|) : ℂ)

noncomputable def laplacePhase (H τ u : ℝ) : ℂ :=
  laplace H u * Complex.exp (-Complex.I * (τ : ℂ) * (u : ℂ))

theorem laplacePhase_scale {H : ℝ} (hH : 0 < H) (τ u : ℝ) :
    (Real.exp (-|2 * H * u| / 2) : ℂ) *
        Complex.exp (-Complex.I * ((τ / (2 * H) : ℝ) : ℂ) * ((2 * H * u : ℝ) : ℂ)) =
      laplacePhase H τ u := by
  have ha : -|2 * H * u| / 2 = -H * |u| := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * H)]
    ring
  have hp : -Complex.I * ((τ / (2 * H) : ℝ) : ℂ) * ((2 * H * u : ℝ) : ℂ) =
      -Complex.I * (τ : ℂ) * (u : ℂ) := by
    have hHC : (H : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hH.ne'
    push_cast
    field_simp [hHC]
  rw [ha, hp]
  rfl

theorem laplacePhase_integrable {H : ℝ} (hH : 0 < H) (τ : ℝ) :
    Integrable (laplacePhase H τ) := by
  have h := (Zeta23.EF.integrable_exp_neg_abs_half_mul (τ / (2 * H))).comp_mul_left'
    (by positivity : 2 * H ≠ 0)
  simpa only [laplacePhase_scale hH] using h

theorem laplace_integrable {H : ℝ} (hH : 0 < H) : Integrable (laplace H) := by
  have heq : laplacePhase H 0 = laplace H := by
    funext u
    simp [laplacePhase]
  rw [← heq]
  exact laplacePhase_integrable hH 0

theorem integral_laplacePhase {H : ℝ} (hH : 0 < H) (τ : ℝ) :
    (∫ u : ℝ, laplacePhase H τ u) =
      (2 * H : ℂ) / ((H : ℂ) ^ 2 + (τ : ℂ) ^ 2) := by
  have h := Measure.integral_comp_mul_left
    (fun u : ℝ => (Real.exp (-|u| / 2) : ℂ) *
      Complex.exp (-Complex.I * ((τ / (2 * H) : ℝ) : ℂ) * (u : ℂ))) (2 * H)
  simp only [laplacePhase_scale hH, Zeta23.EF.integral_exp_neg_abs_half,
    abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * H)), Complex.real_smul] at h
  rw [h]
  have hHC : (H : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hH.ne'
  have hd : (H : ℂ) ^ 2 + (τ : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (show H ^ 2 + τ ^ 2 ≠ 0 by positivity)
  have hd' : (1 / 4 : ℂ) + ((τ / (2 * H) : ℝ) : ℂ) ^ 2 ≠ 0 := by
    rw [show (1 / 4 : ℂ) + ((τ / (2 * H) : ℝ) : ℂ) ^ 2 =
      (((1 / 4 : ℝ) + (τ / (2 * H)) ^ 2 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hd4 : (H : ℂ) ^ 2 * 4 + (τ : ℂ) ^ 2 * 4 ≠ 0 := by
    convert mul_ne_zero hd (by norm_num : (4 : ℂ) ≠ 0) using 1; ring
  push_cast at hd' ⊢
  field_simp [hHC, hd, hd', hd4]
  linear_combination mul_inv_cancel₀ hd4

theorem cauchy_integrable {H : ℝ} (hH : 0 < H) :
    Integrable (fun x : ℝ => 1 / (H ^ 2 + x ^ 2)) := by
  have h := (integrable_inv_one_add_sq.comp_div hH.ne').const_mul (1 / H ^ 2)
  apply h.congr
  filter_upwards [] with x
  have hd : H ^ 2 + x ^ 2 ≠ 0 := by positivity
  field_simp

theorem cauchy_phase_integrable {H : ℝ} (hH : 0 < H) (h : ℝ) :
    Integrable (fun x : ℝ => Complex.exp (Complex.I * (h : ℂ) * (x : ℂ)) /
      ((H : ℂ) ^ 2 + (x : ℂ) ^ 2)) := by
  apply (cauchy_integrable hH).mono'
    (by apply Continuous.aestronglyMeasurable; apply Continuous.div <;> try fun_prop
        intro x; exact_mod_cast (show H ^ 2 + x ^ 2 ≠ 0 by positivity))
  filter_upwards [] with x
  rw [norm_div, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, one_mul,
    sub_zero, zero_add, Real.exp_zero]
  rw [show ((H : ℂ) ^ 2 + (x : ℂ) ^ 2) = ((H ^ 2 + x ^ 2 : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < H ^ 2 + x ^ 2)]

theorem fourier_laplace {H : ℝ} (hH : 0 < H) (ξ : ℝ) :
    𝓕 (laplace H) ξ = (2 * H : ℂ) / ((H : ℂ) ^ 2 + ((2 * Real.pi * ξ : ℝ) : ℂ) ^ 2) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have heq (u : ℝ) : Complex.exp (((-2 * Real.pi * u * ξ : ℝ) : ℂ) * Complex.I) • laplace H u =
      laplacePhase H (2 * Real.pi * ξ) u := by
    simp only [smul_eq_mul, laplacePhase]
    rw [mul_comm]
    congr 1
    congr 1
    push_cast
    ring
  simp_rw [heq]
  exact integral_laplacePhase hH _

theorem fourier_laplace_integrable {H : ℝ} (hH : 0 < H) : Integrable (𝓕 (laplace H)) := by
  have hr := ((cauchy_integrable hH).comp_mul_left'
    (by positivity : 2 * Real.pi ≠ 0)).const_mul (2 * H)
  apply hr.ofReal.congr
  filter_upwards [] with ξ
  rw [fourier_laplace hH]
  push_cast
  ring_nf
  rfl

/-- The Cauchy Fourier integral, proved by Fourier inversion of a two-sided exponential. -/
theorem integral_cauchy_phase {H : ℝ} (hH : 0 < H) (h : ℝ) :
    (∫ x : ℝ, Complex.exp (Complex.I * (h : ℂ) * (x : ℂ)) /
      ((H : ℂ) ^ 2 + (x : ℂ) ^ 2)) =
      (Real.pi : ℂ) / H * (Real.exp (-H * |h|) : ℂ) := by
  let φ : ℝ → ℂ := fun x => Complex.exp (Complex.I * (h : ℂ) * (x : ℂ)) /
    ((H : ℂ) ^ 2 + (x : ℂ) ^ 2)
  have hv := (laplace_integrable hH).fourierInv_fourier_eq (fourier_laplace_integrable hH)
    (show ContinuousAt (laplace H) h by unfold laplace; fun_prop)
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at hv
  simp_rw [fourier_laplace hH] at hv
  have heq (x : ℝ) : Complex.exp (((-2 * Real.pi * x * (-h) : ℝ) : ℂ) * Complex.I) •
      ((2 * H : ℂ) / ((H : ℂ) ^ 2 + ((2 * Real.pi * x : ℝ) : ℂ) ^ 2)) =
        (2 * H : ℂ) * φ (2 * Real.pi * x) := by
    unfold φ
    simp only [smul_eq_mul]
    have hexp : (((-2 * Real.pi * x * (-h) : ℝ) : ℂ) * Complex.I) =
        Complex.I * (h : ℂ) * ((2 * Real.pi * x : ℝ) : ℂ) := by push_cast; ring
    rw [hexp]
    ring
  simp_rw [heq] at hv
  rw [integral_const_mul, Measure.integral_comp_mul_left φ (2 * Real.pi)] at hv
  simp only [abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * Real.pi)), Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat, laplace] at hv
  have hHC : (H : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hH.ne'
  have hpC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  change (∫ x : ℝ, φ x) = _
  field_simp at hv ⊢
  linear_combination hv

end ThetaTrial.RationalFourier
