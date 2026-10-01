import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

/-! # Cancellation and integrability bounds for the Gauss digamma kernel -/

open Set MeasureTheory
open scoped Topology

namespace ThetaTrial.DigammaIntegral

noncomputable def shiftedKernel (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(t : ℂ)) * (1 - Complex.exp (-z * (t : ℂ))) /
    (1 - Complex.exp (-(t : ℂ)))

noncomputable def seriesTerm (z : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (-((n : ℂ) + 1) * (t : ℂ)) * (1 - Complex.exp (-z * (t : ℂ)))

theorem norm_one_sub_exp_neg_mul_le {z : ℂ} (hz : 0 ≤ z.re) {t : ℝ} (ht : 0 ≤ t) :
    ‖1 - Complex.exp (-z * (t : ℂ))‖ ≤ ‖z‖ * t := by
  have hderiv (u : ℝ) : HasDerivAt (fun u : ℝ => Complex.exp (-z * (u : ℂ)))
      (Complex.exp (-z * (u : ℂ)) * (-z)) u := by
    simpa using (((hasDerivAt_id u).ofReal_comp).const_mul (-z)).cexp
  have hbound (u : ℝ) (hu : u ∈ Ico 0 t) :
      ‖Complex.exp (-z * (u : ℂ)) * (-z)‖ ≤ ‖z‖ := by
    rw [norm_mul, norm_neg, Complex.norm_exp]
    have hre : (-z * (u : ℂ)).re ≤ 0 := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz) hu.1
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr hre) (norm_nonneg z)).trans_eq
      (one_mul _)
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun u (_ : u ∈ Icc 0 t) => (hderiv u).hasDerivWithinAt) hbound t ⟨ht, le_rfl⟩
  simpa only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_zero,
    norm_sub_rev] using h

theorem exp_neg_lt_one {t : ℝ} (ht : 0 < t) : Real.exp (-t) < 1 :=
  Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)

theorem one_sub_cexp_neg_ne_zero {t : ℝ} (ht : 0 < t) :
    1 - Complex.exp (-(t : ℂ)) ≠ 0 := by
  have h : (1 : ℝ) - Real.exp (-t) ≠ 0 := ne_of_gt (sub_pos.mpr (exp_neg_lt_one ht))
  exact_mod_cast h

theorem t_div_one_sub_exp_neg_le {t : ℝ} (ht : 0 < t) :
    t / (1 - Real.exp (-t)) ≤ 1 + t := by
  apply (div_le_iff₀ (sub_pos.mpr (exp_neg_lt_one ht))).mpr
  have h := Real.add_one_le_exp t
  have hprod : (1 + t) * Real.exp (-t) ≤ 1 := by
    calc
      _ ≤ Real.exp t * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add]; simp
  nlinarith

theorem norm_shiftedKernel_le {z : ℂ} (hz : 0 ≤ z.re) {t : ℝ} (ht : 0 < t) :
    ‖shiftedKernel z t‖ ≤ ‖z‖ * ((1 + t) * Real.exp (-t)) := by
  have hden : 0 < 1 - Real.exp (-t) := sub_pos.mpr (exp_neg_lt_one ht)
  have hnorm : ‖1 - Complex.exp (-(t : ℂ))‖ = 1 - Real.exp (-t) := by
    rw [show (1 - Complex.exp (-(t : ℂ))) = ((1 - Real.exp (-t) : ℝ) : ℂ) by simp]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
  unfold shiftedKernel
  rw [norm_div, norm_mul, hnorm, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re]
  calc
    _ ≤ Real.exp (-t) * (‖z‖ * t) / (1 - Real.exp (-t)) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (norm_one_sub_exp_neg_mul_le hz ht.le) (Real.exp_nonneg _))
        hden.le
    _ = (‖z‖ * Real.exp (-t)) * (t / (1 - Real.exp (-t))) := by ring
    _ ≤ (‖z‖ * Real.exp (-t)) * (1 + t) :=
      mul_le_mul_of_nonneg_left (t_div_one_sub_exp_neg_le ht) (by positivity)
    _ = _ := by ring

theorem integrableOn_t_mul_exp_neg_mul {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-(r * t))) (Ioi 0) := by
  simpa only [Real.rpow_one, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := r)
      (by norm_num) (by norm_num) hr)

theorem integral_t_mul_exp_neg_mul {r : ℝ} (hr : 0 < r) :
    (∫ t : ℝ in Ioi 0, t * Real.exp (-(r * t))) = 1 / r ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) hr
  norm_num [Real.Gamma_add_one, Real.Gamma_one, Real.rpow_natCast] at h
  simpa only [one_div] using h

theorem shiftedKernel_integrable {z : ℂ} (hz : 0 ≤ z.re) :
    IntegrableOn (shiftedKernel z) (Ioi 0) := by
  have hb : IntegrableOn (fun t : ℝ => ‖z‖ * ((1 + t) * Real.exp (-t))) (Ioi 0) := by
    have h := (integrableOn_exp_neg_Ioi 0).add
      (integrableOn_t_mul_exp_neg_mul (r := 1) (by norm_num))
    apply (h.const_mul ‖z‖).congr
    filter_upwards [] with t
    dsimp
    simp only [one_mul]
    ring
  have hm : AEStronglyMeasurable (shiftedKernel z) (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro t ht
    apply ContinuousWithinAt.div
    · fun_prop
    · fun_prop
    · exact one_sub_cexp_neg_ne_zero ht
  apply hb.mono' hm
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  exact norm_shiftedKernel_le hz ht

theorem norm_seriesTerm_le {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖seriesTerm z n t‖ ≤ ‖z‖ * (t * Real.exp (-(((n : ℝ) + 1) * t))) := by
  unfold seriesTerm
  rw [norm_mul, Complex.norm_exp]
  have hre : (-((n : ℂ) + 1) * (t : ℂ)).re = -(((n : ℝ) + 1) * t) := by simp; ring
  rw [hre]
  calc
    _ ≤ Real.exp (-(((n : ℝ) + 1) * t)) * (‖z‖ * t) :=
      mul_le_mul_of_nonneg_left (norm_one_sub_exp_neg_mul_le hz ht) (Real.exp_nonneg _)
    _ = _ := by ring

end ThetaTrial.DigammaIntegral
