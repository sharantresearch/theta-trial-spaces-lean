import ThetaTrial.DigammaIntegral

/-! # The gamma multiplier as a convergent cosine-difference integral -/

open Set MeasureTheory

namespace ThetaTrial.GammaEnergy

noncomputable def gammaMultiplier (x : ℝ) : ℝ :=
  (Complex.digamma ((1 / 4 : ℂ) + Complex.I * (x / 2 : ℝ))).re - Real.log Real.pi

noncomputable def gammaBase : ℝ := (Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi

noncomputable def shiftKernel (h : ℝ) : ℝ :=
  Real.exp (-h / 2) / (1 - Real.exp (-2 * h))

noncomputable def differenceKernel (z w : ℂ) (t : ℝ) : ℂ :=
  (Complex.exp (-w * (t : ℂ)) - Complex.exp (-z * (t : ℂ))) /
    (1 - Complex.exp (-(t : ℂ)))

theorem differenceKernel_eq (z w : ℂ) (t : ℝ) :
    differenceKernel z w t =
      ThetaTrial.DigammaIntegral.gaussKernel z t - ThetaTrial.DigammaIntegral.gaussKernel w t := by
  unfold differenceKernel ThetaTrial.DigammaIntegral.gaussKernel
  ring

theorem differenceKernel_integrable {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    IntegrableOn (differenceKernel z w) (Ioi 0) := by
  have h : IntegrableOn (fun t => ThetaTrial.DigammaIntegral.gaussKernel z t -
      ThetaTrial.DigammaIntegral.gaussKernel w t) (Ioi 0) :=
    (ThetaTrial.DigammaIntegral.gaussKernel_integrable hz).sub
      (ThetaTrial.DigammaIntegral.gaussKernel_integrable hw)
  apply h.congr_fun _ measurableSet_Ioi
  intro t ht
  exact (differenceKernel_eq z w t).symm

theorem digamma_sub_eq_integral {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    Complex.digamma z - Complex.digamma w =
      ∫ t : ℝ in Ioi 0, differenceKernel z w t := by
  simp_rw [differenceKernel_eq]
  rw [integral_sub (ThetaTrial.DigammaIntegral.gaussKernel_integrable hz)
    (ThetaTrial.DigammaIntegral.gaussKernel_integrable hw),
    ← ThetaTrial.DigammaIntegral.gauss_integral hz, ← ThetaTrial.DigammaIntegral.gauss_integral hw]
  ring

noncomputable def cosineKernel (a b t : ℝ) : ℝ :=
  Real.exp (-(a * t)) * (1 - Real.cos (b * t)) / (1 - Real.exp (-t))

theorem differenceKernel_re (a b t : ℝ) :
    (differenceKernel ((a : ℂ) + Complex.I * b) (a : ℂ) t).re = cosineKernel a b t := by
  unfold differenceKernel cosineKernel
  rw [show (1 - Complex.exp (-(t : ℂ))) = ((1 - Real.exp (-t) : ℝ) : ℂ) by simp,
    Complex.div_ofReal_re, Complex.sub_re, Complex.exp_re, Complex.exp_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero, zero_add,
    one_mul, neg_zero, Real.cos_zero, mul_one, neg_mul, Real.cos_neg]
  congr 1
  ring

theorem cosineKernel_integrable {a : ℝ} (ha : 0 < a) (b : ℝ) :
    IntegrableOn (cosineKernel a b) (Ioi 0) := by
  have hz : 0 < ((a : ℂ) + Complex.I * b).re := by simpa using ha
  have h : IntegrableOn (fun t => (differenceKernel ((a : ℂ) + Complex.I * b) a t).re)
      (Ioi 0) := (differenceKernel_integrable hz (by simpa using ha)).re
  apply h.congr_fun _ measurableSet_Ioi
  intro t ht
  exact differenceKernel_re a b t

theorem digamma_re_sub_eq_integral {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (Complex.digamma ((a : ℂ) + Complex.I * b)).re - (Complex.digamma (a : ℂ)).re =
      ∫ t : ℝ in Ioi 0, cosineKernel a b t := by
  have hz : 0 < ((a : ℂ) + Complex.I * b).re := by simpa using ha
  have h := congrArg Complex.re (digamma_sub_eq_integral (w := (a : ℂ)) hz (by simpa using ha))
  have hr := Complex.reCLM.integral_comp_comm
    (differenceKernel_integrable (w := (a : ℂ)) hz (by simpa using ha))
  simp only [Complex.reCLM_apply] at hr
  rw [Complex.sub_re, ← hr] at h
  simpa only [differenceKernel_re] using h

theorem cosineKernel_rescale (x h : ℝ) :
    cosineKernel (1 / 4) (x / 2) (2 * h) = shiftKernel h * (1 - Real.cos (h * x)) := by
  unfold cosineKernel shiftKernel
  have h1 : -(1 / 4 * (2 * h)) = -h / 2 := by ring
  have h2 : x / 2 * (2 * h) = h * x := by ring
  rw [h1, h2]
  simp only [neg_mul]
  ring

/-- Integrability of the cosine-difference expression, for every real frequency. -/
theorem shiftKernel_cosine_integrable (x : ℝ) :
    IntegrableOn (fun h => shiftKernel h * (1 - Real.cos (h * x))) (Ioi 0) := by
  have h := (integrableOn_Ioi_comp_mul_left_iff (cosineKernel (1 / 4) (x / 2)) 0
    (by norm_num : (0 : ℝ) < 2)).mpr
      (by simpa only [mul_zero] using cosineKernel_integrable (a := 1 / 4) (by norm_num) (x / 2))
  simpa only [cosineKernel_rescale] using h

/-- The multiplier difference identity, with its factor two. -/
theorem gammaMultiplier_sub_base (x : ℝ) :
    gammaMultiplier x - gammaBase =
      2 * ∫ h : ℝ in Ioi 0, shiftKernel h * (1 - Real.cos (h * x)) := by
  have hd := digamma_re_sub_eq_integral (a := 1 / 4) (by norm_num) (x / 2)
  have hs := integral_comp_mul_left_Ioi' (cosineKernel (1 / 4) (x / 2)) 0
    (by norm_num : (0 : ℝ) < 2)
  simp only [mul_zero, smul_eq_mul, cosineKernel_rescale] at hs
  unfold gammaMultiplier gammaBase
  rw [sub_sub_sub_cancel_right]
  calc
    _ = ∫ t : ℝ in Ioi 0, cosineKernel (1 / 4) (x / 2) t := by simpa using hd
    _ = _ := hs.symm

theorem shiftKernel_pos {h : ℝ} (hh : 0 < h) : 0 < shiftKernel h := by
  unfold shiftKernel
  apply div_pos (Real.exp_pos _)
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  linarith

theorem gammaMultiplier_sub_base_nonneg (x : ℝ) : 0 ≤ gammaMultiplier x - gammaBase := by
  rw [gammaMultiplier_sub_base]
  apply mul_nonneg (by norm_num)
  apply setIntegral_nonneg measurableSet_Ioi
  intro h hh
  exact mul_nonneg (shiftKernel_pos hh).le (sub_nonneg.mpr (Real.cos_le_one _))

end ThetaTrial.GammaEnergy
