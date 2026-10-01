import ThetaTrial.RationalFourier.CauchyReal
import ThetaTrial.RationalFourier.LaplaceDigamma
import Mathlib.MeasureTheory.Integral.Prod

/-! The digamma Cauchy mean, with product integrability before Fubini. -/

open Set MeasureTheory

namespace ThetaTrial.RationalFourier
open ThetaTrial.GammaEnergy

noncomputable def gammaCauchyJoint (H h x : ℝ) : ℝ :=
  shiftKernel h * (1 - Real.cos (h * x)) / (H ^ 2 + x ^ 2)

theorem gammaCauchyJoint_measurable (H : ℝ) :
    Measurable (Function.uncurry (gammaCauchyJoint H)) := by
  unfold gammaCauchyJoint shiftKernel
  fun_prop

theorem gammaCauchyJoint_nonneg {H h : ℝ} (hh : 0 < h) (x : ℝ) :
    0 ≤ gammaCauchyJoint H h x := by
  exact div_nonneg (mul_nonneg (shiftKernel_pos hh).le
    (sub_nonneg.mpr (Real.cos_le_one _))) (by positivity)

theorem gammaCauchyJoint_inner_integrable {H : ℝ} (hH : 0 < H) (h : ℝ) :
    Integrable (gammaCauchyJoint H h) := by
  apply ((cauchy_one_sub_cosine_integrable hH h).const_mul (shiftKernel h)).congr
  filter_upwards [] with x
  unfold gammaCauchyJoint
  ring

theorem gammaCauchyJoint_inner_integral {H : ℝ} (hH : 0 < H) {h : ℝ} (hh : 0 ≤ h) :
    (∫ x : ℝ, gammaCauchyJoint H h x) = Real.pi / H * horizontalKernel H h := by
  unfold gammaCauchyJoint horizontalKernel
  simp_rw [mul_div_assoc]
  rw [integral_const_mul, integral_cauchy_one_sub_cosine hH hh]
  ring

/-- The positive iterated norm integral is finite; this proves the required product integrability. -/
theorem gammaCauchyJoint_integrable {H : ℝ} (hH : 0 < H) :
    Integrable (Function.uncurry (gammaCauchyJoint H))
      ((volume.restrict (Ioi 0)).prod volume) := by
  apply (integrable_prod_iff (gammaCauchyJoint_measurable H).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [] with h
    exact gammaCauchyJoint_inner_integrable hH h
  · apply ((horizontalKernel_integrable hH).const_mul (Real.pi / H)).congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with h hh
    dsimp only [Function.uncurry]
    have heq (x : ℝ) : ‖gammaCauchyJoint H h x‖ = gammaCauchyJoint H h x :=
      Real.norm_of_nonneg (gammaCauchyJoint_nonneg hh x)
    simp_rw [heq]
    exact (gammaCauchyJoint_inner_integral hH (le_of_lt hh)).symm

theorem gamma_cauchy_difference_eq_integral (H x : ℝ) :
    (gammaMultiplier x - gammaBase) / (H ^ 2 + x ^ 2) =
      2 * ∫ h : ℝ in Ioi 0, gammaCauchyJoint H h x := by
  rw [gammaMultiplier_sub_base]
  unfold gammaCauchyJoint
  rw [integral_div]
  ring

theorem gamma_cauchy_difference_integrable {H : ℝ} (hH : 0 < H) :
    Integrable (fun x : ℝ => (gammaMultiplier x - gammaBase) / (H ^ 2 + x ^ 2)) := by
  apply ((gammaCauchyJoint_integrable hH).integral_prod_right.const_mul 2).congr
  filter_upwards [] with x
  exact (gamma_cauchy_difference_eq_integral H x).symm

/-- Absolute integrability of the gamma multiplier against the Cauchy weight. -/
theorem gamma_cauchy_integrable {H : ℝ} (hH : 0 < H) :
    Integrable (fun x : ℝ => gammaMultiplier x / (H ^ 2 + x ^ 2)) := by
  apply ((gamma_cauchy_difference_integrable hH).add
    ((cauchy_integrable hH).const_mul gammaBase)).congr
  filter_upwards [] with x
  dsimp
  ring

end ThetaTrial.RationalFourier
