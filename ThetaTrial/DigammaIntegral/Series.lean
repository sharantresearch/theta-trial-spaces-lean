import ThetaTrial.DigammaIntegral.Bounds
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Absolute integral convergence of the geometric digamma expansion -/

open Set MeasureTheory
open scoped Topology

namespace ThetaTrial.DigammaIntegral

theorem seriesTerm_eq_sub (z : ℂ) (n : ℕ) (t : ℝ) :
    seriesTerm z n t = Complex.exp (-((n : ℂ) + 1) * (t : ℂ)) -
      Complex.exp (-(z + n + 1) * (t : ℂ)) := by
  unfold seriesTerm
  rw [mul_sub, mul_one, ← Complex.exp_add]
  congr 2
  ring

theorem seriesTerm_integrable {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) :
    IntegrableOn (seriesTerm z n) (Ioi 0) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have h1 : (-((n : ℂ) + 1)).re < 0 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
    linarith
  have h2 : (-(z + n + 1)).re < 0 := by simp; linarith
  have h := (integrableOn_exp_mul_complex_Ioi h1 0).sub
    (integrableOn_exp_mul_complex_Ioi h2 0)
  apply h.congr_fun _ measurableSet_Ioi
  intro t ht
  exact (seriesTerm_eq_sub z n t).symm

theorem integral_seriesTerm {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) :
    (∫ t : ℝ in Ioi 0, seriesTerm z n t) =
      1 / ((n : ℂ) + 1) - 1 / (z + n + 1) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have h1 : (-((n : ℂ) + 1)).re < 0 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
    linarith
  have h2 : (-(z + n + 1)).re < 0 := by simp; linarith
  simp_rw [seriesTerm_eq_sub]
  rw [integral_sub (integrableOn_exp_mul_complex_Ioi h1 0)
    (integrableOn_exp_mul_complex_Ioi h2 0), integral_exp_mul_complex_Ioi h1,
    integral_exp_mul_complex_Ioi h2]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq]

theorem integral_norm_seriesTerm_le {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) :
    (∫ t : ℝ in Ioi 0, ‖seriesTerm z n t‖) ≤ ‖z‖ * (1 / ((n : ℝ) + 1) ^ 2) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  calc
    _ ≤ ∫ t : ℝ in Ioi 0, ‖z‖ * (t * Real.exp (-(((n : ℝ) + 1) * t))) := by
      apply integral_mono_ae (seriesTerm_integrable hz n).norm
        ((integrableOn_t_mul_exp_neg_mul hn).const_mul ‖z‖)
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact norm_seriesTerm_le hz n ht.le
    _ = _ := by rw [integral_const_mul, integral_t_mul_exp_neg_mul hn]

theorem summable_integral_norm_seriesTerm {z : ℂ} (hz : 0 ≤ z.re) :
    Summable (fun n : ℕ => ∫ t : ℝ in Ioi 0, ‖seriesTerm z n t‖) := by
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)))
  exact Summable.of_nonneg_of_le (fun n => integral_nonneg (fun t => norm_nonneg _))
    (integral_norm_seriesTerm_le hz) (hs.mul_left ‖z‖)

theorem seriesTerm_eq_geometric (z : ℂ) (n : ℕ) (t : ℝ) :
    seriesTerm z n t = (Complex.exp (-(t : ℂ))) ^ n *
      (Complex.exp (-(t : ℂ)) * (1 - Complex.exp (-z * (t : ℂ)))) := by
  unfold seriesTerm
  rw [← Complex.exp_nat_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem hasSum_seriesTerm (z : ℂ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => seriesTerm z n t) (shiftedKernel z t) := by
  have hr : ‖Complex.exp (-(t : ℂ))‖ < 1 := by
    simpa [Complex.norm_exp] using exp_neg_lt_one ht
  have h := (hasSum_geometric_of_norm_lt_one hr).mul_right
    (Complex.exp (-(t : ℂ)) * (1 - Complex.exp (-z * (t : ℂ))))
  have heq : (1 - Complex.exp (-(t : ℂ)))⁻¹ *
      (Complex.exp (-(t : ℂ)) * (1 - Complex.exp (-z * (t : ℂ)))) = shiftedKernel z t := by
    unfold shiftedKernel
    ring
  rw [heq] at h
  exact h.congr_fun (fun n => seriesTerm_eq_geometric z n t)

theorem integral_shiftedKernel_eq_tsum {z : ℂ} (hz : 0 ≤ z.re) :
    (∫ t : ℝ in Ioi 0, shiftedKernel z t) =
      ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
  have h := integral_tsum_of_summable_integral_norm
    (seriesTerm_integrable hz) (summable_integral_norm_seriesTerm hz)
  calc
    _ = ∫ t : ℝ in Ioi 0, ∑' n : ℕ, seriesTerm z n t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact (hasSum_seriesTerm z ht).tsum_eq.symm
    _ = ∑' n : ℕ, ∫ t : ℝ in Ioi 0, seriesTerm z n t := h.symm
    _ = _ := by simp_rw [integral_seriesTerm hz]

end ThetaTrial.DigammaIntegral
