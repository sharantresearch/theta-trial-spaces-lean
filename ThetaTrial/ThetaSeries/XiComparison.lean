/- The comparison `xi(6) < 2 xi(1/2)`, from the theta representation and
elementary geometric majorants. -/
import ThetaTrial.ThetaSeries.PhiIntegral
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

noncomputable section
open Complex Filter MeasureTheory Set
open scoped BigOperators Topology

namespace ThetaTrial.ThetaSeries

theorem exp_pi_gt_sixteen : (16 : ℝ) < Real.exp Real.pi := by
  have he := Real.sum_le_exp_of_nonneg (x := (3 : ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have hp := Real.exp_lt_exp.mpr Real.pi_gt_three
  linarith

theorem exp_neg_pi_le_one_div_sixteen : Real.exp (-Real.pi) ≤ (1 / 16 : ℝ) := by
  have hh := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 16) exp_pi_gt_sixteen
  simpa only [Real.exp_neg, one_div] using hh.le

theorem exp_neg_three_pi_le_one_div_eight : Real.exp (-3 * Real.pi) ≤ (1 / 8 : ℝ) := by
  have he := Real.add_one_le_exp (3 * Real.pi)
  have hh : (8 : ℝ) < Real.exp (3 * Real.pi) := by linarith [Real.pi_gt_three]
  have hi := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 8) hh
  simpa only [neg_mul, Real.exp_neg, one_div] using hi.le

theorem thetaBTerm_exponential_bound (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    thetaBTerm n u ≤ Real.exp (-Real.pi) * Real.exp (-3 * Real.pi) ^ n *
      Real.exp (-(2 * Real.pi - 1 / 2) * u) := by
  have hn : 1 + 3 * (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    cases n with
    | zero => norm_num
    | succ m => push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) m, sq_nonneg (m : ℝ)]
  have hsq : 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have he := Real.add_one_le_exp (2 * u)
  have hExp : 1 ≤ Real.exp (2 * u) := by linarith
  have hm := mul_nonneg (sub_nonneg.mpr hsq) (sub_nonneg.mpr hExp)
  have hprod : 1 + 3 * (n : ℝ) + 2 * u ≤
      ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u) := by nlinarith
  have hp := mul_le_mul_of_nonneg_left hprod Real.pi_pos.le
  have hpow : Real.exp (-3 * Real.pi) ^ n = Real.exp (-3 * Real.pi * (n : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [thetaBTerm, ← Real.exp_add, hpow, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem thetaBTerm_coarse_bound (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    thetaBTerm n u ≤ (1 / 16 : ℝ) * (1 / 8 : ℝ) ^ n * Real.exp ((-11 / 2 : ℝ) * u) := by
  have hr : Real.exp (-(2 * Real.pi - 1 / 2) * u) ≤
      Real.exp ((-11 / 2 : ℝ) * u) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) hu]
  have hpow := pow_le_pow_left₀ (Real.exp_pos (-3 * Real.pi)).le
    exp_neg_three_pi_le_one_div_eight n
  exact (thetaBTerm_exponential_bound n hu).trans
    (mul_le_mul (mul_le_mul exp_neg_pi_le_one_div_sixteen hpow (by positivity) (by norm_num))
      hr (by positivity) (by positivity))

theorem thetaB_coarse_bound {u : ℝ} (hu : 0 ≤ u) :
    thetaB u ≤ (1 / 14 : ℝ) * Real.exp ((-11 / 2 : ℝ) * u) := by
  have hs := ((hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 8)
    (by norm_num : (1 / 8 : ℝ) < 1)).mul_left (1 / 16 : ℝ)).mul_right
      (Real.exp ((-11 / 2 : ℝ) * u))
  have hb := hasSum_le (fun n => thetaBTerm_coarse_bound n hu) (thetaBTerm_hasSum u) hs
  norm_num at hb
  simpa only [one_div, neg_div, neg_mul] using hb

theorem thetaB_integrable : IntegrableOn thetaB (Ioi 0) := by
  have hc : IntegrableOn (fun u : ℝ => (thetaB u : ℂ)) (Ioi 0) := by
    simpa using thetaB_cosh_integrable 0
  convert hc.re using 1; rfl

theorem thetaB_integral_le_one_div_77 : (∫ u : ℝ in Ioi 0, thetaB u) ≤ 1 / 77 := by
  have he := (integrableOn_exp_mul_Ioi (by norm_num : (-11 / 2 : ℝ) < 0) 0).const_mul
    (1 / 14 : ℝ)
  have hle := setIntegral_mono_on thetaB_integrable he measurableSet_Ioi
    (fun u hu => thetaB_coarse_bound hu.le)
  rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-11 / 2 : ℝ) < 0) 0] at hle
  norm_num at hle
  exact hle

theorem two_xi_half_re_eq_one_sub_thetaB_integral :
    2 * (ThetaTrial.xi (1 / 2)).re = 1 - ∫ u : ℝ in Ioi 0, thetaB u := by
  have hc := xi_centered_eq_thetaB 0
  simp only [add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_sub, mul_zero, Complex.cosh_zero, mul_one] at hc
  rw [integral_complex_ofReal] at hc
  have hr := congrArg Complex.re hc
  norm_num [Complex.mul_re] at hr
  linarith

theorem two_xi_half_re_ge_76_div_77 : (76 / 77 : ℝ) ≤ 2 * (ThetaTrial.xi (1 / 2)).re := by
  rw [two_xi_half_re_eq_one_sub_thetaB_integral]
  linarith [thetaB_integral_le_one_div_77]

end ThetaTrial.ThetaSeries
