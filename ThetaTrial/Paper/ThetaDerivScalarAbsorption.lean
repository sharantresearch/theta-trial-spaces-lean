import ThetaTrial.Paper.ThetaConcentration
import Mathlib.Tactic

/-! Uniform scalar absorption for the theta-derivative sector.
The constants are independent of the polynomial and its degree. -/

noncomputable section
namespace ThetaTrial.Paper

theorem thetaDeriv_scalar_absorption (C : ℝ) (hC : 0 < C) :
    ∃ c : ℝ, 0 < c ∧ ∃ a₀ : ℝ, 1 ≤ a₀ ∧
      ∀ a : ℝ, a₀ ≤ a → ∀ d : ℕ, (d : ℝ) ≤ c * Real.exp a →
        1 ≤ a ∧ 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a ∧
        40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a ∧
        40 * thetaDerivTailWidth d a ≤ Real.log 2 ∧
        a / 4 ≤ Real.log (scaleT a) - Real.log ((d : ℝ) + 2) - C -
          C * ((d : ℝ) + 2) * a * Real.exp (-a) := by
  let c : ℝ := 1 / (16 * (C + 1))
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by dsimp [c]; apply (div_le_one (by positivity)).mpr; linarith
  have hCc : 2 * C * c ≤ 1 / 8 := by
    dsimp [c]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
    field_simp
    nlinarith
  let a₀ : ℝ := max 2 (max (2 / c) (max (80 / (Real.pi * Real.log 2)) (2 * C + 1)))
  have ha₀ : 1 ≤ a₀ := by dsimp [a₀]; exact le_trans (by norm_num) (le_max_left _ _)
  refine ⟨c, hc, a₀, ha₀, ?_⟩
  intro a ha d hd
  have ha1 : 1 ≤ a := ha₀.trans ha
  have ha0 : 0 ≤ a := by linarith
  have hEa : a ≤ Real.exp a := le_trans (by linarith) (Real.add_one_le_exp a)
  have he : 0 < Real.exp a := Real.exp_pos a
  have h2c : 2 / c ≤ a := (le_trans (le_max_left _ _) (le_max_right _ _)).trans ha
  have h80 : 80 / (Real.pi * Real.log 2) ≤ a :=
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans ha
  have hCa : 2 * C + 1 ≤ a :=
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans ha
  have h2 : 2 ≤ c * Real.exp a := by
    have hh := (div_le_iff₀ hc).mp (h2c.trans hEa)
    nlinarith
  have hd2 : (d : ℝ) + 2 ≤ 2 * c * Real.exp a := by linarith
  have hdE : (d : ℝ) + 2 ≤ 2 * Real.exp a := by nlinarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl21 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have h80E : 80 ≤ Real.pi * Real.log 2 * Real.exp a := by
    have hh := (div_le_iff₀ (mul_pos Real.pi_pos hl2)).mp (h80.trans hEa)
    nlinarith
  have hexp : Real.exp (2 * a) = Real.exp a * Real.exp a := by
    rw [show 2 * a = a + a by ring, Real.exp_add]
  have hZ : 80 * Real.exp a ≤ scaleZ a := by
    unfold scaleZ
    rw [hexp]
    have hh : 80 ≤ Real.pi * Real.exp a := by nlinarith
    nlinarith
  have hZ6 : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a := by
    rw [thetaQ_zero_eq_scaleZ]
    have he1 : 1 ≤ Real.exp a := Real.one_le_exp_iff.mpr ha0
    linarith
  have hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a := by
    rw [thetaQ_zero_eq_scaleZ]
    nlinarith [show 0 < scaleZ a by unfold scaleZ; positivity]
  have hwidth : 40 * thetaDerivTailWidth d a ≤ Real.log 2 := by
    unfold thetaDerivTailWidth
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (thetaDeriv_scaleT_pos a)).mpr
    unfold scaleT scaleZ
    rw [hexp]
    have hh := mul_le_mul_of_nonneg_right h80E he.le
    nlinarith
  have hlogD : Real.log ((d : ℝ) + 2) ≤ a + Real.log 2 := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < (d : ℝ) + 2) hdE
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) he.ne', Real.log_exp] at hh
    linarith
  have hlogT : Real.log (scaleT a) = 2 * a + Real.log 2 + Real.log Real.pi := by
    unfold scaleT scaleZ
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity),
      Real.log_mul Real.pi_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hcost : C * ((d : ℝ) + 2) * a * Real.exp (-a) ≤ a / 8 := by
    have hh := mul_le_mul_of_nonneg_right hd2 (Real.exp_pos (-a)).le
    have hecancel : Real.exp a * Real.exp (-a) = 1 := by rw [← Real.exp_add]; simp
    have hdsmall : ((d : ℝ) + 2) * Real.exp (-a) ≤ 2 * c := by
      calc _ ≤ (2 * c * Real.exp a) * Real.exp (-a) := hh
           _ = 2 * c := by rw [mul_assoc, hecancel, mul_one]
    have hh2 := mul_le_mul_of_nonneg_left hdsmall (mul_nonneg hC.le ha0)
    have hh3 := mul_le_mul_of_nonneg_right hCc ha0
    nlinarith
  refine ⟨ha1, hZ6, hsize, hwidth, ?_⟩
  rw [hlogT]
  have hlogpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith

end ThetaTrial.Paper
