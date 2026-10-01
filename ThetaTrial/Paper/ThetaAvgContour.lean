import ThetaTrial.Paper.ContourModeEstimate
import ThetaTrial.Paper.ShiftedAverageAnalytic

/-! The contour estimate of Lemma `avg:contour` for the theta average, for every
derivative and on both tails. -/

noncomputable section
open Complex Set Metric

namespace ThetaTrial.Paper

def thetaAvgContourConstant : ℝ :=
  ContourModeEstimate.modeEstimateConstant * Contour.modeConstant

theorem thetaAvgContourConstant_pos : 0 < thetaAvgContourConstant := by
  have hm := Contour.summable_mode_majorant.le_tsum 1
    (fun n _ => by positivity)
  have hm1 : 1 ≤ Contour.modeConstant := by
    simpa [Contour.modeConstant] using hm
  unfold thetaAvgContourConstant ContourModeEstimate.modeEstimateConstant
    ContourModeEstimate.prefactorConstant
  positivity

theorem scaleZ_pos (a : ℝ) : 0 < scaleZ a :=
  mul_pos Real.pi_pos (Real.exp_pos _)

def thetaAvgContourEnvelope (a x : ℝ) : ℝ :=
  thetaAvgContourConstant * Real.exp (9 * |x| / 2) *
    (scaleZ a) ^ (13 / 4 : ℝ) *
    Real.exp (-2 * scaleZ a - Real.exp (2 * (|x| - a)))

theorem thetaAvgContourEnvelope_pos (a x : ℝ) : 0 < thetaAvgContourEnvelope a x := by
  unfold thetaAvgContourEnvelope
  exact mul_pos (mul_pos (mul_pos thetaAvgContourConstant_pos (Real.exp_pos _))
    (Real.rpow_pos_of_pos (scaleZ_pos a) _)) (Real.exp_pos _)

theorem shiftedAverage_norm_le_disc_both_tails {a x : ℝ} (ha0 : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (hax : a ≤ |x|) {h : ℂ}
    (hh : ‖h‖ ≤ Contour.discRadius (scaleZ a)) :
    ‖shiftedAverage a ((x : ℂ) + h)‖ ≤ thetaAvgContourEnvelope a x := by
  by_cases hx : 0 ≤ x
  · simpa only [thetaAvgContourEnvelope, thetaAvgContourConstant, abs_of_nonneg hx] using
      ContourModeEstimate.shiftedAverage_norm_le_disc ha0 hZ
        (by simpa only [abs_of_nonneg hx] using hax) hh
  · have hxn : x ≤ 0 := le_of_not_ge hx
    have hhneg : ‖-h‖ ≤ Contour.discRadius (scaleZ a) := by simpa using hh
    have hz : |(((x : ℂ) + h)).im| < 1 / scaleZ a := by
      apply Contour.cauchy_disc_subset_strip hZ x
      simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left] using hh
    have he := shiftedAverage_neg hZ hz
    have hbound := ContourModeEstimate.shiftedAverage_norm_le_disc ha0 hZ
      (x := -x) (by simpa only [abs_of_nonpos hxn] using hax) hhneg
    have hearg : ((-x : ℝ) : ℂ) + -h = -((x : ℂ) + h) := by push_cast; ring
    rw [hearg, he] at hbound
    simpa only [thetaAvgContourEnvelope, thetaAvgContourConstant, abs_of_nonpos hxn] using hbound

/-- The paper's all-order estimate for the average. -/
theorem thetaAvg_contour_derivative_bound {a x : ℝ} (ha0 : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (hax : a ≤ |x|) (j : ℕ) :
    ‖iteratedDeriv j (shiftedAverage a) (x : ℂ)‖ ≤
      j.factorial * (scaleZ a) ^ (2 * j) * thetaAvgContourEnvelope a x := by
  exact Contour.cauchy_derivative_of_strip_and_disc_bound hZ
    (shiftedAverage_differentiableOn hZ)
    (fun _ hh => shiftedAverage_norm_le_disc_both_tails ha0 hZ hax hh) j

theorem shiftedAverage_iteratedDeriv_analytic {a : ℝ} (hZ : 16 ≤ scaleZ a) (j : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv j (shiftedAverage a))
      {z : ℂ | |z.im| < 1 / scaleZ a} := by
  induction j with
  | zero => simpa using shiftedAverage_analyticOnNhd hZ
  | succ j ih => simpa only [iteratedDeriv_succ] using ih.deriv

/-- The real derivatives coincide with complex derivatives on the real line. -/
theorem shiftedAverage_real_iteratedDeriv {a : ℝ} (hZ : 16 ≤ scaleZ a)
    (j : ℕ) (x : ℝ) :
    iteratedDeriv j (fun u : ℝ => shiftedAverage a (u : ℂ)) x =
      iteratedDeriv j (shiftedAverage a) (x : ℂ) := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ, funext ih]
    have hx : |(x : ℂ).im| < 1 / scaleZ a := by
      simp only [Complex.ofReal_im, abs_zero]
      positivity
    exact ((shiftedAverage_iteratedDeriv_analytic hZ j (x : ℂ) hx).differentiableAt.hasDerivAt.comp_ofReal).deriv

/-- Both tails, every ordinary real derivative, and the paper's exact Z power. -/
theorem thetaAvg_real_derivative_bound {a x : ℝ} (ha0 : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (hax : a ≤ |x|) (j : ℕ) :
    ‖iteratedDeriv j (fun u : ℝ => shiftedAverage a (u : ℂ)) x‖ ≤
      j.factorial * (scaleZ a) ^ (2 * j) * thetaAvgContourEnvelope a x := by
  rw [shiftedAverage_real_iteratedDeriv hZ]
  exact thetaAvg_contour_derivative_bound ha0 hZ hax j

end ThetaTrial.Paper
