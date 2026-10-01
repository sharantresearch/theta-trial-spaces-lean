import ThetaTrial.Paper.ThetaAvgTail
import ThetaTrial.Paper.TailFormBound
import ThetaTrial.Paper.ShiftedAverageInterior
import ThetaTrial.Paper.TrialBounds

/-! Bounds for the Weil energy of the exterior tail of the theta average. -/

noncomputable section
open Complex MeasureTheory Set

namespace ThetaTrial.Paper

theorem thetaAvg_tail_fullWeilForm_bound {a : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) :
    |fullWeilForm (exteriorTail a (fun u : ℝ => shiftedAverage a (u : ℂ)))| ≤
      tailFormConstant * (hardTailBudget (thetaAvgTrialDerivative a 0) (thetaAvgTrialDerivative a 1) a) ^ 2 := by
  exact exteriorTail_fullWeilForm_abs_le (thetaAvgTrialDerivative_continuous hZ 0) ha
    (fun x _ => thetaAvgTrialDerivative_hasDerivAt hZ 0 x)
    (thetaAvgTrialDerivative_weighted_integrableOn ha hZ 0)
    (thetaAvgTrialDerivative_weighted_integrableOn ha hZ 1)

theorem thetaAvg_tail_energy_exp_bound {a : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) :
    |fullWeilForm (exteriorTail a (fun u : ℝ => shiftedAverage a (u : ℂ)))| ≤
      (tailFormConstant * thetaAvgBudgetConstant ^ 2) * Real.exp (-2 * scaleT a + 32 * a) := by
  have hsq := pow_le_pow_left₀
    (hardTailBudget_nonneg (thetaAvgTrialDerivative a 0) (thetaAvgTrialDerivative a 1) a)
    (thetaAvg_trial_hardTailBudget_exp_bound ha hZ) 2
  apply (thetaAvg_tail_fullWeilForm_bound ha hZ).trans
  apply (mul_le_mul_of_nonneg_left hsq tailFormConstant_pos.le).trans_eq
  rw [mul_pow, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have he : 2 * (16 * a - scaleT a) = -2 * scaleT a + 32 * a := by ring
  rw [he]
  ring

/-- The exterior energy divided by the norm of the window part. -/
theorem thetaAvg_tail_normalized_energy :
    ∃ C > 0, ∃ a₀ : ℝ, 16 ≤ a₀ ∧ ∀ a ≥ a₀,
      |fullWeilForm (exteriorTail a (fun u : ℝ => shiftedAverage a (u : ℂ)))| /
        squaredNorm (windowCut a (fun u : ℝ => shiftedAverage a (u : ℂ))) ≤
          C * Real.exp (-2 * scaleT a + 34 * a) := by
  obtain ⟨c, hc, a₁, ha₁, hnorm⟩ := shiftedAverage_window_squaredNorm_lower
  let C := tailFormConstant * thetaAvgBudgetConstant ^ 2 * Real.pi / c
  have hC : 0 < C := div_pos (mul_pos (mul_pos tailFormConstant_pos
    (sq_pos_of_pos thetaAvgBudgetConstant_pos)) Real.pi_pos) hc
  refine ⟨C, hC, max 16 a₁, le_max_left _ _, ?_⟩
  intro a ha
  have ha16 : 16 ≤ a := (le_max_left _ _).trans ha
  have ha0 : 0 ≤ a := by linarith
  have hZ : 16 ≤ scaleZ a := ha16.trans (scaleZ_ge_self_of_nonneg ha0)
  have hnorm' := hnorm a ((le_max_right _ _).trans ha)
  have ht := TrialBounds.normalized_energy_of_bv_bounds a
    (fullWeilForm (exteriorTail a (fun u : ℝ => shiftedAverage a (u : ℂ))))
    (squaredNorm (windowCut a (fun u : ℝ => shiftedAverage a (u : ℂ))))
    (hardTailBudget (thetaAvgTrialDerivative a 0) (thetaAvgTrialDerivative a 1) a)
    tailFormConstant thetaAvgBudgetConstant c tailFormConstant_pos.le
    thetaAvgBudgetConstant_pos.le hc (hardTailBudget_nonneg _ _ _)
    (thetaAvg_tail_fullWeilForm_bound ha0 hZ)
    (thetaAvg_trial_hardTailBudget_exp_bound ha0 hZ) hnorm'
  simpa only [TrialBounds.T, TrialBounds.Z, scaleT, scaleZ, C] using ht

end ThetaTrial.Paper
