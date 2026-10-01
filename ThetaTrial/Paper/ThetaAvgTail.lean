import ThetaTrial.Paper.ThetaAvgTailEnvelope
import ThetaTrial.Paper.TailVariation

/-! Quantitative bounds for the hard tails of the theta average, including both
endpoint jumps. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set Filter
open scoped Topology

namespace ThetaTrial.Paper

theorem le_abs_of_mem_exterior {a x : ℝ} (hx : x ∈ (Icc (-a) a)ᶜ) : a ≤ |x| := by
  by_contra! h
  exact hx ⟨by linarith [(neg_le_abs x)], by linarith [le_abs_self x]⟩

/-- An ordinary continuous function under the contour envelope is
exponentially weighted integrable on the exterior. -/
theorem thetaAvg_weighted_integrableOn_of_bound {a M : ℝ} {F : ℝ → ℂ}
    (hc : Continuous F) (_hM : 0 ≤ M)
    (hb : ∀ x, a ≤ |x| → ‖F x‖ ≤ M * thetaAvgContourEnvelope a x) :
    IntegrableOn (ThetaTrial.PrimeContinuity.weightedProfile 1 F) (Icc (-a) a)ᶜ := by
  apply ((thetaAvg_weighted_envelope_integrable a).const_mul M).integrableOn.mono'
    (weightedProfile_one_continuous hc).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with x hx
  rw [ThetaTrial.PrimeContinuity.weightedProfile_norm, one_mul]
  simpa only [mul_assoc, mul_left_comm] using
    mul_le_mul_of_nonneg_left (hb x (le_abs_of_mem_exterior hx)) (Real.exp_pos |x|).le

def thetaAvgTailConstant : ℝ := 2 * (1 + thetaAvgTailProfileMass)

theorem thetaAvgTailConstant_pos : 0 < thetaAvgTailConstant := by
  unfold thetaAvgTailConstant
  linarith [thetaAvgTailProfileMass_nonneg]

/-- A quantitative tail bound, with both endpoint jumps, from a pointwise
bound. The theta specialization is below. -/
theorem thetaAvg_hardTailBudget_of_bound {a M : ℝ} {F F' : ℝ → ℂ}
    (ha : 0 ≤ a) (hM : 0 ≤ M) (hc : Continuous F) (hc' : Continuous F')
    (hb : ∀ x, a ≤ |x| → ‖F x‖ + ‖F' x‖ ≤ M * thetaAvgContourEnvelope a x) :
    hardTailBudget F F' a ≤ M * thetaAvgWeightedScale a * thetaAvgTailConstant := by
  have hb0 (x : ℝ) (hx : a ≤ |x|) : ‖F x‖ ≤ M * thetaAvgContourEnvelope a x :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans (hb x hx)
  have hb1 (x : ℝ) (hx : a ≤ |x|) : ‖F' x‖ ≤ M * thetaAvgContourEnvelope a x :=
    (le_add_of_nonneg_left (norm_nonneg _)).trans (hb x hx)
  have hi := thetaAvg_weighted_integrableOn_of_bound hc hM hb0
  have hi' := thetaAvg_weighted_integrableOn_of_bound hc' hM hb1
  have hfi : IntegrableOn (fun x => Real.exp |x| * (‖F x‖ + ‖F' x‖))
      (Icc (-a) a)ᶜ := by
    change Integrable _ (volume.restrict (Icc (-a) a)ᶜ)
    convert hi.norm.add hi'.norm using 1
    all_goals first | rfl | (funext x; simp [ThetaTrial.PrimeContinuity.weightedProfile_norm, mul_add])
  have hint : (∫ x in (Icc (-a) a)ᶜ, Real.exp |x| * (‖F x‖ + ‖F' x‖)) ≤
      M * thetaAvgWeightedScale a * (2 * thetaAvgTailProfileMass) := by
    calc
      _ ≤ ∫ x in (Icc (-a) a)ᶜ, M * (Real.exp |x| * thetaAvgContourEnvelope a x) := by
        apply setIntegral_mono_on hfi
          ((thetaAvg_weighted_envelope_integrable a).const_mul M).integrableOn measurableSet_Icc.compl
        intro x hx
        have hm := mul_le_mul_of_nonneg_left (hb x (le_abs_of_mem_exterior hx))
          (Real.exp_pos |x|).le
        simpa only [mul_assoc, mul_left_comm] using hm
      _ ≤ ∫ x : ℝ, M * (Real.exp |x| * thetaAvgContourEnvelope a x) :=
        setIntegral_le_integral ((thetaAvg_weighted_envelope_integrable a).const_mul M)
          (Filter.Eventually.of_forall (fun x => mul_nonneg hM
            (mul_nonneg (Real.exp_pos _).le (thetaAvgContourEnvelope_pos a x).le)))
      _ ≤ M * thetaAvgWeightedScale a * (2 * thetaAvgTailProfileMass) := by
        rw [integral_const_mul]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (thetaAvg_weighted_envelope_integral_le a) hM
  have hend (x : ℝ) (hx : |x| = a) :
      Real.exp a * ‖F x‖ ≤ M * thetaAvgWeightedScale a := by
    have hb' := mul_le_mul_of_nonneg_left (hb0 x hx.ge) (Real.exp_pos a).le
    have he : Real.exp a * thetaAvgContourEnvelope a x =
        thetaAvgWeightedScale a * Real.exp (-1) := by
      rw [← hx, thetaAvg_weighted_envelope_identity, hx]
      simp [thetaAvgTailProfile]
    calc
      _ ≤ M * (Real.exp a * thetaAvgContourEnvelope a x) := by nlinarith [hb']
      _ = M * (thetaAvgWeightedScale a * Real.exp (-1)) := by rw [he]
      _ ≤ M * thetaAvgWeightedScale a := by
        have hh : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
        nlinarith [mul_le_mul_of_nonneg_left hh (mul_nonneg hM (thetaAvgWeightedScale_pos a).le)]
  have hl := hend (-a) (by simp [abs_of_nonneg ha])
  have hr := hend a (abs_of_nonneg ha)
  unfold hardTailBudget thetaAvgTailConstant
  nlinarith [hint, hl, hr]

def thetaAvgTrialDerivative (a : ℝ) (j : ℕ) (x : ℝ) : ℂ :=
  iteratedDeriv j (shiftedAverage a) (x : ℂ)

theorem thetaAvgTrialDerivative_continuous {a : ℝ} (hZ : 16 ≤ scaleZ a) (j : ℕ) :
    Continuous (thetaAvgTrialDerivative a j) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hx : |(x : ℂ).im| < 1 / scaleZ a := by
    simp only [Complex.ofReal_im, abs_zero]
    exact one_div_pos.mpr (scaleZ_pos a)
  exact ((shiftedAverage_iteratedDeriv_analytic hZ j (x : ℂ) hx).continuousAt.comp
    Complex.continuous_ofReal.continuousAt)

theorem thetaAvgTrialDerivative_hasDerivAt {a : ℝ} (hZ : 16 ≤ scaleZ a) (j : ℕ) (x : ℝ) :
    HasDerivAt (thetaAvgTrialDerivative a j) (thetaAvgTrialDerivative a (j + 1) x) x := by
  have hx : |(x : ℂ).im| < 1 / scaleZ a := by
    simp only [Complex.ofReal_im, abs_zero]
    exact one_div_pos.mpr (scaleZ_pos a)
  unfold thetaAvgTrialDerivative
  rw [iteratedDeriv_succ]
  convert ((shiftedAverage_iteratedDeriv_analytic hZ j (x : ℂ) hx).differentiableAt.hasDerivAt.comp_ofReal) using 1

theorem thetaAvgTrialDerivative_weighted_integrableOn {a : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (j : ℕ) :
    IntegrableOn (ThetaTrial.PrimeContinuity.weightedProfile 1 (thetaAvgTrialDerivative a j))
      (Icc (-a) a)ᶜ := by
  apply thetaAvg_weighted_integrableOn_of_bound (thetaAvgTrialDerivative_continuous hZ j)
    (M := j.factorial * (scaleZ a) ^ (2 * j)) (by positivity)
  intro x hx
  exact thetaAvg_contour_derivative_bound ha hZ hx j

theorem thetaAvgTrialDerivative_weighted_integrable {a : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (j : ℕ) :
    Integrable (ThetaTrial.PrimeContinuity.weightedProfile 1 (thetaAvgTrialDerivative a j)) := by
  have hi : IntegrableOn (ThetaTrial.PrimeContinuity.weightedProfile 1 (thetaAvgTrialDerivative a j))
      (Icc (-a) a) :=
    (weightedProfile_one_continuous (thetaAvgTrialDerivative_continuous hZ j)).continuousOn.integrableOn_Icc
  simpa only [union_compl_self, integrableOn_univ] using
    hi.union (thetaAvgTrialDerivative_weighted_integrableOn ha hZ j)

theorem thetaAvgTrialDerivative_integrable {a : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (j : ℕ) :
    Integrable (thetaAvgTrialDerivative a j) := by
  have hi := thetaAvgTrialDerivative_weighted_integrable ha hZ j
  exact integrableOn_univ.mp (integrableOn_of_weightedProfile_one hi.integrableOn)

/-- All real exponential weights, not only the weight needed by the BV bound. -/
theorem thetaAvgTrialDerivative_all_weights_integrable {a : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (j : ℕ) (R : ℝ) :
    Integrable (ThetaTrial.PrimeContinuity.weightedProfile R (thetaAvgTrialDerivative a j)) := by
  have hc : Continuous (ThetaTrial.PrimeContinuity.weightedProfile R (thetaAvgTrialDerivative a j)) := by
    unfold ThetaTrial.PrimeContinuity.weightedProfile
    exact (by fun_prop : Continuous (fun x : ℝ => (Real.exp (R * |x|) : ℂ))).mul
      (thetaAvgTrialDerivative_continuous hZ j)
  have hi : IntegrableOn (ThetaTrial.PrimeContinuity.weightedProfile R (thetaAvgTrialDerivative a j))
      (Icc (-a) a) := hc.continuousOn.integrableOn_Icc
  have ho : IntegrableOn (ThetaTrial.PrimeContinuity.weightedProfile R (thetaAvgTrialDerivative a j))
      (Icc (-a) a)ᶜ := by
    apply ((thetaAvg_envelope_all_weights_integrable a R).const_mul
      ((j.factorial : ℝ) * (scaleZ a) ^ (2 * j))).integrableOn.mono' hc.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with x hx
    rw [ThetaTrial.PrimeContinuity.weightedProfile_norm]
    have hb := thetaAvg_contour_derivative_bound ha hZ (le_abs_of_mem_exterior hx) j
    simpa only [thetaAvgTrialDerivative, mul_assoc, mul_left_comm] using
      mul_le_mul_of_nonneg_left hb (Real.exp_pos (R * |x|)).le
  simpa only [union_compl_self, integrableOn_univ] using hi.union ho

/-- The tail bound for the unnormalized trial function. -/
theorem thetaAvg_trial_hardTailBudget_le {a : ℝ} (ha : 0 ≤ a) (hZ : 16 ≤ scaleZ a) :
    hardTailBudget (thetaAvgTrialDerivative a 0) (thetaAvgTrialDerivative a 1) a ≤
      2 * (scaleZ a) ^ 2 * thetaAvgWeightedScale a * thetaAvgTailConstant := by
  apply thetaAvg_hardTailBudget_of_bound ha (by positivity)
    (thetaAvgTrialDerivative_continuous hZ 0) (thetaAvgTrialDerivative_continuous hZ 1)
  intro x hx
  have h0 := thetaAvg_contour_derivative_bound ha hZ hx 0
  have h1 := thetaAvg_contour_derivative_bound ha hZ hx 1
  simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, mul_zero, pow_zero,
    one_mul, mul_one] at h0 h1
  have hpow : 1 ≤ (scaleZ a) ^ 2 := by nlinarith
  have hp := thetaAvgContourEnvelope_pos a x
  change ‖thetaAvgTrialDerivative a 0 x‖ ≤ _ at h0
  change ‖thetaAvgTrialDerivative a 1 x‖ ≤ _ at h1
  nlinarith [mul_le_mul_of_nonneg_right hpow hp.le]

theorem thetaAvgWeightedScale_eq (a : ℝ) :
    thetaAvgWeightedScale a = thetaAvgContourConstant * Real.pi ^ (13 / 4 : ℝ) *
      Real.exp (12 * a - scaleT a) := by
  have hp : (scaleZ a) ^ (13 / 4 : ℝ) =
      Real.pi ^ (13 / 4 : ℝ) * Real.exp (13 * a / 2) := by
    rw [scaleZ, Real.mul_rpow Real.pi_pos.le (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2
    ring
  rw [thetaAvgWeightedScale, hp]
  calc
    _ = (thetaAvgContourConstant * Real.pi ^ (13 / 4 : ℝ)) *
        (Real.exp (13 * a / 2) * Real.exp (11 * a / 2 - 2 * scaleZ a)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; unfold scaleT; ring

def thetaAvgBudgetConstant : ℝ :=
  2 * Real.pi ^ 2 * thetaAvgContourConstant * Real.pi ^ (13 / 4 : ℝ) * thetaAvgTailConstant

theorem thetaAvgBudgetConstant_pos : 0 < thetaAvgBudgetConstant := by
  unfold thetaAvgBudgetConstant
  exact mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos Real.pi_pos))
    thetaAvgContourConstant_pos) (Real.rpow_pos_of_pos Real.pi_pos _)) thetaAvgTailConstant_pos

theorem thetaAvg_budget_scale_identity (a : ℝ) :
    2 * (scaleZ a) ^ 2 * thetaAvgWeightedScale a * thetaAvgTailConstant =
      thetaAvgBudgetConstant * Real.exp (16 * a - scaleT a) := by
  have hz : (scaleZ a) ^ 2 = Real.pi ^ 2 * Real.exp (4 * a) := by
    rw [scaleZ, mul_pow, ← Real.exp_nat_mul]
    norm_num
    ring_nf
  rw [hz, thetaAvgWeightedScale_eq]
  have he : Real.exp (4 * a) * Real.exp (12 * a - scaleT a) =
      Real.exp (16 * a - scaleT a) := by rw [← Real.exp_add]; congr 1; ring
  unfold thetaAvgBudgetConstant
  calc
    _ = (2 * Real.pi ^ 2 * thetaAvgContourConstant * Real.pi ^ (13 / 4 : ℝ) * thetaAvgTailConstant) *
        (Real.exp (4 * a) * Real.exp (12 * a - scaleT a)) := by ring
    _ = _ := by rw [he]

/-- The paper exponent 16a-T_a for the hard cutoff. -/
theorem thetaAvg_trial_hardTailBudget_exp_bound {a : ℝ} (ha : 0 ≤ a) (hZ : 16 ≤ scaleZ a) :
    hardTailBudget (thetaAvgTrialDerivative a 0) (thetaAvgTrialDerivative a 1) a ≤
      thetaAvgBudgetConstant * Real.exp (16 * a - scaleT a) := by
  exact (thetaAvg_trial_hardTailBudget_le ha hZ).trans_eq (thetaAvg_budget_scale_identity a)

end ThetaTrial.Paper
