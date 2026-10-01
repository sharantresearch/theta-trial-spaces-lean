import ThetaTrial.Paper.ThetaAvgNormalization
import ThetaTrial.Paper.WindowTrial
import ThetaTrial.Paper.FullFormScaling

/-! Theorem `avg:main`: the normalized theta-average trial function. The
energy of the window part equals that of the exterior tail by the truncation
identity. -/

noncomputable section
open Complex MeasureTheory Set Polynomial

namespace ThetaTrial.Paper

theorem thetaAvgWindowTrial_inDomain {a : ℝ} (ha : 0 ≤ a) (hZ : 16 ≤ scaleZ a) :
    InWindowFormDomain a (thetaAvgWindowTrial a) := by
  simpa only [polynomialDerivative_one, thetaAvgWindowTrial] using
    thetaAvg_polynomial_window_domain ha hZ (1 : ℂ[X])

theorem thetaAvgNormalizedTrial_inDomain {a : ℝ} (ha : 0 ≤ a) (hZ : 16 ≤ scaleZ a) :
    InWindowFormDomain a (thetaAvgNormalizedTrial a) :=
  (thetaAvgWindowTrial_inDomain ha hZ).const_mul (thetaAvgNormalizationFactor a : ℂ)

theorem thetaAvgNormalizedTrial_energy_eq_ratio {a : ℝ}
    (hN : 0 < squaredNorm (thetaAvgWindowTrial a)) :
    |fullWeilForm (thetaAvgNormalizedTrial a)| =
      |fullWeilForm (thetaAvgWindowTrial a)| / squaredNorm (thetaAvgWindowTrial a) := by
  unfold thetaAvgNormalizedTrial
  rw [fullWeilForm_const_mul, abs_mul, abs_of_nonneg (Complex.normSq_nonneg _),
    ← Complex.sq_norm, thetaAvgNormalizationFactor_norm_sq hN]
  ring

theorem squaredNorm_eq_norm_toLp_sq {f : ℝ → ℂ} (hf : MemLp f 2) :
    squaredNorm f = ‖hf.toLp f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq (hf.toLp f), MeasureTheory.L2.inner_def]
  unfold squaredNorm
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with u hu
  rw [hu, real_inner_self_eq_norm_sq]

theorem norm_toLp_eq_one_of_squaredNorm_eq_one {f : ℝ → ℂ} (hf : MemLp f 2)
    (h : squaredNorm f = 1) : ‖hf.toLp f‖ = 1 := by
  rw [squaredNorm_eq_norm_toLp_sq hf] at h
  nlinarith [norm_nonneg (hf.toLp f)]

/-- Theorem `avg:main`: a real, even, unit-norm trial vector in the form
domain whose Weil energy is at most `C exp(-2T_a + 34a)` in absolute value. -/
theorem thetaAvg_main :
    ∃ C > 0, ∃ a₀ : ℝ, 16 ≤ a₀ ∧ ∀ a ≥ a₀,
      InWindowFormDomain a (thetaAvgNormalizedTrial a) ∧
      MemLp (thetaAvgNormalizedTrial a) 2 ∧
      Function.Even (thetaAvgNormalizedTrial a) ∧
      (∀ u : ℝ, (thetaAvgNormalizedTrial a u).im = 0) ∧
      squaredNorm (thetaAvgNormalizedTrial a) = 1 ∧
      |fullWeilForm (thetaAvgNormalizedTrial a)| ≤ C * Real.exp (-2 * scaleT a + 34 * a) := by
  obtain ⟨C, hC, aE, haE, henergy⟩ := thetaAvg_tail_normalized_energy
  obtain ⟨c, hc, aN, _haN, hnorm⟩ := shiftedAverage_window_squaredNorm_lower
  refine ⟨C, hC, max aE aN, haE.trans (le_max_left _ _), ?_⟩
  intro a ha
  have haE' : aE ≤ a := (le_max_left _ _).trans ha
  have haN' : aN ≤ a := (le_max_right _ _).trans ha
  have ha16 : 16 ≤ a := haE.trans haE'
  have ha0 : 0 ≤ a := by linarith
  have hZ : 16 ≤ scaleZ a := ha16.trans (scaleZ_ge_self_of_nonneg ha0)
  have hN : 0 < squaredNorm (thetaAvgWindowTrial a) :=
    (div_pos hc (scaleZ_pos a)).trans_le (hnorm a haN')
  have hdom := thetaAvgNormalizedTrial_inDomain ha0 hZ
  refine ⟨hdom, hdom.2.1, thetaAvgNormalizedTrial_even hZ,
    thetaAvgNormalizedTrial_real hZ, thetaAvgNormalizedTrial_squaredNorm hN, ?_⟩
  rw [thetaAvgNormalizedTrial_energy_eq_ratio hN, thetaAvgWindowTrial_hardCutoff ha0 hZ]
  exact henergy a haE'

/-- The same normalized vectors have norm one in the L²
equivalence-class space, independently of the proof of membership supplied. -/
theorem thetaAvg_main_unitLp :
    ∃ a₀ : ℝ, 16 ≤ a₀ ∧ ∀ a ≥ a₀, ∀ hf : MemLp (thetaAvgNormalizedTrial a) 2,
      ‖hf.toLp (thetaAvgNormalizedTrial a)‖ = 1 := by
  obtain ⟨C, hC, a₀, ha₀, hmain⟩ := thetaAvg_main
  refine ⟨a₀, ha₀, ?_⟩
  intro a ha hf
  exact norm_toLp_eq_one_of_squaredNorm_eq_one hf (hmain a ha).2.2.2.2.1

end ThetaTrial.Paper
