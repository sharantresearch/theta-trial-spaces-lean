import ThetaTrial.Paper.WindowTrial
import ThetaTrial.Paper.ThetaAvgPolynomialTail
import ThetaTrial.Paper.ThetaAvgScalarAbsorption
import ThetaTrial.Paper.ThetaAvgRadical
import ThetaTrial.Paper.ShiftedAverageInterior

/-! The analytic growing-polynomial-space theorem for the full Weil
form. All bounds below concern the theta average and its hard cutoff. -/

noncomputable section
open Complex MeasureTheory Set Polynomial

namespace ThetaTrial.Paper

theorem thetaAvg_polynomial_budget_from_coefficient_bound
    {a d A : ℝ} (ha : 0 ≤ a) (hZ : 16 ≤ scaleZ a)
    {k : ℕ} {P : ℂ[X]} (hdeg : P.natDegree ≤ k)
    (hcoef : (∑ j ∈ Finset.range (k+1), ‖P.coeff j‖) ≤
      A^(k+1) * Real.sqrt (CoefficientBounds.complexIntervalSqAt d P)) :
    hardTailBudget (polynomialDerivative P (fun u : ℝ => shiftedAverage a u))
      (deriv (polynomialDerivative P (fun u : ℝ => shiftedAverage a u))) a ≤
        thetaAvgScalarAmplitude thetaAvgBudgetConstant A a k *
          Real.sqrt (CoefficientBounds.complexIntervalSqAt d P) := by
  have hb := thetaAvg_polynomial_hardTailBudget_exp_bound ha hZ hdeg
  have hB := thetaAvgBudgetConstant_pos
  apply hb.trans
  unfold thetaAvgScalarAmplitude thetaAvgCoefficientSum
  calc
    _ ≤ thetaAvgBudgetConstant *
        (A^(k+1) * Real.sqrt (CoefficientBounds.complexIntervalSqAt d P)) *
        (k+1).factorial * (scaleZ a)^(2*k) * Real.exp (16*a-scaleT a) := by
      gcongr
    _ = _ := by ring

/-- The growing trial-space estimates, including form-domain membership
and nonzero L2 norm. The dimension is computed in `ThetaAvgTrialDimension`. -/
theorem thetaAvg_polynomial_window_estimates :
    ∃ C₁ > 0, ∃ C₂ > 0, ∃ a₁ : ℝ, 1 ≤ a₁ ∧
      ∀ a ≥ a₁, ∀ k : ℕ,
        (k : ℝ) * (Real.log ((k : ℝ)+1) + 4*a) + C₁*((k : ℝ)+a) ≤ scaleT a →
        ∀ P : ℂ[X], P.natDegree ≤ k →
          InWindowFormDomain a (windowCut a (polynomialDerivative P
            (fun u : ℝ => shiftedAverage a u))) ∧
          (P ≠ 0 → 0 < squaredNorm (windowCut a (polynomialDerivative P
            (fun u : ℝ => shiftedAverage a u)))) ∧
          |fullWeilForm (windowCut a (polynomialDerivative P
            (fun u : ℝ => shiftedAverage a u)))| ≤
            Real.exp (-2*scaleT a + 8*(k : ℝ)*a +
              2*(k : ℝ)*Real.log ((k : ℝ)+1) + C₂*((k : ℝ)+a)) *
              squaredNorm (windowCut a (polynomialDerivative P
                (fun u : ℝ => shiftedAverage a u))) := by
  obtain ⟨d, hd, hd1, c, hc, A, hA, hcoef, hnorm⟩ := thetaAvg_polynomial_norm_constants
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  let C₁ := thetaAvgAbsorptionConstant thetaAvgBudgetConstant A c
  let C₂ := thetaAvgEnergyAbsorptionConstant thetaAvgBudgetConstant A c tailFormConstant
  refine ⟨C₁, thetaAvgAbsorptionConstant_pos _ _ _, C₂,
    thetaAvgEnergyAbsorptionConstant_pos _ _ _ _, 16, by norm_num, ?_⟩
  intro a ha k hdegree P hdeg
  have ha0 : 0 ≤ a := by linarith
  have ha1 : 1 ≤ a := by linarith
  have hZ : 16 ≤ scaleZ a := ha.trans (scaleZ_ge_self_of_nonneg ha0)
  have hz := scaleZ_pos a
  have hB := thetaAvgBudgetConstant_pos
  let F : ℝ → ℂ := polynomialDerivative P (fun u : ℝ => shiftedAverage a u)
  let E := CoefficientBounds.complexIntervalSqAt d P
  let K := thetaAvgScalarAmplitude thetaAvgBudgetConstant A a k
  have hE : 0 ≤ E := CoefficientBounds.complexIntervalSqAt_nonneg hd.le P
  have hK : 0 ≤ K := by dsimp [K, thetaAvgScalarAmplitude]; positivity
  have hF := polynomialDerivative_shiftedAverage_contDiff hZ P
  have hF2 : MemLp F 2 := polynomialDerivative_shiftedAverage_memLp_two ha0 hZ P
  have hdi : ∀ x ∈ (Icc (-a) a)ᶜ, HasDerivAt F (deriv F x) x :=
    fun x hx => (hF.differentiable (by simp) x).hasDerivAt
  have hi : IntegrableOn (ThetaTrial.PrimeContinuity.weightedProfile 1 F) (Icc (-a) a)ᶜ :=
    (polynomialDerivative_shiftedAverage_all_weights_integrable ha0 hZ P 1).integrableOn
  have hi' : IntegrableOn (ThetaTrial.PrimeContinuity.weightedProfile 1 (deriv F)) (Icc (-a) a)ᶜ :=
    (polynomialDerivative_shiftedAverage_deriv_all_weights_integrable ha0 hZ P 1).integrableOn
  have hb : hardTailBudget F (deriv F) a ≤ K * Real.sqrt E :=
    thetaAvg_polynomial_budget_from_coefficient_bound ha0 hZ hdeg (hcoef k P hdeg)
  have hb2 : (hardTailBudget F (deriv F) a)^2 ≤ K^2 * E := by
    have h := pow_le_pow_left₀ (hardTailBudget_nonneg F (deriv F) a) hb 2
    simpa only [mul_pow, Real.sq_sqrt hE] using h
  have hsmall : K^2 ≤ c / (4*scaleZ a) :=
    thetaAvg_amplitude_small_of_degree thetaAvgBudgetConstant_pos hAp hc ha1 k hdegree
  have htail : squaredNorm (exteriorTail a F) ≤ c / (4*scaleZ a) * E :=
    (exteriorTail_squaredNorm_le_budget ha0 hF.continuous hF2 hdi hi hi').trans
      (hb2.trans (mul_le_mul_of_nonneg_right hsmall hE))
  have hfull : c / scaleZ a * E ≤ squaredNorm F := hnorm a ha0 hZ P
  have hsplit := squaredNorm_window_add_tail hF2 (a := a)
  have he : c / scaleZ a * E = 4 * (c / (4*scaleZ a) * E) := by ring
  have hwlower : c / (4*scaleZ a) * E ≤ squaredNorm (windowCut a F) := by
    rw [he] at hfull
    have hz : 0 ≤ c / (4*scaleZ a) * E := by positivity
    linarith
  have hw0 : 0 ≤ squaredNorm (windowCut a F) := integral_nonneg (fun u => sq_nonneg _)
  refine ⟨thetaAvg_polynomial_window_domain ha0 hZ P, ?_, ?_⟩
  · intro hp
    exact (mul_pos (div_pos hc (by positivity : 0 < 4*scaleZ a))
      (polynomial_intervalSq_pos hd hd1 hp)).trans_le hwlower
  · change |fullWeilForm (windowCut a F)| ≤ _
    have hqe : |fullWeilForm (windowCut a F)| ≤ tailFormConstant * K^2 * E := by
      rw [polynomialDerivative_shiftedAverage_hardCutoff ha0 hZ P ha0]
      have hq := exteriorTail_fullWeilForm_abs_le hF.continuous ha0 hdi hi hi'
      exact hq.trans (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hb2 tailFormConstant_pos.le)
    have hfactor : E ≤ (4*scaleZ a/c) * squaredNorm (windowCut a F) := by
      have h := mul_le_mul_of_nonneg_left hwlower (by positivity : 0 ≤ 4*scaleZ a/c)
      have he' : (4*scaleZ a/c) * (c/(4*scaleZ a)*E) = E := by
        field_simp [hc.ne', (scaleZ_pos a).ne']
      rwa [he'] at h
    have henergy := thetaAvg_energy_amplitude_bound thetaAvgBudgetConstant_pos hAp hc
      tailFormConstant_pos ha1 k
    calc
      _ ≤ tailFormConstant * K^2 * E := hqe
      _ ≤ tailFormConstant * K^2 * ((4*scaleZ a/c) * squaredNorm (windowCut a F)) :=
        mul_le_mul_of_nonneg_left hfactor
          (mul_nonneg tailFormConstant_pos.le (sq_nonneg K))
      _ = ((4*scaleZ a/c)*tailFormConstant*K^2) * squaredNorm (windowCut a F) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right henergy hw0

end ThetaTrial.Paper
