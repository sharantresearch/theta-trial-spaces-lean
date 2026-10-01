import ThetaTrial.Paper.ThetaAvgPolynomialTheorem
import ThetaTrial.Paper.ThetaAvgTrialDimension
import ThetaTrial.Paper.TrialBounds

/-! Theorem `avg:spaces` and Corollary `avg:large-space`: growing-dimensional
theta-average spaces. The dimension is that of the image in `L2`. -/

noncomputable section
open Complex MeasureTheory Set Polynomial Filter
open scoped Topology

namespace ThetaTrial.Paper

/-- The subspace statement corresponding to theorem `avg:spaces`.
Its source parameterization ranges over every polynomial of the stated degree. -/
theorem thetaAvg_spaces :
    ∃ C₁ > 0, ∃ C₂ > 0, ∃ a₁ : ℝ, 1 ≤ a₁ ∧
      ∀ a ≥ a₁, ∃ ha : 0 ≤ a, ∃ hZ : 16 ≤ scaleZ a,
        ∀ k : ℕ,
          (k : ℝ) * (Real.log ((k : ℝ)+1)+4*a) + C₁*((k : ℝ)+a) ≤ scaleT a →
          Module.finrank ℂ (thetaAvgTrialSpace a ha hZ k) = k+1 ∧
          ∀ P : ℂ[X], P.natDegree ≤ k →
            InWindowFormDomain a (thetaAvgWindowProfile a P) ∧
            (P ≠ 0 → 0 < squaredNorm (thetaAvgWindowProfile a P)) ∧
            |fullWeilForm (thetaAvgWindowProfile a P)| ≤
              Real.exp (-2*scaleT a+8*(k : ℝ)*a+
                2*(k : ℝ)*Real.log ((k : ℝ)+1)+C₂*((k : ℝ)+a)) *
                squaredNorm (thetaAvgWindowProfile a P) := by
  obtain ⟨C₁, hC₁, C₂, hC₂, a₁, ha₁, hmain⟩ := thetaAvg_polynomial_window_estimates
  refine ⟨C₁, hC₁, C₂, hC₂, max a₁ 16, ha₁.trans (le_max_left _ _), ?_⟩
  intro a ha
  have haa : a₁ ≤ a := (le_max_left _ _).trans ha
  have ha16 : 16 ≤ a := (le_max_right _ _).trans ha
  have ha0 : 0 ≤ a := by linarith
  have hZ : 16 ≤ scaleZ a := ha16.trans (scaleZ_ge_self_of_nonneg ha0)
  refine ⟨ha0, hZ, ?_⟩
  intro k hk
  have h := hmain a haa k hk
  refine ⟨thetaAvgTrialSpace_finrank_of_separation ha0 hZ k (fun P hp => (h P hp).2.1), ?_⟩
  exact h

/-- All sufficiently large windows have the explicit dimension
floor(T_a/(32a))+1 and absolute energy at most exp(-T_a) on the entire space. -/
theorem thetaAvg_large_space :
    ∀ᶠ a : ℝ in atTop, ∃ ha : 0 ≤ a, ∃ hZ : 16 ≤ scaleZ a,
      Module.finrank ℂ (thetaAvgTrialSpace a ha hZ (TrialBounds.selectedDegree a)) =
        TrialBounds.selectedDegree a + 1 ∧
      ∀ P : ℂ[X], P.natDegree ≤ TrialBounds.selectedDegree a →
        InWindowFormDomain a (thetaAvgWindowProfile a P) ∧
        (P ≠ 0 → 0 < squaredNorm (thetaAvgWindowProfile a P)) ∧
        |fullWeilForm (thetaAvgWindowProfile a P)| ≤
          Real.exp (-scaleT a) * squaredNorm (thetaAvgWindowProfile a P) := by
  obtain ⟨C₁, hC₁, C₂, hC₂, a₁, ha₁, hmain⟩ := thetaAvg_spaces
  filter_upwards [eventually_ge_atTop a₁,
    TrialBounds.eventually_selected_degree C₁ C₂ hC₁.le hC₂.le] with a ha hdegree
  obtain ⟨ha0, hZ, hspace⟩ := hmain a ha
  have hk : (TrialBounds.selectedDegree a : ℝ) *
      (Real.log ((TrialBounds.selectedDegree a : ℝ)+1)+4*a) +
        C₁*((TrialBounds.selectedDegree a : ℝ)+a) ≤ scaleT a := hdegree.1
  obtain ⟨hdim, hP⟩ := hspace (TrialBounds.selectedDegree a) hk
  refine ⟨ha0, hZ, hdim, ?_⟩
  intro P hp
  obtain ⟨hdom, hpos, hq⟩ := hP P hp
  refine ⟨hdom, hpos, hq.trans ?_⟩
  exact mul_le_mul_of_nonneg_right hdegree.2 (integral_nonneg (fun u => sq_nonneg _))

end ThetaTrial.Paper
