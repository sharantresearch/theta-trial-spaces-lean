import ThetaTrial.Paper.FormDomain
import ThetaTrial.Paper.TailFormBound
import ThetaTrial.Paper.ThetaAvgPolynomialNorm

/-! The hard window: domain membership and norms. Endpoint values need not
vanish, and the exterior norm is controlled by the jump terms. -/

noncomputable section
open Complex MeasureTheory Set

namespace ThetaTrial.Paper

theorem boundedVariation_sub_complex {f g : ℝ → ℂ}
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ) :
    BoundedVariationOn (f-g) univ := by
  apply ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩)
  unfold eVariationOn at ⊢
  refine iSup_le fun ⟨n, u, hu, hus⟩ => ?_
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (edist (f (u (i+1))) (f (u i)) + edist (g (u (i+1))) (g (u i))) := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [Pi.sub_apply, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg]
      exact ENNReal.ofReal_le_ofReal (dist_sub_sub_le _ _ _ _)
    _ = (∑ i ∈ Finset.range n, edist (f (u (i+1))) (f (u i))) +
        (∑ i ∈ Finset.range n, edist (g (u (i+1))) (g (u i))) := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)

theorem integrableBV_logEnergy {f : ℝ → ℂ}
    (hi : Integrable f) (hv : BoundedVariationOn f univ) :
    Integrable (fun r : ℝ => Real.log (2 + |r|) * ‖paperFourier f r‖^2) := by
  have h2 := memLp_two_of_integrable_bv hi hv
  have hg := gamma_term_integrable_of_fourier_decay
    (paperFourier_continuous_real hi).aestronglyMeasurable
    (paperFourier_sq_le_cauchy_of_bv hi hv)
  have hs := paperFourier_squared_integrable hi h2
  obtain ⟨C, hC, hb⟩ := gammaWeight_sub_log_bounded
  have hm : AEStronglyMeasurable (fun r : ℝ =>
      Real.log (2 + |r|) * ‖paperFourier f r‖^2) := by
    apply Continuous.aestronglyMeasurable
    exact (continuous_const.add continuous_abs).log
      (fun r => by change 2 + |r| ≠ 0; linarith [abs_nonneg r]) |>.mul
        ((paperFourier_continuous_real hi).norm.pow 2)
  apply (hg.norm.add (hs.const_mul C)).mono' hm
  filter_upwards [] with r
  have hl : Real.log (2 + |r|) ≤ |gammaWeight r| + C := by
    linarith [(abs_le.mp (hb r)).1, le_abs_self (gammaWeight r)]
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul,
    ← Complex.sq_norm, abs_of_nonneg (sq_nonneg ‖paperFourier f r‖),
    abs_of_nonneg (logWindowWeight_pos r).le]
  nlinarith [mul_le_mul_of_nonneg_right hl (sq_nonneg ‖paperFourier f r‖)]

theorem supported_integrableBV_inDomain {a : ℝ} {f : ℝ → ℂ}
    (hs : Function.support f ⊆ Icc (-a) a)
    (hi : Integrable f) (hv : BoundedVariationOn f univ) : InWindowFormDomain a f :=
  ⟨hs, memLp_two_of_integrable_bv hi hv, integrableBV_logEnergy hi hv⟩

theorem windowCut_inDomain_of_source {a : ℝ} (ha : 0 ≤ a) {F F' : ℝ → ℂ}
    (hc : Continuous F) (hi : Integrable F) (hv : BoundedVariationOn F univ)
    (hd : ∀ x ∈ (Icc (-a) a)ᶜ, HasDerivAt F (F' x) x)
    (hi' : IntegrableOn F' (Icc (-a) a)ᶜ) :
    InWindowFormDomain a (windowCut a F) := by
  have ht := exteriorTail_boundedVariation hc ha hd hi'
  have hw : BoundedVariationOn (windowCut a F) univ := by
    rw [window_eq_sub_tail]
    exact boundedVariation_sub_complex hv ht
  exact supported_integrableBV_inDomain support_indicator_subset
    (hi.indicator measurableSet_Icc) hw

theorem squaredNorm_window_add_tail {a : ℝ} {F : ℝ → ℂ} (hf : MemLp F 2) :
    squaredNorm (windowCut a F) + squaredNorm (exteriorTail a F) = squaredNorm F := by
  have he (s : Set ℝ) : (fun u => ‖s.indicator F u‖^2) =
      s.indicator (fun u => ‖F u‖^2) := by
    funext u
    by_cases hu : u ∈ s <;> simp [hu]
  simp only [squaredNorm, windowCut, exteriorTail, he,
    integral_indicator measurableSet_Icc, integral_indicator measurableSet_Icc.compl]
  exact integral_add_compl measurableSet_Icc (hf.integrable_norm_pow (by norm_num))

theorem exteriorTail_squaredNorm_le_budget {a : ℝ} (ha : 0 ≤ a) {F F' : ℝ → ℂ}
    (hc : Continuous F) (hf : MemLp F 2)
    (hd : ∀ x ∈ (Icc (-a) a)ᶜ, HasDerivAt F (F' x) x)
    (hi : IntegrableOn (ThetaTrial.PrimeContinuity.weightedProfile 1 F) (Icc (-a) a)ᶜ)
    (hi' : IntegrableOn (ThetaTrial.PrimeContinuity.weightedProfile 1 F') (Icc (-a) a)ᶜ) :
    squaredNorm (exteriorTail a F) ≤ (hardTailBudget F F' a)^2 := by
  have ht := exteriorTail_integrable (integrableOn_of_weightedProfile_one hi)
  have ht2 : MemLp (exteriorTail a F) 2 := hf.indicator measurableSet_Icc.compl
  have hB := hardTailBudget_nonneg F F' a
  have hp (u : ℝ) : ‖exteriorTail a F u‖ ≤ hardTailBudget F F' a := by
    have hh := exteriorTail_weighted_pointwise hc ha hd hi hi' u
    exact (le_mul_of_one_le_left (norm_nonneg _)
      (Real.one_le_exp_iff.mpr (abs_nonneg u))).trans hh
  calc
    _ ≤ ∫ u : ℝ, hardTailBudget F F' a * ‖exteriorTail a F u‖ := by
      apply integral_mono (ht2.integrable_norm_pow (by norm_num)) (ht.norm.const_mul _)
      intro u
      nlinarith [hp u, norm_nonneg (exteriorTail a F u)]
    _ = hardTailBudget F F' a * (∫ u : ℝ, ‖exteriorTail a F u‖) := integral_const_mul _ _
    _ ≤ hardTailBudget F F' a * hardTailBudget F F' a :=
      mul_le_mul_of_nonneg_left (exteriorTail_l1_le_budget hi hi') hB
    _ = _ := by ring

theorem thetaAvg_polynomial_window_domain {a : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (P : Polynomial ℂ) :
    InWindowFormDomain a (windowCut a
      (polynomialDerivative P (fun u : ℝ => shiftedAverage a u))) := by
  apply windowCut_inDomain_of_source ha
    (polynomialDerivative_shiftedAverage_contDiff hZ P).continuous
    (polynomialDerivative_shiftedAverage_integrable ha hZ P)
    (polynomialDerivative_shiftedAverage_boundedVariation ha hZ P)
  · intro x hx
    exact ((polynomialDerivative_shiftedAverage_contDiff hZ P).differentiable (by simp) x).hasDerivAt
  · exact (polynomialDerivative_shiftedAverage_deriv_integrable ha hZ P).integrableOn

end ThetaTrial.Paper
