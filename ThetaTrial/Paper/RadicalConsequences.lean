import ThetaTrial.Paper.RadicalSource
import ThetaTrial.Paper.WindowTrial

/-! All form-domain, radical, hard-cutoff, and absolute-bound consequences
for the proved smooth-source explicit-formula class. -/

noncomputable section
open Complex MeasureTheory Set
open scoped ComplexConjugate

namespace ThetaTrial.Paper.RadicalSource
open RadicalCorrelation RadicalCutoff

variable {F : ℝ → ℂ} (hF : RegularSource F)
include hF

theorem RegularSource.integrable : Integrable F :=
  weighted_integrable hF.smooth.continuous.aestronglyMeasurable (hF.weight0 0)

theorem RegularSource.deriv_integrable : Integrable (deriv F) :=
  weighted_integrable (hF.smooth.continuous_deriv (by norm_num)).aestronglyMeasurable (hF.weight1 0)

theorem RegularSource.boundedVariation : BoundedVariationOn F univ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (variation_le_integral_deriv ordConnected_univ
      (fun u _ => (hF.smooth.differentiable (by norm_num) u).hasDerivAt) hF.deriv_integrable.integrableOn)

theorem RegularSource.window_inDomain {a : ℝ} (ha : 0 ≤ a) :
    InWindowFormDomain a (windowCut a F) :=
  windowCut_inDomain_of_source ha hF.smooth.continuous hF.integrable hF.boundedVariation
    (fun u _ => (hF.smooth.differentiable (by norm_num) u).hasDerivAt)
    hF.deriv_integrable.integrableOn

theorem source_fullWeilForm_zero {m : ℂ → ℂ}
    (hfactor : ∀ z, paperFourier F z = xiFunction z * m z) : fullWeilForm F = 0 := by
  have hq : Radical.fullQuadratic F = 0 :=
    source_fullPairing_eq_zero hF hfactor hF.smooth.continuous.aestronglyMeasurable hF.weight0
  rw [Radical.fullQuadratic_eq_paperForm (source_fourier_integrable hF)] at hq
  exact_mod_cast hq

theorem source_tail_pairing_zero {m : ℂ → ℂ}
    (hfactor : ∀ z, paperFourier F z = xiFunction z * m z) (a : ℝ) :
    Radical.fullPairing F (exteriorTail a F) = 0 ∧
      Radical.fullPairing (exteriorTail a F) F = 0 := by
  have hz : Radical.fullPairing F (exteriorTail a F) = 0 :=
    source_fullPairing_eq_zero hF hfactor
      (hF.smooth.continuous.aestronglyMeasurable.indicator measurableSet_Icc.compl)
      (fun R => weighted_indicator measurableSet_Icc.compl (hF.weight0 R))
  exact ⟨hz, by rw [fullPairing_hermitian, hz, map_zero]⟩

theorem source_window_abs_bound {m : ℂ → ℂ}
    (hfactor : ∀ z, paperFourier F z = xiFunction z * m z)
    {a : ℝ} (ha : 0 ≤ a) :
    |fullWeilForm (windowCut a F)| ≤ tailFormConstant * (hardTailBudget F (deriv F) a) ^ 2 := by
  rw [source_hardCutoff hF hfactor ha]
  exact exteriorTail_fullWeilForm_abs_le hF.smooth.continuous ha
    (fun u _ => (hF.smooth.differentiable (by norm_num) u).hasDerivAt)
    (weightedProfile_integrable hF.smooth.continuous.aestronglyMeasurable (hF.weight0 1)).integrableOn
    (weightedProfile_integrable (hF.smooth.continuous_deriv (by norm_num)).aestronglyMeasurable
      (hF.weight1 1)).integrableOn

end ThetaTrial.Paper.RadicalSource

#print axioms ThetaTrial.Paper.RadicalSource.RegularSource.window_inDomain
#print axioms ThetaTrial.Paper.RadicalSource.source_window_abs_bound
