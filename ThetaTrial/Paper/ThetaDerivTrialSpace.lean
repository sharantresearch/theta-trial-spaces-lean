import ThetaTrial.Paper.ThetaDerivSector
import ThetaTrial.Paper.ThetaAvgTrialDimension
import ThetaTrial.Paper.WindowTrial

/-!
# The theta-derivative trial space in L²

Uses the polynomial-to-window map from `ThetaAvgTrialDimension`; positivity
comes from Theorem `deriv:main`.
-/

noncomputable section
open MeasureTheory Set Polynomial
open scoped Polynomial

namespace ThetaTrial.Paper

theorem fullWeilForm_congr_ae {f g : ℝ → ℂ} (hfg : f =ᵐ[volume] g) :
    fullWeilForm f = fullWeilForm g := by
  have hft (z : ℂ) : paperFourier f z = paperFourier g z := by
    unfold paperFourier
    apply integral_congr_ae
    filter_upwards [hfg] with u hu
    rw [hu]
  have hc (x : ℝ) : correlation f x = correlation g x := by
    unfold correlation
    apply integral_congr_ae
    have ht := (measurePreserving_add_right volume (-x)).quasiMeasurePreserving.ae_eq_comp hfg
    filter_upwards [hfg, ht] with u hu hv
    change f (u - x) = g (u - x) at hv
    rw [hu, hv]
  simp only [fullWeilForm, hft, hc]

theorem fullWeilForm_eq_zero_of_ae_zero {f : ℝ → ℂ} (hf : f =ᵐ[volume] 0) :
    fullWeilForm f = 0 := by
  rw [fullWeilForm_congr_ae hf]
  simp [fullWeilForm, paperFourier, correlation]

theorem squaredNorm_pos_of_fullWeilForm_pos {f : ℝ → ℂ} (hf : MemLp f 2)
    (hQ : 0 < fullWeilForm f) : 0 < squaredNorm f := by
  by_contra hnot
  have hz : squaredNorm f = 0 := le_antisymm (not_lt.mp hnot)
    (integral_nonneg (fun u => sq_nonneg _))
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hae : f =ᵐ[volume] 0 := by
    have hn := (integral_eq_zero_iff_of_nonneg (fun u => sq_nonneg ‖f u‖) hi).mp hz
    filter_upwards [hn] with u hu
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hu)
  have hzero := fullWeilForm_eq_zero_of_ae_zero hae
  linarith

theorem thetaDerivWindow_memLp (a : ℝ) (P : ℂ[X]) :
    MemLp (windowCut a (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))) 2 volume :=
  (polynomialDerivative_thetaDensity_memLp_two P).indicator measurableSet_Icc

theorem thetaDerivWindow_inDomain (P : ℂ[X]) {a : ℝ} (ha : 0 ≤ a) :
    InWindowFormDomain a (windowCut a (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))) := by
  apply windowCut_inDomain_of_source ha
    (polynomialDerivative_thetaDensity_continuous P)
    (polynomialDerivative_thetaDensity_integrable P)
    (polynomialDerivative_thetaDensity_boundedVariation P)
  · intro u hu
    exact ((polynomialDerivative_thetaDensity_contDiff P).differentiable (by simp) u).hasDerivAt
  · exact (polynomialDerivative_thetaDensity_deriv_integrable P).integrableOn

def thetaDerivTrialSpace (a : ℝ) (d : ℕ) : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) :=
  polynomialWindowTrialSpace a (fun u => (thetaDensity u : ℂ)) (thetaDerivWindow_memLp a) d

/-- Theorem `deriv:main` on `L²` classes: dimension `d+1` and positive
definiteness. -/
theorem thetaDeriv_trialSpace_main :
    ∃ c : ℝ, 0 < c ∧ ∃ a₀ : ℝ, 1 ≤ a₀ ∧
      ∀ a : ℝ, a₀ ≤ a → ∀ d : ℕ, (d : ℝ) ≤ c * Real.exp a →
      Module.finrank ℂ (thetaDerivTrialSpace a d) = d + 1 ∧
      ∀ v : Lp ℂ 2 (volume : Measure ℝ), v ∈ thetaDerivTrialSpace a d → v ≠ 0 →
        0 < fullWeilForm (fun u => v u) := by
  obtain ⟨c, hc, a₀, ha₀, hpos⟩ := thetaDeriv_positive_sector
  refine ⟨c, hc, a₀, ha₀, ?_⟩
  intro a haa d hd
  refine ⟨?_, ?_⟩
  · apply polynomialWindowTrialSpace_finrank_of_separation
    intro P hdegree hP
    exact squaredNorm_pos_of_fullWeilForm_pos (thetaDerivWindow_memLp a P)
      (hpos a haa d hd P hP hdegree)
  · intro v hv hvne
    obtain ⟨P, rfl⟩ := hv
    have hP : (P : ℂ[X]) ≠ 0 := by
      intro hz
      have hz' : P = 0 := Subtype.ext hz
      subst P
      exact hvne (map_zero _)
    have hdegree : (P : ℂ[X]).natDegree ≤ d := by
      apply Nat.lt_succ_iff.mp
      exact (Polynomial.natDegree_lt_iff_degree_lt hP).mpr (Polynomial.mem_degreeLT.mp P.property)
    have hp := hpos a haa d hd (P : ℂ[X]) hP hdegree
    have he := polynomialWindowL2LinearMap_coeFn a (fun u => (thetaDensity u : ℂ))
      (thetaDerivWindow_memLp a) (P : ℂ[X])
    change 0 < fullWeilForm
      (fun u => polynomialWindowL2LinearMap a (fun v => (thetaDensity v : ℂ))
        (thetaDerivWindow_memLp a) (P : ℂ[X]) u)
    rw [fullWeilForm_congr_ae he]
    exact hp

theorem thetaDeriv_trialSpace_main_sqrtT :
    ∃ c : ℝ, 0 < c ∧ ∃ a₀ : ℝ, 1 ≤ a₀ ∧
      ∀ a : ℝ, a₀ ≤ a → ∀ d : ℕ, (d : ℝ) ≤ c * Real.sqrt (scaleT a) →
      Module.finrank ℂ (thetaDerivTrialSpace a d) = d + 1 ∧
      ∀ v : Lp ℂ 2 (volume : Measure ℝ), v ∈ thetaDerivTrialSpace a d → v ≠ 0 →
        0 < fullWeilForm (fun u => v u) := by
  obtain ⟨c, hc, a₀, ha₀, hall⟩ := thetaDeriv_trialSpace_main
  refine ⟨c / Real.sqrt (2 * Real.pi), div_pos hc (Real.sqrt_pos.mpr (by positivity)),
    a₀, ha₀, ?_⟩
  intro a haa d hd
  rw [thetaDeriv_rescaled_degree_factor] at hd
  exact hall a haa d hd

#print axioms thetaDerivWindow_inDomain
#print axioms thetaDeriv_trialSpace_main
#print axioms thetaDeriv_trialSpace_main_sqrtT

end ThetaTrial.Paper
