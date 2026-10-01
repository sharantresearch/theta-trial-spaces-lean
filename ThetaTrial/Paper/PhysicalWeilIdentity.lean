import ThetaTrial.Paper.PhysicalGammaConstant
import ThetaTrial.Paper.GammaCross
import ThetaTrial.Paper.ReflectionPairing
import ThetaTrial.Paper.RadicalBV

/-! The compensated physical-space Weil expression on weighted BV
correlations, with the paper's exact Euler/logarithmic constant. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set
open scoped ComplexConjugate

namespace ThetaTrial.Paper
open ThetaTrial.GammaEnergy

def physicalGammaCompensand (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  (g x + g (-x) - 2 * (Real.exp (-x / 2) : ℂ) * g 0) * (shiftKernel x : ℂ)

def physicalWeil (g : ℝ → ℂ) : ℂ :=
  (∫ u : ℝ, (2 * Real.cosh (u / 2) : ℝ) * g u) -
    ((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : ℝ) : ℂ) * g 0 -
    (∫ x : ℝ in Ioi 0, physicalGammaCompensand g x) -
    ∑' n : ℕ, Radical.primeTerm g n

theorem correlation_zero (f : ℝ → ℂ) : correlation f 0 = (squaredNorm f : ℂ) := by
  unfold correlation squaredNorm
  simp only [sub_zero, Complex.mul_conj, ← Complex.sq_norm]
  exact integral_complex_ofReal

theorem physicalShiftSq_eq_correlation {f : ℝ → ℂ} (hf2 : MemLp f 2) (x : ℝ) :
    physicalShiftSq f x = 2 * (squaredNorm f - (correlation f x).re) := by
  have hi := hf2.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hc : Integrable (fun u : ℝ => f (u + x) * conj (f u)) := by
    simpa only [add_sub_cancel_right] using
      (RadicalCutoff.l2_correlation_integrable hf2 hf2 x).comp_add_right x
  have hr : (∫ u : ℝ, (f (u + x) * conj (f u)).re) = (correlation f x).re := by
    rw [correlation_eq_weilFormula]
    exact Complex.reCLM.integral_comp_comm hc
  have hcre : Integrable (fun u : ℝ => (f (u + x) * conj (f u)).re) :=
    Complex.reCLM.integrable_comp hc
  have hsum : Integrable (fun u : ℝ => ‖f (u + x)‖ ^ 2 + ‖f u‖ ^ 2) :=
    (hi.comp_add_right x).add hi
  have htrans : (∫ u : ℝ, ‖f (u + x)‖ ^ 2) = ∫ u : ℝ, ‖f u‖ ^ 2 := by
    convert integral_add_right_eq_self (fun u : ℝ => ‖f u‖ ^ 2) x
      (μ := (volume : Measure ℝ)) using 1
  unfold physicalShiftSq
  have he (u : ℝ) : ‖f (u + x) - f u‖ ^ 2 =
      ‖f (u + x)‖ ^ 2 + ‖f u‖ ^ 2 - 2 * (f (u + x) * conj (f u)).re := by
    simp only [Complex.sq_norm, Complex.normSq_sub]
  simp_rw [he]
  rw [integral_sub hsum (hcre.const_mul 2),
    integral_add (hi.comp_add_right x) hi, integral_const_mul,
    htrans, hr]
  unfold squaredNorm
  ring

theorem physicalGammaCompensand_correlation {f : ℝ → ℂ}
    (hf2 : MemLp f 2) (x : ℝ) :
    physicalGammaCompensand (correlation f) x =
      ((2 * squaredNorm f * gammaCompensationKernel x -
        shiftKernel x * physicalShiftSq f x : ℝ) : ℂ) := by
  unfold physicalGammaCompensand
  rw [correlation_neg, Complex.add_conj, correlation_zero,
    physicalShiftSq_eq_correlation hf2]
  unfold gammaCompensationKernel
  push_cast
  ring

theorem physicalGammaCompensand_correlation_integrable {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2)
    (hg : Integrable (fun r : ℝ => gammaWeight r *
      Complex.normSq (paperFourier f r))) :
    IntegrableOn (physicalGammaCompensand (correlation f)) (Ioi 0) := by
  have hi := Complex.ofRealCLM.integrable_comp
    ((gammaCompensationKernel_integrable.const_mul (2 * squaredNorm f)).sub
      (physical_shift_energy_integrable hf hf2 hg))
  apply hi.congr
  filter_upwards with x
  exact (physicalGammaCompensand_correlation hf2 x).symm

theorem physicalGamma_correlation_eq_archimedean {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2)
    (hg : Integrable (fun r : ℝ => gammaWeight r *
      Complex.normSq (paperFourier f r))) :
    -((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : ℝ) : ℂ) *
        correlation f 0 -
      (∫ x : ℝ in Ioi 0, physicalGammaCompensand (correlation f) x) =
      (archimedeanEnergy f : ℂ) := by
  rw [correlation_zero, archimedeanEnergy_eq_shift hf hf2 hg]
  simp_rw [physicalGammaCompensand_correlation hf2]
  rw [integral_complex_ofReal,
    integral_sub (gammaCompensationKernel_integrable.const_mul (2 * squaredNorm f))
      (physical_shift_energy_integrable hf hf2 hg), integral_const_mul]
  have hconstant := gammaBase_compensation_constant
  unfold shiftEnergy
  push_cast
  have h := congrArg (fun v : ℝ => (v : ℂ)) hconstant
  push_cast at h
  linear_combination -(squaredNorm f : ℂ) * h

theorem physicalPole_integrand (g : ℝ → ℂ) (u : ℝ) :
    (2 * Real.cosh (u / 2) : ℝ) * g u =
      g u * Complex.exp (-I * (I / 2) * (u : ℂ)) +
      g u * Complex.exp (-I * (-I / 2) * (u : ℂ)) := by
  have hp : -I * (I / 2) * (u : ℂ) = ((u / 2 : ℝ) : ℂ) := by
    push_cast
    calc
      _ = -(I * I) * (u : ℂ) / 2 := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  have hm : -I * (-I / 2) * (u : ℂ) = ((-u / 2 : ℝ) : ℂ) := by
    push_cast
    calc
      _ = (I * I) * (u : ℂ) / 2 := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [hp, hm, ← Complex.ofReal_exp, ← Complex.ofReal_exp, Real.cosh_eq]
  push_cast
  ring

theorem physicalPole_integrable {g : ℝ → ℂ}
    (hp : Radical.FourierIntegrableAt g (I / 2))
    (hm : Radical.FourierIntegrableAt g (-I / 2)) :
    Integrable (fun u : ℝ => (2 * Real.cosh (u / 2) : ℝ) * g u) := by
  apply (hp.add hm).congr
  filter_upwards with u
  exact (physicalPole_integrand g u).symm

theorem physicalPole_integral {g : ℝ → ℂ}
    (hp : Radical.FourierIntegrableAt g (I / 2))
    (hm : Radical.FourierIntegrableAt g (-I / 2)) :
    (∫ u : ℝ, (2 * Real.cosh (u / 2) : ℝ) * g u) =
      Zeta23.paperFT g (I / 2) + Zeta23.paperFT g (-I / 2) := by
  simp_rw [physicalPole_integrand]
  rw [integral_add hp hm]
  change paperFourier g (I / 2) + paperFourier g (-I / 2) = _
  simp only [paperFourier_eq_source, neg_div, neg_neg, add_comm]

theorem weilTest_self_eq_correlation (f : ℝ → ℂ) :
    Zeta23.EF.weilTest f f = correlation f := by
  funext x
  exact RadicalCorrelation.weilTest_eq_integral f f x

theorem physicalWeil_correlation_eq_fullWeilForm {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2)
    (hg : Integrable (fun r : ℝ => gammaWeight r *
      Complex.normSq (paperFourier f r)))
    (hs : ∀ z : ℂ, |z.im| ≤ 1 → Radical.FourierIntegrableAt f z) :
    physicalWeil (correlation f) = (fullWeilForm f : ℂ) := by
  have hc (z : ℂ) (hz : |z.im| ≤ 1) : Radical.FourierIntegrableAt (correlation f) z := by
    rw [← weilTest_self_eq_correlation]
    exact RadicalCutoff.FourierIntegrableAt.weilTest (hs z hz)
      (hs (conj z) (by simpa only [Complex.conj_im, abs_neg] using hz))
  have hp := physicalPole_integral (hc (I / 2) (by norm_num)) (hc (-I / 2) (by norm_num))
  rw [← weilTest_self_eq_correlation] at hp
  rw [RadicalBV.pole_pair_of_strip hs] at hp
  have hprime : (∑' n : ℕ, Radical.primeTerm (correlation f) n) =
      (2 : ℂ) * ((∑' n : ℕ,
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          (correlation f (Real.log n)).re : ℝ) : ℂ) := by
    simp only [Radical.primeTerm, correlation_neg, Complex.add_conj]
    rw [Complex.ofReal_tsum, ← tsum_mul_left]
    apply tsum_congr
    intro n
    push_cast
    ring
  unfold physicalWeil
  rw [weilTest_self_eq_correlation] at hp
  rw [hp, hprime]
  have hgam := physicalGamma_correlation_eq_archimedean hf hf2 hg
  unfold fullWeilForm archimedeanEnergy at *
  push_cast at *
  linear_combination hgam

theorem weightedBV_physicalWeil_identity {f : ℝ → ℂ}
    (hv : BoundedVariationOn f univ)
    (hw : Integrable (ThetaTrial.PrimeContinuity.weightedProfile 1 f))
    (hm : Integrable (fun x : ℝ => Real.exp |x|) hv.vectorMeasure.variation) :
    physicalWeil (correlation f) = (fullWeilForm f : ℂ) := by
  have hc := weightedBVMeasure_fullForm_converges hv hw hm
  exact physicalWeil_correlation_eq_fullWeilForm
    (integrable_of_weightedProfile_one hw)
    ((weightedBVMeasure_weightedL2 hv hw hm).memLp (by norm_num)) hc.1 hc.2.2.1

/-- Every term of the geometric expression is absolutely convergent; the
compensated gamma integrand is kept as a single expression. The prime sum is
indexed by all naturals, with zero terms at zero and one. -/
theorem weightedBV_physical_terms_converge {f : ℝ → ℂ}
    (hv : BoundedVariationOn f univ)
    (hw : Integrable (ThetaTrial.PrimeContinuity.weightedProfile 1 f))
    (hm : Integrable (fun x : ℝ => Real.exp |x|) hv.vectorMeasure.variation) :
    IntegrableOn (physicalGammaCompensand (correlation f)) (Ioi 0) ∧
    Integrable (fun u : ℝ => (2 * Real.cosh (u / 2) : ℝ) * correlation f u) ∧
    Summable (fun n : ℕ => ‖Radical.primeTerm (correlation f) n‖) := by
  have hc := weightedBVMeasure_fullForm_converges hv hw hm
  have hf := integrable_of_weightedProfile_one hw
  have hf2 := (weightedBVMeasure_weightedL2 hv hw hm).memLp (by norm_num : (0 : ℝ) ≤ 1)
  have hcorr (z : ℂ) (hz : |z.im| ≤ 1) :
      Radical.FourierIntegrableAt (correlation f) z := by
    rw [← weilTest_self_eq_correlation]
    exact RadicalCutoff.FourierIntegrableAt.weilTest (hc.2.2.1 z hz)
      (hc.2.2.1 (conj z) (by simpa only [Complex.conj_im, abs_neg] using hz))
  refine ⟨physicalGammaCompensand_correlation_integrable hf hf2 hc.1,
    physicalPole_integrable (hcorr (I / 2) (by norm_num))
      (hcorr (-I / 2) (by norm_num)), ?_⟩
  apply (hc.2.1.mul_left 2).congr
  intro n
  simp only [Radical.primeTerm, correlation_neg, Complex.add_conj,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  norm_num
  ring

end ThetaTrial.Paper
