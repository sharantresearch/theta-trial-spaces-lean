import ThetaTrial.Paper.ShiftMeasure
import ThetaTrial.Paper.TrialFourierComplex

/-! Finite complex measures of imaginary theta shifts, using the Jordan decompositions of their real and imaginary signed measures. This is
the standard complex measure integral; no absolute continuity is required. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set Filter
open scoped Topology ComplexConjugate

namespace ThetaTrial.Paper.ComplexShiftMeasure
open RadicalApproximation RadicalCorrelation RadicalCutoff RadicalSource ShiftMeasure

/-- The standard integral over the closed shift interval with respect to a
complex measure, explicitly through its four finite Jordan measures. -/
def integral (μ : ComplexMeasure ℝ) (b : ℝ) (f : ℝ → ℂ) : ℂ :=
  (∫ y in Icc (-b) b, f y ∂μ.re.toJordanDecomposition.posPart) -
  (∫ y in Icc (-b) b, f y ∂μ.re.toJordanDecomposition.negPart) +
  I * ((∫ y in Icc (-b) b, f y ∂μ.im.toJordanDecomposition.posPart) -
    (∫ y in Icc (-b) b, f y ∂μ.im.toJordanDecomposition.negPart))

def jet (μ : ComplexMeasure ℝ) (b : ℝ) (j : ℕ) (z : ℂ) : ℂ :=
  integral μ b (fun y => iteratedDeriv j complexThetaDensity (z + I * (y : ℂ)))

def source (μ : ComplexMeasure ℝ) (b : ℝ) : ℂ → ℂ := jet μ b 0

def multiplier (μ : ComplexMeasure ℝ) (b : ℝ) (z : ℂ) : ℂ :=
  integral μ b (fun y => Complex.exp (-z * (y : ℂ)))

theorem jet_eq (μ : ComplexMeasure ℝ) (b : ℝ) (j : ℕ) (z : ℂ) :
    jet μ b j z = shiftJet μ.re.toJordanDecomposition.posPart b j z -
      shiftJet μ.re.toJordanDecomposition.negPart b j z + I *
      (shiftJet μ.im.toJordanDecomposition.posPart b j z -
        shiftJet μ.im.toJordanDecomposition.negPart b j z) := rfl

theorem jet_hasDerivAt (μ : ComplexMeasure ℝ) {b : ℝ} {z : ℂ}
    (hz : z ∈ shiftStrip b) (j : ℕ) : HasDerivAt (jet μ b j) (jet μ b (j + 1) z) z :=
  ((shiftJet_hasDerivAt μ.re.toJordanDecomposition.posPart hz j).sub
    (shiftJet_hasDerivAt μ.re.toJordanDecomposition.negPart hz j)).add
    (((shiftJet_hasDerivAt μ.im.toJordanDecomposition.posPart hz j).sub
      (shiftJet_hasDerivAt μ.im.toJordanDecomposition.negPart hz j)).const_mul I)

theorem jet_analytic (μ : ComplexMeasure ℝ) (b : ℝ) (j : ℕ) :
    AnalyticOnNhd ℂ (jet μ b j) (shiftStrip b) := by
  have hd : DifferentiableOn ℂ (jet μ b j) (shiftStrip b) :=
    fun z hz => (jet_hasDerivAt μ hz j).differentiableAt.differentiableWithinAt
  exact hd.analyticOnNhd (shiftStrip_open b)

theorem jet_real_contDiff (μ : ComplexMeasure ℝ) {b : ℝ}
    (hbpi : b < Real.pi / 4) (j : ℕ) : ContDiff ℝ ⊤ (fun u : ℝ => jet μ b j (u : ℂ)) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  have h : ContDiffAt ℝ ⊤ (jet μ b j) (u : ℂ) :=
    (jet_analytic μ b j (u : ℂ) (real_mem_shiftStrip hbpi u)).contDiffAt.restrict_scalars ℝ
  simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
    h.comp u Complex.ofRealCLM.contDiff.contDiffAt

theorem jet_real_deriv (μ : ComplexMeasure ℝ) {b : ℝ} (hbpi : b < Real.pi / 4) (j : ℕ) :
    deriv (fun u : ℝ => jet μ b j (u : ℂ)) = fun u : ℝ => jet μ b (j + 1) (u : ℂ) := by
  funext u
  exact ((jet_hasDerivAt μ (real_mem_shiftStrip hbpi u) j).comp_ofReal).deriv

theorem source_real_iteratedDeriv (μ : ComplexMeasure ℝ) {b : ℝ}
    (hbpi : b < Real.pi / 4) (j : ℕ) :
    iteratedDeriv j (fun u : ℝ => source μ b (u : ℂ)) =
      fun u : ℝ => jet μ b j (u : ℂ) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [iteratedDeriv_succ, ih, jet_real_deriv μ hbpi j]

theorem jet_weighted_integrable (μ : ComplexMeasure ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) (j : ℕ) (R : ℝ) :
    Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖jet μ b j (u : ℂ)‖) := by
  have hpos (ν : Measure ℝ) [IsFiniteMeasure ν] :
      Integrable (ThetaTrial.PrimeContinuity.weightedProfile R (fun u : ℝ => shiftJet ν b j (u : ℂ))) :=
    weightedProfile_integrable (shiftJet_real_contDiff ν hbpi j).continuous.aestronglyMeasurable
      (shiftJet_weighted_integrable ν hb hbpi j R)
  have hi := ((hpos μ.re.toJordanDecomposition.posPart).sub
    (hpos μ.re.toJordanDecomposition.negPart)).add
    (((hpos μ.im.toJordanDecomposition.posPart).sub
      (hpos μ.im.toJordanDecomposition.negPart)).const_mul I)
  have hj : Integrable (ThetaTrial.PrimeContinuity.weightedProfile R (fun u : ℝ => jet μ b j (u : ℂ))) := by
    apply hi.congr
    filter_upwards with u
    simp only [Pi.add_apply, Pi.sub_apply, ThetaTrial.PrimeContinuity.weightedProfile, jet_eq]
    ring
  simpa only [ThetaTrial.PrimeContinuity.weightedProfile_norm] using hj.norm

theorem jet_exponential (μ : ComplexMeasure ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) (j : ℕ) (R : ℝ) :
    ∃ M > 0, ∀ u : ℝ, ‖jet μ b j (u : ℂ)‖ ≤ M * Real.exp (-(R * |u|)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := shiftJet_exponential μ.re.toJordanDecomposition.posPart hb hbpi j R
  obtain ⟨C₂, hC₂, h₂⟩ := shiftJet_exponential μ.re.toJordanDecomposition.negPart hb hbpi j R
  obtain ⟨C₃, hC₃, h₃⟩ := shiftJet_exponential μ.im.toJordanDecomposition.posPart hb hbpi j R
  obtain ⟨C₄, hC₄, h₄⟩ := shiftJet_exponential μ.im.toJordanDecomposition.negPart hb hbpi j R
  refine ⟨C₁ + C₂ + (C₃ + C₄), by positivity, ?_⟩
  intro u
  rw [jet_eq]
  calc
    _ ≤ (‖shiftJet μ.re.toJordanDecomposition.posPart b j (u : ℂ)‖ +
        ‖shiftJet μ.re.toJordanDecomposition.negPart b j (u : ℂ)‖) +
        (‖shiftJet μ.im.toJordanDecomposition.posPart b j (u : ℂ)‖ +
          ‖shiftJet μ.im.toJordanDecomposition.negPart b j (u : ℂ)‖) := by
      have h := norm_add_le
        (shiftJet μ.re.toJordanDecomposition.posPart b j (u : ℂ) -
          shiftJet μ.re.toJordanDecomposition.negPart b j (u : ℂ))
        (I * (shiftJet μ.im.toJordanDecomposition.posPart b j (u : ℂ) -
          shiftJet μ.im.toJordanDecomposition.negPart b j (u : ℂ)))
      simp only [norm_mul, norm_I, one_mul] at h
      exact h.trans (add_le_add (norm_sub_le _ _) (norm_sub_le _ _))
    _ ≤ (C₁ * Real.exp (-(R * |u|)) + C₂ * Real.exp (-(R * |u|))) +
        (C₃ * Real.exp (-(R * |u|)) + C₄ * Real.exp (-(R * |u|))) := by
      gcongr
      · exact h₁ u
      · exact h₂ u
      · exact h₃ u
      · exact h₄ u
    _ = _ := by ring

theorem jet_regularSource (μ : ComplexMeasure ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) (j : ℕ) :
    RegularSource (fun u : ℝ => jet μ b j (u : ℂ)) := by
  refine ⟨(jet_real_contDiff μ hbpi j).of_le le_top, jet_weighted_integrable μ hb hbpi j,
    ?_, ?_, jet_exponential μ hb hbpi j⟩
  · intro R
    rw [jet_real_deriv μ hbpi j]
    exact jet_weighted_integrable μ hb hbpi (j + 1) R
  · intro R
    rw [jet_real_deriv μ hbpi j, jet_real_deriv μ hbpi (j + 1)]
    exact jet_weighted_integrable μ hb hbpi (j + 1 + 1) R

theorem fourierIntegrable_sub {f g : ℝ → ℂ} {z : ℂ}
    (hf : Radical.FourierIntegrableAt f z) (hg : Radical.FourierIntegrableAt g z) :
    Radical.FourierIntegrableAt (f - g) z := by
  apply (hf.sub hg).congr
  filter_upwards with u
  simp only [Pi.sub_apply, sub_mul]

theorem fourierIntegrable_const_mul {f : ℝ → ℂ} {z : ℂ}
    (hf : Radical.FourierIntegrableAt f z) (c : ℂ) :
    Radical.FourierIntegrableAt (fun u => c * f u) z := by
  apply (hf.const_mul c).congr
  filter_upwards with u
  exact (mul_assoc _ _ _).symm

theorem paperFourier_add_complex {f g : ℝ → ℂ} {z : ℂ}
    (hf : Radical.FourierIntegrableAt f z) (hg : Radical.FourierIntegrableAt g z) :
    paperFourier (f + g) z = paperFourier f z + paperFourier g z := by
  simp only [paperFourier, Pi.add_apply, add_mul]
  exact integral_add hf hg

theorem paperFourier_sub_complex {f g : ℝ → ℂ} {z : ℂ}
    (hf : Radical.FourierIntegrableAt f z) (hg : Radical.FourierIntegrableAt g z) :
    paperFourier (f - g) z = paperFourier f z - paperFourier g z := by
  simp only [paperFourier, Pi.sub_apply, sub_mul]
  exact integral_sub hf hg

theorem source_fourier (μ : ComplexMeasure ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) (z : ℂ) :
    paperFourier (fun u : ℝ => source μ b (u : ℂ)) z = xiFunction z * multiplier μ b z := by
  let f₁ : ℝ → ℂ := fun u => positiveShift μ.re.toJordanDecomposition.posPart b (u : ℂ)
  let f₂ : ℝ → ℂ := fun u => positiveShift μ.re.toJordanDecomposition.negPart b (u : ℂ)
  let f₃ : ℝ → ℂ := fun u => positiveShift μ.im.toJordanDecomposition.posPart b (u : ℂ)
  let f₄ : ℝ → ℂ := fun u => positiveShift μ.im.toJordanDecomposition.negPart b (u : ℂ)
  have h₁ : Radical.FourierIntegrableAt f₁ z :=
    source_fourier_integrable (shiftJet_regularSource μ.re.toJordanDecomposition.posPart hb hbpi 0) z
  have h₂ : Radical.FourierIntegrableAt f₂ z :=
    source_fourier_integrable (shiftJet_regularSource μ.re.toJordanDecomposition.negPart hb hbpi 0) z
  have h₃ : Radical.FourierIntegrableAt f₃ z :=
    source_fourier_integrable (shiftJet_regularSource μ.im.toJordanDecomposition.posPart hb hbpi 0) z
  have h₄ : Radical.FourierIntegrableAt f₄ z :=
    source_fourier_integrable (shiftJet_regularSource μ.im.toJordanDecomposition.negPart hb hbpi 0) z
  change paperFourier ((f₁ - f₂) + (fun u => I * (f₃ - f₄) u)) z = _
  rw [paperFourier_add_complex (fourierIntegrable_sub h₁ h₂)
      (fourierIntegrable_const_mul (fourierIntegrable_sub h₃ h₄) I),
    paperFourier_sub_complex h₁ h₂, paperFourier_const_mul,
    paperFourier_sub_complex h₃ h₄]
  simp only [f₁, f₂, f₃, f₄, positiveShift_fourier _ hb hbpi]
  change _ = xiFunction z *
    (positiveMultiplier μ.re.toJordanDecomposition.posPart b z -
      positiveMultiplier μ.re.toJordanDecomposition.negPart b z + I *
        (positiveMultiplier μ.im.toJordanDecomposition.posPart b z -
          positiveMultiplier μ.im.toJordanDecomposition.negPart b z))
  ring

theorem source_hardCutoff (μ : ComplexMeasure ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) {a : ℝ} (ha : 0 ≤ a) :
    fullWeilForm (windowCut a (fun u : ℝ => source μ b (u : ℂ))) =
      fullWeilForm (exteriorTail a (fun u : ℝ => source μ b (u : ℂ))) :=
  RadicalSource.source_hardCutoff (jet_regularSource μ hb hbpi 0) (source_fourier μ hb hbpi) ha

end ThetaTrial.Paper.ComplexShiftMeasure

#print axioms ThetaTrial.Paper.ComplexShiftMeasure.source_fourier
#print axioms ThetaTrial.Paper.ComplexShiftMeasure.source_hardCutoff
