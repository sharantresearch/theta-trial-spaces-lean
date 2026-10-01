import ThetaTrial.Paper.RadicalSource
import ThetaTrial.Paper.ShiftedAverageFourier
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Finite measures of imaginary theta shifts. Complex measures are handled
through the Jordan decompositions of their real and imaginary parts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set Filter Metric
open scoped Topology ComplexConjugate

namespace ThetaTrial.Paper.ShiftMeasure
open RadicalApproximation RadicalSource

def shiftJet (ν : Measure ℝ) (b : ℝ) (j : ℕ) (z : ℂ) : ℂ :=
  ∫ y : ℝ in Icc (-b) b, iteratedDeriv j complexThetaDensity (z + I * (y : ℂ)) ∂ν

def positiveShift (ν : Measure ℝ) (b : ℝ) : ℂ → ℂ := shiftJet ν b 0

def positiveMultiplier (ν : Measure ℝ) (b : ℝ) (z : ℂ) : ℂ :=
  ∫ y : ℝ in Icc (-b) b, Complex.exp (-z * (y : ℂ)) ∂ν

def shiftStrip (b : ℝ) : Set ℂ := {z | |z.im| < Real.pi / 4 - b}

theorem shiftStrip_open (b : ℝ) : IsOpen (shiftStrip b) :=
  isOpen_lt (by fun_prop) continuous_const

theorem shifted_mem_thetaStrip {b : ℝ} {z : ℂ} (hz : z ∈ shiftStrip b)
    {y : ℝ} (hy : y ∈ Icc (-b) b) : z + I * (y : ℂ) ∈ thetaStrip := by
  change |(z + I * (y : ℂ)).im| < Real.pi / 4
  have hyb : |y| ≤ b := abs_le.mpr hy
  have hz' : |z.im| < Real.pi / 4 - b := hz
  simp only [add_im, mul_im, I_re, ofReal_im, mul_zero, I_im, ofReal_re, one_mul, zero_add]
  exact (abs_add_le _ _).trans_lt (by linarith)

theorem shiftJet_integrand_continuousOn {b : ℝ} {z : ℂ}
    (hz : z ∈ shiftStrip b) (j : ℕ) :
    ContinuousOn (fun y : ℝ => iteratedDeriv j complexThetaDensity (z + I * (y : ℂ)))
      (Icc (-b) b) :=
  (analytic_iteratedTheta j).continuousOn.comp (by fun_prop)
    (fun _ hy => shifted_mem_thetaStrip hz hy)

theorem shiftJet_hasDerivAt (ν : Measure ℝ) [IsFiniteMeasure ν]
    {b : ℝ} {z : ℂ} (hz : z ∈ shiftStrip b) (j : ℕ) :
    HasDerivAt (shiftJet ν b j) (shiftJet ν b (j + 1) z) z := by
  let U := shiftStrip b
  let J := Icc (-b) b
  have hU : IsOpen U := shiftStrip_open b
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  let r := ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hdisc : closedBall z r ⊆ U := by
    intro w hw
    apply hεsub
    rw [Metric.mem_ball]
    have hw' := Metric.mem_closedBall.mp hw
    dsimp [r] at hw'
    linarith
  let K := (fun p : ℂ × ℝ => p.1 + I * (p.2 : ℂ)) '' (closedBall z r ×ˢ J)
  have hK : IsCompact K :=
    ((isCompact_closedBall z r).prod (isCompact_Icc : IsCompact J)).image (by fun_prop)
  have hKstrip : K ⊆ thetaStrip := by
    rintro v ⟨⟨w, y⟩, ⟨hw, hy⟩, rfl⟩
    exact shifted_mem_thetaStrip (hdisc hw) hy
  have hj := analytic_iteratedTheta j
  have hj' := analytic_iteratedTheta (j + 1)
  obtain ⟨C, hC⟩ := hK.bddAbove_image (hj'.continuousOn.norm.mono hKstrip)
  have hmeas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable
      (fun y : ℝ => iteratedDeriv j complexThetaDensity (w + I * (y : ℂ)))
      (ν.restrict J) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (shiftJet_integrand_continuousOn hw j).aestronglyMeasurable measurableSet_Icc
  have hbase : Integrable
      (fun y : ℝ => iteratedDeriv j complexThetaDensity (z + I * (y : ℂ)))
      (ν.restrict J) := (shiftJet_integrand_continuousOn hz j).integrableOn_Icc
  have hdmeas : AEStronglyMeasurable
      (fun y : ℝ => iteratedDeriv (j + 1) complexThetaDensity (z + I * (y : ℂ)))
      (ν.restrict J) :=
    (shiftJet_integrand_continuousOn hz (j + 1)).aestronglyMeasurable measurableSet_Icc
  have hbound : ∀ᵐ (y : ℝ) ∂ν.restrict J, ∀ w ∈ ball z r,
      ‖iteratedDeriv (j + 1) complexThetaDensity (w + I * (y : ℂ))‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy w hw
    exact hC (mem_image_of_mem _ (mem_image_of_mem _
      (show (w, y) ∈ closedBall z r ×ˢ J from ⟨ball_subset_closedBall hw, hy⟩)))
  have hdiff : ∀ᵐ (y : ℝ) ∂ν.restrict J, ∀ w ∈ ball z r,
      HasDerivAt (fun v : ℂ => iteratedDeriv j complexThetaDensity (v + I * (y : ℂ)))
        (iteratedDeriv (j + 1) complexThetaDensity (w + I * (y : ℂ))) w := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy w hw
    have hs := shifted_mem_thetaStrip (hdisc (ball_subset_closedBall hw)) hy
    have hd := (hj _ hs).differentiableAt.hasDerivAt
    simpa only [iteratedDeriv_succ, mul_one, Function.comp_def, id_eq] using
      hd.comp w ((hasDerivAt_id w).add_const (I * (y : ℂ)))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := ν.restrict J) (s := ball z r) (bound := fun _ => C)
    (F' := fun w y => iteratedDeriv (j + 1) complexThetaDensity (w + I * (y : ℂ)))
    (ball_mem_nhds z hr) hmeas hbase hdmeas hbound (integrable_const _) hdiff).2

theorem shiftJet_analytic (ν : Measure ℝ) [IsFiniteMeasure ν] (b : ℝ) (j : ℕ) :
    AnalyticOnNhd ℂ (shiftJet ν b j) (shiftStrip b) := by
  have hd : DifferentiableOn ℂ (shiftJet ν b j) (shiftStrip b) :=
    fun z hz => (shiftJet_hasDerivAt ν hz j).differentiableAt.differentiableWithinAt
  exact hd.analyticOnNhd (shiftStrip_open b)

theorem real_mem_shiftStrip {b : ℝ} (hb : b < Real.pi / 4) (u : ℝ) :
    (u : ℂ) ∈ shiftStrip b := by
  simp only [shiftStrip, mem_setOf_eq, Complex.ofReal_im, abs_zero]
  linarith

theorem shiftJet_real_contDiff (ν : Measure ℝ) [IsFiniteMeasure ν]
    {b : ℝ} (hb : b < Real.pi / 4) (j : ℕ) :
    ContDiff ℝ ⊤ (fun u : ℝ => shiftJet ν b j (u : ℂ)) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  have h : ContDiffAt ℝ ⊤ (shiftJet ν b j) (u : ℂ) :=
    (shiftJet_analytic ν b j (u : ℂ) (real_mem_shiftStrip hb u)).contDiffAt.restrict_scalars ℝ
  simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
    h.comp u Complex.ofRealCLM.contDiff.contDiffAt

theorem positiveShift_real_iteratedDeriv (ν : Measure ℝ) [IsFiniteMeasure ν]
    {b : ℝ} (hb : b < Real.pi / 4) (j : ℕ) :
    iteratedDeriv j (fun u : ℝ => positiveShift ν b (u : ℂ)) =
      fun u : ℝ => shiftJet ν b j (u : ℂ) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    exact ((shiftJet_hasDerivAt ν (real_mem_shiftStrip hb u) j).comp_ofReal).deriv

theorem shiftJet_decay (ν : Measure ℝ) [IsFiniteMeasure ν]
    {b : ℝ} (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) :
    ∃ c > 0, ∀ j : ℕ, ∃ C > 0, ∀ u : ℝ,
      ‖shiftJet ν b j (u : ℂ)‖ ≤ C *
        ThetaTrial.ThetaSeries.doubleExpEnvelope ((9 / 2 : ℝ) + 2 * (j : ℝ)) c |u| := by
  obtain ⟨c, hc, hder⟩ := complexThetaDensity_iteratedDeriv_closed_strip_decay hb hbpi
  refine ⟨c, hc, ?_⟩
  intro j
  obtain ⟨C, hC, hbound⟩ := hder j
  let m := (ν.restrict (Icc (-b) b)).real univ
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  refine ⟨C * (m + 1), by positivity, ?_⟩
  intro u
  have hh : ∀ᵐ (y : ℝ) ∂ν.restrict (Icc (-b) b),
      ‖iteratedDeriv j complexThetaDensity ((u : ℂ) + I * (y : ℂ))‖ ≤
        C * ThetaTrial.ThetaSeries.doubleExpEnvelope ((9 / 2 : ℝ) + 2 * (j : ℝ)) c |u| := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have he := hbound ((u : ℂ) + I * (y : ℂ)) (by simpa [Complex.mul_im] using abs_le.mpr hy)
    simpa only [ThetaTrial.ThetaSeries.doubleExpEnvelope, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, add_zero, mul_assoc] using he
  have hi := norm_integral_le_of_norm_le_const hh
  change ‖shiftJet ν b j (u : ℂ)‖ ≤
    (C * ThetaTrial.ThetaSeries.doubleExpEnvelope ((9 / 2 : ℝ) + 2 * (j : ℝ)) c |u|) * m at hi
  refine hi.trans ?_
  calc
    _ ≤ (C * ThetaTrial.ThetaSeries.doubleExpEnvelope ((9 / 2 : ℝ) + 2 * (j : ℝ)) c |u|) * (m + 1) := by
      apply mul_le_mul_of_nonneg_left (by linarith)
      unfold ThetaTrial.ThetaSeries.doubleExpEnvelope
      positivity
    _ = _ := by ring

theorem shiftJet_weighted_integrable (ν : Measure ℝ) [IsFiniteMeasure ν]
    {b : ℝ} (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) (j : ℕ) (R : ℝ) :
    Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖shiftJet ν b j (u : ℂ)‖) := by
  obtain ⟨c, hc, hder⟩ := shiftJet_decay ν hb hbpi
  obtain ⟨C, hC, hbound⟩ := hder j
  have hcont : Continuous (fun u : ℝ => Real.exp (R * |u|) * ‖shiftJet ν b j (u : ℂ)‖) :=
    (by fun_prop : Continuous (fun u : ℝ => Real.exp (R * |u|))).mul
      (shiftJet_real_contDiff ν hbpi j).continuous.norm
  apply ((doubleExpEnvelope_abs_integrable (R + (9 / 2 + 2 * (j : ℝ))) hc).const_mul C).mono'
    hcont.aestronglyMeasurable
  filter_upwards with u
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ Real.exp (R * |u|) * (C *
        ThetaTrial.ThetaSeries.doubleExpEnvelope (9 / 2 + 2 * (j : ℝ)) c |u|) :=
      mul_le_mul_of_nonneg_left (hbound u) (Real.exp_pos _).le
    _ = _ := by
      have he : Real.exp ((R + (9 / 2 + 2 * (j : ℝ))) * |u|) =
          Real.exp (R * |u|) * Real.exp ((9 / 2 + 2 * (j : ℝ)) * |u|) := by
        rw [add_mul, Real.exp_add]
      unfold ThetaTrial.ThetaSeries.doubleExpEnvelope
      rw [he]
      ring

theorem shiftJet_exponential (ν : Measure ℝ) [IsFiniteMeasure ν]
    {b : ℝ} (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) (j : ℕ) (R : ℝ) :
    ∃ M > 0, ∀ u : ℝ, ‖shiftJet ν b j (u : ℂ)‖ ≤ M * Real.exp (-(R * |u|)) := by
  obtain ⟨c, hc, hder⟩ := shiftJet_decay ν hb hbpi
  obtain ⟨C, hC, hbound⟩ := hder j
  obtain ⟨B, hB, henv⟩ := doubleExpEnvelope_bounded (R + (9 / 2 + 2 * (j : ℝ))) hc
  refine ⟨C * B, mul_pos hC hB, ?_⟩
  intro u
  have hw : Real.exp (R * |u|) * ‖shiftJet ν b j (u : ℂ)‖ ≤ C * B := by
    calc
      _ ≤ Real.exp (R * |u|) * (C *
          ThetaTrial.ThetaSeries.doubleExpEnvelope (9 / 2 + 2 * (j : ℝ)) c |u|) :=
        mul_le_mul_of_nonneg_left (hbound u) (Real.exp_pos _).le
      _ = C * ThetaTrial.ThetaSeries.doubleExpEnvelope (R + (9 / 2 + 2 * (j : ℝ))) c |u| := by
        have he : Real.exp ((R + (9 / 2 + 2 * (j : ℝ))) * |u|) =
            Real.exp (R * |u|) * Real.exp ((9 / 2 + 2 * (j : ℝ)) * |u|) := by
          rw [add_mul, Real.exp_add]
        unfold ThetaTrial.ThetaSeries.doubleExpEnvelope
        rw [he]
        ring
      _ ≤ C * B := mul_le_mul_of_nonneg_left (henv |u| (abs_nonneg u)) hC.le
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
  simpa only [mul_comm] using hw

def fourierIntegrand (z : ℂ) (u y : ℝ) : ℂ :=
  complexThetaDensity ((u : ℂ) + I * (y : ℂ)) * Complex.exp (-I * z * (u : ℂ))

theorem fourierIntegrand_integrable (ν : Measure ℝ) [IsFiniteMeasure ν]
    {b : ℝ} (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) (z : ℂ) :
    Integrable (Function.uncurry (fourierIntegrand z))
      (volume.prod (ν.restrict (Icc (-b) b))) := by
  obtain ⟨g, hg, hbound⟩ := shiftedTheta_weighted_majorant 0 |z.im| hb hbpi
  have hmeas : Measurable (Function.uncurry (fourierIntegrand z)) := by
    unfold fourierIntegrand Function.uncurry
    exact (complexThetaDensity_measurable.comp (by fun_prop)).mul (by fun_prop)
  have hy : ∀ᵐ p : ℝ × ℝ ∂volume.prod (ν.restrict (Icc (-b) b)), p.2 ∈ Icc (-b) b := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_snd)).mpr
    exact Eventually.of_forall (fun _ => ae_restrict_mem measurableSet_Icc)
  apply (hg.comp_fst (ν.restrict (Icc (-b) b))).mono' hmeas.aestronglyMeasurable
  filter_upwards [hy] with p hp
  have he : ‖Complex.exp (-I * z * (p.1 : ℂ))‖ ≤ Real.exp (|z.im| * |p.1|) := by
    simpa using norm_fourier_complex_exp_le z (p.1 : ℂ)
  change ‖complexThetaDensity ((p.1 : ℂ) + I * (p.2 : ℂ)) *
    Complex.exp (-I * z * (p.1 : ℂ))‖ ≤ g p.1
  rw [norm_mul]
  calc
    _ ≤ ‖complexThetaDensity ((p.1 : ℂ) + I * (p.2 : ℂ))‖ *
        Real.exp (|z.im| * |p.1|) := mul_le_mul_of_nonneg_left he (norm_nonneg _)
    _ ≤ g p.1 := by
      simpa only [iteratedDeriv_zero, mul_comm] using hbound p.1 p.2 (abs_le.mpr hp)

theorem positiveShift_fourier (ν : Measure ℝ) [IsFiniteMeasure ν]
    {b : ℝ} (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) (z : ℂ) :
    paperFourier (fun u : ℝ => positiveShift ν b (u : ℂ)) z =
      xiFunction z * positiveMultiplier ν b z := by
  calc
    _ = ∫ u : ℝ, ∫ y : ℝ in Icc (-b) b, fourierIntegrand z u y ∂ν := by
      simp only [paperFourier, positiveShift, shiftJet, iteratedDeriv_zero,
        fourierIntegrand, integral_mul_const]
    _ = ∫ y : ℝ in Icc (-b) b, (∫ u : ℝ, fourierIntegrand z u y) ∂ν :=
      integral_integral_swap (fourierIntegrand_integrable ν hb hbpi z)
    _ = ∫ y : ℝ in Icc (-b) b, Complex.exp (-z * (y : ℂ)) * xiFunction z ∂ν := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro y hy
      exact paperFourier_theta_shifted z ((abs_le.mpr hy).trans_lt hbpi)
    _ = _ := by rw [integral_mul_const]; exact mul_comm _ _

theorem shiftJet_real_deriv (ν : Measure ℝ) [IsFiniteMeasure ν]
    {b : ℝ} (hbpi : b < Real.pi / 4) (j : ℕ) :
    deriv (fun u : ℝ => shiftJet ν b j (u : ℂ)) =
      fun u : ℝ => shiftJet ν b (j + 1) (u : ℂ) := by
  funext u
  exact ((shiftJet_hasDerivAt ν (real_mem_shiftStrip hbpi u) j).comp_ofReal).deriv

theorem shiftJet_regularSource (ν : Measure ℝ) [IsFiniteMeasure ν]
    {b : ℝ} (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) (j : ℕ) :
    RegularSource (fun u : ℝ => shiftJet ν b j (u : ℂ)) := by
  refine ⟨(shiftJet_real_contDiff ν hbpi j).of_le le_top,
    shiftJet_weighted_integrable ν hb hbpi j, ?_, ?_, shiftJet_exponential ν hb hbpi j⟩
  · intro R
    rw [shiftJet_real_deriv ν hbpi j]
    exact shiftJet_weighted_integrable ν hb hbpi (j + 1) R
  · intro R
    rw [shiftJet_real_deriv ν hbpi j, shiftJet_real_deriv ν hbpi (j + 1)]
    exact shiftJet_weighted_integrable ν hb hbpi (j + 1 + 1) R

theorem positiveShift_hardCutoff (ν : Measure ℝ) [IsFiniteMeasure ν]
    {b : ℝ} (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) {a : ℝ} (ha : 0 ≤ a) :
    fullWeilForm (windowCut a (fun u : ℝ => positiveShift ν b (u : ℂ))) =
      fullWeilForm (exteriorTail a (fun u : ℝ => positiveShift ν b (u : ℂ))) :=
  source_hardCutoff (shiftJet_regularSource ν hb hbpi 0) (positiveShift_fourier ν hb hbpi) ha

end ThetaTrial.Paper.ShiftMeasure
