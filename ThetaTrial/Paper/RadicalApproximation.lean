import ThetaTrial.Paper.Radical
import ThetaTrial.Paper.ThetaStripDecay
import ThetaTrial.Paper.FullForm
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Weighted bounds for the noncompact radical approximation

To pass from compactly supported tests to the theta density, we approximate
by compactly supported functions. The Fourier bounds for compactly supported
tests depend on the size of the support, so the bounds below use exponentially
weighted derivative integrals instead. The approximation is completed in
`RadicalCorrelation`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set Filter
open scoped Topology ContDiff

namespace ThetaTrial.Paper.RadicalApproximation

theorem real_mem_thetaStrip (u : ℝ) : (u : ℂ) ∈ thetaStrip := by
  simp only [thetaStrip, mem_ofPred_eq, Complex.ofReal_im, abs_zero]
  positivity

theorem analytic_iteratedTheta (j : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv j complexThetaDensity) thetaStrip := by
  induction j with
  | zero => simpa using complexThetaDensity_analyticOnNhd_strip
  | succ j ih => simpa only [iteratedDeriv_succ] using ih.deriv

/-- All real derivatives are the restrictions of the corresponding complex
derivatives of the theta series, including at the origin, where the
even extension is glued. -/
theorem theta_real_iteratedDeriv (j : ℕ) (u : ℝ) :
    iteratedDeriv j (fun x : ℝ => (thetaDensity x : ℂ)) u =
      iteratedDeriv j complexThetaDensity (u : ℂ) := by
  induction j generalizing u with
  | zero => simpa using (complexThetaDensity_ofReal u).symm
  | succ j ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ, funext ih]
    exact ((analytic_iteratedTheta j (u : ℂ) (real_mem_thetaStrip u)).differentiableAt.hasDerivAt.comp_ofReal).deriv

theorem thetaDensity_contDiff :
    ContDiff ℝ ⊤ (fun u : ℝ => (thetaDensity u : ℂ)) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  have h : ContDiffAt ℝ ⊤ complexThetaDensity (u : ℂ) :=
    (complexThetaDensity_analyticOnNhd_strip (u : ℂ)
      (real_mem_thetaStrip u)).contDiffAt.restrict_scalars ℝ
  have hc := h.comp u Complex.ofRealCLM.contDiff.contDiffAt
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, complexThetaDensity_ofReal] using hc

theorem doubleExpEnvelope_abs_integrable (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun u : ℝ => ThetaTrial.ThetaSeries.doubleExpEnvelope a c |u|) := by
  let g : ℝ → ℝ := fun u => ThetaTrial.ThetaSeries.doubleExpEnvelope a c |u|
  have hp : IntegrableOn g (Ioi 0) := by
    apply (ThetaTrial.ThetaSeries.doubleExpEnvelope_integrable a hc).congr_fun _ measurableSet_Ioi
    intro u hu
    change 0 < u at hu
    simp only [g, abs_of_pos hu]
  have hn : IntegrableOn g (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun x : ℝ => -x) :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp only [Function.comp_def, g, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hp
  simpa only [Iic_union_Ioi, integrableOn_univ, g] using hn.union hp

/-- The theta density has finite exponentially weighted L¹ norms for every
derivative. -/
theorem theta_iteratedDeriv_weighted_integrable (j : ℕ) (R : ℝ) :
    Integrable (fun u : ℝ => Real.exp (R * |u|) *
      ‖iteratedDeriv j (fun x : ℝ => (thetaDensity x : ℂ)) u‖) := by
  obtain ⟨c, hc, hder⟩ := complexThetaDensity_iteratedDeriv_closed_strip_decay
    (b := 0) le_rfl (by positivity)
  obtain ⟨C, hC, hb⟩ := hder j
  have hcont : Continuous (fun u : ℝ => iteratedDeriv j complexThetaDensity (u : ℂ)) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    exact (analytic_iteratedTheta j (u : ℂ) (real_mem_thetaStrip u)).continuousAt.comp
      Complex.continuous_ofReal.continuousAt
  have hmeas : AEStronglyMeasurable (fun u : ℝ => Real.exp (R * |u|) *
      ‖iteratedDeriv j (fun x : ℝ => (thetaDensity x : ℂ)) u‖) := by
    simp_rw [theta_real_iteratedDeriv]
    exact ((by fun_prop : Continuous (fun u : ℝ => Real.exp (R * |u|))).mul
      hcont.norm).aestronglyMeasurable
  apply ((doubleExpEnvelope_abs_integrable
    (R + (9 / 2 + 2 * (j : ℝ))) hc).const_mul C).mono' hmeas
  filter_upwards with u
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)),
    theta_real_iteratedDeriv]
  have hb' := hb (u : ℂ) (by simp)
  simp only [Complex.ofReal_re] at hb'
  calc
    _ ≤ Real.exp (R * |u|) *
        (C * Real.exp ((9 / 2 + 2 * (j : ℝ)) * |u|) *
          Real.exp (-c * Real.exp (2 * |u|))) :=
      mul_le_mul_of_nonneg_left hb' (Real.exp_pos _).le
    _ = _ := by
      have he : Real.exp ((R + (9 / 2 + 2 * (j : ℝ))) * |u|) =
          Real.exp (R * |u|) * Real.exp ((9 / 2 + 2 * (j : ℝ)) * |u|) := by
        rw [add_mul, Real.exp_add]
      unfold ThetaTrial.ThetaSeries.doubleExpEnvelope
      rw [he]
      ring

theorem shiftedTheta_iteratedDeriv_continuous (j : ℕ) {y : ℝ}
    (hy : |y| < Real.pi / 4) :
    Continuous (fun u : ℝ =>
      iteratedDeriv j complexThetaDensity ((u : ℂ) + I * (y : ℂ))) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  apply (analytic_iteratedTheta j _ ?_).continuousAt.comp (by fun_prop)
  simpa [thetaStrip, Complex.mul_im] using hy

/-- A common integrable whole-line majorant for a fixed derivative order on
an entire closed theta strip, with any exponential real-axis weight. -/
theorem shiftedTheta_weighted_majorant (j : ℕ) (R : ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) :
    ∃ g : ℝ → ℝ, Integrable g ∧ ∀ u y : ℝ, |y| ≤ b →
      Real.exp (R * |u|) *
        ‖iteratedDeriv j complexThetaDensity ((u : ℂ) + I * (y : ℂ))‖ ≤ g u := by
  obtain ⟨c, hc, hder⟩ := complexThetaDensity_iteratedDeriv_closed_strip_decay hb hbpi
  obtain ⟨C, hC, hbound⟩ := hder j
  refine ⟨fun u => C * ThetaTrial.ThetaSeries.doubleExpEnvelope
    (R + (9 / 2 + 2 * (j : ℝ))) c |u|,
    (doubleExpEnvelope_abs_integrable _ hc).const_mul C, ?_⟩
  intro u y hy
  have h := hbound ((u : ℂ) + I * (y : ℂ)) (by simpa [Complex.mul_im] using hy)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] at h
  calc
    _ ≤ Real.exp (R * |u|) *
        (C * Real.exp ((9 / 2 + 2 * (j : ℝ)) * |u|) *
          Real.exp (-c * Real.exp (2 * |u|))) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := by
      dsimp only
      have he : Real.exp ((R + (9 / 2 + 2 * (j : ℝ))) * |u|) =
          Real.exp (R * |u|) * Real.exp ((9 / 2 + 2 * (j : ℝ)) * |u|) := by
        rw [add_mul, Real.exp_add]
      unfold ThetaTrial.ThetaSeries.doubleExpEnvelope
      rw [he]
      ring

theorem shiftedTheta_iteratedDeriv_weighted_integrable (j : ℕ) (R : ℝ) {y : ℝ}
    (hy : |y| < Real.pi / 4) :
    Integrable (fun u : ℝ => Real.exp (R * |u|) *
      ‖iteratedDeriv j complexThetaDensity ((u : ℂ) + I * (y : ℂ))‖) := by
  obtain ⟨g, hg, hbound⟩ := shiftedTheta_weighted_majorant j R (abs_nonneg y) hy
  apply hg.mono' (((by fun_prop : Continuous (fun u : ℝ => Real.exp (R * |u|))).mul
    (shiftedTheta_iteratedDeriv_continuous j hy).norm).aestronglyMeasurable)
  filter_upwards with u
  change ‖Real.exp (R * |u|) *
    ‖iteratedDeriv j complexThetaDensity ((u : ℂ) + I * (y : ℂ))‖‖ ≤ g u
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
  exact hbound u y le_rfl

/-- Exponentially weighted ordinary L¹ norm. -/
def weightedL1 (R : ℝ) (f : ℝ → ℂ) : ℝ :=
  ∫ u : ℝ, Real.exp (R * |u|) * ‖f u‖

theorem norm_exp_I_mul_le_weight (z : ℂ) (u R : ℝ) (hz : |z.im| ≤ R) :
    ‖Complex.exp (I * z * (u : ℂ))‖ ≤ Real.exp (R * |u|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have h : -(z.im * u) ≤ |z.im| * |u| := by
    simpa only [abs_mul] using neg_le_abs (z.im * u)
  have h' := mul_le_mul_of_nonneg_right hz (abs_nonneg u)
  simpa only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, one_mul, sub_zero, zero_sub, neg_mul] using h.trans h'

theorem norm_paperFT_le_weightedL1 {f : ℝ → ℂ} {R : ℝ}
    (hfi : Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖f u‖))
    {z : ℂ} (hz : |z.im| ≤ R) :
    ‖Zeta23.paperFT f z‖ ≤ weightedL1 R f := by
  unfold Zeta23.paperFT weightedL1
  apply norm_integral_le_of_norm_le hfi
  filter_upwards with u
  rw [norm_mul]
  calc
    _ ≤ ‖f u‖ * Real.exp (R * |u|) :=
      mul_le_mul_of_nonneg_left (norm_exp_I_mul_le_weight z u R hz) (norm_nonneg _)
    _ = _ := mul_comm _ _

theorem weightedL1_integrable_of_compact {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (R : ℝ) :
    Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖f u‖) := by
  have hc : Continuous (fun u : ℝ => Real.exp (R * |u|) * ‖f u‖) := by
    fun_prop
  exact hc.integrable_of_hasCompactSupport hfc.norm.mul_left

/-- Two integrations by parts, keeping the exponential weight. -/
theorem norm_paperFT_mul_sq_le_weightedL1 {f : ℝ → ℂ} {R : ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {z : ℂ} (hz : |z.im| ≤ R) :
    ‖Zeta23.paperFT f z‖ * ‖z‖ ^ 2 ≤ weightedL1 R (deriv (deriv f)) := by
  have hi := weightedL1_integrable_of_compact
    (hf.deriv'.continuous_deriv le_rfl) hfc.deriv.deriv R
  have h := norm_paperFT_le_weightedL1 hi hz
  rw [Zeta23.paperFT_deriv_deriv hf hfc, norm_mul, norm_neg, norm_pow, mul_comm] at h
  exact h

/-- Uniform inverse-quadratic strip decay from weighted Sobolev norms. This
constant is independent of support radius and also covers frequency zero. -/
theorem norm_paperFT_le_weightedSobolev {f : ℝ → ℂ} {R : ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {z : ℂ} (hz : |z.im| ≤ R) :
    ‖Zeta23.paperFT f z‖ ≤
      (weightedL1 R f + weightedL1 R (deriv (deriv f))) / (1 + ‖z‖ ^ 2) := by
  have h0 := norm_paperFT_le_weightedL1
    (weightedL1_integrable_of_compact hf.continuous hfc R) hz
  have h2 := norm_paperFT_mul_sq_le_weightedL1 hf hfc hz
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- The inverse-square majorant over the zeta zeros, with multiplicity. -/
theorem xiZero_inverse_square_summable :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zetaZeroConfig.mult ρ : ℝ) /
        (1 + ‖Zeta23.gammaOf ρ‖ ^ 2)) := by
  obtain ⟨A, hA, hloc⟩ := Zeta23.RvM.zeta_local_zero_count
  simpa only [Complex.normSq_eq_norm_sq] using
    Zeta23.WeilEF.zero_sum_inv_sq_gen Zeta23.zetaZeroConfig hA
      (fun t => by simpa only [Zeta23.zetaZeroConfig_N] using hloc t)

theorem xiZero_uniform_majorant {ks : ℕ → ℝ → ℂ} {C : ℝ}
    (hs : ∀ j, ContDiff ℝ 2 (ks j)) (hc : ∀ j, HasCompactSupport (ks j))
    (hC : ∀ j, weightedL1 (1 / 2) (ks j) +
      weightedL1 (1 / 2) (deriv (deriv (ks j))) ≤ C) :
    ∃ b : Zeta23.zetaZeroConfig.carrier → ℝ, Summable b ∧
      ∀ j ρ, ‖Radical.zeroTerm (ks j) ρ‖ ≤ b ρ := by
  refine ⟨fun ρ => C * ((Zeta23.zetaZeroConfig.mult ρ : ℝ) /
    (1 + ‖Zeta23.gammaOf ρ‖ ^ 2)), xiZero_inverse_square_summable.mul_left C, ?_⟩
  intro j ρ
  have hz := Zeta23.WeilEF.abs_gammaOf_im_le
    (Zeta23.zetaZeroConfig.strip ρ ρ.property)
  have h := (norm_paperFT_le_weightedSobolev (hs j) (hc j) hz).trans
    (div_le_div_of_nonneg_right (hC j) (by positivity))
  unfold Radical.zeroTerm
  rw [norm_mul, Complex.norm_natCast]
  calc
    _ ≤ (Zeta23.zetaZeroConfig.mult ρ : ℝ) *
        (C / (1 + ‖Zeta23.gammaOf ρ‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
    _ = _ := by ring

/-- A fixed smooth bump, rescaled below to exhaust the line. -/
def cutoffBase (u : ℝ) : ℂ := ((default : ContDiffBump (0 : ℝ)) u : ℂ)

theorem cutoffBase_contDiff : ContDiff ℝ ∞ cutoffBase := by
  exact Complex.ofRealCLM.contDiff.comp (default : ContDiffBump (0 : ℝ)).contDiff

theorem cutoffBase_compact : HasCompactSupport cutoffBase := by
  exact (default : ContDiffBump (0 : ℝ)).hasCompactSupport.comp_left Complex.ofReal_zero

theorem cutoffBase_norm_le (u : ℝ) : ‖cutoffBase u‖ ≤ 1 := by
  rw [cutoffBase, Complex.norm_real, Real.norm_of_nonneg
    (default : ContDiffBump (0 : ℝ)).nonneg]
  exact (default : ContDiffBump (0 : ℝ)).le_one

def cutoffScale (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹
def cutoff (n : ℕ) (u : ℝ) : ℂ := cutoffBase (cutoffScale n * u)

theorem cutoffScale_pos (n : ℕ) : 0 < cutoffScale n := by unfold cutoffScale; positivity

theorem cutoffScale_le_one (n : ℕ) : cutoffScale n ≤ 1 := by
  unfold cutoffScale
  exact inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])

theorem cutoff_contDiff (n : ℕ) : ContDiff ℝ ∞ (cutoff n) := by
  exact cutoffBase_contDiff.comp (by fun_prop)

theorem cutoff_compact (n : ℕ) : HasCompactSupport (cutoff n) := by
  change HasCompactSupport (fun u => cutoffBase (cutoffScale n * u))
  simpa only [smul_eq_mul] using
    cutoffBase_compact.comp_smul (ne_of_gt (cutoffScale_pos n))

theorem cutoff_norm_le (n : ℕ) (u : ℝ) : ‖cutoff n u‖ ≤ 1 := cutoffBase_norm_le _

theorem cutoff_eventually_eq_one (u : ℝ) : ∀ᶠ n : ℕ in atTop, cutoff n u = 1 := by
  refine eventually_atTop.mpr ⟨⌈|u|⌉₊, fun n hn => ?_⟩
  have hun : |u| ≤ (n : ℝ) :=
    (Nat.le_ceil |u|).trans (Nat.cast_le.mpr hn)
  have harg : ‖cutoffScale n * u‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (cutoffScale_pos n)]
    calc
      _ ≤ cutoffScale n * ((n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (cutoffScale_pos n).le
      _ = 1 := by unfold cutoffScale; rw [inv_mul_cancel₀ (by positivity)]
  have hb : (default : ContDiffBump (0 : ℝ)) (cutoffScale n * u) = 1 := by
    apply ContDiffBump.one_of_mem_closedBall
    change dist (cutoffScale n * u) 0 ≤ 1
    simpa only [Metric.mem_closedBall, dist_zero_right] using harg
  simp only [cutoff, cutoffBase, hb, Complex.ofReal_one]

theorem cutoff_tendsto (u : ℝ) : Tendsto (fun n : ℕ => cutoff n u) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [cutoff_eventually_eq_one u] with n hn
  exact hn.symm

def compactApprox (n : ℕ) (f : ℝ → ℂ) (u : ℝ) : ℂ := cutoff n u * f u

theorem compactApprox_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (n : ℕ) :
    ContDiff ℝ 2 (compactApprox n f) :=
  ((cutoff_contDiff n).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))).mul hf

theorem compactApprox_compact (f : ℝ → ℂ) (n : ℕ) :
    HasCompactSupport (compactApprox n f) := (cutoff_compact n).mul_right

theorem compactApprox_paperFT_tendsto {f : ℝ → ℂ} (hf : Continuous f)
    (hfi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖f u‖)) (z : ℂ) :
    Tendsto (fun n : ℕ => Zeta23.paperFT (compactApprox n f) z) atTop
      (𝓝 (Zeta23.paperFT f z)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun u : ℝ => Real.exp (|z.im| * |u|) * ‖f u‖)
  · intro n
    exact (((cutoff_contDiff n).continuous.mul hf).mul (by fun_prop)).aestronglyMeasurable
  · exact hfi |z.im|
  · intro n
    filter_upwards with u
    simp only [compactApprox, norm_mul]
    have hc := cutoff_norm_le n u
    have he := norm_exp_I_mul_le_weight z u |z.im| le_rfl
    calc
      _ ≤ 1 * ‖f u‖ * ‖Complex.exp (I * z * (u : ℂ))‖ := by gcongr
      _ ≤ 1 * ‖f u‖ * Real.exp (|z.im| * |u|) := by gcongr
      _ = _ := by ring
  · filter_upwards with u
    simpa only [compactApprox, one_mul] using
      ((cutoff_tendsto u).mul_const (f u)).mul_const (Complex.exp (I * z * (u : ℂ)))

/-- A concrete approximation of the full theta density, at every
complex frequency, with smooth compact approximants. -/
theorem theta_compactApprox_paperFT_tendsto (z : ℂ) :
    Tendsto (fun n : ℕ => Zeta23.paperFT
      (compactApprox n (fun u : ℝ => (thetaDensity u : ℂ))) z) atTop
      (𝓝 (Zeta23.paperFT (fun u : ℝ => (thetaDensity u : ℂ)) z)) := by
  apply compactApprox_paperFT_tendsto thetaDensity_contDiff.continuous
  intro R
  simpa only [iteratedDeriv_zero] using theta_iteratedDeriv_weighted_integrable 0 R

theorem cutoff_deriv (n : ℕ) (u : ℝ) :
    deriv (cutoff n) u = (cutoffScale n : ℂ) * deriv cutoffBase (cutoffScale n * u) := by
  have hb := (cutoffBase_contDiff.differentiable (by simp) (cutoffScale n * u)).hasDerivAt
  have hi : HasDerivAt (fun x : ℝ => cutoffScale n * x) (cutoffScale n) u := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id u).const_mul (cutoffScale n)
  change deriv (fun x => cutoffBase (cutoffScale n * x)) u = _
  simpa only [Function.comp_def, Complex.real_smul] using (hb.scomp u hi).deriv

theorem cutoff_second_deriv (n : ℕ) (u : ℝ) :
    deriv (deriv (cutoff n)) u =
      (cutoffScale n : ℂ) ^ 2 * deriv (deriv cutoffBase) (cutoffScale n * u) := by
  have hb2 : ContDiff ℝ 2 cutoffBase :=
    cutoffBase_contDiff.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hb := (hb2.deriv'.differentiable_one (cutoffScale n * u)).hasDerivAt
  have hi : HasDerivAt (fun x : ℝ => cutoffScale n * x) (cutoffScale n) u := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id u).const_mul (cutoffScale n)
  have h := ((hb.scomp u hi).const_mul (cutoffScale n : ℂ)).deriv
  rw [show deriv (cutoff n) = fun x => (cutoffScale n : ℂ) *
    deriv cutoffBase (cutoffScale n * x) from funext (cutoff_deriv n)]
  convert h using 1 <;> simp only [Function.comp_def, Complex.real_smul] <;> ring

theorem cutoff_derivatives_uniformly_bounded :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      (∀ n u, ‖deriv (cutoff n) u‖ ≤ C₁) ∧
      (∀ n u, ‖deriv (deriv (cutoff n)) u‖ ≤ C₂) := by
  have hb2 : ContDiff ℝ 2 cutoffBase :=
    cutoffBase_contDiff.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  obtain ⟨C₁, hC₁⟩ := (hb2.continuous_deriv (by norm_num)).bounded_above_of_compact_support
    cutoffBase_compact.deriv
  obtain ⟨C₂, hC₂⟩ := (hb2.deriv'.continuous_deriv le_rfl).bounded_above_of_compact_support
    cutoffBase_compact.deriv.deriv
  have hC₁0 := (norm_nonneg (deriv cutoffBase 0)).trans (hC₁ 0)
  have hC₂0 := (norm_nonneg (deriv (deriv cutoffBase) 0)).trans (hC₂ 0)
  refine ⟨C₁, C₂, hC₁0, hC₂0, ?_, ?_⟩
  · intro n u
    rw [cutoff_deriv, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (cutoffScale_pos n).le]
    calc
      _ ≤ 1 * C₁ := mul_le_mul (cutoffScale_le_one n) (hC₁ _)
        (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  · intro n u
    rw [cutoff_second_deriv, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (cutoffScale_pos n).le]
    have hs : (cutoffScale n) ^ 2 ≤ 1 := by
      nlinarith [cutoffScale_pos n, cutoffScale_le_one n]
    calc
      _ ≤ 1 * C₂ := mul_le_mul hs (hC₂ _) (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _

theorem second_deriv_product {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (u : ℝ) :
    deriv (deriv (fun x => f x * g x)) u =
      deriv (deriv f) u * g u + 2 * deriv f u * deriv g u +
        f u * deriv (deriv g) u := by
  have hfd := hf.differentiable (by norm_num)
  have hgd := hg.differentiable (by norm_num)
  have hfd' := hf.deriv'.differentiable_one
  have hgd' := hg.deriv'.differentiable_one
  have he : deriv (fun x => f x * g x) =
      fun x => deriv f x * g x + f x * deriv g x := by
    ext x
    exact deriv_mul (hfd x) (hgd x)
  rw [he]
  change deriv (deriv f * g + f * deriv g) u = _
  rw [deriv_add ((hfd' u).mul (hgd u)) ((hfd u).mul (hgd' u)),
    deriv_mul (hfd' u) (hgd u), deriv_mul (hfd u) (hgd' u)]
  ring

theorem compactApprox_second_deriv_norm_le {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    {C₁ C₂ : ℝ} (hC₁ : ∀ n u, ‖deriv (cutoff n) u‖ ≤ C₁)
    (hC₂ : ∀ n u, ‖deriv (deriv (cutoff n)) u‖ ≤ C₂) (n : ℕ) (u : ℝ) :
    ‖deriv (deriv (compactApprox n f)) u‖ ≤
      C₂ * ‖f u‖ + 2 * C₁ * ‖deriv f u‖ + ‖deriv (deriv f) u‖ := by
  change ‖deriv (deriv (fun x => cutoff n x * f x)) u‖ ≤ _
  rw [second_deriv_product
    ((cutoff_contDiff n).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) hf]
  calc
    _ ≤ ‖deriv (deriv (cutoff n)) u * f u‖ +
        ‖2 * deriv (cutoff n) u * deriv f u‖ +
        ‖cutoff n u * deriv (deriv f) u‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖deriv (deriv (cutoff n)) u‖ * ‖f u‖ +
        2 * ‖deriv (cutoff n) u‖ * ‖deriv f u‖ +
        ‖cutoff n u‖ * ‖deriv (deriv f) u‖ := by simp only [norm_mul, Complex.norm_ofNat]
    _ ≤ C₂ * ‖f u‖ + 2 * C₁ * ‖deriv f u‖ +
        1 * ‖deriv (deriv f) u‖ := by
      gcongr
      · exact hC₂ n u
      · exact hC₁ n u
      · exact cutoff_norm_le n u
    _ = _ := by ring

theorem compactApprox_weightedL1_le {f : ℝ → ℂ} {R : ℝ}
    (hf : ContDiff ℝ 2 f)
    (hfi : Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖f u‖)) (n : ℕ) :
    weightedL1 R (compactApprox n f) ≤ weightedL1 R f := by
  apply integral_mono
    (weightedL1_integrable_of_compact (compactApprox_contDiff hf n).continuous
      (compactApprox_compact f n) R) hfi
  intro u
  change Real.exp (R * |u|) * ‖cutoff n u * f u‖ ≤
    Real.exp (R * |u|) * ‖f u‖
  rw [norm_mul]
  have h := mul_le_mul_of_nonneg_right (cutoff_norm_le n u) (norm_nonneg (f u))
  exact mul_le_mul_of_nonneg_left (by simpa only [one_mul] using h) (Real.exp_pos _).le

theorem compactApprox_second_weightedL1_le {f : ℝ → ℂ} {R C₁ C₂ : ℝ}
    (hf : ContDiff ℝ 2 f)
    (h0 : Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖f u‖))
    (h1 : Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖deriv f u‖))
    (h2 : Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖deriv (deriv f) u‖))
    (hC₁ : ∀ n u, ‖deriv (cutoff n) u‖ ≤ C₁)
    (hC₂ : ∀ n u, ‖deriv (deriv (cutoff n)) u‖ ≤ C₂) (n : ℕ) :
    weightedL1 R (deriv (deriv (compactApprox n f))) ≤
      C₂ * weightedL1 R f + 2 * C₁ * weightedL1 R (deriv f) +
        weightedL1 R (deriv (deriv f)) := by
  have ha := compactApprox_contDiff hf n
  have hi := weightedL1_integrable_of_compact (ha.deriv'.continuous_deriv le_rfl)
    (compactApprox_compact f n).deriv.deriv R
  have h01 : Integrable (fun u : ℝ => C₂ * (Real.exp (R * |u|) * ‖f u‖) +
      (2 * C₁) * (Real.exp (R * |u|) * ‖deriv f u‖)) :=
    (h0.const_mul C₂).add (h1.const_mul (2 * C₁))
  have hu : Integrable (fun u : ℝ => C₂ * (Real.exp (R * |u|) * ‖f u‖) +
      (2 * C₁) * (Real.exp (R * |u|) * ‖deriv f u‖) +
      Real.exp (R * |u|) * ‖deriv (deriv f) u‖) := h01.add h2
  calc
    _ ≤ ∫ u : ℝ, C₂ * (Real.exp (R * |u|) * ‖f u‖) +
        (2 * C₁) * (Real.exp (R * |u|) * ‖deriv f u‖) +
        Real.exp (R * |u|) * ‖deriv (deriv f) u‖ := by
      apply integral_mono hi hu
      intro u
      dsimp only
      have h := mul_le_mul_of_nonneg_left
        (compactApprox_second_deriv_norm_le hf hC₁ hC₂ n u) (Real.exp_pos (R * |u|)).le
      convert h using 1 <;> ring
    _ = _ := by
      rw [integral_add h01 h2,
        integral_add (h0.const_mul C₂) (h1.const_mul (2 * C₁)),
        integral_const_mul, integral_const_mul]
      rfl

theorem compactApprox_uniform_weightedSobolev {f : ℝ → ℂ} {R : ℝ}
    (hf : ContDiff ℝ 2 f)
    (h0 : Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖f u‖))
    (h1 : Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖deriv f u‖))
    (h2 : Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖deriv (deriv f) u‖)) :
    ∃ C : ℝ, ∀ n, weightedL1 R (compactApprox n f) +
      weightedL1 R (deriv (deriv (compactApprox n f))) ≤ C := by
  obtain ⟨C₁, C₂, _, _, hb1, hb2⟩ := cutoff_derivatives_uniformly_bounded
  refine ⟨weightedL1 R f + (C₂ * weightedL1 R f +
    2 * C₁ * weightedL1 R (deriv f) + weightedL1 R (deriv (deriv f))), ?_⟩
  intro n
  exact add_le_add (compactApprox_weightedL1_le hf h0 n)
    (compactApprox_second_weightedL1_le hf h0 h1 h2 hb1 hb2 n)

/-- Uniform Sobolev control of the expanding theta approximants. -/
theorem theta_compactApprox_uniform_weightedSobolev (R : ℝ) :
    ∃ C : ℝ, ∀ n,
      weightedL1 R (compactApprox n (fun u : ℝ => (thetaDensity u : ℂ))) +
      weightedL1 R (deriv (deriv (compactApprox n (fun u : ℝ => (thetaDensity u : ℂ))))) ≤ C := by
  apply compactApprox_uniform_weightedSobolev (thetaDensity_contDiff.of_le le_top)
  · simpa only [iteratedDeriv_zero] using theta_iteratedDeriv_weighted_integrable 0 R
  · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      theta_iteratedDeriv_weighted_integrable 1 R
  · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      theta_iteratedDeriv_weighted_integrable 2 R

theorem doubleExpEnvelope_bounded (a : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ B : ℝ, 0 < B ∧ ∀ u : ℝ, 0 ≤ u → ThetaTrial.ThetaSeries.doubleExpEnvelope a c u ≤ B := by
  have hcont : Continuous (ThetaTrial.ThetaSeries.doubleExpEnvelope a c) := by
    unfold ThetaTrial.ThetaSeries.doubleExpEnvelope
    fun_prop
  have he : ∀ᶠ u : ℝ in atTop, ThetaTrial.ThetaSeries.doubleExpEnvelope a c u < 1 :=
    (ThetaTrial.ThetaSeries.doubleExpEnvelope_tendsto a hc).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨r, hr⟩ := eventually_atTop.mp he
  obtain ⟨B, hB⟩ := ((isCompact_Icc : IsCompact (Icc (0 : ℝ) (max r 0))).image hcont).bddAbove
  refine ⟨max B 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro u hu
  by_cases hur : u ≤ max r 0
  · exact (hB (mem_image_of_mem _ ⟨hu, hur⟩)).trans (le_max_left _ _)
  · exact (hr u (by linarith [le_max_left r 0])).le.trans (le_max_right _ _)

/-- A pointwise exponential envelope for the theta density. -/
theorem theta_exponential_bound (R : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ u : ℝ,
      ‖(thetaDensity u : ℂ)‖ ≤ M * Real.exp (-(R * |u|)) := by
  obtain ⟨c, hc, hder⟩ := complexThetaDensity_iteratedDeriv_closed_strip_decay
    (b := 0) le_rfl (by positivity)
  obtain ⟨C, hC, hb⟩ := hder 0
  obtain ⟨B, hB, henv⟩ := doubleExpEnvelope_bounded (R + 9 / 2) hc
  refine ⟨C * B, mul_pos hC hB, ?_⟩
  intro u
  have h := hb (u : ℂ) (by simp)
  simp only [iteratedDeriv_zero, complexThetaDensity_ofReal, Complex.ofReal_re,
    Nat.cast_zero, mul_zero, add_zero] at h
  have hw : Real.exp (R * |u|) * ‖(thetaDensity u : ℂ)‖ ≤ C * B := by
    calc
      _ ≤ Real.exp (R * |u|) *
          (C * Real.exp (9 / 2 * |u|) * Real.exp (-c * Real.exp (2 * |u|))) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = C * ThetaTrial.ThetaSeries.doubleExpEnvelope (R + 9 / 2) c |u| := by
        unfold ThetaTrial.ThetaSeries.doubleExpEnvelope
        rw [add_mul, Real.exp_add]
        ring
      _ ≤ C * B := mul_le_mul_of_nonneg_left (henv |u| (abs_nonneg u)) hC.le
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
  simpa only [mul_comm] using hw

def primeEnvelope (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * Real.exp (-|Real.log n|)

theorem primeEnvelope_summable : Summable primeEnvelope := by
  apply (summable_subtype_and_compl (s := {n : ℕ | 2 ≤ n})).mp
  constructor
  · have hs := ThetaTrial.PrimeContinuity.primeCoeff_summable (a := 1) (by norm_num)
    change Summable (fun n : {n : ℕ // 2 ≤ n} =>
      (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * Real.exp (-1 * Real.log n)) at hs
    change Summable (fun n : {n : ℕ // 2 ≤ n} => primeEnvelope (n : ℕ))
    apply hs.congr
    intro n
    simp only [primeEnvelope, abs_of_nonneg (Real.log_natCast_nonneg _), neg_mul, one_mul]
  · have hz : ∀ n : ↥({n : ℕ | 2 ≤ n}ᶜ), primeEnvelope n = 0 := by
      intro n
      have hn : ¬ 2 ≤ (n : ℕ) := n.property
      have he : (n : ℕ) = 0 ∨ (n : ℕ) = 1 := by omega
      rcases he with hn0 | hn1
      · simp [primeEnvelope, hn0]
      · simp [primeEnvelope, hn1]
    simp only [hz, summable_zero]

theorem prime_uniform_majorant {ks : ℕ → ℝ → ℂ} {M : ℝ}
    (hM : ∀ j u, ‖ks j u‖ ≤ M * Real.exp (-|u|)) :
    ∃ b : ℕ → ℝ, Summable b ∧ ∀ j n, ‖Radical.primeTerm (ks j) n‖ ≤ b n := by
  refine ⟨fun n => 2 * M * primeEnvelope n, primeEnvelope_summable.mul_left (2 * M), ?_⟩
  intro j n
  have hc : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  unfold Radical.primeTerm
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
  calc
    _ ≤ (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        (‖ks j (Real.log n)‖ + ‖ks j (-Real.log n)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) hc
    _ ≤ (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        (M * Real.exp (-|Real.log n|) + M * Real.exp (-|-Real.log n|)) :=
      mul_le_mul_of_nonneg_left (add_le_add (hM j _) (hM j _)) hc
    _ = _ := by simp only [abs_neg, primeEnvelope]; ring

theorem theta_compactApprox_prime_majorant :
    ∃ b : ℕ → ℝ, Summable b ∧ ∀ j n,
      ‖Radical.primeTerm (compactApprox j (fun u : ℝ => (thetaDensity u : ℂ))) n‖ ≤ b n := by
  obtain ⟨M, _, hb⟩ := theta_exponential_bound 1
  apply prime_uniform_majorant (M := M)
  intro j u
  unfold compactApprox
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖(thetaDensity u : ℂ)‖ :=
      mul_le_mul_of_nonneg_right (cutoff_norm_le j u) (norm_nonneg _)
    _ ≤ M * Real.exp (-|u|) := by simpa only [one_mul] using hb u

theorem gamma_uniform_majorant {ks : ℕ → ℝ → ℂ} {C : ℝ}
    (hs : ∀ j, ContDiff ℝ 2 (ks j)) (hc : ∀ j, HasCompactSupport (ks j))
    (hC : ∀ j, weightedL1 0 (ks j) + weightedL1 0 (deriv (deriv (ks j))) ≤ C) :
    ∃ b : ℝ → ℝ, Integrable b ∧ ∀ j r, ‖Radical.gammaTerm (ks j) r‖ ≤ b r := by
  refine ⟨fun r => C * (|gammaWeight r| / (1 + r ^ 2)),
    gamma_cauchy_integrable.const_mul C, ?_⟩
  intro j r
  have h := (norm_paperFT_le_weightedSobolev (hs j) (hc j)
    (z := (r : ℂ)) (R := 0) (by simp)).trans
      (div_le_div_of_nonneg_right (hC j) (by positivity))
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  unfold Radical.gammaTerm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (C / (1 + r ^ 2)) * |Zeta23.EF.gammaBracket r| :=
      mul_le_mul_of_nonneg_right h (abs_nonneg _)
    _ = _ := by change _ = C * (|Zeta23.EF.gammaBracket r| / (1 + r ^ 2)); ring

theorem gammaTerm_compact_measurable {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    AEStronglyMeasurable (Radical.gammaTerm f) := by
  have hFT : Continuous (fun r : ℝ => Zeta23.paperFT f r) :=
    (Zeta23.WeilEF.differentiable_paperFT hf hfc).continuous.comp Complex.continuous_ofReal
  have hg : AEStronglyMeasurable gammaWeight := by
    have he : gammaWeight = ThetaTrial.GammaEnergy.gammaMultiplier := funext gammaWeight_eq_weilFormula
    rw [he]
    exact ThetaTrial.RationalFourier.gammaMultiplier_aestronglyMeasurable
  exact hFT.aestronglyMeasurable.mul
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hg)

/-- The explicit formula for exponentially weighted `C²` tests, under
regularity, integrability and pointwise bounds on the test. -/
theorem dominatedApproximation_of_weightedC2 {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f)
    (h0 : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖f u‖))
    (h1 : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖deriv f u‖))
    (h2 : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖deriv (deriv f) u‖))
    (hdecay : ∃ M : ℝ, ∀ u : ℝ, ‖f u‖ ≤ M * Real.exp (-|u|)) :
    Radical.DominatedWeilApproximation f (fun n => compactApprox n f) := by
  have hs : ∀ n, ContDiff ℝ 2 (compactApprox n f) := compactApprox_contDiff hf
  have hc : ∀ n, HasCompactSupport (compactApprox n f) := compactApprox_compact f
  have hlim : ∀ u, Tendsto (fun n => compactApprox n f u) atTop (𝓝 (f u)) := by
    intro u
    simpa only [compactApprox, one_mul] using (cutoff_tendsto u).mul_const (f u)
  have hFT := compactApprox_paperFT_tendsto hf.continuous h0
  obtain ⟨M, hM⟩ := hdecay
  have happ : ∀ n u, ‖compactApprox n f u‖ ≤ M * Real.exp (-|u|) := by
    intro n u
    unfold compactApprox
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (cutoff_norm_le n u) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hM u)
  obtain ⟨bp, hbp, hp⟩ := prime_uniform_majorant happ
  obtain ⟨Cg, hCg⟩ := compactApprox_uniform_weightedSobolev hf (h0 0) (h1 0) (h2 0)
  obtain ⟨bg, hbg, hg⟩ := gamma_uniform_majorant hs hc hCg
  obtain ⟨Cz, hCz⟩ := compactApprox_uniform_weightedSobolev hf
    (h0 (1 / 2)) (h1 (1 / 2)) (h2 (1 / 2))
  obtain ⟨bz, hbz, hz⟩ := xiZero_uniform_majorant hs hc hCz
  refine ⟨hs, hc, hFT _, hFT _, ?_,
    ⟨bp, hbp, Filter.Eventually.of_forall hp⟩, ?_, ?_,
    ⟨bg, hbg, fun j => Filter.Eventually.of_forall (hg j)⟩,
    ?_, ⟨bz, hbz, Filter.Eventually.of_forall hz⟩⟩
  · intro n
    exact tendsto_const_nhds.mul ((hlim (Real.log n)).add (hlim (-Real.log n)))
  · intro n
    exact gammaTerm_compact_measurable (hs n).continuous (hc n)
  · filter_upwards with r
    exact (hFT r).mul_const (Zeta23.EF.gammaBracket r : ℂ)
  · intro ρ
    exact tendsto_const_nhds.mul (hFT (Zeta23.gammaOf ρ))

theorem fullWeil_of_weightedC2 {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f)
    (h0 : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖f u‖))
    (h1 : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖deriv f u‖))
    (h2 : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖deriv (deriv f) u‖))
    (hdecay : ∃ M : ℝ, ∀ u : ℝ, ‖f u‖ ≤ M * Real.exp (-|u|)) :
    Summable (Radical.zeroTerm f) ∧ Radical.fullWeil f = ∑' ρ, Radical.zeroTerm f ρ :=
  Radical.fullWeil_of_dominated_approximation
    (dominatedApproximation_of_weightedC2 hf h0 h1 h2 hdecay)

/-- Fully constructed dominated explicit-formula data for one noncompact scalar test: the theta density. -/
theorem theta_dominatedApproximation :
    Radical.DominatedWeilApproximation (fun u : ℝ => (thetaDensity u : ℂ))
      (fun n => compactApprox n (fun u : ℝ => (thetaDensity u : ℂ))) := by
  let f : ℝ → ℂ := fun u => (thetaDensity u : ℂ)
  have hs : ∀ n, ContDiff ℝ 2 (compactApprox n f) :=
    fun n => compactApprox_contDiff (thetaDensity_contDiff.of_le le_top) n
  have hc : ∀ n, HasCompactSupport (compactApprox n f) := compactApprox_compact f
  have hlim : ∀ u, Tendsto (fun n => compactApprox n f u) atTop (𝓝 (f u)) := by
    intro u
    simpa only [compactApprox, one_mul] using (cutoff_tendsto u).mul_const (f u)
  obtain ⟨Cp, hCp, hp⟩ := theta_compactApprox_prime_majorant
  obtain ⟨Cg, hCg⟩ := theta_compactApprox_uniform_weightedSobolev 0
  obtain ⟨bg, hbg, hg⟩ := gamma_uniform_majorant hs hc hCg
  obtain ⟨Cz, hCz⟩ := theta_compactApprox_uniform_weightedSobolev (1 / 2)
  obtain ⟨bz, hbz, hz⟩ := xiZero_uniform_majorant hs hc hCz
  refine ⟨hs, hc, theta_compactApprox_paperFT_tendsto _,
    theta_compactApprox_paperFT_tendsto _, ?_,
    ⟨Cp, hCp, Filter.Eventually.of_forall hp⟩, ?_, ?_,
    ⟨bg, hbg, fun j => Filter.Eventually.of_forall (hg j)⟩,
    ?_, ⟨bz, hbz, Filter.Eventually.of_forall hz⟩⟩
  · intro n
    exact tendsto_const_nhds.mul ((hlim (Real.log n)).add (hlim (-Real.log n)))
  · intro n
    exact gammaTerm_compact_measurable (hs n).continuous (hc n)
  · filter_upwards with r
    exact (theta_compactApprox_paperFT_tendsto r).mul_const
      (Zeta23.EF.gammaBracket r : ℂ)
  · intro ρ
    exact tendsto_const_nhds.mul (theta_compactApprox_paperFT_tendsto (Zeta23.gammaOf ρ))

/-- The explicit formula for the theta test itself. -/
theorem theta_fullWeil_scalar_eq_zero :
    Radical.fullWeil (fun u : ℝ => (thetaDensity u : ℂ)) = 0 := by
  rw [(Radical.fullWeil_of_dominated_approximation theta_dominatedApproximation).2]
  have hzero : ∀ ρ, Radical.zeroTerm (fun u : ℝ => (thetaDensity u : ℂ)) ρ = 0 := by
    intro ρ
    have he : Zeta23.paperFT (fun u : ℝ => (thetaDensity u : ℂ)) (Zeta23.gammaOf ρ) =
        Radical.paperFourier (fun u : ℝ => (thetaDensity u : ℂ))
          (ThetaTrial.zetaZeroEquivXiZeros ρ) := by
      change Zeta23.paperFT _ (Zeta23.gammaOf ρ) =
        Zeta23.paperFT _ (-ThetaTrial.FourierNormalization.spectralCoord (ρ : ℂ))
      rw [ThetaTrial.FourierNormalization.spectralCoord_eq_neg_gammaOf, neg_neg]
    unfold Radical.zeroTerm
    rw [he, Radical.theta_fourier, (ThetaTrial.zetaZeroEquivXiZeros ρ).property, mul_zero]
  simp only [hzero, tsum_zero]

end ThetaTrial.Paper.RadicalApproximation

#print axioms ThetaTrial.Paper.RadicalApproximation.norm_paperFT_le_weightedSobolev
#print axioms ThetaTrial.Paper.RadicalApproximation.theta_iteratedDeriv_weighted_integrable
#print axioms ThetaTrial.Paper.RadicalApproximation.dominatedApproximation_of_weightedC2
#print axioms ThetaTrial.Paper.RadicalApproximation.theta_fullWeil_scalar_eq_zero
