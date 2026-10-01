import ThetaTrial.Paper.RadicalApproximation
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Theta mixed correlations in the full explicit formula

The right factor may have hard-cutoff jumps. We regularize only the theta
factor and multiply the right factor by an exhausting smooth cutoff. The
resulting correlations are compact C² tests even when the right factor is
merely integrable. All spectral, prime, and gamma majorants are uniform.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set Filter
open scoped Topology ContDiff Convolution ComplexConjugate

namespace ThetaTrial.Paper.RadicalCorrelation
open RadicalApproximation

def theta : ℝ → ℂ := fun u => (thetaDensity u : ℂ)

theorem theta_weighted (R : ℝ) :
    Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖theta u‖) := by
  simpa only [theta, iteratedDeriv_zero] using theta_iteratedDeriv_weighted_integrable 0 R

theorem weighted_fourierIntegrable {f : ℝ → ℂ}
    (hm : AEStronglyMeasurable f)
    (hi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖f u‖))
    (z : ℂ) : Radical.FourierIntegrableAt f z := by
  apply (hi |z.im|).mono' (hm.mul (by fun_prop))
  filter_upwards with u
  change ‖f u * Complex.exp (-I * z * (u : ℂ))‖ ≤ _
  rw [norm_mul]
  have he := norm_exp_I_mul_le_weight (-z) u |z.im| (by simp)
  simp only [mul_neg, neg_mul] at he
  simpa only [neg_mul] using
    (mul_le_mul_of_nonneg_left he (norm_nonneg (f u))).trans_eq (mul_comm _ _)

theorem compactApprox_norm_le (n : ℕ) (f : ℝ → ℂ) (u : ℝ) :
    ‖compactApprox n f u‖ ≤ ‖f u‖ := by
  simpa only [compactApprox, norm_mul, one_mul] using
    mul_le_mul_of_nonneg_right (cutoff_norm_le n u) (norm_nonneg (f u))

theorem compactApprox_measurable {f : ℝ → ℂ}
    (hm : AEStronglyMeasurable f) (n : ℕ) :
    AEStronglyMeasurable (compactApprox n f) :=
  (cutoff_contDiff n).continuous.aestronglyMeasurable.mul hm

theorem compactApprox_weighted {f : ℝ → ℂ}
    (hm : AEStronglyMeasurable f) {R : ℝ}
    (hi : Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖f u‖)) (n : ℕ) :
    Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖compactApprox n f u‖) := by
  apply hi.mono' ((by fun_prop : Continuous (fun u : ℝ => Real.exp (R * |u|))).aestronglyMeasurable.mul
    (compactApprox_measurable hm n).norm)
  filter_upwards with u
  change ‖Real.exp (R * |u|) * ‖compactApprox n f u‖‖ ≤ _
  rw [Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (compactApprox_norm_le n f u) (Real.exp_pos _).le

theorem compactApprox_paperFT_tendsto_measurable {f : ℝ → ℂ}
    (hm : AEStronglyMeasurable f)
    (hi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖f u‖)) (z : ℂ) :
    Tendsto (fun n => Zeta23.paperFT (compactApprox n f) z) atTop
      (𝓝 (Zeta23.paperFT f z)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun u : ℝ => Real.exp (|z.im| * |u|) * ‖f u‖)
  · intro n
    exact (compactApprox_measurable hm n).mul (by fun_prop)
  · exact hi |z.im|
  · intro n
    filter_upwards with u
    rw [norm_mul]
    calc
      _ ≤ ‖f u‖ * Real.exp (|z.im| * |u|) :=
        mul_le_mul (compactApprox_norm_le n f u)
          (norm_exp_I_mul_le_weight z u |z.im| le_rfl) (norm_nonneg _) (norm_nonneg _)
      _ = _ := mul_comm _ _
  · filter_upwards with u
    simpa only [compactApprox, one_mul] using
      ((cutoff_tendsto u).mul_const (f u)).mul_const (Complex.exp (I * z * (u : ℂ)))

def approximant (h : ℝ → ℂ) (n : ℕ) : ℝ → ℂ :=
  Zeta23.EF.weilTest (compactApprox n theta) (compactApprox n h)

theorem approximant_compact (h : ℝ → ℂ) (n : ℕ) :
    HasCompactSupport (approximant h n) := by
  exact (compactApprox_compact theta n).convolution (ContinuousLinearMap.mul ℝ ℂ)
    (Zeta23.EF.hasCompactSupport_tilde (compactApprox_compact h n))

theorem approximant_contDiff {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h)
    (hi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖h u‖)) (n : ℕ) :
    ContDiff ℝ 2 (approximant h n) := by
  have hh : Integrable (compactApprox n h) := by
    have h0 := compactApprox_weighted hm (hi 0) n
    simpa only [zero_mul, Real.exp_zero, one_mul, integrable_norm_iff
      (compactApprox_measurable hm n)] using h0
  have ht : Integrable (Zeta23.EF.tilde (compactApprox n h)) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hh.comp_neg
  exact (compactApprox_compact theta n).contDiff_convolution_left
    (ContinuousLinearMap.mul ℝ ℂ)
    (compactApprox_contDiff (thetaDensity_contDiff.of_le le_top) n) ht.locallyIntegrable

theorem compactApprox_weightedL1_le_measurable {f : ℝ → ℂ}
    (hm : AEStronglyMeasurable f) {R : ℝ}
    (hi : Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖f u‖)) (n : ℕ) :
    weightedL1 R (compactApprox n f) ≤ weightedL1 R f := by
  apply integral_mono (compactApprox_weighted hm hi n) hi
  intro u
  exact mul_le_mul_of_nonneg_left (compactApprox_norm_le n f u) (Real.exp_pos _).le

theorem paperFT_weilTest {f h : ℝ → ℂ}
    (fm : AEStronglyMeasurable f) (hm : AEStronglyMeasurable h)
    (fi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖f u‖))
    (hi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖h u‖)) (z : ℂ) :
    Zeta23.paperFT (Zeta23.EF.weilTest f h) z =
      Zeta23.paperFT f z * conj (Zeta23.paperFT h (conj z)) := by
  have he := Radical.paperFourier_weilTest_of_integrable
    (weighted_fourierIntegrable fm fi (-z))
    (weighted_fourierIntegrable hm hi (conj (-z)))
  simpa only [Radical.paperFourier, map_neg, neg_neg] using he

theorem approximant_paperFT_tendsto {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h)
    (hi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖h u‖)) (z : ℂ) :
    Tendsto (fun n => Zeta23.paperFT (approximant h n) z) atTop
      (𝓝 (Zeta23.paperFT (Zeta23.EF.weilTest theta h) z)) := by
  have fm : AEStronglyMeasurable theta := thetaDensity_contDiff.continuous.aestronglyMeasurable
  rw [paperFT_weilTest fm hm theta_weighted hi z]
  have hn : ∀ n, Zeta23.paperFT (approximant h n) z =
      Zeta23.paperFT (compactApprox n theta) z *
        conj (Zeta23.paperFT (compactApprox n h) (conj z)) := by
    intro n
    exact paperFT_weilTest (compactApprox_measurable fm n) (compactApprox_measurable hm n)
      (fun R => compactApprox_weighted fm (theta_weighted R) n)
      (fun R => compactApprox_weighted hm (hi R) n) z
  simp only [hn]
  exact (compactApprox_paperFT_tendsto_measurable fm theta_weighted z).mul
    ((Complex.continuous_conj.tendsto _).comp
      (compactApprox_paperFT_tendsto_measurable hm hi (conj z)))

/-- Product decay uses two derivatives of the smooth left factor only, so the
right factor may have jumps. -/
theorem approximant_uniform_strip_bound {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h)
    (hi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖h u‖)) (R : ℝ) :
    ∃ C : ℝ, ∀ n (z : ℂ), |z.im| ≤ R →
      ‖Zeta23.paperFT (approximant h n) z‖ ≤ C / (1 + ‖z‖ ^ 2) := by
  obtain ⟨C, hC⟩ := theta_compactApprox_uniform_weightedSobolev R
  have fm : AEStronglyMeasurable theta := thetaDensity_contDiff.continuous.aestronglyMeasurable
  have hC0 : 0 ≤ C := by
    have hn : 0 ≤ weightedL1 R (compactApprox 0 theta) +
        weightedL1 R (deriv (deriv (compactApprox 0 theta))) :=
      add_nonneg (integral_nonneg (fun _ => by positivity))
        (integral_nonneg (fun _ => by positivity))
    exact hn.trans (hC 0)
  refine ⟨C * weightedL1 R h, ?_⟩
  intro n z hz
  rw [show Zeta23.paperFT (approximant h n) z =
      Zeta23.paperFT (compactApprox n theta) z *
        conj (Zeta23.paperFT (compactApprox n h) (conj z)) from
    paperFT_weilTest (compactApprox_measurable fm n) (compactApprox_measurable hm n)
      (fun R => compactApprox_weighted fm (theta_weighted R) n)
      (fun R => compactApprox_weighted hm (hi R) n) z, norm_mul, norm_conj]
  have hl := (norm_paperFT_le_weightedSobolev
    (compactApprox_contDiff (thetaDensity_contDiff.of_le le_top) n)
      (compactApprox_compact theta n) hz).trans
        (div_le_div_of_nonneg_right (hC n) (by positivity))
  have hr := (norm_paperFT_le_weightedL1 (compactApprox_weighted hm (hi R) n)
    (z := conj z) (by simpa only [Complex.conj_im, abs_neg] using hz)).trans
      (compactApprox_weightedL1_le_measurable hm (hi R) n)
  calc
    _ ≤ (C / (1 + ‖z‖ ^ 2)) * weightedL1 R h :=
      mul_le_mul hl hr (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem weighted_integrable {h : ℝ → ℂ} (hm : AEStronglyMeasurable h)
    (hi : Integrable (fun u : ℝ => Real.exp (0 * |u|) * ‖h u‖)) : Integrable h := by
  have hn : Integrable (fun u => ‖h u‖) := by simpa only [zero_mul, Real.exp_zero, one_mul] using hi
  exact (integrable_norm_iff hm).mp hn

theorem weilTest_eq_integral (f h : ℝ → ℂ) (x : ℝ) :
    Zeta23.EF.weilTest f h x = ∫ u : ℝ, f u * conj (h (u - x)) := by
  simp only [Zeta23.EF.weilTest, convolution_def, ContinuousLinearMap.mul_apply',
    Zeta23.EF.tilde, neg_sub]

theorem approximant_tendsto {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h)
    (hi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖h u‖)) (x : ℝ) :
    Tendsto (fun n => approximant h n x) atTop (𝓝 (Zeta23.EF.weilTest theta h x)) := by
  obtain ⟨M, hM, hb⟩ := theta_exponential_bound 0
  have htheta : ∀ u, ‖theta u‖ ≤ M := by
    intro u
    simpa only [theta, zero_mul, neg_zero, Real.exp_zero, mul_one] using hb u
  have hh := weighted_integrable hm (hi 0)
  simp only [approximant, weilTest_eq_integral]
  apply tendsto_integral_of_dominated_convergence (fun u : ℝ => M * ‖h (u - x)‖)
  · intro n
    have hn := weighted_integrable (compactApprox_measurable hm n)
      (compactApprox_weighted hm (hi 0) n)
    exact (compactApprox_contDiff (thetaDensity_contDiff.of_le le_top) n).continuous.aestronglyMeasurable.mul
      (Complex.continuous_conj.comp_aestronglyMeasurable (hn.comp_sub_right x).aestronglyMeasurable)
  · exact (hh.comp_sub_right x).norm.const_mul M
  · intro n
    filter_upwards with u
    rw [norm_mul, norm_conj]
    exact mul_le_mul ((compactApprox_norm_le n theta u).trans (htheta u))
      (compactApprox_norm_le n h (u - x)) (norm_nonneg _) hM.le
  · filter_upwards with u
    simpa only [compactApprox, one_mul, Function.comp_def] using
      ((cutoff_tendsto u).mul_const (theta u)).mul
      ((Complex.continuous_conj.tendsto _).comp
        ((cutoff_tendsto (u - x)).mul_const (h (u - x))))

theorem approximant_exponential_bound {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h)
    (hi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖h u‖)) :
    ∃ M : ℝ, ∀ n x, ‖approximant h n x‖ ≤ M * Real.exp (-|x|) := by
  obtain ⟨M, hM, hb⟩ := theta_exponential_bound 1
  refine ⟨M * weightedL1 1 h, ?_⟩
  intro n x
  have henv : ∀ u : ℝ,
      ‖compactApprox n theta u * conj (compactApprox n h (u - x))‖ ≤
        (M * Real.exp (-|x|)) * (Real.exp (1 * |u - x|) * ‖h (u - x)‖) := by
    intro u
    have he : Real.exp (-|u|) ≤ Real.exp (-|x|) * Real.exp |u - x| := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have ha : |x| ≤ |u| + |u - x| := by
        simpa only [sub_sub_cancel, abs_sub_comm] using (abs_sub u (u - x))
      linarith
    rw [norm_mul, norm_conj]
    calc
      _ ≤ (M * Real.exp (-|u|)) * ‖h (u - x)‖ :=
        mul_le_mul ((compactApprox_norm_le n theta u).trans
          (by simpa only [theta, one_mul] using hb u))
          (compactApprox_norm_le n h (u - x)) (norm_nonneg _) (by positivity)
      _ ≤ (M * (Real.exp (-|x|) * Real.exp |u - x|)) * ‖h (u - x)‖ := by gcongr
      _ = _ := by simp only [one_mul]; ring
  rw [approximant, weilTest_eq_integral]
  calc
    _ ≤ ∫ u : ℝ, (M * Real.exp (-|x|)) *
        (Real.exp (1 * |u - x|) * ‖h (u - x)‖) :=
      norm_integral_le_of_norm_le ((hi 1).comp_sub_right x |>.const_mul _) (Filter.Eventually.of_forall henv)
    _ = (M * Real.exp (-|x|)) * weightedL1 1 h := by
      rw [integral_const_mul]
      exact congrArg (fun t : ℝ => (M * Real.exp (-|x|)) * t)
        (integral_sub_right_eq_self (fun u : ℝ => Real.exp (1 * |u|) * ‖h u‖) x)
    _ = _ := by ring

theorem approximant_zero_majorant {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h)
    (hi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖h u‖)) :
    ∃ b : Zeta23.zetaZeroConfig.carrier → ℝ, Summable b ∧
      ∀ n ρ, ‖Radical.zeroTerm (approximant h n) ρ‖ ≤ b ρ := by
  obtain ⟨C, hC⟩ := approximant_uniform_strip_bound hm hi (1 / 2)
  refine ⟨fun ρ => C * ((Zeta23.zetaZeroConfig.mult ρ : ℝ) /
    (1 + ‖Zeta23.gammaOf ρ‖ ^ 2)), xiZero_inverse_square_summable.mul_left C, ?_⟩
  intro n ρ
  have hz := Zeta23.WeilEF.abs_gammaOf_im_le
    (Zeta23.zetaZeroConfig.strip ρ ρ.property)
  unfold Radical.zeroTerm
  rw [norm_mul, Complex.norm_natCast]
  calc
    _ ≤ (Zeta23.zetaZeroConfig.mult ρ : ℝ) *
        (C / (1 + ‖Zeta23.gammaOf ρ‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (hC n _ hz) (Nat.cast_nonneg _)
    _ = _ := by ring

theorem approximant_gamma_majorant {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h)
    (hi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖h u‖)) :
    ∃ b : ℝ → ℝ, Integrable b ∧
      ∀ n r, ‖Radical.gammaTerm (approximant h n) r‖ ≤ b r := by
  obtain ⟨C, hC⟩ := approximant_uniform_strip_bound hm hi 0
  refine ⟨fun r => C * (|gammaWeight r| / (1 + r ^ 2)),
    gamma_cauchy_integrable.const_mul C, ?_⟩
  intro n r
  have hb := hC n (r : ℂ) (by simp)
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hb
  unfold Radical.gammaTerm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (C / (1 + r ^ 2)) * |Zeta23.EF.gammaBracket r| :=
      mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    _ = _ := by change _ = C * (|Zeta23.EF.gammaBracket r| / (1 + r ^ 2)); ring

/-- The noncompact mixed theta test has a constructed compact
explicit-formula approximation. Its right factor may be a hard indicator. -/
theorem theta_correlation_dominatedApproximation {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h)
    (hi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖h u‖)) :
    Radical.DominatedWeilApproximation (Zeta23.EF.weilTest theta h) (approximant h) := by
  obtain ⟨M, hM⟩ := approximant_exponential_bound hm hi
  obtain ⟨bp, hbp, hp⟩ := prime_uniform_majorant hM
  obtain ⟨bg, hbg, hg⟩ := approximant_gamma_majorant hm hi
  obtain ⟨bz, hbz, hz⟩ := approximant_zero_majorant hm hi
  refine ⟨approximant_contDiff hm hi, approximant_compact h,
    approximant_paperFT_tendsto hm hi _, approximant_paperFT_tendsto hm hi _,
    ?_, ⟨bp, hbp, Filter.Eventually.of_forall hp⟩, ?_, ?_,
    ⟨bg, hbg, fun n => Filter.Eventually.of_forall (hg n)⟩,
    ?_, ⟨bz, hbz, Filter.Eventually.of_forall hz⟩⟩
  · intro n
    exact tendsto_const_nhds.mul ((approximant_tendsto hm hi (Real.log n)).add
      (approximant_tendsto hm hi (-Real.log n)))
  · intro n
    exact gammaTerm_compact_measurable (approximant_contDiff hm hi n).continuous
      (approximant_compact h n)
  · filter_upwards with r
    exact (approximant_paperFT_tendsto hm hi r).mul_const (Zeta23.EF.gammaBracket r : ℂ)
  · intro ρ
    exact tendsto_const_nhds.mul (approximant_paperFT_tendsto hm hi (Zeta23.gammaOf ρ))

/-- The theta density lies in the radical of the form (gamma term plus poles
minus primes) on exponentially integrable tests. The proof does not use the
Riemann hypothesis. -/
theorem theta_fullPairing_eq_zero {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h)
    (hi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖h u‖)) :
    Radical.fullPairing theta h = 0 := by
  apply Radical.fullPairing_radical_of_dominated_approximation (m := fun _ => 1)
    _ (fun z => Radical.theta_fourier_integrable z)
    (fun z => weighted_fourierIntegrable hm hi (conj (z : ℂ)))
    (theta_correlation_dominatedApproximation hm hi)
  intro z
  simpa only [mul_one] using Radical.theta_fourier z

theorem weighted_indicator {h : ℝ → ℂ} {s : Set ℝ} (hs : MeasurableSet s)
    {R : ℝ} (hi : Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖h u‖)) :
    Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖s.indicator h u‖) := by
  apply (hi.indicator hs).congr
  filter_upwards with u
  by_cases hu : u ∈ s <;> simp [hu]

theorem theta_window_pairing_eq_zero (a : ℝ) :
    Radical.fullPairing theta (Radical.window a theta) = 0 := by
  apply theta_fullPairing_eq_zero
  · exact thetaDensity_contDiff.continuous.aestronglyMeasurable.indicator measurableSet_Icc
  · intro R
    exact weighted_indicator measurableSet_Icc (theta_weighted R)

theorem theta_tail_pairing_eq_zero (a : ℝ) :
    Radical.fullPairing theta (Radical.tail a theta) = 0 := by
  apply theta_fullPairing_eq_zero
  · exact thetaDensity_contDiff.continuous.aestronglyMeasurable.indicator measurableSet_Icc.compl
  · intro R
    exact weighted_indicator measurableSet_Icc.compl (theta_weighted R)

theorem theta_fullQuadratic_eq_zero : Radical.fullQuadratic theta = 0 :=
  theta_fullPairing_eq_zero thetaDensity_contDiff.continuous.aestronglyMeasurable theta_weighted

theorem theta_fullWeilForm_eq_zero : fullWeilForm theta = 0 := by
  have h := theta_fullQuadratic_eq_zero
  rw [Radical.fullQuadratic_eq_paperForm (f := theta) Radical.theta_fourier_integrable] at h
  exact_mod_cast h

end ThetaTrial.Paper.RadicalCorrelation

#print axioms ThetaTrial.Paper.RadicalCorrelation.theta_fullPairing_eq_zero
#print axioms ThetaTrial.Paper.RadicalCorrelation.theta_fullWeilForm_eq_zero
