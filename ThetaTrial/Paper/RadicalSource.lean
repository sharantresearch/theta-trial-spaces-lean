import ThetaTrial.Paper.RadicalCutoff

/-! The explicit formula and the radical property for smooth sources with
exponential derivative bounds. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set Filter
open scoped Topology ContDiff Convolution ComplexConjugate

namespace ThetaTrial.Paper.RadicalSource
open RadicalApproximation RadicalCorrelation RadicalCutoff

structure RegularSource (F : ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ 2 F
  weight0 : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖F u‖)
  weight1 : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖deriv F u‖)
  weight2 : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖deriv (deriv F) u‖)
  exponential : ∀ R : ℝ, ∃ M > 0, ∀ u : ℝ, ‖F u‖ ≤ M * Real.exp (-(R * |u|))

def approximant (F h : ℝ → ℂ) (n : ℕ) : ℝ → ℂ :=
  Zeta23.EF.weilTest (compactApprox n F) (compactApprox n h)

theorem approximant_compact (F h : ℝ → ℂ) (n : ℕ) :
    HasCompactSupport (approximant F h n) :=
  (compactApprox_compact F n).convolution (ContinuousLinearMap.mul ℝ ℂ)
    (Zeta23.EF.hasCompactSupport_tilde (compactApprox_compact h n))

variable {F : ℝ → ℂ} (hF : RegularSource F)
include hF

theorem approximant_contDiff {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h)
    (hi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖h u‖)) (n : ℕ) :
    ContDiff ℝ 2 (approximant F h n) := by
  have hh : Integrable (compactApprox n h) := by
    have h0 := compactApprox_weighted hm (hi 0) n
    simpa only [zero_mul, Real.exp_zero, one_mul, integrable_norm_iff
      (compactApprox_measurable hm n)] using h0
  have ht : Integrable (Zeta23.EF.tilde (compactApprox n h)) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hh.comp_neg
  exact (compactApprox_compact F n).contDiff_convolution_left
    (ContinuousLinearMap.mul ℝ ℂ)
    (compactApprox_contDiff (hF.smooth) n) ht.locallyIntegrable

theorem approximant_paperFT_tendsto {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h)
    (hi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖h u‖)) (z : ℂ) :
    Tendsto (fun n => Zeta23.paperFT (approximant F h n) z) atTop
      (𝓝 (Zeta23.paperFT (Zeta23.EF.weilTest F h) z)) := by
  have fm : AEStronglyMeasurable F := hF.smooth.continuous.aestronglyMeasurable
  rw [paperFT_weilTest fm hm hF.weight0 hi z]
  have hn : ∀ n, Zeta23.paperFT (approximant F h n) z =
      Zeta23.paperFT (compactApprox n F) z *
        conj (Zeta23.paperFT (compactApprox n h) (conj z)) := by
    intro n
    exact paperFT_weilTest (compactApprox_measurable fm n) (compactApprox_measurable hm n)
      (fun R => compactApprox_weighted fm (hF.weight0 R) n)
      (fun R => compactApprox_weighted hm (hi R) n) z
  simp only [hn]
  exact (compactApprox_paperFT_tendsto_measurable fm hF.weight0 z).mul
    ((Complex.continuous_conj.tendsto _).comp
      (compactApprox_paperFT_tendsto_measurable hm hi (conj z)))

/-- Product decay uses two derivatives of the smooth left factor only, so the
right factor may have jumps. -/
theorem approximant_uniform_strip_bound {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h)
    (hi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖h u‖)) (R : ℝ) :
    ∃ C : ℝ, ∀ n (z : ℂ), |z.im| ≤ R →
      ‖Zeta23.paperFT (approximant F h n) z‖ ≤ C / (1 + ‖z‖ ^ 2) := by
  obtain ⟨C, hC⟩ := compactApprox_uniform_weightedSobolev hF.smooth (hF.weight0 R) (hF.weight1 R) (hF.weight2 R)
  have fm : AEStronglyMeasurable F := hF.smooth.continuous.aestronglyMeasurable
  have hC0 : 0 ≤ C := by
    have hn : 0 ≤ weightedL1 R (compactApprox 0 F) +
        weightedL1 R (deriv (deriv (compactApprox 0 F))) :=
      add_nonneg (integral_nonneg (fun _ => by positivity))
        (integral_nonneg (fun _ => by positivity))
    exact hn.trans (hC 0)
  refine ⟨C * weightedL1 R h, ?_⟩
  intro n z hz
  rw [show Zeta23.paperFT (approximant F h n) z =
      Zeta23.paperFT (compactApprox n F) z *
        conj (Zeta23.paperFT (compactApprox n h) (conj z)) from
    paperFT_weilTest (compactApprox_measurable fm n) (compactApprox_measurable hm n)
      (fun R => compactApprox_weighted fm (hF.weight0 R) n)
      (fun R => compactApprox_weighted hm (hi R) n) z, norm_mul, norm_conj]
  have hl := (norm_paperFT_le_weightedSobolev
    (compactApprox_contDiff (hF.smooth) n)
      (compactApprox_compact F n) hz).trans
        (div_le_div_of_nonneg_right (hC n) (by positivity))
  have hr := (norm_paperFT_le_weightedL1 (compactApprox_weighted hm (hi R) n)
    (z := conj z) (by simpa only [Complex.conj_im, abs_neg] using hz)).trans
      (compactApprox_weightedL1_le_measurable hm (hi R) n)
  calc
    _ ≤ (C / (1 + ‖z‖ ^ 2)) * weightedL1 R h :=
      mul_le_mul hl hr (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem approximant_tendsto {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h)
    (hi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖h u‖)) (x : ℝ) :
    Tendsto (fun n => approximant F h n x) atTop (𝓝 (Zeta23.EF.weilTest F h x)) := by
  obtain ⟨M, hM, hb⟩ := hF.exponential 0
  have htheta : ∀ u, ‖F u‖ ≤ M := by
    intro u
    simpa only [zero_mul, neg_zero, Real.exp_zero, mul_one] using hb u
  have hh := weighted_integrable hm (hi 0)
  simp only [approximant, weilTest_eq_integral]
  apply tendsto_integral_of_dominated_convergence (fun u : ℝ => M * ‖h (u - x)‖)
  · intro n
    have hn := weighted_integrable (compactApprox_measurable hm n)
      (compactApprox_weighted hm (hi 0) n)
    exact (compactApprox_contDiff (hF.smooth) n).continuous.aestronglyMeasurable.mul
      (Complex.continuous_conj.comp_aestronglyMeasurable (hn.comp_sub_right x).aestronglyMeasurable)
  · exact (hh.comp_sub_right x).norm.const_mul M
  · intro n
    filter_upwards with u
    rw [norm_mul, norm_conj]
    exact mul_le_mul ((compactApprox_norm_le n F u).trans (htheta u))
      (compactApprox_norm_le n h (u - x)) (norm_nonneg _) hM.le
  · filter_upwards with u
    simpa only [compactApprox, one_mul, Function.comp_def] using
      ((cutoff_tendsto u).mul_const (F u)).mul
      ((Complex.continuous_conj.tendsto _).comp
        ((cutoff_tendsto (u - x)).mul_const (h (u - x))))

theorem approximant_exponential_bound {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h)
    (hi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖h u‖)) :
    ∃ M : ℝ, ∀ n x, ‖approximant F h n x‖ ≤ M * Real.exp (-|x|) := by
  obtain ⟨M, hM, hb⟩ := hF.exponential 1
  refine ⟨M * weightedL1 1 h, ?_⟩
  intro n x
  have henv : ∀ u : ℝ,
      ‖compactApprox n F u * conj (compactApprox n h (u - x))‖ ≤
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
        mul_le_mul ((compactApprox_norm_le n F u).trans
          (by simpa only [one_mul] using hb u))
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
      ∀ n ρ, ‖Radical.zeroTerm (approximant F h n) ρ‖ ≤ b ρ := by
  obtain ⟨C, hC⟩ := approximant_uniform_strip_bound hF hm hi (1 / 2)
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
      ∀ n r, ‖Radical.gammaTerm (approximant F h n) r‖ ≤ b r := by
  obtain ⟨C, hC⟩ := approximant_uniform_strip_bound hF hm hi 0
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

/-- The noncompact mixed F test has a constructed compact
explicit-formula approximation. Its right factor may be a hard indicator. -/
theorem source_correlation_dominatedApproximation {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h)
    (hi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖h u‖)) :
    Radical.DominatedWeilApproximation (Zeta23.EF.weilTest F h) (approximant F h) := by
  obtain ⟨M, hM⟩ := approximant_exponential_bound hF hm hi
  obtain ⟨bp, hbp, hp⟩ := prime_uniform_majorant hM
  obtain ⟨bg, hbg, hg⟩ := approximant_gamma_majorant hF hm hi
  obtain ⟨bz, hbz, hz⟩ := approximant_zero_majorant hF hm hi
  refine ⟨approximant_contDiff hF hm hi, approximant_compact F h,
    approximant_paperFT_tendsto hF hm hi _, approximant_paperFT_tendsto hF hm hi _,
    ?_, ⟨bp, hbp, Filter.Eventually.of_forall hp⟩, ?_, ?_,
    ⟨bg, hbg, fun n => Filter.Eventually.of_forall (hg n)⟩,
    ?_, ⟨bz, hbz, Filter.Eventually.of_forall hz⟩⟩
  · intro n
    exact tendsto_const_nhds.mul ((approximant_tendsto hF hm hi (Real.log n)).add
      (approximant_tendsto hF hm hi (-Real.log n)))
  · intro n
    exact gammaTerm_compact_measurable (approximant_contDiff hF hm hi n).continuous
      (approximant_compact F h n)
  · filter_upwards with r
    exact (approximant_paperFT_tendsto hF hm hi r).mul_const (Zeta23.EF.gammaBracket r : ℂ)
  · intro ρ
    exact tendsto_const_nhds.mul (approximant_paperFT_tendsto hF hm hi (Zeta23.gammaOf ρ))


theorem source_fourier_integrable (z : ℂ) : Radical.FourierIntegrableAt F z :=
  weighted_fourierIntegrable hF.smooth.continuous.aestronglyMeasurable hF.weight0 z

theorem source_correlation_domain {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h)
    (hi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖h u‖)) :
    Domain (Zeta23.EF.weilTest F h) := by
  have ha := source_correlation_dominatedApproximation hF hm hi
  exact ⟨fun z => RadicalCutoff.FourierIntegrableAt.weilTest (source_fourier_integrable hF z)
    (weighted_fourierIntegrable hm hi (conj z)), ha.integrable_gamma, ha.summable_prime⟩

/-- The full arithmetic radical identity for any regular source with
the paper's exact Xi multiplier transform. -/
theorem source_fullPairing_eq_zero {m : ℂ → ℂ}
    (hfactor : ∀ z, paperFourier F z = xiFunction z * m z)
    {h : ℝ → ℂ} (hm : AEStronglyMeasurable h)
    (hi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖h u‖)) :
    Radical.fullPairing F h = 0 := by
  apply Radical.fullPairing_radical_of_dominated_approximation (m := m)
    _ (fun z => source_fourier_integrable hF z)
    (fun z => weighted_fourierIntegrable hm hi (conj (z : ℂ)))
    (source_correlation_dominatedApproximation hF hm hi)
  intro z
  simpa only [Radical.paperFourier_eq_paper, xiFunction_eq_weilFormula] using hfactor z

theorem source_tail_domain {a : ℝ} (ha : 0 ≤ a) :
    Domain (Zeta23.EF.weilTest (Radical.tail a F) (Radical.tail a F)) := by
  have hi := weightedProfile_integrable hF.smooth.continuous.aestronglyMeasurable (hF.weight0 1)
  have hi' := weightedProfile_integrable
    (hF.smooth.continuous_deriv (by norm_num)).aestronglyMeasurable (hF.weight1 1)
  have hd : ∀ x ∈ (Icc (-a) a)ᶜ, HasDerivAt F (deriv F x) x :=
    fun x _ => (hF.smooth.differentiable (by norm_num) x).hasDerivAt
  have he := exteriorTail_fullForm_converges hF.smooth.continuous ha hd hi.integrableOn hi'.integrableOn
  exact autocorrelation_domain (fun z => (source_fourier_integrable hF z).tail a) he.1 he.2.1

/-- Sharp truncation for the paper form, justified by ordinary
source regularity and an exact Fourier multiplier identity. This includes
the endpoint jumps and all primes, gamma compensation, and both poles. -/
theorem source_hardCutoff {m : ℂ → ℂ}
    (hfactor : ∀ z, paperFourier F z = xiFunction z * m z)
    {a : ℝ} (ha : 0 ≤ a) :
    fullWeilForm (windowCut a F) = fullWeilForm (exteriorTail a F) := by
  have fm : AEStronglyMeasurable F := hF.smooth.continuous.aestronglyMeasurable
  have fi := weighted_integrable fm (hF.weight0 0)
  have tm : AEStronglyMeasurable (Radical.tail a F) := fm.indicator measurableSet_Icc.compl
  have ti : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖Radical.tail a F u‖) :=
    fun R => weighted_indicator measurableSet_Icc.compl (hF.weight0 R)
  obtain ⟨M, hM, hb⟩ := hF.exponential 0
  have fb : ∀ u, ‖F u‖ ≤ M := by
    intro u
    simpa only [zero_mul, neg_zero, Real.exp_zero, mul_one] using hb u
  have tb : ∀ u, ‖Radical.tail a F u‖ ≤ M := by
    intro u
    by_cases hu : u ∈ Icc (-a) a
    · simpa [Radical.tail, hu] using hM.le
    · simpa [Radical.tail, hu] using fb u
  have he := fullQuadratic_sub_of_radical fi (weighted_integrable tm (ti 0))
    ⟨M, fb⟩ ⟨M, tb⟩ (source_correlation_domain hF fm hF.weight0)
    (source_correlation_domain hF tm ti) (source_tail_domain hF ha)
    (source_fullPairing_eq_zero hF hfactor fm hF.weight0)
    (source_fullPairing_eq_zero hF hfactor tm ti)
  have hw : F - Radical.tail a F = Radical.window a F := by
    have h := Radical.window_add_tail a F
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using h.symm)
  rw [hw, Radical.fullQuadratic_eq_paperForm (f := Radical.window a F)
      (fun z => (source_fourier_integrable hF z).window a),
    Radical.fullQuadratic_eq_paperForm (f := Radical.tail a F)
      (fun z => (source_fourier_integrable hF z).tail a)] at he
  exact_mod_cast he

end ThetaTrial.Paper.RadicalSource

#print axioms ThetaTrial.Paper.RadicalSource.source_fullPairing_eq_zero
#print axioms ThetaTrial.Paper.RadicalSource.source_hardCutoff

