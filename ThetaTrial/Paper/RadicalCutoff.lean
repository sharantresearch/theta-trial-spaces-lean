import ThetaTrial.Paper.RadicalCorrelation
import ThetaTrial.Paper.TailFormBound

/-! Algebra of the Weil form needed for the truncation identity. Sums and
integrals are split only where they converge absolutely. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set Filter
open scoped Topology ComplexConjugate Convolution

namespace ThetaTrial.Paper.RadicalCutoff
open Radical RadicalApproximation RadicalCorrelation

structure Domain (k : ℝ → ℂ) : Prop where
  transform : ∀ z : ℂ, FourierIntegrableAt k z
  gamma : Integrable (gammaTerm k)
  prime : Summable (primeTerm k)

theorem paperFT_sub {k l : ℝ → ℂ} {z : ℂ}
    (hk : FourierIntegrableAt k (-z)) (hl : FourierIntegrableAt l (-z)) :
    Zeta23.paperFT (k - l) z = Zeta23.paperFT k z - Zeta23.paperFT l z := by
  have hk' : Integrable (fun u : ℝ => k u * Complex.exp (I * z * (u : ℂ))) := by
    simpa only [FourierIntegrableAt, mul_neg, neg_mul, neg_neg] using hk
  have hl' : Integrable (fun u : ℝ => l u * Complex.exp (I * z * (u : ℂ))) := by
    simpa only [FourierIntegrableAt, mul_neg, neg_mul, neg_neg] using hl
  simp only [Zeta23.paperFT, Pi.sub_apply, sub_mul]
  exact integral_sub hk' hl'

theorem Domain.sub {k l : ℝ → ℂ} (hk : Domain k) (hl : Domain l) : Domain (k - l) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z
    apply ((hk.transform z).sub (hl.transform z)).congr
    filter_upwards with u
    simp only [Pi.sub_apply, sub_mul]
  · have he : gammaTerm (k - l) = gammaTerm k - gammaTerm l := by
      funext r
      simp only [gammaTerm, paperFT_sub (hk.transform _) (hl.transform _), sub_mul, Pi.sub_apply]
    rw [he]
    exact hk.gamma.sub hl.gamma
  · have he : primeTerm (k - l) = primeTerm k - primeTerm l := by
      funext n
      simp only [primeTerm, Pi.sub_apply]
      ring
    rw [he]
    exact hk.prime.sub hl.prime

theorem fullWeil_sub {k l : ℝ → ℂ} (hk : Domain k) (hl : Domain l) :
    fullWeil (k - l) = fullWeil k - fullWeil l := by
  have hg : gammaTerm (k - l) = gammaTerm k - gammaTerm l := by
    funext r
    simp only [gammaTerm, paperFT_sub (hk.transform _) (hl.transform _), Pi.sub_apply, sub_mul]
  have hp : primeTerm (k - l) = primeTerm k - primeTerm l := by
    funext n
    simp only [primeTerm, Pi.sub_apply]
    ring
  change Zeta23.paperFT (k - l) (I / 2) + Zeta23.paperFT (k - l) (-I / 2) -
    ∑' n, primeTerm (k - l) n + (1 / (2 * Real.pi) : ℂ) * ∫ r, gammaTerm (k - l) r = _
  rw [paperFT_sub (hk.transform _) (hl.transform _), paperFT_sub (hk.transform _) (hl.transform _),
    hp, hg]
  simp only [Pi.sub_apply]
  rw [hk.prime.tsum_sub hl.prime, integral_sub hk.gamma hl.gamma]
  unfold fullWeil Zeta23.EF.literatureRHS
  simp only [primeTerm, gammaTerm]
  ring

theorem fullWeil_tilde (k : ℝ → ℂ) : fullWeil (Zeta23.EF.tilde k) = conj (fullWeil k) := by
  have hp : ∀ n, primeTerm (Zeta23.EF.tilde k) n = conj (primeTerm k n) := by
    intro n
    simp only [primeTerm, Zeta23.EF.tilde, neg_neg, map_mul, map_add, conj_ofReal]
    ring
  have hg : ∀ r, gammaTerm (Zeta23.EF.tilde k) r = conj (gammaTerm k r) := by
    intro r
    simp only [gammaTerm, Zeta23.EF.paperFT_tilde, conj_ofReal, map_mul]
  change Zeta23.paperFT (Zeta23.EF.tilde k) (I / 2) +
    Zeta23.paperFT (Zeta23.EF.tilde k) (-I / 2) - ∑' n, primeTerm (Zeta23.EF.tilde k) n +
    (1 / (2 * Real.pi) : ℂ) * ∫ r, gammaTerm (Zeta23.EF.tilde k) r = _
  simp only [Zeta23.EF.paperFT_tilde, map_div₀, conj_I, map_ofNat, map_neg,
    neg_neg, neg_div, hp, hg, integral_conj, ← Complex.conj_tsum]
  unfold fullWeil Zeta23.EF.literatureRHS
  simp only [map_add, map_sub, map_mul, map_div₀, map_one, map_ofNat, conj_ofReal,
    primeTerm, gammaTerm]
  ring

theorem Domain.tilde {k : ℝ → ℂ} (hk : Domain k) : Domain (Zeta23.EF.tilde k) := by
  refine ⟨fun z => (hk.transform (conj z)).tilde, ?_, ?_⟩
  · apply ((Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hk.gamma).congr
    filter_upwards with r
    change conj (gammaTerm k r) = gammaTerm (Zeta23.EF.tilde k) r
    simp only [gammaTerm, Zeta23.EF.paperFT_tilde, map_mul, conj_ofReal]
  · apply (hk.prime.map (Complex.conjCLE : ℂ →L[ℝ] ℂ) Complex.conjCLE.continuous).congr
    intro n
    change conj (primeTerm k n) = primeTerm (Zeta23.EF.tilde k) n
    simp only [primeTerm, Zeta23.EF.tilde, neg_neg, map_mul, map_add, conj_ofReal]
    ring

theorem weilTest_swap (f h : ℝ → ℂ) :
    Zeta23.EF.weilTest h f = Zeta23.EF.tilde (Zeta23.EF.weilTest f h) := by
  funext x
  simp only [Zeta23.EF.tilde, weilTest_eq_integral]
  rw [← integral_conj,
    ← integral_sub_right_eq_self (fun u : ℝ => conj (f u * conj (h (u - -x)))) x]
  apply integral_congr_ae
  filter_upwards with u
  simp only [sub_neg_eq_add, sub_add_cancel, map_mul, conj_conj]
  ring

theorem fullPairing_hermitian (f h : ℝ → ℂ) :
    fullPairing h f = conj (fullPairing f h) := by
  unfold fullPairing
  rw [weilTest_swap, fullWeil_tilde]

theorem FourierIntegrableAt.weilTest {f h : ℝ → ℂ} {z : ℂ}
    (hf : FourierIntegrableAt f z) (hh : FourierIntegrableAt h (conj z)) :
    FourierIntegrableAt (Zeta23.EF.weilTest f h) z := by
  let fz : ℝ → ℂ := fun u => f u * Complex.exp (-I * z * (u : ℂ))
  let hz : ℝ → ℂ := fun u => Zeta23.EF.tilde h u * Complex.exp (-I * z * (u : ℂ))
  have he : (fun x : ℝ => Zeta23.EF.weilTest f h x * Complex.exp (-I * z * (x : ℂ))) =
      fz ⋆[ContinuousLinearMap.mul ℝ ℂ] hz := by
    funext x
    simp only [Zeta23.EF.weilTest, convolution_def, ContinuousLinearMap.mul_apply']
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with u
    dsimp [fz, hz]
    have hx : Complex.exp (-I * z * (x : ℂ)) =
        Complex.exp (-I * z * (u : ℂ)) * Complex.exp (-I * z * ((x - u : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hx]
    ring
  unfold Radical.FourierIntegrableAt
  rw [he]
  exact hf.integrable_convolution (ContinuousLinearMap.mul ℝ ℂ) hh.tilde

theorem theta_correlation_domain {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h)
    (hi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖h u‖)) :
    Domain (Zeta23.EF.weilTest theta h) := by
  have ha := theta_correlation_dominatedApproximation hm hi
  exact ⟨fun z => FourierIntegrableAt.weilTest (Radical.theta_fourier_integrable z)
    (weighted_fourierIntegrable hm hi (conj z)), ha.integrable_gamma, ha.summable_prime⟩

theorem autocorrelation_domain {f : ℝ → ℂ}
    (hf : ∀ z : ℂ, Radical.FourierIntegrableAt f z)
    (hg : Integrable (fun r : ℝ => gammaWeight r * Complex.normSq
      (ThetaTrial.Paper.paperFourier f r)))
    (hp : Summable (fun n : ℕ => |(ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
      (correlation f (Real.log n)).re|)) : Domain (Zeta23.EF.weilTest f f) := by
  refine ⟨fun z => FourierIntegrableAt.weilTest (hf z) (hf (conj z)), ?_, ?_⟩
  · apply (Complex.ofRealCLM.integrable_comp hg.comp_neg).congr
    filter_upwards with r
    change ((gammaWeight (-r) * Complex.normSq
      (ThetaTrial.Paper.paperFourier f ((-r : ℝ) : ℂ)) : ℝ) : ℂ) = _
    unfold gammaTerm
    rw [Radical.paperFT_weilTest_of_integrable hf]
    simp only [conj_ofReal, Complex.mul_conj, Radical.paperFourier_eq_paper,
      ← Complex.ofReal_neg,
      show gammaWeight (-r) = gammaWeight r from ThetaTrial.WeilFormula.gammaBracket_neg r,
      Complex.ofReal_mul]
    exact mul_comm _ _
  · have hp' : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        (correlation f (Real.log n)).re) := by
      apply summable_norm_iff.mp
      simpa only [Real.norm_eq_abs] using hp
    have hc := (hp'.map Complex.ofRealCLM Complex.ofRealCLM.continuous).mul_left (2 : ℂ)
    apply hc.congr
    intro n
    change (2 : ℂ) * (((ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
      (correlation f (Real.log n)).re : ℝ) : ℂ) = _
    simp only [primeTerm, ThetaTrial.WeilFormula.weilTest_add_neg, Radical.weilFormulaCorrelation_eq_paper]
    push_cast
    ring

theorem weightedProfile_integrable {f : ℝ → ℂ} (hm : AEStronglyMeasurable f) {R : ℝ}
    (hi : Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖f u‖)) :
    Integrable (ThetaTrial.PrimeContinuity.weightedProfile R f) := by
  apply (integrable_norm_iff ((by fun_prop : Continuous (fun u : ℝ =>
    (Real.exp (R * |u|) : ℂ))).aestronglyMeasurable.mul hm)).mp
  change Integrable (fun u => ‖ThetaTrial.PrimeContinuity.weightedProfile R f u‖)
  simpa only [ThetaTrial.PrimeContinuity.weightedProfile_norm] using hi

theorem theta_tail_domain {a : ℝ} (ha : 0 ≤ a) :
    Domain (Zeta23.EF.weilTest (Radical.tail a theta) (Radical.tail a theta)) := by
  have hc : ContDiff ℝ 2 theta := thetaDensity_contDiff.of_le le_top
  have hi := weightedProfile_integrable hc.continuous.aestronglyMeasurable (theta_weighted 1)
  have hid : Integrable (fun u : ℝ => Real.exp (1 * |u|) * ‖deriv theta u‖) := by
    change Integrable (fun u : ℝ => Real.exp (1 * |u|) * ‖deriv (fun x => (thetaDensity x : ℂ)) u‖)
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      theta_iteratedDeriv_weighted_integrable 1 1
  have hi' := weightedProfile_integrable (hc.continuous_deriv (by norm_num)).aestronglyMeasurable hid
  have hd : ∀ x ∈ (Icc (-a) a)ᶜ, HasDerivAt theta (deriv theta x) x :=
    fun x _ => (hc.differentiable (by norm_num) x).hasDerivAt
  have he := exteriorTail_fullForm_converges hc.continuous ha hd hi.integrableOn hi'.integrableOn
  apply autocorrelation_domain (fun z => (Radical.theta_fourier_integrable z).tail a) he.1 he.2.1

theorem bounded_correlation_integrable {f h : ℝ → ℂ}
    (fm : AEStronglyMeasurable f) (hi : Integrable h) {M : ℝ}
    (hb : ∀ u, ‖f u‖ ≤ M) (x : ℝ) :
    Integrable (fun u : ℝ => f u * conj (h (u - x))) := by
  apply ((hi.comp_sub_right x).norm.const_mul M).mono'
    (fm.mul (Complex.continuous_conj.comp_aestronglyMeasurable (hi.comp_sub_right x).aestronglyMeasurable))
  filter_upwards with u
  change ‖f u * conj (h (u - x))‖ ≤ _
  rw [norm_mul, norm_conj]
  exact mul_le_mul_of_nonneg_right (hb u) (norm_nonneg _)

theorem weilTest_sub_sub {f h : ℝ → ℂ}
    (hff : ∀ x, Integrable (fun u : ℝ => f u * conj (f (u - x))))
    (hfh : ∀ x, Integrable (fun u : ℝ => f u * conj (h (u - x))))
    (hhf : ∀ x, Integrable (fun u : ℝ => h u * conj (f (u - x))))
    (hhh : ∀ x, Integrable (fun u : ℝ => h u * conj (h (u - x)))) :
    Zeta23.EF.weilTest (f - h) (f - h) =
      (Zeta23.EF.weilTest f f - Zeta23.EF.weilTest f h) -
        (Zeta23.EF.weilTest h f - Zeta23.EF.weilTest h h) := by
  funext x
  simp only [weilTest_eq_integral, Pi.sub_apply]
  have h1 : Integrable (fun u : ℝ => f u * conj (f (u - x)) - f u * conj (h (u - x))) :=
    (hff x).sub (hfh x)
  have h2 : Integrable (fun u : ℝ => h u * conj (f (u - x)) - h u * conj (h (u - x))) :=
    (hhf x).sub (hhh x)
  rw [← integral_sub (hff x) (hfh x), ← integral_sub (hhf x) (hhh x),
    ← integral_sub h1 h2]
  apply integral_congr_ae
  filter_upwards with u
  simp only [Pi.sub_apply, map_sub]
  ring

theorem fullQuadratic_sub_of_radical {f h : ℝ → ℂ}
    (fi : Integrable f) (hi : Integrable h)
    (fb : ∃ M : ℝ, ∀ u, ‖f u‖ ≤ M) (hb : ∃ M : ℝ, ∀ u, ‖h u‖ ≤ M)
    (dff : Domain (Zeta23.EF.weilTest f f))
    (dfh : Domain (Zeta23.EF.weilTest f h))
    (dhh : Domain (Zeta23.EF.weilTest h h))
    (zff : fullPairing f f = 0) (zfh : fullPairing f h = 0) :
    fullQuadratic (f - h) = fullQuadratic h := by
  obtain ⟨M, hM⟩ := fb
  obtain ⟨N, hN⟩ := hb
  have hff := bounded_correlation_integrable fi.aestronglyMeasurable fi hM
  have hfh := bounded_correlation_integrable fi.aestronglyMeasurable hi hM
  have hhf := bounded_correlation_integrable hi.aestronglyMeasurable fi hN
  have hhh := bounded_correlation_integrable hi.aestronglyMeasurable hi hN
  have dhf : Domain (Zeta23.EF.weilTest h f) := by rw [weilTest_swap]; exact dfh.tilde
  have zhf : fullPairing h f = 0 := by rw [fullPairing_hermitian, zfh, map_zero]
  change fullWeil (Zeta23.EF.weilTest (f - h) (f - h)) = _
  rw [weilTest_sub_sub hff hfh hhf hhh, fullWeil_sub (dff.sub dfh) (dhf.sub dhh),
    fullWeil_sub dff dfh, fullWeil_sub dhf dhh]
  change (fullPairing f f - fullPairing f h) - (fullPairing h f - fullQuadratic h) = _
  rw [zff, zfh, zhf]
  ring

/-- Sharp truncation for the theta density. The explicit formula is not
applied directly to the discontinuous window or tail. -/
theorem theta_hardCutoff {a : ℝ} (ha : 0 ≤ a) :
    fullWeilForm (windowCut a theta) = fullWeilForm (exteriorTail a theta) := by
  have fm : AEStronglyMeasurable theta := thetaDensity_contDiff.continuous.aestronglyMeasurable
  have fi := weighted_integrable fm (theta_weighted 0)
  have tm : AEStronglyMeasurable (Radical.tail a theta) := fm.indicator measurableSet_Icc.compl
  have ti : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖Radical.tail a theta u‖) :=
    fun R => weighted_indicator measurableSet_Icc.compl (theta_weighted R)
  obtain ⟨M, hM, hb⟩ := theta_exponential_bound 0
  have fb : ∀ u, ‖theta u‖ ≤ M := by
    intro u
    simpa only [theta, zero_mul, neg_zero, Real.exp_zero, mul_one] using hb u
  have tb : ∀ u, ‖Radical.tail a theta u‖ ≤ M := by
    intro u
    by_cases hu : u ∈ Icc (-a) a
    · simpa [Radical.tail, hu] using hM.le
    · simpa [Radical.tail, hu] using fb u
  have he := fullQuadratic_sub_of_radical fi (weighted_integrable tm (ti 0))
    ⟨M, fb⟩ ⟨M, tb⟩ (theta_correlation_domain fm theta_weighted)
    (theta_correlation_domain tm ti) (theta_tail_domain ha)
    theta_fullQuadratic_eq_zero (theta_tail_pairing_eq_zero a)
  have hw : theta - Radical.tail a theta = Radical.window a theta := by
    have h := Radical.window_add_tail a theta
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using h.symm)
  rw [hw, fullQuadratic_eq_paperForm (f := Radical.window a theta)
      (fun z => (Radical.theta_fourier_integrable z).window a),
    fullQuadratic_eq_paperForm (f := Radical.tail a theta)
      (fun z => (Radical.theta_fourier_integrable z).tail a)] at he
  exact_mod_cast he

end ThetaTrial.Paper.RadicalCutoff

#print axioms ThetaTrial.Paper.RadicalCutoff.theta_hardCutoff
