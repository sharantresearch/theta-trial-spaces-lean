import ThetaTrial.WeilFormula
import ThetaTrial.XiSymmetry
import ThetaTrial.Paper.ThetaFourier
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The Weil form and the truncation identity

The explicit formula for compactly supported `C²` tests, conditions under
which it extends to noncompact tests, and the algebra of the radical. For the
theta density the extension is completed in `RadicalApproximation` and
`RadicalCorrelation`. The paper's Fourier transform `paperFourier` has no
`2π` normalization; its relation to the unitary transform in
`FourierNormalization` is recorded explicitly.
-/

noncomputable section

open Complex MeasureTheory Set Filter
open scoped ComplexConjugate Topology Convolution

namespace ThetaTrial.Paper.Radical

/-- The paper's unnormalized minus-sign transform at complex arguments. -/
def paperFourier (f : ℝ → ℂ) (z : ℂ) : ℂ := Zeta23.paperFT f (-z)

theorem paperFourier_eq_integral (f : ℝ → ℂ) (z : ℂ) :
    paperFourier f z = ∫ u : ℝ, f u * Complex.exp (-I * z * (u : ℂ)) := by
  unfold paperFourier Zeta23.paperFT
  simp only [mul_neg, neg_mul]

theorem paperFourier_eq_paper (f : ℝ → ℂ) (z : ℂ) :
    paperFourier f z = ThetaTrial.Paper.paperFourier f z :=
  (ThetaTrial.Paper.paperFourier_eq_source f z).symm

theorem paperFourier_eq_unitary (f : ℝ → ℂ) (z : ℂ) :
    paperFourier f z = (Real.sqrt (2 * Real.pi) : ℂ) *
      ThetaTrial.FourierNormalization.fourier f z := by
  unfold paperFourier ThetaTrial.FourierNormalization.fourier
  field_simp [ThetaTrial.FourierNormalization.sqrt_two_pi_ne_zero]

/-- `ThetaTrial.Xi` agrees with the centering used in the paper. -/
theorem Xi_eq_paper_centering (z : ℂ) :
    ThetaTrial.Xi z = ThetaTrial.xi (1 / 2 + I * z) := ThetaTrial.xi_centered_even (I * z)

/-- Full Weil functional: both poles, every von Mangoldt term,
and the digamma integral. This definition makes no convergence claim. -/
def fullWeil (k : ℝ → ℂ) : ℂ := Zeta23.EF.literatureRHS k

/-- The concrete correlation form, with no support truncation of the primes. -/
def fullPairing (f h : ℝ → ℂ) : ℂ :=
  fullWeil (Zeta23.EF.weilTest f h)

def fullQuadratic (f : ℝ → ℂ) : ℂ := fullPairing f f

/-- The explicit formula for compactly supported `C²` tests. -/
theorem fullWeil_compact {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    fullWeil k = ∑' ρ : Zeta23.zetaZeroConfig.carrier,
      (Zeta23.zetaZeroConfig.mult ρ : ℂ) *
        Zeta23.paperFT k (Zeta23.gammaOf ρ) :=
  (ThetaTrial.weil_compact_formula hk hkc).symm

/-- The expression agrees with `WeilFormula.fullForm` on compactly supported
tests, including the positive pole term. -/
theorem fullQuadratic_eq_windowForm {a : ℝ} {f : ℝ → ℂ}
    (hf : Continuous f) (hfs : tsupport f ⊆ Icc (-a) a) :
    fullQuadratic f = ThetaTrial.WeilFormula.fullForm a f := by
  exact ThetaTrial.WeilFormula.literatureRHS_eq_fullForm hf hfs

/-- Hard truncation; the endpoints belong to the interior piece. -/
def window (a : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := (Icc (-a) a).indicator f

/-- Complementary tail; no artificial smoothing or endpoint condition. -/
def tail (a : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := (Icc (-a) a)ᶜ.indicator f

theorem window_add_tail (a : ℝ) (f : ℝ → ℂ) : window a f + tail a f = f := by
  funext u
  by_cases hu : u ∈ Icc (-a) a <;> simp [window, tail, hu]

/-- The exponential integrability needed to evaluate the Fourier transform at
one complex frequency. -/
def FourierIntegrableAt (f : ℝ → ℂ) (z : ℂ) : Prop :=
  Integrable (fun u : ℝ => f u * Complex.exp (-I * z * (u : ℂ)))

theorem FourierIntegrableAt.tilde {f : ℝ → ℂ} {z : ℂ}
    (hf : FourierIntegrableAt f (conj z)) :
    FourierIntegrableAt (Zeta23.EF.tilde f) z := by
  have h := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hf.comp_neg
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  change conj (f (-u) * Complex.exp (-I * conj z * ((-u : ℝ) : ℂ))) = _
  simp only [map_mul,
    ← Complex.exp_conj, map_neg, conj_I, conj_conj, conj_ofReal,
    Complex.ofReal_neg, Zeta23.EF.tilde]
  congr 2
  ring

theorem FourierIntegrableAt.window {f : ℝ → ℂ} {z : ℂ}
    (hf : FourierIntegrableAt f z) (a : ℝ) : FourierIntegrableAt (window a f) z := by
  refine (hf.indicator (measurableSet_Icc (a := -a) (b := a))).congr ?_
  filter_upwards with u
  by_cases hu : u ∈ Icc (-a) a <;> simp [Radical.window, hu]

theorem FourierIntegrableAt.tail {f : ℝ → ℂ} {z : ℂ}
    (hf : FourierIntegrableAt f z) (a : ℝ) : FourierIntegrableAt (tail a f) z := by
  refine (hf.indicator (measurableSet_Icc (a := -a) (b := a)).compl).congr ?_
  filter_upwards with u
  by_cases hu : u ∈ Icc (-a) a <;> simp [Radical.tail, hu]

/-- The complex Fourier convolution identity for noncompact inputs, under two
weighted-L¹ hypotheses. No continuity or support condition is needed, so it
applies to a hard cutoff. -/
theorem paperFourier_weilTest_of_integrable {f h : ℝ → ℂ} {z : ℂ}
    (hf : FourierIntegrableAt f z) (hh : FourierIntegrableAt h (conj z)) :
    paperFourier (Zeta23.EF.weilTest f h) z =
      paperFourier f z * conj (paperFourier h (conj z)) := by
  let fz : ℝ → ℂ := fun u => f u * Complex.exp (-I * z * (u : ℂ))
  let hz : ℝ → ℂ := fun u => Zeta23.EF.tilde h u * Complex.exp (-I * z * (u : ℂ))
  have heq : (fun x : ℝ => Zeta23.EF.weilTest f h x *
      Complex.exp (-I * z * (x : ℂ))) =
      fz ⋆[ContinuousLinearMap.mul ℝ ℂ] hz := by
    funext x
    simp only [Zeta23.EF.weilTest, convolution_def, ContinuousLinearMap.mul_apply']
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with u
    dsimp [fz, hz]
    have hexp : Complex.exp (-I * z * (x : ℂ)) =
        Complex.exp (-I * z * (u : ℂ)) *
          Complex.exp (-I * z * ((x - u : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    ring
  rw [paperFourier_eq_integral, heq]
  have hint := integral_convolution (ContinuousLinearMap.mul ℝ ℂ) hf hh.tilde
  change (∫ x : ℝ, (fz ⋆[ContinuousLinearMap.mul ℝ ℂ] hz) x) = _ at hint
  rw [hint]
  simp only [ContinuousLinearMap.mul_apply']
  rw [← paperFourier_eq_integral f z,
    ← paperFourier_eq_integral (Zeta23.EF.tilde h) z]
  unfold paperFourier
  rw [Zeta23.EF.paperFT_tilde]
  simp only [map_neg]

theorem weilTest_eq_paperCorrelation (f : ℝ → ℂ) (x : ℝ) :
    Zeta23.EF.weilTest f f x = ThetaTrial.Paper.correlation f x := by
  simp only [Zeta23.EF.weilTest, convolution_def, ContinuousLinearMap.mul_apply',
    Zeta23.EF.tilde, neg_sub, ThetaTrial.Paper.correlation]

theorem weilFormulaCorrelation_eq_paper (f : ℝ → ℂ) (x : ℝ) :
    ThetaTrial.WeilFormula.correlation f x = ThetaTrial.Paper.correlation f x := by
  rw [← ThetaTrial.WeilFormula.weilTest_eq_correlation, weilTest_eq_paperCorrelation]

theorem paperFT_weilTest_of_integrable {f : ℝ → ℂ}
    (hf : ∀ z : ℂ, FourierIntegrableAt f z) (z : ℂ) :
    Zeta23.paperFT (Zeta23.EF.weilTest f f) z =
      paperFourier f (-z) * conj (paperFourier f (-conj z)) := by
  have h := paperFourier_weilTest_of_integrable (hf (-z)) (hf (conj (-z)))
  simpa only [paperFourier, neg_neg, map_neg] using h

/-- The pole term, with its positive sign and both moments. -/
theorem pole_pair_of_integrable {f : ℝ → ℂ}
    (hf : ∀ z : ℂ, FourierIntegrableAt f z) :
    Zeta23.paperFT (Zeta23.EF.weilTest f f) (I / 2) +
      Zeta23.paperFT (Zeta23.EF.weilTest f f) (-I / 2) =
      (2 : ℂ) * ((ThetaTrial.Paper.paperFourier f (I / 2) *
        conj (ThetaTrial.Paper.paperFourier f (-I / 2))).re : ℂ) := by
  rw [paperFT_weilTest_of_integrable hf, paperFT_weilTest_of_integrable hf]
  simp only [map_div₀, conj_I, map_ofNat, map_neg, neg_neg, neg_div,
    paperFourier_eq_paper]
  have h := Complex.add_conj (ThetaTrial.Paper.paperFourier f (I / 2) *
    conj (ThetaTrial.Paper.paperFourier f (-I / 2)))
  simpa only [map_mul, conj_conj, add_comm, mul_comm, Complex.ofReal_mul,
    Complex.ofReal_ofNat, neg_div] using h

theorem gamma_integral_of_integrable {f : ℝ → ℂ}
    (hf : ∀ z : ℂ, FourierIntegrableAt f z) :
    (∫ r : ℝ, Zeta23.paperFT (Zeta23.EF.weilTest f f) r *
      (Zeta23.EF.gammaBracket r : ℂ)) =
      ((∫ r : ℝ, ThetaTrial.Paper.gammaWeight r *
        Complex.normSq (ThetaTrial.Paper.paperFourier f r)) : ℝ) := by
  calc
    _ = ∫ r : ℝ, (Complex.normSq (paperFourier f (-r)) : ℂ) *
        (Zeta23.EF.gammaBracket r : ℂ) := by
      apply integral_congr_ae
      filter_upwards with r
      rw [paperFT_weilTest_of_integrable hf]
      simp only [conj_ofReal, Complex.mul_conj]
    _ = ∫ r : ℝ, (Complex.normSq (paperFourier f (-(-r : ℝ))) : ℂ) *
        (Zeta23.EF.gammaBracket (-r) : ℂ) :=
      (integral_neg_eq_self _ volume).symm
    _ = _ := by
      simp only [Complex.ofReal_neg, neg_neg, ThetaTrial.WeilFormula.gammaBracket_neg,
        paperFourier_eq_paper]
      have he : (fun r : ℝ => (Complex.normSq (ThetaTrial.Paper.paperFourier f r) : ℂ) *
          (Zeta23.EF.gammaBracket r : ℂ)) = fun r : ℝ =>
          ((ThetaTrial.Paper.gammaWeight r *
            Complex.normSq (ThetaTrial.Paper.paperFourier f r) : ℝ) : ℂ) := by
        funext r
        simp only [Zeta23.EF.gammaBracket, ThetaTrial.Paper.gammaWeight,
          Complex.ofReal_mul, mul_comm]
      rw [he]
      exact integral_complex_ofReal

/-- Dictionary to the paper's real form, valid also for noncompact
or discontinuous inputs with all exponential moments. The identity itself
does not assert convergence of the prime sum or gamma integral; that is
separately supplied by the dominated-approximation results below. -/
theorem fullQuadratic_eq_paperForm {f : ℝ → ℂ}
    (hf : ∀ z : ℂ, FourierIntegrableAt f z) :
    fullQuadratic f = (ThetaTrial.Paper.fullWeilForm f : ℂ) := by
  have hp : (∑' n : ℕ,
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (Zeta23.EF.weilTest f f (Real.log n) +
          Zeta23.EF.weilTest f f (-Real.log n))) =
      (2 : ℂ) * ((∑' n : ℕ,
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          (ThetaTrial.Paper.correlation f (Real.log n)).re : ℝ) : ℂ) := by
    simp_rw [ThetaTrial.WeilFormula.weilTest_add_neg, weilFormulaCorrelation_eq_paper]
    rw [Complex.ofReal_tsum, ← tsum_mul_left]
    apply tsum_congr
    intro n
    push_cast
    ring
  unfold fullQuadratic fullPairing fullWeil Zeta23.EF.literatureRHS
  rw [pole_pair_of_integrable hf, hp, gamma_integral_of_integrable hf]
  unfold ThetaTrial.Paper.fullWeilForm
  push_cast
  ring

theorem paperFourier_window_add_tail {a : ℝ} {f : ℝ → ℂ} {z : ℂ}
    (hf : FourierIntegrableAt f z) :
    paperFourier (window a f) z + paperFourier (tail a f) z = paperFourier f z := by
  have hwi := hf.indicator (measurableSet_Icc (a := -a) (b := a))
  have hti := hf.indicator (measurableSet_Icc (a := -a) (b := a)).compl
  have hw : (fun u : ℝ => window a f u * Complex.exp (-I * z * (u : ℂ))) =
      (Icc (-a) a).indicator (fun u => f u * Complex.exp (-I * z * (u : ℂ))) := by
    funext u
    by_cases hu : u ∈ Icc (-a) a <;> simp [window, hu]
  have ht : (fun u : ℝ => tail a f u * Complex.exp (-I * z * (u : ℂ))) =
      (Icc (-a) a)ᶜ.indicator (fun u => f u * Complex.exp (-I * z * (u : ℂ))) := by
    funext u
    by_cases hu : u ∈ Icc (-a) a <;> simp [tail, hu]
  rw [paperFourier_eq_integral, paperFourier_eq_integral, paperFourier_eq_integral,
    hw, ht, ← integral_add hwi hti]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ Icc (-a) a <;> simp [hu]

/-- Zero summand in the paper's unnormalized convention. -/
def spectralSummand (f h : ℝ → ℂ) (z : ThetaTrial.XiZeros) : ℂ :=
  (ThetaTrial.XiMultiplicity z : ℂ) * paperFourier f z *
    conj (paperFourier h (conj (z : ℂ)))

def spectralPairing (f h : ℝ → ℂ) : ℂ := ∑' z : ThetaTrial.XiZeros, spectralSummand f h z

theorem spectralSummand_eq_unitary (f : ℝ → ℂ) (z : ThetaTrial.XiZeros) :
    spectralSummand f f z = (2 * Real.pi : ℂ) *
      ThetaTrial.WeilFormula.xiSummand f z := by
  unfold spectralSummand ThetaTrial.WeilFormula.xiSummand
  rw [paperFourier_eq_unitary, paperFourier_eq_unitary]
  simp only [map_mul, conj_ofReal]
  have hs := ThetaTrial.FourierNormalization.sqrt_two_pi_sq
  calc
    _ = (Real.sqrt (2 * Real.pi) : ℂ) ^ 2 *
        ((ThetaTrial.XiMultiplicity z : ℂ) * ThetaTrial.FourierNormalization.fourier f z *
          conj (ThetaTrial.FourierNormalization.fourier f (conj (z : ℂ)))) := by ring
    _ = _ := by rw [hs]

/-- A proved bridge to the full arithmetic form on compact C² inputs. -/
theorem fullQuadratic_compact_sampling {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    Summable (spectralSummand f f) ∧ fullQuadratic f = spectralPairing f f := by
  obtain ⟨hs, _, heq⟩ := ThetaTrial.WeilFormula.compact_signed_sampling hf hfs
  have he : spectralSummand f f = fun z =>
      (2 * Real.pi : ℂ) * ThetaTrial.WeilFormula.xiSummand f z := by
    funext z
    exact spectralSummand_eq_unitary f z
  constructor
  · rw [he]
    exact hs.mul_left _
  · rw [fullQuadratic_eq_windowForm hf.continuous hfs, heq]
    simp only [spectralPairing, he, tsum_mul_left]

/-- If the Fourier transform of `F` is divisible by `Xi`, the sum over zeros
in the explicit formula vanishes. -/
theorem spectralPairing_eq_zero_of_factor {F : ℝ → ℂ} {m : ℂ → ℂ}
    (hfactor : ∀ z, paperFourier F z = ThetaTrial.Xi z * m z) (h : ℝ → ℂ) :
    spectralPairing F h = 0 := by
  have hzero : ∀ z : ThetaTrial.XiZeros, spectralSummand F h z = 0 := by
    intro z
    have hz : ThetaTrial.Xi z = 0 := z.property
    simp [spectralSummand, hfactor, hz]
  simp [spectralPairing, hzero]

theorem spectralPairing_right_eq_zero_of_factor {F : ℝ → ℂ} {m : ℂ → ℂ}
    (hfactor : ∀ z, paperFourier F z = ThetaTrial.Xi z * m z) (h : ℝ → ℂ) :
    spectralPairing h F = 0 := by
  have hzero : ∀ z : ThetaTrial.XiZeros, spectralSummand h F z = 0 := by
    intro z
    have hz : ThetaTrial.Xi z = 0 := z.property
    simp [spectralSummand, hfactor, ThetaTrial.Xi_conj, hz]
  simp [spectralPairing, hzero]

/-- The truncation identity on the zero side of the explicit formula. -/
theorem spectral_hardCutoff_support {a : ℝ} {F : ℝ → ℂ} {m : ℂ → ℂ}
    (hfactor : ∀ z, paperFourier F z = ThetaTrial.Xi z * m z)
    (hint : ∀ z : ThetaTrial.XiZeros,
      FourierIntegrableAt F z ∧ FourierIntegrableAt F (conj (z : ℂ))) :
    spectralPairing (window a F) (window a F) =
      spectralPairing (tail a F) (tail a F) := by
  apply tsum_congr
  intro z
  have hz : ThetaTrial.Xi z = 0 := z.property
  have hfz : paperFourier F z = 0 := by rw [hfactor, hz, zero_mul]
  have hfzc : paperFourier F (conj (z : ℂ)) = 0 := by
    rw [hfactor, ThetaTrial.Xi_conj, hz, map_zero, zero_mul]
  have h1 := (paperFourier_window_add_tail (a := a) (hint z).1).trans hfz
  have h2 := (paperFourier_window_add_tail (a := a) (hint z).2).trans hfzc
  have h1' : paperFourier (window a F) z = -paperFourier (tail a F) z :=
    eq_neg_iff_add_eq_zero.mpr h1
  have h2' : paperFourier (window a F) (conj (z : ℂ)) =
      -paperFourier (tail a F) (conj (z : ℂ)) := eq_neg_iff_add_eq_zero.mpr h2
  simp only [spectralSummand, h1', h2', map_neg, mul_neg, neg_mul, neg_neg]

/-- All arithmetic terms remain in this extension criterion. -/
def primeTerm (k : ℝ → ℂ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
    (k (Real.log n) + k (-Real.log n))

def gammaTerm (k : ℝ → ℂ) (r : ℝ) : ℂ :=
  Zeta23.paperFT k r * (Zeta23.EF.gammaBracket r : ℂ)

def zeroTerm (k : ℝ → ℂ) (ρ : Zeta23.zetaZeroConfig.carrier) : ℂ :=
  (Zeta23.zetaZeroConfig.mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)

/-- Conditions under which the explicit formula extends from compactly
supported tests to one noncompact test. -/
structure DominatedWeilApproximation (k : ℝ → ℂ) (ks : ℕ → ℝ → ℂ) : Prop where
  smooth : ∀ j, ContDiff ℝ 2 (ks j)
  compact : ∀ j, HasCompactSupport (ks j)
  polePlus : Tendsto (fun j => Zeta23.paperFT (ks j) (I / 2)) atTop
    (𝓝 (Zeta23.paperFT k (I / 2)))
  poleMinus : Tendsto (fun j => Zeta23.paperFT (ks j) (-I / 2)) atTop
    (𝓝 (Zeta23.paperFT k (-I / 2)))
  primeLimit : ∀ n, Tendsto (fun j => primeTerm (ks j) n) atTop (𝓝 (primeTerm k n))
  primeDominated : ∃ b : ℕ → ℝ, Summable b ∧
    ∀ᶠ j in atTop, ∀ n, ‖primeTerm (ks j) n‖ ≤ b n
  gammaMeasurable : ∀ j, AEStronglyMeasurable (gammaTerm (ks j))
  gammaLimit : ∀ᵐ r, Tendsto (fun j => gammaTerm (ks j) r) atTop (𝓝 (gammaTerm k r))
  gammaDominated : ∃ b : ℝ → ℝ, Integrable b ∧
    ∀ j, ∀ᵐ r, ‖gammaTerm (ks j) r‖ ≤ b r
  zeroLimit : ∀ ρ, Tendsto (fun j => zeroTerm (ks j) ρ) atTop (𝓝 (zeroTerm k ρ))
  zeroDominated : ∃ b : Zeta23.zetaZeroConfig.carrier → ℝ, Summable b ∧
    ∀ᶠ j in atTop, ∀ ρ, ‖zeroTerm (ks j) ρ‖ ≤ b ρ

theorem DominatedWeilApproximation.summable_prime {k : ℝ → ℂ} {ks : ℕ → ℝ → ℂ}
    (h : DominatedWeilApproximation k ks) : Summable (primeTerm k) := by
  obtain ⟨b, hb, hbound⟩ := h.primeDominated
  apply hb.of_norm_bounded
  intro n
  exact le_of_tendsto ((h.primeLimit n).norm) (hbound.mono fun j hj => hj n)

theorem DominatedWeilApproximation.integrable_gamma {k : ℝ → ℂ} {ks : ℕ → ℝ → ℂ}
    (h : DominatedWeilApproximation k ks) : Integrable (gammaTerm k) := by
  obtain ⟨b, hb, hbound⟩ := h.gammaDominated
  apply hb.mono' (aestronglyMeasurable_of_tendsto_ae atTop h.gammaMeasurable h.gammaLimit)
  filter_upwards [h.gammaLimit, ae_all_iff.mpr hbound] with r hr hbr
  exact le_of_tendsto hr.norm (Filter.Eventually.of_forall hbr)

/-- Extension of the explicit formula to a noncompact test, under the
convergence conditions above for the poles, the primes, the gamma integral
and the sum over zeros. -/
theorem fullWeil_of_dominated_approximation {k : ℝ → ℂ} {ks : ℕ → ℝ → ℂ}
    (h : DominatedWeilApproximation k ks) :
    Summable (zeroTerm k) ∧ fullWeil k = ∑' ρ, zeroTerm k ρ := by
  obtain ⟨bp, hbp, hpb⟩ := h.primeDominated
  obtain ⟨bg, hbg, hgb⟩ := h.gammaDominated
  obtain ⟨bz, hbz, hzb⟩ := h.zeroDominated
  have hp := tendsto_tsum_of_dominated_convergence hbp h.primeLimit hpb
  have hg := tendsto_integral_of_dominated_convergence bg h.gammaMeasurable
    hbg hgb h.gammaLimit
  have hz := tendsto_tsum_of_dominated_convergence hbz h.zeroLimit hzb
  have hs : Summable (zeroTerm k) := by
    apply hbz.of_norm_bounded
    intro ρ
    exact le_of_tendsto ((h.zeroLimit ρ).norm) (hzb.mono fun j hj => hj ρ)
  refine ⟨hs, ?_⟩
  have hw : Tendsto (fun j => fullWeil (ks j)) atTop (𝓝 (fullWeil k)) := by
    exact ((h.polePlus.add h.poleMinus).sub hp).add
      (tendsto_const_nhds.mul hg)
  have heq : (fun j => fullWeil (ks j)) = fun j => ∑' ρ, zeroTerm (ks j) ρ := by
    funext j
    exact fullWeil_compact (h.smooth j) (h.compact j)
  rw [heq] at hw
  exact tendsto_nhds_unique hw hz

theorem zeroTerm_weilTest_eq_spectral {f h : ℝ → ℂ}
    (hf : ∀ z : ThetaTrial.XiZeros, FourierIntegrableAt f z)
    (hh : ∀ z : ThetaTrial.XiZeros, FourierIntegrableAt h (conj (z : ℂ)))
    (ρ : Zeta23.zetaZeroConfig.carrier) :
    zeroTerm (Zeta23.EF.weilTest f h) ρ =
      spectralSummand f h (ThetaTrial.zetaZeroEquivXiZeros ρ) := by
  have he : Zeta23.paperFT (Zeta23.EF.weilTest f h) (Zeta23.gammaOf ρ) =
      paperFourier (Zeta23.EF.weilTest f h) (ThetaTrial.zetaZeroEquivXiZeros ρ) := by
    change Zeta23.paperFT (Zeta23.EF.weilTest f h) (Zeta23.gammaOf ρ) =
      Zeta23.paperFT (Zeta23.EF.weilTest f h)
        (-ThetaTrial.FourierNormalization.spectralCoord (ρ : ℂ))
    rw [ThetaTrial.FourierNormalization.spectralCoord_eq_neg_gammaOf, neg_neg]
  unfold zeroTerm spectralSummand
  rw [ThetaTrial.zetaZeroEquivXiZeros_multiplicity, he,
    paperFourier_weilTest_of_integrable (hf (ThetaTrial.zetaZeroEquivXiZeros ρ))
      (hh (ThetaTrial.zetaZeroEquivXiZeros ρ))]
  ring

/-- Concrete full arithmetic-to-spectral bridge for a noncompact correlation
whenever its separate dominated-approximation estimates have been supplied. -/
theorem fullPairing_dominated_sampling {f h : ℝ → ℂ} {ks : ℕ → ℝ → ℂ}
    (hf : ∀ z : ThetaTrial.XiZeros, FourierIntegrableAt f z)
    (hh : ∀ z : ThetaTrial.XiZeros, FourierIntegrableAt h (conj (z : ℂ)))
    (ha : DominatedWeilApproximation (Zeta23.EF.weilTest f h) ks) :
    Summable (spectralSummand f h) ∧ fullPairing f h = spectralPairing f h := by
  obtain ⟨hs, heq⟩ := fullWeil_of_dominated_approximation ha
  have he : zeroTerm (Zeta23.EF.weilTest f h) = fun ρ =>
      spectralSummand f h (ThetaTrial.zetaZeroEquivXiZeros ρ) := by
    funext ρ
    exact zeroTerm_weilTest_eq_spectral hf hh ρ
  rw [he] at hs heq
  constructor
  · rw [← ThetaTrial.zetaZeroEquivXiZeros.summable_iff]
    exact hs
  · unfold fullPairing spectralPairing
    rw [heq]
    exact ThetaTrial.zetaZeroEquivXiZeros.tsum_eq (spectralSummand f h)

/-- The radical property, under weighted Fourier integrability, divisibility by
`Xi`, and the approximation conditions above. -/
theorem fullPairing_radical_of_dominated_approximation
    {F h : ℝ → ℂ} {m : ℂ → ℂ} {ks : ℕ → ℝ → ℂ}
    (hfactor : ∀ z, paperFourier F z = ThetaTrial.Xi z * m z)
    (hF : ∀ z : ThetaTrial.XiZeros, FourierIntegrableAt F z)
    (hh : ∀ z : ThetaTrial.XiZeros, FourierIntegrableAt h (conj (z : ℂ)))
    (ha : DominatedWeilApproximation (Zeta23.EF.weilTest F h) ks) :
    fullPairing F h = 0 := by
  rw [(fullPairing_dominated_sampling hF hh ha).2]
  exact spectralPairing_eq_zero_of_factor hfactor h

/-- The truncation identity for the window part and the complementary tail,
given the approximation data above. For the theta density these data are
constructed in `RadicalApproximation` and `RadicalCorrelation`. -/
theorem fullQuadratic_hardCutoff_of_dominated_approximations
    {a : ℝ} {F : ℝ → ℂ} {m : ℂ → ℂ} {ks kt : ℕ → ℝ → ℂ}
    (hfactor : ∀ z, paperFourier F z = ThetaTrial.Xi z * m z)
    (hint : ∀ z : ThetaTrial.XiZeros,
      FourierIntegrableAt F z ∧ FourierIntegrableAt F (conj (z : ℂ)))
    (hw : DominatedWeilApproximation
      (Zeta23.EF.weilTest (window a F) (window a F)) ks)
    (ht : DominatedWeilApproximation
      (Zeta23.EF.weilTest (tail a F) (tail a F)) kt) :
    fullQuadratic (window a F) = fullQuadratic (tail a F) := by
  have hwq := (fullPairing_dominated_sampling
    (fun z => (hint z).1.window a) (fun z => (hint z).2.window a) hw).2
  have htq := (fullPairing_dominated_sampling
    (fun z => (hint z).1.tail a) (fun z => (hint z).2.tail a) ht).2
  exact hwq.trans ((spectral_hardCutoff_support hfactor hint).trans htq.symm)

/-- The same truncation identity, written for the real-valued expression
gamma term plus poles minus primes. -/
theorem paperForm_hardCutoff_of_dominated_approximations
    {a : ℝ} {F : ℝ → ℂ} {m : ℂ → ℂ} {ks kt : ℕ → ℝ → ℂ}
    (hfactor : ∀ z, paperFourier F z = ThetaTrial.Xi z * m z)
    (hint : ∀ z : ℂ, FourierIntegrableAt F z)
    (hw : DominatedWeilApproximation
      (Zeta23.EF.weilTest (window a F) (window a F)) ks)
    (ht : DominatedWeilApproximation
      (Zeta23.EF.weilTest (tail a F) (tail a F)) kt) :
    ThetaTrial.Paper.fullWeilForm (ThetaTrial.Paper.windowCut a F) =
      ThetaTrial.Paper.fullWeilForm (ThetaTrial.Paper.exteriorTail a F) := by
  have h := fullQuadratic_hardCutoff_of_dominated_approximations hfactor
    (fun z => ⟨hint z, hint (conj (z : ℂ))⟩) hw ht
  rw [fullQuadratic_eq_paperForm (fun z => (hint z).window a),
    fullQuadratic_eq_paperForm (fun z => (hint z).tail a)] at h
  exact Complex.ofReal_injective h

/-- Exponential integrability of the paper's full theta density. -/
theorem theta_fourier_integrable (z : ℂ) :
    FourierIntegrableAt (fun u => (ThetaTrial.Paper.thetaDensity u : ℂ)) z :=
  ThetaTrial.Paper.paperFourier_theta_integrable z

/-- Uses the representation of xi as an integral of the theta density. -/
theorem theta_fourier (z : ℂ) :
    paperFourier (fun u => (ThetaTrial.Paper.thetaDensity u : ℂ)) z = ThetaTrial.Xi z := by
  rw [paperFourier_eq_paper, ThetaTrial.Paper.paperFourier_theta,
    ThetaTrial.Paper.xiFunction_eq_weilFormula]

/-- Unconditional spectral radical statement for the full theta
density. Transferring it to the arithmetic form still needs the explicit
noncompact approximation estimates. -/
theorem theta_spectral_radical (h : ℝ → ℂ) :
    spectralPairing (fun u => (ThetaTrial.Paper.thetaDensity u : ℂ)) h = 0 := by
  apply spectralPairing_eq_zero_of_factor (m := fun _ => 1)
  intro z
  simpa only [mul_one] using theta_fourier z

theorem theta_spectral_hardCutoff (a : ℝ) :
    spectralPairing (window a (fun u => (ThetaTrial.Paper.thetaDensity u : ℂ)))
        (window a (fun u => (ThetaTrial.Paper.thetaDensity u : ℂ))) =
      spectralPairing (tail a (fun u => (ThetaTrial.Paper.thetaDensity u : ℂ)))
        (tail a (fun u => (ThetaTrial.Paper.thetaDensity u : ℂ))) := by
  apply spectral_hardCutoff_support (m := fun _ => 1)
  · intro z
    simpa only [mul_one] using theta_fourier z
  · intro z
    exact ⟨theta_fourier_integrable z, theta_fourier_integrable (conj (z : ℂ))⟩

/-- The truncation identity for the theta density, under the approximation
conditions above. The unconditional version is `RadicalCutoff.theta_hardCutoff`. -/
theorem theta_paperForm_hardCutoff_of_dominated_approximations
    {a : ℝ} {ks kt : ℕ → ℝ → ℂ}
    (hw : DominatedWeilApproximation
      (Zeta23.EF.weilTest (window a (fun u => (ThetaTrial.Paper.thetaDensity u : ℂ)))
        (window a (fun u => (ThetaTrial.Paper.thetaDensity u : ℂ)))) ks)
    (ht : DominatedWeilApproximation
      (Zeta23.EF.weilTest (tail a (fun u => (ThetaTrial.Paper.thetaDensity u : ℂ)))
        (tail a (fun u => (ThetaTrial.Paper.thetaDensity u : ℂ)))) kt) :
    ThetaTrial.Paper.fullWeilForm
        (ThetaTrial.Paper.windowCut a (fun u => (ThetaTrial.Paper.thetaDensity u : ℂ))) =
      ThetaTrial.Paper.fullWeilForm
        (ThetaTrial.Paper.exteriorTail a (fun u => (ThetaTrial.Paper.thetaDensity u : ℂ))) := by
  apply paperForm_hardCutoff_of_dominated_approximations (m := fun _ => 1)
    _ theta_fourier_integrable hw ht
  intro z
  simpa only [mul_one] using theta_fourier z

/-- Hermitian expansion at a vector in the radical (algebra only). -/
theorem hermitian_truncation_support {V : Type*} [AddCommGroup V]
    (B : V → V → ℂ)
    (hsub_left : ∀ x y z, B (x - y) z = B x z - B y z)
    (hsub_right : ∀ x y z, B x (y - z) = B x y - B x z)
    (hherm : ∀ x y, B y x = conj (B x y))
    (F t : V) (hFF : B F F = 0) (hFt : B F t = 0) :
    B (F - t) (F - t) = B t t := by
  rw [hsub_left, hsub_right, hsub_right, hFF, hFt, hherm F t]
  simp [hFt]

end ThetaTrial.Paper.Radical

#print axioms ThetaTrial.weil_compact_formula
#print axioms ThetaTrial.Paper.Radical.fullWeil_compact
#print axioms ThetaTrial.Paper.Radical.hermitian_truncation_support
#print axioms ThetaTrial.Paper.Radical.fullWeil_of_dominated_approximation
#print axioms ThetaTrial.Paper.Radical.fullQuadratic_hardCutoff_of_dominated_approximations
#print axioms ThetaTrial.Paper.Radical.fullQuadratic_eq_paperForm
#print axioms ThetaTrial.Paper.Radical.theta_spectral_radical
#print axioms ThetaTrial.Paper.Radical.theta_paperForm_hardCutoff_of_dominated_approximations
