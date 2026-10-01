import ThetaTrial.FourierNormalization
import ThetaTrial.WeilInputs

/-!
# The arithmetic side of the explicit formula

The pole, gamma and prime expression, as a complex number, so that the
explicit formula can be stated before taking real parts.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ThetaTrial.WeilFormula

open Complex MeasureTheory Set
open scoped ComplexConjugate ArithmeticFunction Convolution
open ThetaTrial.FourierNormalization

/-- The translation correlation, linear in the first argument. -/
def correlation (f : ℝ → ℂ) (h : ℝ) : ℂ :=
  ∫ u : ℝ, f (u + h) * conj (f u)

/-- An exponential moment; the two pole terms use `b = ±1/2`. -/
def poleMoment (f : ℝ → ℂ) (b : ℝ) : ℂ :=
  ∫ u : ℝ, f u * (Real.exp (b * u) : ℂ)

theorem weilTest_eq_correlation (f : ℝ → ℂ) (h : ℝ) :
    Zeta23.EF.weilTest f f h = correlation f h := by
  simp only [Zeta23.EF.weilTest, convolution_def, ContinuousLinearMap.mul_apply',
    Zeta23.EF.tilde, neg_sub]
  rw [← integral_add_right_eq_self (fun t : ℝ => f t * conj (f (t - h))) h]
  simp only [add_sub_cancel_right, correlation]

theorem correlation_neg (f : ℝ → ℂ) (h : ℝ) :
    correlation f (-h) = conj (correlation f h) := by
  unfold correlation
  rw [← integral_conj]
  rw [← integral_sub_right_eq_self (fun u : ℝ => conj (f (u + h) * conj (f u))) h]
  apply integral_congr_ae
  filter_upwards with u
  simp only [sub_add_cancel, map_mul, conj_conj, ← sub_eq_add_neg]
  ring

theorem weilTest_add_neg (f : ℝ → ℂ) (h : ℝ) :
    Zeta23.EF.weilTest f f h + Zeta23.EF.weilTest f f (-h) =
      (2 : ℂ) * ((correlation f h).re : ℂ) := by
  rw [weilTest_eq_correlation, weilTest_eq_correlation, correlation_neg, Complex.add_conj]
  push_cast
  rfl

theorem paperFT_imag_eq_poleMoment (f : ℝ → ℂ) (b : ℝ) :
    Zeta23.paperFT f (I * b) = poleMoment f (-b) := by
  unfold Zeta23.paperFT poleMoment
  apply integral_congr_ae
  filter_upwards with u
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  calc
    I * (I * b) * u = (I * I) * (b * u) := by ring
    _ = -b * u := by rw [I_mul_I]; ring

theorem pole_pair (f : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    Zeta23.paperFT (Zeta23.EF.weilTest f f) (I / 2) +
        Zeta23.paperFT (Zeta23.EF.weilTest f f) (-I / 2) =
      2 * ((poleMoment f (1 / 2) * conj (poleMoment f (-1 / 2))).re : ℂ) := by
  rw [Zeta23.EF.paperFT_weilTest hf hf hfc hfc,
    Zeta23.EF.paperFT_weilTest hf hf hfc hfc]
  have hp : Zeta23.paperFT f (I / 2) = poleMoment f (-1 / 2) := by
    have he : I * ((1 / 2 : ℝ) : ℂ) = I / 2 := by push_cast; ring
    simpa only [he, neg_div] using paperFT_imag_eq_poleMoment f (1 / 2)
  have hm : Zeta23.paperFT f (-I / 2) = poleMoment f (1 / 2) := by
    have he : I * ((-1 / 2 : ℝ) : ℂ) = -I / 2 := by push_cast; ring
    have hb : -(-1 / 2 : ℝ) = 1 / 2 := by ring
    simpa only [he, hb] using paperFT_imag_eq_poleMoment f (-1 / 2)
  simp only [map_div₀, conj_I, map_ofNat, map_neg, neg_neg, hp, hm]
  have h := Complex.add_conj (poleMoment f (1 / 2) * conj (poleMoment f (-1 / 2)))
  simpa only [map_mul, conj_conj, add_comm, mul_comm, Complex.ofReal_mul,
    Complex.ofReal_ofNat] using h

/-- The full arithmetic expression; it includes the (harmless) prime term at the
endpoint of the support. -/
def fullForm (a : ℝ) (f : ℝ → ℂ) : ℂ :=
  (∫ t : ℝ, (Zeta23.EF.gammaBracket t : ℂ) *
      (Complex.normSq (fourier f t) : ℂ))
  - 2 * ∑ n ∈ Finset.Ioc 0 ⌊Real.exp (2 * a)⌋₊,
      ((Λ n / Real.sqrt n : ℝ) : ℂ) * ((correlation f (Real.log n)).re : ℂ)
  + 2 * ((poleMoment f (1 / 2) * conj (poleMoment f (-1 / 2))).re : ℂ)

theorem gammaBracket_eq_two_pi_mu (t : ℝ) :
    Zeta23.EF.gammaBracket t = 2 * Real.pi * Zeta23.mu t := by
  unfold Zeta23.EF.gammaBracket Zeta23.mu
  field_simp

theorem gammaBracket_neg (t : ℝ) :
    Zeta23.EF.gammaBracket (-t) = Zeta23.EF.gammaBracket t := by
  rw [gammaBracket_eq_two_pi_mu, Zeta23.gammaFacts.even, ← gammaBracket_eq_two_pi_mu]

theorem weilTest_fourier_real (f : ℝ → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (t : ℝ) :
    Zeta23.paperFT (Zeta23.EF.weilTest f f) t =
      (2 * Real.pi : ℂ) * (Complex.normSq (fourier f (-t)) : ℂ) := by
  rw [Zeta23.EF.paperFT_weilTest hf hf hfc hfc, paperFT_pair_eq]
  simp only [map_neg, conj_ofReal, Complex.mul_conj]

theorem gamma_integral (f : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    (1 / (2 * Real.pi) : ℂ) *
        (∫ t : ℝ, Zeta23.paperFT (Zeta23.EF.weilTest f f) t *
          (Zeta23.EF.gammaBracket t : ℂ)) =
      ∫ t : ℝ, (Zeta23.EF.gammaBracket t : ℂ) *
        (Complex.normSq (fourier f t) : ℂ) := by
  calc
    _ = ∫ t : ℝ, (Complex.normSq (fourier f (-t)) : ℂ) *
        (Zeta23.EF.gammaBracket t : ℂ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      rw [weilTest_fourier_real f hf hfc]
      field_simp
    _ = ∫ t : ℝ, (Complex.normSq (fourier f (-(-t : ℝ))) : ℂ) *
        (Zeta23.EF.gammaBracket (-t) : ℂ) :=
      (integral_neg_eq_self _ volume).symm
    _ = _ := by
      simp only [Complex.ofReal_neg, neg_neg, gammaBracket_neg, mul_comm]

theorem gamma_integrable {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    Integrable (fun t : ℝ => (Zeta23.EF.gammaBracket t : ℂ) *
      (Complex.normSq (fourier f t) : ℂ)) := by
  have hk := Zeta23.EF.weilTest_contDiff hf hf.continuous hfc
  have hkc := Zeta23.EF.weilTest_hasCompactSupport hfc hfc
  have h := ThetaTrial.weil_archimedean_integrable hk hkc
  have he : (fun t : ℝ => Zeta23.paperFT (Zeta23.EF.weilTest f f) t * (Zeta23.mu t : ℂ)) =
      fun t : ℝ => (Zeta23.EF.gammaBracket t : ℂ) *
        (Complex.normSq (fourier f (-t)) : ℂ) := by
    funext t
    rw [weilTest_fourier_real f hf.continuous hfc, gammaBracket_eq_two_pi_mu]
    push_cast
    ring
  rw [he] at h
  have hn := h.comp_neg
  simpa only [gammaBracket_neg, Complex.ofReal_neg, neg_neg] using hn

theorem literatureRHS_eq_fullForm {a : ℝ} {f : ℝ → ℂ} (hf : Continuous f)
    (hfs : tsupport f ⊆ Icc (-a) a) :
    Zeta23.EF.literatureRHS (Zeta23.EF.weilTest f f) = fullForm a f := by
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  have hs : tsupport f ⊆ Icc (-((2 * a) / 2)) ((2 * a) / 2) := by
    simpa only [mul_div_cancel_left₀ a (two_ne_zero : (2 : ℝ) ≠ 0)] using hfs
  have hks := Zeta23.EF.tsupport_weilTest_subset hs hs
  have hprime : (∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) *
        (Zeta23.EF.weilTest f f (Real.log n) + Zeta23.EF.weilTest f f (-Real.log n))) =
      2 * ∑ n ∈ Finset.Ioc 0 ⌊Real.exp (2 * a)⌋₊,
        ((Λ n / Real.sqrt n : ℝ) : ℂ) * ((correlation f (Real.log n)).re : ℂ) := by
    rw [tsum_eq_sum (s := Finset.Ioc 0 ⌊Real.exp (2 * a)⌋₊)
      (fun n hn => Zeta23.EF.prime_summand_eq_zero hks hn)]
    simp_rw [weilTest_add_neg]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  unfold Zeta23.EF.literatureRHS fullForm
  rw [pole_pair f hf hfc, hprime, gamma_integral f hf hfc]
  ring

end ThetaTrial.WeilFormula
