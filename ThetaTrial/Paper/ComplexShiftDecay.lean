import ThetaTrial.Paper.ComplexShiftPolynomial

/-! Uniform double-exponential decay, including every derivative and
arbitrary polynomial differential operators, for finite complex shift measures. -/

noncomputable section
open Complex MeasureTheory Set Polynomial
open scoped ComplexConjugate

namespace ThetaTrial.Paper.ComplexShiftMeasure
open ShiftMeasure

theorem shiftJet_bound_from_strip (ν : Measure ℝ) [IsFiniteMeasure ν]
    {b C c : ℝ} (j : ℕ)
    (hbnd : ∀ z : ℂ, |z.im| ≤ b → ‖iteratedDeriv j complexThetaDensity z‖ ≤
      C * Real.exp (((9 / 2 : ℝ) + 2 * (j : ℝ)) * |z.re|) *
        Real.exp (-c * Real.exp (2 * |z.re|))) (u : ℝ) :
    ‖shiftJet ν b j (u : ℂ)‖ ≤
      (C * (ν.restrict (Icc (-b) b)).real univ) *
        ThetaTrial.ThetaSeries.doubleExpEnvelope ((9 / 2 : ℝ) + 2 * (j : ℝ)) c |u| := by
  have hh : ∀ᵐ (y : ℝ) ∂ν.restrict (Icc (-b) b),
      ‖iteratedDeriv j complexThetaDensity ((u : ℂ) + I * (y : ℂ))‖ ≤
        C * ThetaTrial.ThetaSeries.doubleExpEnvelope ((9 / 2 : ℝ) + 2 * (j : ℝ)) c |u| := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have he := hbnd ((u : ℂ) + I * (y : ℂ)) (by simpa [Complex.mul_im] using abs_le.mpr hy)
    simpa only [ThetaTrial.ThetaSeries.doubleExpEnvelope, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, add_zero, mul_assoc] using he
  have h := norm_integral_le_of_norm_le_const hh
  change ‖shiftJet ν b j (u : ℂ)‖ ≤
    (C * ThetaTrial.ThetaSeries.doubleExpEnvelope ((9 / 2 : ℝ) + 2 * (j : ℝ)) c |u|) *
      (ν.restrict (Icc (-b) b)).real univ at h
  convert h using 1 <;> ring

theorem jet_norm_le_four (μ : ComplexMeasure ℝ) (b : ℝ) (j : ℕ) (z : ℂ) :
    ‖jet μ b j z‖ ≤
      (‖shiftJet μ.re.toJordanDecomposition.posPart b j z‖ +
        ‖shiftJet μ.re.toJordanDecomposition.negPart b j z‖) +
      (‖shiftJet μ.im.toJordanDecomposition.posPart b j z‖ +
        ‖shiftJet μ.im.toJordanDecomposition.negPart b j z‖) := by
  rw [jet_eq]
  have h := norm_add_le
    (shiftJet μ.re.toJordanDecomposition.posPart b j z -
      shiftJet μ.re.toJordanDecomposition.negPart b j z)
    (I * (shiftJet μ.im.toJordanDecomposition.posPart b j z -
      shiftJet μ.im.toJordanDecomposition.negPart b j z))
  simp only [norm_mul, norm_I, one_mul] at h
  exact h.trans (add_le_add (norm_sub_le _ _) (norm_sub_le _ _))

theorem jet_doubleExp_decay (μ : ComplexMeasure ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) :
    ∃ c > 0, ∀ j : ℕ, ∃ C > 0, ∀ u : ℝ,
      ‖jet μ b j (u : ℂ)‖ ≤ C *
        ThetaTrial.ThetaSeries.doubleExpEnvelope ((9 / 2 : ℝ) + 2 * (j : ℝ)) c |u| := by
  obtain ⟨c, hc, hder⟩ := complexThetaDensity_iteratedDeriv_closed_strip_decay hb hbpi
  refine ⟨c, hc, ?_⟩
  intro j
  obtain ⟨C, hC, hbound⟩ := hder j
  let m₁ := (μ.re.toJordanDecomposition.posPart.restrict (Icc (-b) b)).real univ
  let m₂ := (μ.re.toJordanDecomposition.negPart.restrict (Icc (-b) b)).real univ
  let m₃ := (μ.im.toJordanDecomposition.posPart.restrict (Icc (-b) b)).real univ
  let m₄ := (μ.im.toJordanDecomposition.negPart.restrict (Icc (-b) b)).real univ
  have hm₁ : 0 ≤ m₁ := ENNReal.toReal_nonneg
  have hm₂ : 0 ≤ m₂ := ENNReal.toReal_nonneg
  have hm₃ : 0 ≤ m₃ := ENNReal.toReal_nonneg
  have hm₄ : 0 ≤ m₄ := ENNReal.toReal_nonneg
  refine ⟨C * (m₁ + m₂ + (m₃ + m₄) + 1), by positivity, ?_⟩
  intro u
  have he : 0 ≤ ThetaTrial.ThetaSeries.doubleExpEnvelope ((9 / 2 : ℝ) + 2 * (j : ℝ)) c |u| := by
    unfold ThetaTrial.ThetaSeries.doubleExpEnvelope
    positivity
  have h₁ := shiftJet_bound_from_strip μ.re.toJordanDecomposition.posPart j hbound u
  have h₂ := shiftJet_bound_from_strip μ.re.toJordanDecomposition.negPart j hbound u
  have h₃ := shiftJet_bound_from_strip μ.im.toJordanDecomposition.posPart j hbound u
  have h₄ := shiftJet_bound_from_strip μ.im.toJordanDecomposition.negPart j hbound u
  have hs := jet_norm_le_four μ b j (u : ℂ)
  dsimp only [m₁, m₂, m₃, m₄] at *
  nlinarith

theorem polynomial_iteratedDeriv (μ : ComplexMeasure ℝ) {b : ℝ}
    (hbpi : b < Real.pi / 4) (P : ℂ[X]) (r : ℕ) :
    iteratedDeriv r (polynomialDerivative P (fun u : ℝ => source μ b (u : ℂ))) =
      fun u : ℝ => ∑ j ∈ P.support, (P.coeff j * (-I) ^ j) * jet μ b (j + r) (u : ℂ) := by
  induction r with
  | zero =>
    funext u
    simp only [iteratedDeriv_zero, polynomialDerivative, differentialOperator_iterate,
      source_real_iteratedDeriv μ hbpi, Nat.add_zero, mul_assoc]
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    have hd := HasDerivAt.fun_sum (u := P.support) (fun j _hj =>
      ((jet_hasDerivAt μ (real_mem_shiftStrip hbpi u) (j + r)).comp_ofReal).const_mul
        (P.coeff j * (-I) ^ j))
    simpa only [Nat.add_assoc] using hd.deriv

theorem polynomial_all_derivatives_doubleExp_decay (μ : ComplexMeasure ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) (P : ℂ[X]) :
    ∃ c > 0, ∀ r : ℕ, ∃ C > 0, ∀ u : ℝ,
      ‖iteratedDeriv r (polynomialDerivative P (fun v : ℝ => source μ b (v : ℂ))) u‖ ≤
        C * ThetaTrial.ThetaSeries.doubleExpEnvelope
          ((9 / 2 : ℝ) + 2 * ((P.natDegree + r : ℕ) : ℝ)) c |u| := by
  obtain ⟨c, hc, hder⟩ := jet_doubleExp_decay μ hb hbpi
  choose C hC hbound using hder
  refine ⟨c, hc, ?_⟩
  intro r
  let K := ∑ j ∈ P.support, ‖P.coeff j * (-I) ^ j‖ * C (j + r)
  have hK : 0 ≤ K := Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (hC _).le)
  refine ⟨K + 1, by positivity, ?_⟩
  intro u
  rw [polynomial_iteratedDeriv μ hbpi P r]
  let E := ThetaTrial.ThetaSeries.doubleExpEnvelope
    ((9 / 2 : ℝ) + 2 * ((P.natDegree + r : ℕ) : ℝ)) c |u|
  have hE : 0 ≤ E := by unfold E ThetaTrial.ThetaSeries.doubleExpEnvelope; positivity
  have henv (j : ℕ) (hj : j ∈ P.support) :
      ThetaTrial.ThetaSeries.doubleExpEnvelope (9 / 2 + 2 * ((j + r : ℕ) : ℝ)) c |u| ≤ E := by
    have hjd : j ≤ P.natDegree := Polynomial.le_natDegree_of_mem_supp j hj
    unfold E ThetaTrial.ThetaSeries.doubleExpEnvelope
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg u)
    have hjr : ((j + r : ℕ) : ℝ) ≤ ((P.natDegree + r : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hjd r
    linarith
  calc
    _ ≤ ∑ j ∈ P.support, ‖(P.coeff j * (-I) ^ j) * jet μ b (j + r) (u : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ P.support, (‖P.coeff j * (-I) ^ j‖ * C (j + r)) * E := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        ((hbound (j + r) u).trans (mul_le_mul_of_nonneg_left (henv j hj) (hC _).le))
        (norm_nonneg _)
    _ = K * E := (Finset.sum_mul ..).symm
    _ ≤ (K + 1) * E := mul_le_mul_of_nonneg_right (by linarith) hE

end ThetaTrial.Paper.ComplexShiftMeasure

#print axioms ThetaTrial.Paper.ComplexShiftMeasure.polynomial_all_derivatives_doubleExp_decay
