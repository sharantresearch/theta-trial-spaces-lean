import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
# Positive-integer endpoints of Gauss' digamma integral

These statements concern mathlib's logarithmic derivative of Gamma.
The integer values follow from Gamma's proved recurrence and the proved
value at one. The integral is a finite sum of decaying exponentials; all
integrability assertions are proved explicitly. No infinite-series or
Fubini argument is used in this endpoint module.
-/

noncomputable section

namespace ThetaTrial.DigammaIntegral

open Complex Set MeasureTheory

/-- Digamma at every positive integer. -/
theorem digamma_nat_add_one (m : ℕ) :
    Complex.digamma ((m : ℂ) + 1) = (harmonic m : ℂ) -
      (Real.eulerMascheroniConstant : ℂ) := by
  induction m with
  | zero => simp [Complex.digamma_one]
  | succ m ih =>
    have hp : ∀ n : ℕ, (m : ℂ) + 1 ≠ -n := by
      intro n hn
      have h := congrArg Complex.re hn
      simp only [add_re, natCast_re, one_re, neg_re] at h
      have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith
    simp only [Nat.cast_add, Nat.cast_one]
    rw [Complex.digamma_apply_add_one _ hp, ih, harmonic_succ]
    push_cast
    ring

/-- A single decaying exponential is integrable on the positive half-line. -/
theorem integer_exp_integrable (j : ℕ) :
    IntegrableOn (fun t : ℝ => Complex.exp (-((j : ℂ) + 1) * (t : ℂ)))
      (Ioi (0 : ℝ)) := by
  apply integrableOn_exp_mul_complex_Ioi
  simp only [neg_re, add_re, natCast_re, one_re]
  linarith [Nat.cast_nonneg (α := ℝ) j]

/-- Its improper integral is the exact reciprocal integer. -/
theorem integer_exp_integral (j : ℕ) :
    (∫ t : ℝ in Ioi (0 : ℝ), Complex.exp (-((j : ℂ) + 1) * (t : ℂ))) =
      ((j : ℂ) + 1)⁻¹ := by
  rw [integral_exp_mul_complex_Ioi (by
    simp only [neg_re, add_re, natCast_re, one_re]
    linarith [Nat.cast_nonneg (α := ℝ) j])]
  simp only [ofReal_zero, mul_zero, exp_zero, neg_div_neg_eq, one_div]

/-- The Gauss kernel at a positive integer is exactly a finite geometric sum
away from its removable endpoint at zero. -/
theorem integer_gauss_kernel (m : ℕ) {t : ℝ} (ht : 0 < t) :
    (Complex.exp (-(t : ℂ)) - Complex.exp (-((m : ℂ) + 1) * (t : ℂ))) /
        (1 - Complex.exp (-(t : ℂ))) =
      ∑ j ∈ Finset.range m, Complex.exp (-((j : ℂ) + 1) * (t : ℂ)) := by
  have he : Complex.exp (-(t : ℂ)) ≠ 1 := by
    have hn : ‖Complex.exp (-(t : ℂ))‖ < 1 := by
      rw [Complex.norm_exp]
      simpa using Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)
    intro h
    simp [h] at hn
  have hd : 1 - Complex.exp (-(t : ℂ)) ≠ 0 := sub_ne_zero.mpr he.symm
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [Nat.cast_add, Nat.cast_one]
    have hs : Complex.exp (-(((m : ℂ) + 1) + 1) * (t : ℂ)) =
        Complex.exp (-((m : ℂ) + 1) * (t : ℂ)) * Complex.exp (-(t : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [hs]
    field_simp
    ring

/-- The exact convergent finite geometric integral equals the harmonic number. -/
theorem integer_gauss_integral_eq_harmonic (m : ℕ) :
    (∫ t : ℝ in Ioi (0 : ℝ),
      (Complex.exp (-(t : ℂ)) - Complex.exp (-((m : ℂ) + 1) * (t : ℂ))) /
        (1 - Complex.exp (-(t : ℂ)))) = (harmonic m : ℂ) := by
  calc
    _ = ∫ t : ℝ in Ioi (0 : ℝ), ∑ j ∈ Finset.range m,
        Complex.exp (-((j : ℂ) + 1) * (t : ℂ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact integer_gauss_kernel m ht
    _ = ∑ j ∈ Finset.range m, ((j : ℂ) + 1)⁻¹ := by
      rw [integral_finsetSum _ (fun j _ => integer_exp_integrable j)]
      simp only [integer_exp_integral]
    _ = (harmonic m : ℂ) := by
      simp [harmonic]

/-- Gauss' digamma integral at all positive integers, including one. -/
theorem integer_gauss_integral (m : ℕ) :
    Complex.digamma ((m : ℂ) + 1) + (Real.eulerMascheroniConstant : ℂ) =
      ∫ t : ℝ in Ioi (0 : ℝ),
        (Complex.exp (-(t : ℂ)) - Complex.exp (-((m : ℂ) + 1) * (t : ℂ))) /
          (1 - Complex.exp (-(t : ℂ))) := by
  rw [integer_gauss_integral_eq_harmonic, digamma_nat_add_one]
  ring

end ThetaTrial.DigammaIntegral
