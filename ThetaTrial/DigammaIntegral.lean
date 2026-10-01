import ThetaTrial.DigammaInputs
import ThetaTrial.DigammaIntegral.Series
import ThetaTrial.DigammaIntegral.IntegerValues

/-!
# Gauss' integral for the digamma function

The integral is a complex Bochner integral over the positive real half-line.
Its integrability is proved independently of its evaluation. The infinite
geometric expansion has a summable sequence of integral norms; positive
integer values are supplied by the finite Gamma-recurrence argument.
-/

open Set MeasureTheory

namespace ThetaTrial.DigammaIntegral

noncomputable def gaussKernel (z : ℂ) (t : ℝ) : ℂ :=
  (Complex.exp (-(t : ℂ)) - Complex.exp (-z * (t : ℂ))) /
    (1 - Complex.exp (-(t : ℂ)))

theorem gaussKernel_eq_shifted_sub (z : ℂ) {t : ℝ} (ht : 0 < t) :
    gaussKernel z t = shiftedKernel z t - Complex.exp (-z * (t : ℂ)) := by
  unfold gaussKernel shiftedKernel
  field_simp [one_sub_cexp_neg_ne_zero ht]
  ring

/-- Integrability, including the cancellation at the origin. -/
theorem gaussKernel_integrable {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (gaussKernel z) (Ioi 0) := by
  have he : IntegrableOn (fun t : ℝ => Complex.exp (-z * (t : ℂ))) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hz) 0
  have h : IntegrableOn (fun t : ℝ => shiftedKernel z t - Complex.exp (-z * (t : ℂ)))
      (Ioi 0) := (shiftedKernel_integrable hz.le).sub he
  apply h.congr_fun _ measurableSet_Ioi
  intro t ht
  exact (gaussKernel_eq_shifted_sub z ht).symm

theorem integral_gaussKernel_eq_tsum {z : ℂ} (hz : 0 < z.re) :
    (∫ t : ℝ in Ioi 0, gaussKernel z t) =
      -1 / z + ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
  have hneg : (-z).re < 0 := by simpa using neg_neg_of_pos hz
  calc
    _ = ∫ t : ℝ in Ioi 0, shiftedKernel z t - Complex.exp (-z * (t : ℂ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact gaussKernel_eq_shifted_sub z ht
    _ = (∫ t : ℝ in Ioi 0, shiftedKernel z t) - 1 / z := by
      rw [integral_sub (shiftedKernel_integrable hz.le)
        (integrableOn_exp_mul_complex_Ioi hneg 0), integral_exp_mul_complex_Ioi hneg]
      simp
    _ = _ := by rw [integral_shiftedKernel_eq_tsum hz.le]; ring

/-- Evaluation first on the precise domain of the imported partial fractions. -/
theorem gauss_integral_of_noninteger {z : ℂ} (hz : 0 < z.re)
    (hi : z ∈ Complex.integerComplement) :
    Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) =
      ∫ t : ℝ in Ioi 0, gaussKernel z t := by
  rw [integral_gaussKernel_eq_tsum hz, ThetaTrial.digamma_partial_fractions hi]
  ring

/-- Gauss' formula for the digamma at every point of the open right half-plane. -/
theorem gauss_integral {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) =
      ∫ t : ℝ in Ioi 0, gaussKernel z t := by
  by_cases hi : z ∈ Complex.integerComplement
  · exact gauss_integral_of_noninteger hz hi
  · simp only [Complex.mem_integerComplement_iff, not_not] at hi
    obtain ⟨k, rfl⟩ := hi
    cases k with
    | ofNat n =>
      cases n with
      | zero => simp at hz
      | succ n =>
        simpa [gaussKernel, Int.ofNat_eq_natCast] using
          integer_gauss_integral n
    | negSucc n =>
      simp only [Int.cast_negSucc, Complex.neg_re, Complex.natCast_re] at hz
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      linarith

end ThetaTrial.DigammaIntegral
