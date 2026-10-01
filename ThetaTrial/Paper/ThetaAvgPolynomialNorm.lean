import ThetaTrial.Paper.PolynomialCoefficientBounds
import ThetaTrial.Paper.ThetaKernel
import ThetaTrial.Paper.Multiplier
import ThetaTrial.Paper.TrialFourier
import ThetaTrial.Paper.LogUncertainty
import ThetaTrial.Paper.ThetaAvgPolynomialRegularity

/-! Uniform Fourier lower bounds for the polynomial trial family. The
constants come from a fixed interval around `0` on which `Xi` does not vanish. -/

noncomputable section
open Complex MeasureTheory Set Polynomial
open scoped FourierTransform

namespace ThetaTrial.Paper

theorem paperFourier_squared_integrable {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2) :
    Integrable (fun r : ℝ => ‖paperFourier f (r : ℂ)‖^2) := by
  simpa only [paperFourier_eq_mathlib, LogUncertainty.paperFourier] using
    ((LogUncertainty.ordinary_fourier_memLp hf hf2).integrable_norm_pow
      (by norm_num : (2 : ℕ) ≠ 0)).comp_div (by positivity : 2 * Real.pi ≠ 0)

theorem paperFourier_squared_integral {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2) :
    (∫ r : ℝ, ‖paperFourier f (r : ℂ)‖^2) = 2 * Real.pi * squaredNorm f := by
  simpa only [paperFourier_eq_mathlib, LogUncertainty.paperFourier, squaredNorm] using
    LogUncertainty.paperFourier_mass hf hf2

theorem thetaAvg_polynomial_norm_from_factorization
    {a d c : ℝ} (hd : 0 < d) (hc : 0 < c) (hZ : 16 ≤ scaleZ a)
    (hxi : ∀ r : ℝ, |r| ≤ d → c ≤ ‖xiFunction (r : ℂ)‖)
    (P : ℂ[X]) {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2)
    (hF : ∀ r : ℝ, paperFourier f r =
      P.eval (r : ℂ) * xiFunction r * shiftMultiplier a r) :
    (c^2 * Real.exp (-2) / (2 * Real.pi)) / scaleZ a *
        CoefficientBounds.complexIntervalSqAt d P ≤ squaredNorm f := by
  have hz : 0 < scaleZ a := scaleZ_pos a
  have hroot : 0 < Real.sqrt (scaleZ a) := Real.sqrt_pos.mpr hz
  let b : ℝ := c * (Real.exp (-1) / Real.sqrt (scaleZ a))
  have hb : 0 < b := by dsimp [b]; positivity
  have hm (r : ℝ) : Real.exp (-1) / Real.sqrt (scaleZ a) ≤
      ‖shiftMultiplier a (r : ℂ)‖ :=
    (shiftMultiplier_zero_lower_sqrt hZ).trans
      ((shiftMultiplier_real_ge_zero_value a r).trans (Complex.re_le_norm _))
  have hp (r : ℝ) (hr : r ∈ Icc (-d) d) :
      b^2 * ‖P.eval (r : ℂ)‖^2 ≤ ‖paperFourier f r‖^2 := by
    have hx := hxi r (abs_le.mpr hr)
    have hh : b ≤ ‖xiFunction (r : ℂ)‖ * ‖shiftMultiplier a (r : ℂ)‖ :=
      mul_le_mul hx (hm r) (by positivity) (norm_nonneg _)
    have hmul := mul_le_mul_of_nonneg_left hh (norm_nonneg (P.eval (r : ℂ)))
    rw [hF, norm_mul, norm_mul]
    nlinarith [sq_nonneg (‖P.eval (r : ℂ)‖ *
      (‖xiFunction (r : ℂ)‖ * ‖shiftMultiplier a (r : ℂ)‖ - b))]
  have hi : IntegrableOn (fun r : ℝ => b^2 * ‖P.eval (r : ℂ)‖^2)
      (Icc (-d) d) := ContinuousOn.integrableOn_Icc (by fun_prop)
  have hfour := paperFourier_squared_integrable hf hf2
  have hint := setIntegral_mono_on hi hfour.integrableOn measurableSet_Icc hp
  have hsub : (∫ r in Icc (-d) d, ‖paperFourier f r‖^2) ≤
      ∫ r : ℝ, ‖paperFourier f r‖^2 :=
    setIntegral_le_integral hfour (ae_of_all _ (fun r => sq_nonneg _))
  have hpint : (∫ r in Icc (-d) d, b^2 * ‖P.eval (r : ℂ)‖^2) =
      b^2 * CoefficientBounds.complexIntervalSqAt d P := by
    rw [integral_const_mul, CoefficientBounds.complexIntervalSqAt,
      intervalIntegral.integral_of_le (by linarith : -d ≤ d), integral_Icc_eq_integral_Ioc]
  rw [hpint] at hint
  rw [paperFourier_squared_integral hf hf2] at hsub
  have hmain := hint.trans hsub
  have hb2 : b^2 = c^2 * Real.exp (-2) / scaleZ a := by
    dsimp [b]
    rw [mul_pow, div_pow, Real.sq_sqrt hz.le, ← Real.exp_nat_mul]
    norm_num
    ring
  rw [hb2] at hmain
  have hmain' : c^2 * Real.exp (-2) / scaleZ a *
      CoefficientBounds.complexIntervalSqAt d P ≤ squaredNorm f * (2 * Real.pi) := by
    simpa only [mul_comm (2 * Real.pi)] using hmain
  have hdiv := (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr hmain'
  calc
    _ = (c^2 * Real.exp (-2) / scaleZ a *
        CoefficientBounds.complexIntervalSqAt d P) / (2 * Real.pi) := by ring
    _ ≤ _ := hdiv

/-- One fixed interval and positive constant work for all degrees, coefficients,
and admissible averages. The only analytic inputs here are an L1/L2
function and its explicitly stated Fourier identity. -/
theorem thetaAvg_uniform_polynomial_norm_constants :
    ∃ d > 0, d ≤ 1 ∧ ∃ c > 0, ∃ A ≥ (1 : ℝ),
      (∀ k : ℕ, ∀ P : ℂ[X], P.natDegree ≤ k →
        (∑ j ∈ Finset.range (k+1), ‖P.coeff j‖) ≤
          A^(k+1) * Real.sqrt (CoefficientBounds.complexIntervalSqAt d P)) ∧
      ∀ a : ℝ, 16 ≤ scaleZ a → ∀ P : ℂ[X], ∀ f : ℝ → ℂ,
        Integrable f → MemLp f 2 →
        (∀ r : ℝ, paperFourier f r =
          P.eval (r : ℂ) * xiFunction r * shiftMultiplier a r) →
        c / scaleZ a * CoefficientBounds.complexIntervalSqAt d P ≤ squaredNorm f := by
  obtain ⟨d₀, hd₀, c₀, hc₀, hxi⟩ := xiFunction_fixed_lower_interval
  let d := min d₀ 1
  have hd : 0 < d := lt_min hd₀ (by norm_num)
  have hd1 : d ≤ 1 := min_le_right _ _
  obtain ⟨A, hA, hcoef⟩ := CoefficientBounds.uniform_interval_coefficient_bound hd hd1
  refine ⟨d, hd, hd1, c₀^2 * Real.exp (-2) / (2 * Real.pi), by positivity,
    A, hA, hcoef, ?_⟩
  intro a ha P f hf hf2 hF
  exact thetaAvg_polynomial_norm_from_factorization hd hc₀ ha
    (fun r hr => hxi r (hr.trans (min_le_left _ _))) P hf hf2 hF

theorem thetaAvg_polynomialFourier_real {a : ℝ} (ha : 0 ≤ a) (hZ : 16 ≤ scaleZ a)
    (P : ℂ[X]) (r : ℝ) :
    paperFourier (polynomialDerivative P (fun u : ℝ => shiftedAverage a u)) r =
      P.eval (r : ℂ) * xiFunction r * shiftMultiplier a r := by
  have hfi (j : ℕ) : Integrable (iteratedDeriv j
      (fun u : ℝ => shiftedAverage a u)) := by
    rw [shiftedAverage_real_iteratedDeriv_fun hZ]
    exact thetaAvgTrialDerivative_integrable ha hZ j
  rw [paperFourier_polynomialDerivative (shiftedAverage_real_contDiff hZ) hfi,
    paperFourier_shiftedAverage (ContourArcIdentity.shiftWidth_arc_bounds hZ).1]
  ring

/-- The same bounds, stated for functions. -/
theorem thetaAvg_polynomial_norm_constants :
    ∃ d > 0, d ≤ 1 ∧ ∃ c > 0, ∃ A ≥ (1 : ℝ),
      (∀ k : ℕ, ∀ P : ℂ[X], P.natDegree ≤ k →
        (∑ j ∈ Finset.range (k+1), ‖P.coeff j‖) ≤
          A^(k+1) * Real.sqrt (CoefficientBounds.complexIntervalSqAt d P)) ∧
      ∀ a : ℝ, 0 ≤ a → 16 ≤ scaleZ a → ∀ P : ℂ[X],
        c / scaleZ a * CoefficientBounds.complexIntervalSqAt d P ≤
          squaredNorm (polynomialDerivative P (fun u : ℝ => shiftedAverage a u)) := by
  obtain ⟨d, hd, hd1, c, hc, A, hA, hcoef, hnorm⟩ := thetaAvg_uniform_polynomial_norm_constants
  refine ⟨d, hd, hd1, c, hc, A, hA, hcoef, ?_⟩
  intro a ha hZ P
  exact hnorm a hZ P _ (polynomialDerivative_shiftedAverage_integrable ha hZ P)
    (polynomialDerivative_shiftedAverage_memLp_two ha hZ P)
    (thetaAvg_polynomialFourier_real ha hZ P)

theorem sum_norm_coeff_pos {k : ℕ} {P : ℂ[X]} (hP : P ≠ 0) (hdeg : P.natDegree ≤ k) :
    0 < ∑ j ∈ Finset.range (k+1), ‖P.coeff j‖ := by
  have hn : 0 < ‖P.coeff P.natDegree‖ := by
    rw [coeff_natDegree]
    exact norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hP)
  exact hn.trans_le (Finset.single_le_sum (fun j hj => norm_nonneg _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hdeg)))

theorem polynomial_intervalSq_pos {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    {P : ℂ[X]} (hP : P ≠ 0) : 0 < CoefficientBounds.complexIntervalSqAt d P := by
  obtain ⟨A, hA, hcoef⟩ := CoefficientBounds.uniform_interval_coefficient_bound hd hd1
  have hb := hcoef P.natDegree P le_rfl
  have hp := (sum_norm_coeff_pos hP le_rfl).trans_le hb
  have hs : 0 < Real.sqrt (CoefficientBounds.complexIntervalSqAt d P) := by
    rcases mul_pos_iff.mp hp with hh | hh
    · exact hh.2
    · linarith [Real.sqrt_nonneg (CoefficientBounds.complexIntervalSqAt d P)]
  exact Real.sqrt_pos.mp hs

end ThetaTrial.Paper
