import ThetaTrial.ZetaDefinitions
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
A logarithmic majorant for the prime sum. Summability follows from Mathlib's
abscissa of absolute convergence for the logarithmic derivative of the
constant-one L-series.
-/

noncomputable section

namespace ThetaTrial.PrimeContinuity

open scoped BigOperators

/-- The summand of the paper's exact constant `Z_a`. -/
def logMajorant (a : ℝ) (n : {n : ℕ // 2 ≤ n}) : ℝ :=
  Real.log (n : ℕ) / (n : ℝ) ^ (a + 1 / 2)

/-- The logarithmic majorant, indexed by all natural numbers at least two. -/
def logMajorantSum (a : ℝ) : ℝ :=
  ∑' n : {n : ℕ // 2 ≤ n}, logMajorant a n

/-- The natural-number logarithm has an absolutely convergent real Dirichlet
series at every real exponent strictly larger than one. -/
theorem summable_log_div_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ s) := by
  have hlog : (fun n : ℕ => (Real.log (n : ℝ) : ℂ)) =
      LSeries.logMul (1 : ℕ → ℂ) := by
    funext n
    simpa only [LSeries.logMul, Pi.one_apply, mul_one] using
      (Complex.natCast_log (n := n))
  apply LSeries.summable_real_of_abscissaOfAbsConv_lt
  rw [hlog, LSeries.abscissaOfAbsConv_logMul, LSeries.abscissaOfAbsConv_one]
  exact_mod_cast hs

theorem logMajorant_summable {a : ℝ} (ha : 1 / 2 < a) :
    Summable (logMajorant a) := by
  have hs : 1 < a + 1 / 2 := by linarith
  exact (summable_log_div_rpow hs).subtype (fun n : ℕ => 2 ≤ n)

theorem logMajorant_hasSum {a : ℝ} (ha : 1 / 2 < a) :
    HasSum (logMajorant a) (logMajorantSum a) :=
  (logMajorant_summable ha).hasSum

theorem logMajorant_nonneg (a : ℝ) (n : {n : ℕ // 2 ≤ n}) :
    0 ≤ logMajorant a n := by
  exact div_nonneg (Real.log_natCast_nonneg (n : ℕ))
    (Real.rpow_nonneg (Nat.cast_nonneg (n : ℕ)) _)

theorem logMajorantSum_nonneg (a : ℝ) : 0 ≤ logMajorantSum a :=
  tsum_nonneg (logMajorant_nonneg a)

/-- The critical coefficient after the weighted correlation estimate. -/
def primeCoeff (a : ℝ) (n : {n : ℕ // 2 ≤ n}) : ℝ :=
  (ArithmeticFunction.vonMangoldt (n : ℕ) / Real.sqrt (n : ℕ)) *
    Real.exp (-a * Real.log (n : ℕ))

/-- Conversion keeping the factor `n^(-1/2)`. -/
theorem primeCoeff_eq_vonMangoldt_div_rpow (a : ℝ) (n : {n : ℕ // 2 ≤ n}) :
    primeCoeff a n =
      ArithmeticFunction.vonMangoldt (n : ℕ) / (n : ℝ) ^ (a + 1 / 2) := by
  have hn : 0 < (n : ℝ) :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) n.property)
  unfold primeCoeff
  rw [Real.rpow_add hn, ← Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn,
    show -a * Real.log (n : ℕ) = -(Real.log (n : ℕ) * a) by ring,
    Real.exp_neg]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem primeCoeff_nonneg (a : ℝ) (n : {n : ℕ // 2 ≤ n}) :
    0 ≤ primeCoeff a n := by
  exact mul_nonneg
    (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    (Real.exp_pos _).le

/-- The coefficient estimate uses the von Mangoldt arithmetic function. -/
theorem primeCoeff_le_logMajorant (a : ℝ) (n : {n : ℕ // 2 ≤ n}) :
    primeCoeff a n ≤ logMajorant a n := by
  rw [primeCoeff_eq_vonMangoldt_div_rpow]
  exact div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log
    (Real.rpow_nonneg (Nat.cast_nonneg (n : ℕ)) _)

theorem primeCoeff_summable {a : ℝ} (ha : 1 / 2 < a) :
    Summable (primeCoeff a) :=
  (logMajorant_summable ha).of_nonneg_of_le (primeCoeff_nonneg a)
    (primeCoeff_le_logMajorant a)

end ThetaTrial.PrimeContinuity
