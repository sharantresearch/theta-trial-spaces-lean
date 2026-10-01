import ThetaTrial.PrimeContinuity.Weighted
import ThetaTrial.PrimeContinuity.LogSeries
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Fin.Rev
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Base
/-!
Continuity of the prime part of the form on an exponentially weighted `L2`
space: for weight `a > 1/2`, the series with coefficients `Λ(n)/√n` converges
absolutely, with continuity constant given by a logarithmic series `Z_a`.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped BigOperators ComplexConjugate

namespace ThetaTrial.PrimeContinuity

def primeTerm (f : ℝ → ℂ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ) *
    (ThetaTrial.WeilFormula.correlation f (Real.log (n : ℝ))).re

def fullPrimeForm (f : ℝ → ℂ) : ℝ := ∑' n : ℕ, primeTerm f n

theorem primeTerm_zero (f : ℝ → ℂ) : primeTerm f 0 = 0 := by
  simp [primeTerm]

theorem primeTerm_one (f : ℝ → ℂ) : primeTerm f 1 = 0 := by
  simp [primeTerm]

theorem fullPrimeForm_eq_from_two (f : ℝ → ℂ) :
    fullPrimeForm f = ∑' n : {n : ℕ // 2 ≤ n}, primeTerm f n := by
  symm
  apply tsum_subtype_eq_of_support_subset
  intro n hn
  by_contra h
  change ¬ 2 ≤ n at h
  change primeTerm f n ≠ 0 at hn
  have hn01 : n = 0 ∨ n = 1 := by omega
  rcases hn01 with rfl | rfl
  · exact hn (primeTerm_zero f)
  · exact hn (primeTerm_one f)

theorem primeTerm_norm_le {a : ℝ} (ha : 1 / 2 < a) {f : ℝ → ℂ}
    (hf : WeightedL2 a f) (n : {n : ℕ // 2 ≤ n}) :
    |primeTerm f n| ≤ logMajorant a n * (weightedNorm a f * weightedNorm a f) := by
  have ha0 : 0 ≤ a := by linarith
  have hc : 0 ≤ ArithmeticFunction.vonMangoldt (n : ℕ) / Real.sqrt (n : ℝ) :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have hh := (Complex.abs_re_le_norm
    (ThetaTrial.WeilFormula.correlation f (Real.log (n : ℝ)))).trans
    (mixedCorrelation_norm_le ha0 hf hf (Real.log (n : ℝ)))
  rw [abs_of_nonneg (Real.log_natCast_nonneg (n : ℕ))] at hh
  rw [primeTerm, abs_mul, abs_of_nonneg hc]
  calc
    _ ≤ (ArithmeticFunction.vonMangoldt (n : ℕ) / Real.sqrt (n : ℝ)) *
        (Real.exp (-a * Real.log (n : ℝ)) * (weightedNorm a f * weightedNorm a f)) :=
      mul_le_mul_of_nonneg_left hh hc
    _ = primeCoeff a n * (weightedNorm a f * weightedNorm a f) := by
      unfold primeCoeff
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (primeCoeff_le_logMajorant a n)
      (mul_nonneg (weightedNorm_nonneg a f) (weightedNorm_nonneg a f))

theorem primeTerm_from_two_absolutely_summable {a : ℝ} (ha : 1 / 2 < a)
    {f : ℝ → ℂ} (hf : WeightedL2 a f) :
    Summable (fun n : {n : ℕ // 2 ≤ n} => |primeTerm f n|) := by
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (primeTerm_norm_le ha hf)
  exact (logMajorant_summable ha).mul_right (weightedNorm a f * weightedNorm a f)

theorem primeTerm_from_two_summable {a : ℝ} (ha : 1 / 2 < a)
    {f : ℝ → ℂ} (hf : WeightedL2 a f) :
    Summable (fun n : {n : ℕ // 2 ≤ n} => primeTerm f n) := by
  apply Summable.of_norm
  simpa only [Real.norm_eq_abs] using primeTerm_from_two_absolutely_summable ha hf

theorem primeTerm_summable {a : ℝ} (ha : 1 / 2 < a)
    {f : ℝ → ℂ} (hf : WeightedL2 a f) : Summable (primeTerm f) := by
  apply (summable_subtype_and_compl (s := {n : ℕ | 2 ≤ n})).mp
  refine ⟨primeTerm_from_two_summable ha hf, ?_⟩
  have hz (n : ↥({n : ℕ | 2 ≤ n}ᶜ)) : primeTerm f n = 0 := by
    have hn : ¬ 2 ≤ (n : ℕ) := n.property
    have hn01 : (n : ℕ) = 0 ∨ (n : ℕ) = 1 := by omega
    rcases hn01 with hn0 | hn1
    · rw [hn0, primeTerm_zero]
    · rw [hn1, primeTerm_one]
  simpa only [hz] using
    (summable_zero : Summable (fun _ : ↥({n : ℕ | 2 ≤ n}ᶜ) => (0 : ℝ)))

theorem primeTerm_absolutely_summable {a : ℝ} (ha : 1 / 2 < a)
    {f : ℝ → ℂ} (hf : WeightedL2 a f) :
    Summable (fun n : ℕ => |primeTerm f n|) := by
  simpa only [Real.norm_eq_abs] using (primeTerm_summable ha hf).norm

theorem primeTerm_difference_le {a : ℝ} (ha : 1 / 2 < a) {f g : ℝ → ℂ}
    (hf : WeightedL2 a f) (hg : WeightedL2 a g) (n : {n : ℕ // 2 ≤ n}) :
    |primeTerm f n - primeTerm g n| ≤ logMajorant a n *
      (weightedNorm a (f - g) * (weightedNorm a f + weightedNorm a g)) := by
  have ha0 : 0 ≤ a := by linarith
  have hc : 0 ≤ ArithmeticFunction.vonMangoldt (n : ℕ) / Real.sqrt (n : ℝ) :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have hh := correlation_real_part_difference_le ha0 hf hg (Real.log (n : ℝ))
  rw [abs_of_nonneg (Real.log_natCast_nonneg (n : ℕ))] at hh
  rw [primeTerm, primeTerm, ← mul_sub, abs_mul, abs_of_nonneg hc]
  calc
    _ ≤ (ArithmeticFunction.vonMangoldt (n : ℕ) / Real.sqrt (n : ℝ)) *
        (Real.exp (-a * Real.log (n : ℝ)) * weightedNorm a (f - g) *
          (weightedNorm a f + weightedNorm a g)) := mul_le_mul_of_nonneg_left hh hc
    _ = primeCoeff a n *
        (weightedNorm a (f - g) * (weightedNorm a f + weightedNorm a g)) := by
      unfold primeCoeff
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (primeCoeff_le_logMajorant a n)
      (mul_nonneg (weightedNorm_nonneg a (f - g))
        (add_nonneg (weightedNorm_nonneg a f) (weightedNorm_nonneg a g)))

/-- The prime form is bounded by `Z_a` times the weighted norms, for functions
in the exponentially weighted `L2` space. -/
theorem fullPrimeForm_lipschitz {a : ℝ} (ha : 1 / 2 < a) {f g : ℝ → ℂ}
    (hf : WeightedL2 a f) (hg : WeightedL2 a g) :
    |fullPrimeForm f - fullPrimeForm g| ≤ logMajorantSum a *
      weightedNorm a (f - g) * (weightedNorm a f + weightedNorm a g) := by
  have hs := (primeTerm_from_two_summable ha hf).sub
    (primeTerm_from_two_summable ha hg)
  have hb := hasSum_le
    (fun n : {n : ℕ // 2 ≤ n} => by
      simpa only [Real.norm_eq_abs] using primeTerm_difference_le ha hf hg n)
    hs.norm.hasSum
    ((logMajorant_hasSum ha).mul_right
      (weightedNorm a (f - g) * (weightedNorm a f + weightedNorm a g)))
  rw [fullPrimeForm_eq_from_two, fullPrimeForm_eq_from_two,
    ← (primeTerm_from_two_summable ha hf).tsum_sub (primeTerm_from_two_summable ha hg)]
  calc
    _ ≤ ∑' n : {n : ℕ // 2 ≤ n}, ‖primeTerm f n - primeTerm g n‖ := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
    _ ≤ logMajorantSum a *
        (weightedNorm a (f - g) * (weightedNorm a f + weightedNorm a g)) := hb
    _ = _ := by ring

end ThetaTrial.PrimeContinuity
