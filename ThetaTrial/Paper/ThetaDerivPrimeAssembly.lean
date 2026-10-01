import ThetaTrial.Paper.ThetaDerivPrimeSums
import ThetaTrial.Paper.Definitions

/-!
# Summing the three arithmetic majorants

These are summation lemmas. Their pointwise envelope is explicit and must
be proved from the source estimates before they yield a prime-form
bound. The three constituent majorants are summable.
-/

noncomputable section

namespace ThetaTrial.Paper.ThetaDerivPrimeAssembly

open ThetaDerivPrimeSums

def threePartEnvelope (A B C N U c D : ℝ) (n : ℕ) : ℝ :=
  A * diagonalKernel n + B * (if n ∈ centralBand N U then 1 else 0) +
    C * integerCrossoverTerm N c D n

def threePartBound (A B C N U c D : ℝ) : ℝ :=
  A * diagonalKernelSum + B * (centralBand N U).card + C * exponentialTailBound c D

lemma centralBand_indicator_summable (N U : ℝ) :
    Summable (fun n : ℕ => if n ∈ centralBand N U then (1 : ℝ) else 0) := by
  apply summable_of_ne_finset_zero (s := centralBand N U)
  intro n hn
  simp only [hn, if_false]

lemma tsum_centralBand_indicator (N U : ℝ) :
    (∑' n : ℕ, if n ∈ centralBand N U then (1 : ℝ) else 0) =
      (centralBand N U).card := by
  rw [tsum_eq_sum (s := centralBand N U) (fun n hn => by simp only [hn, if_false])]
  simp

theorem threePartEnvelope_summable (A B C U : ℝ) {N c D : ℝ}
    (hN : 0 ≤ N) (hc : 0 < c) (hD : 0 ≤ D) :
    Summable (threePartEnvelope A B C N U c D) := by
  exact ((diagonalKernel_summable.mul_left A).add
    ((centralBand_indicator_summable N U).mul_left B)).add
      ((integerCrossoverTerm_summable hN hc hD).mul_left C)

theorem tsum_threePartEnvelope_le {A B C N U c D : ℝ}
    (hN : 0 ≤ N) (hc : 0 < c) (hD : 0 ≤ D) (hC : 0 ≤ C) :
    (∑' n : ℕ, threePartEnvelope A B C N U c D n) ≤ threePartBound A B C N U c D := by
  unfold threePartEnvelope threePartBound
  rw [Summable.tsum_add ((diagonalKernel_summable.mul_left A).add
      ((centralBand_indicator_summable N U).mul_left B))
      ((integerCrossoverTerm_summable hN hc hD).mul_left C),
    Summable.tsum_add (diagonalKernel_summable.mul_left A)
      ((centralBand_indicator_summable N U).mul_left B),
    tsum_mul_left, tsum_mul_left, tsum_mul_left, tsum_centralBand_indicator]
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (tsum_integerCrossoverTerm_le hN hc hD) hC)

theorem abs_summable_of_envelope {t : ℕ → ℝ} {A B C N U c D : ℝ}
    (hN : 0 ≤ N) (hc : 0 < c) (hD : 0 ≤ D)
    (ht : ∀ n, |t n| ≤ threePartEnvelope A B C N U c D n) :
    Summable (fun n : ℕ => |t n|) :=
  (threePartEnvelope_summable A B C U hN hc hD).of_nonneg_of_le
    (fun n => abs_nonneg (t n)) ht

theorem summable_of_envelope {t : ℕ → ℝ} {A B C N U c D : ℝ}
    (hN : 0 ≤ N) (hc : 0 < c) (hD : 0 ≤ D)
    (ht : ∀ n, |t n| ≤ threePartEnvelope A B C N U c D n) : Summable t := by
  apply Summable.of_norm
  simpa only [Real.norm_eq_abs] using abs_summable_of_envelope hN hc hD ht

theorem abs_two_tsum_le_of_envelope {t : ℕ → ℝ} {A B C N U c D : ℝ}
    (hN : 0 ≤ N) (hc : 0 < c) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (ht : ∀ n, |t n| ≤ threePartEnvelope A B C N U c D n) :
    |2 * ∑' n : ℕ, t n| ≤ 2 * threePartBound A B C N U c D := by
  have habs := abs_summable_of_envelope hN hc hD ht
  have hnorm : |∑' n : ℕ, t n| ≤ ∑' n : ℕ, |t n| := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm
      (show Summable (fun n => ‖t n‖) by simpa only [Real.norm_eq_abs] using habs)
  have hcomp := habs.tsum_le_tsum ht (threePartEnvelope_summable A B C U hN hc hD)
  have hbound := hnorm.trans (hcomp.trans (tsum_threePartEnvelope_le hN hc hD hC))
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul_of_nonneg_left hbound (by norm_num)

/-- Absolute convergence of every natural-indexed prime-power term, once
the pointwise source envelope has been established. -/
theorem prime_absolutely_summable_of_envelope {f : ℝ → ℂ} {A B C N U c D : ℝ}
    (hN : 0 ≤ N) (hc : 0 < c) (hD : 0 ≤ D)
    (ht : ∀ n : ℕ,
      |(ArithmeticFunction.vonMangoldt n / Real.sqrt n) * (correlation f (Real.log n)).re| ≤
        A * diagonalKernel n + B * (if n ∈ centralBand N U then 1 else 0) +
          C * integerCrossoverTerm N c D n) :
    Summable (fun n : ℕ =>
      |(ArithmeticFunction.vonMangoldt n / Real.sqrt n) * (correlation f (Real.log n)).re|) :=
  abs_summable_of_envelope hN hc hD ht

/-- Assembles the summation bounds, with the coefficient two of the Weil form. -/
theorem prime_sum_bound_of_envelope {f : ℝ → ℂ} {A B C N U c D : ℝ}
    (hN : 0 ≤ N) (hc : 0 < c) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (ht : ∀ n : ℕ,
      |(ArithmeticFunction.vonMangoldt n / Real.sqrt n) * (correlation f (Real.log n)).re| ≤
        A * diagonalKernel n + B * (if n ∈ centralBand N U then 1 else 0) +
          C * integerCrossoverTerm N c D n) :
    |2 * ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
      (correlation f (Real.log n)).re| ≤
        2 * (A * diagonalKernelSum + B * (centralBand N U).card +
          C * exponentialTailBound c D) :=
  abs_two_tsum_le_of_envelope hN hc hD hC ht

theorem prime_sum_bound_interval_of_envelope {f : ℝ → ℂ} {A B C N U c D : ℝ}
    (hN : 0 ≤ N) (hNU : N ≤ U) (hc : 0 < c) (hD : 0 ≤ D)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ht : ∀ n : ℕ,
      |(ArithmeticFunction.vonMangoldt n / Real.sqrt n) * (correlation f (Real.log n)).re| ≤
        A * diagonalKernel n + B * (if n ∈ centralBand N U then 1 else 0) +
          C * integerCrossoverTerm N c D n) :
    |2 * ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
      (correlation f (Real.log n)).re| ≤
        2 * (A * diagonalKernelSum + B * (U - N + 1) + C * exponentialTailBound c D) := by
  have hprime := prime_sum_bound_of_envelope hN hc hD hC ht
  have hcard := mul_le_mul_of_nonneg_left (card_centralBand_le hN hNU) hB
  linarith

#print axioms prime_absolutely_summable_of_envelope
#print axioms prime_sum_bound_of_envelope
#print axioms prime_sum_bound_interval_of_envelope

end ThetaTrial.Paper.ThetaDerivPrimeAssembly
