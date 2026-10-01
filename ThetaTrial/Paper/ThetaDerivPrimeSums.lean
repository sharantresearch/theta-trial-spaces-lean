import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Exponential integer tails beyond a real crossover

The crossover `N ≥ 0` is real. Summation starts at `floor N + 1`, so the first
gap lies in `(0,1]`.
-/

noncomputable section

namespace ThetaTrial.Paper.ThetaDerivPrimeSums

def integerCrossoverTerm (N c B : ℝ) (n : ℕ) : ℝ :=
  if N < (n : ℝ) then (B + (n : ℝ) - N) * Real.exp (-c * ((n : ℝ) - N)) else 0

def crossoverGap (N : ℝ) : ℝ := (⌊N⌋₊ : ℝ) + 1 - N

def exponentialTailBound (c B : ℝ) : ℝ :=
  (B + 1) / (1 - Real.exp (-c)) + Real.exp (-c) / (1 - Real.exp (-c)) ^ 2

lemma crossoverGap_pos (N : ℝ) : 0 < crossoverGap N := by
  unfold crossoverGap
  linarith [Nat.lt_floor_add_one N]

lemma crossoverGap_le_one {N : ℝ} (hN : 0 ≤ N) : crossoverGap N ≤ 1 := by
  unfold crossoverGap
  linarith [Nat.floor_le hN]

lemma hasSum_affine_geometric (B : ℝ) {q : ℝ} (hq : ‖q‖ < 1) :
    HasSum (fun j : ℕ => (B + 1 + (j : ℝ)) * q ^ j)
      ((B + 1) / (1 - q) + q / (1 - q) ^ 2) := by
  have h0 := (hasSum_geometric_of_norm_lt_one hq).mul_left (B + 1)
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hq
  convert! h0.add h1 using 1
  ext j
  ring

lemma exp_neg_norm_lt_one {c : ℝ} (hc : 0 < c) : ‖Real.exp (-c)‖ < 1 := by
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_lt_one_iff]
  linarith

lemma shiftedExp_le_geometric {c B h : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (j : ℕ) :
    (B + h + (j : ℝ)) * Real.exp (-c * (h + (j : ℝ))) ≤
      (B + 1 + (j : ℝ)) * Real.exp (-c) ^ j := by
  have he : Real.exp (-c * (h + (j : ℝ))) ≤ Real.exp (-c * (j : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ (B + 1 + (j : ℝ)) * Real.exp (-c * (j : ℝ)) :=
      mul_le_mul (by linarith) he (Real.exp_pos _).le (by positivity)
    _ = _ := by rw [mul_comm (-c), Real.exp_nat_mul]

theorem shiftedExp_summable {c B h : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    Summable (fun j : ℕ => (B + h + (j : ℝ)) * Real.exp (-c * (h + (j : ℝ)))) := by
  exact (hasSum_affine_geometric B (exp_neg_norm_lt_one hc)).summable.of_nonneg_of_le
    (fun j => by positivity) (shiftedExp_le_geometric hc hB hh0 hh1)

theorem tsum_shiftedExp_le {c B h : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    (∑' j : ℕ, (B + h + (j : ℝ)) * Real.exp (-c * (h + (j : ℝ)))) ≤
      exponentialTailBound c B := by
  have hmajor := hasSum_affine_geometric B (exp_neg_norm_lt_one hc)
  have hle := (shiftedExp_summable hc hB hh0 hh1).tsum_le_tsum
    (shiftedExp_le_geometric hc hB hh0 hh1) hmajor.summable
  simpa only [hmajor.tsum_eq, exponentialTailBound] using hle

lemma integerCrossoverTerm_add_floor (N c B : ℝ) (j : ℕ) :
    integerCrossoverTerm N c B (j + (⌊N⌋₊ + 1)) =
      (B + crossoverGap N + (j : ℝ)) *
        Real.exp (-c * (crossoverGap N + (j : ℝ))) := by
  have hlt : N < ((j + (⌊N⌋₊ + 1) : ℕ) : ℝ) := by
    have hj : (0 : ℝ) ≤ j := by positivity
    push_cast
    linarith [Nat.lt_floor_add_one N]
  have hd : ((j + (⌊N⌋₊ + 1) : ℕ) : ℝ) - N = crossoverGap N + (j : ℝ) := by
    unfold crossoverGap
    push_cast
    ring
  have hB : B + ((j + (⌊N⌋₊ + 1) : ℕ) : ℝ) - N = B + crossoverGap N + (j : ℝ) := by
    linarith [hd]
  rw [integerCrossoverTerm, if_pos hlt, hB, hd]

lemma integerCrossoverTerm_eq_zero {N c B : ℝ} (hN : 0 ≤ N)
    {n : ℕ} (hn : n < ⌊N⌋₊ + 1) : integerCrossoverTerm N c B n = 0 := by
  have hn' : n ≤ ⌊N⌋₊ := Nat.lt_succ_iff.mp hn
  have hle : (n : ℝ) ≤ N := (Nat.cast_le.mpr hn').trans (Nat.floor_le hN)
  simp only [integerCrossoverTerm, not_lt.mpr hle, if_false]

/-- Summability for every real crossover `N ≥ 0`. -/
theorem integerCrossoverTerm_summable {N c B : ℝ}
    (hN : 0 ≤ N) (hc : 0 < c) (hB : 0 ≤ B) :
    Summable (integerCrossoverTerm N c B) := by
  apply (summable_nat_add_iff (⌊N⌋₊ + 1)).mp
  simpa only [integerCrossoverTerm_add_floor] using
    shiftedExp_summable hc hB (crossoverGap_pos N).le (crossoverGap_le_one hN)

/-- The bound is uniform in the fractional part of the crossover. -/
theorem tsum_integerCrossoverTerm_le {N c B : ℝ}
    (hN : 0 ≤ N) (hc : 0 < c) (hB : 0 ≤ B) :
    (∑' n : ℕ, integerCrossoverTerm N c B n) ≤ exponentialTailBound c B := by
  have hs := integerCrossoverTerm_summable hN hc hB
  have hprefix : (∑ n ∈ Finset.range (⌊N⌋₊ + 1), integerCrossoverTerm N c B n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    exact integerCrossoverTerm_eq_zero hN (Finset.mem_range.mp hn)
  rw [← hs.sum_add_tsum_nat_add (⌊N⌋₊ + 1), hprefix, zero_add]
  simp_rw [integerCrossoverTerm_add_floor]
  exact tsum_shiftedExp_le hc hB (crossoverGap_pos N).le (crossoverGap_le_one hN)

/-! ## The numerical diagonal kernel -/

def diagonalKernel (n : ℕ) : ℝ :=
  if 2 ≤ n then (Real.log (n : ℝ) / Real.sqrt (n : ℝ)) *
    Real.exp (-(((n : ℝ) ^ 2 - 4) / 8)) else 0

lemma diagonalKernel_nonneg (n : ℕ) : 0 ≤ diagonalKernel n := by
  unfold diagonalKernel
  split_ifs with hn
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    exact mul_nonneg (div_nonneg (Real.log_nonneg hn1) (Real.sqrt_nonneg _))
      (Real.exp_pos _).le
  · exact le_rfl

lemma exp_neg_nat_div_eight (n : ℕ) :
    Real.exp (-(n : ℝ) / 8) = Real.exp (-(1 / 8 : ℝ)) ^ n := by
  rw [show -(n : ℝ) / 8 = (n : ℝ) * -(1 / 8 : ℝ) by ring, Real.exp_nat_mul]

lemma diagonalKernel_le_geometric (n : ℕ) :
    diagonalKernel n ≤ Real.exp (1 / 2 : ℝ) *
      ((n : ℝ) * Real.exp (-(1 / 8 : ℝ)) ^ n) := by
  unfold diagonalKernel
  split_ifs with hn
  · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hnp : (0 : ℝ) < n := by linarith
    have hs : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr (by linarith)
    have hlog : Real.log (n : ℝ) / Real.sqrt (n : ℝ) ≤ n := by
      apply (div_le_iff₀ (Real.sqrt_pos.mpr hnp)).mpr
      have hlogn := Real.log_le_self hn0
      nlinarith
    have hexp : Real.exp (-(((n : ℝ) ^ 2 - 4) / 8)) ≤
        Real.exp (1 / 2 : ℝ) * Real.exp (-(n : ℝ) / 8) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    calc
      _ ≤ (n : ℝ) * (Real.exp (1 / 2 : ℝ) * Real.exp (-(n : ℝ) / 8)) :=
        mul_le_mul hlog hexp (Real.exp_pos _).le hn0
      _ = _ := by rw [exp_neg_nat_div_eight]; ring
  · positivity

theorem diagonalKernel_summable : Summable diagonalKernel := by
  have hq : ‖Real.exp (-(1 / 8 : ℝ))‖ < 1 := exp_neg_norm_lt_one (by norm_num)
  exact ((hasSum_coe_mul_geometric_of_norm_lt_one hq).summable.mul_left
    (Real.exp (1 / 2 : ℝ))).of_nonneg_of_le diagonalKernel_nonneg diagonalKernel_le_geometric

/-- A finite numerical constant, defined by its convergent series. -/
def diagonalKernelSum : ℝ := ∑' n : ℕ, diagonalKernel n

lemma diagonalKernelSum_nonneg : 0 ≤ diagonalKernelSum :=
  tsum_nonneg diagonalKernel_nonneg

theorem diagonalKernelSum_le : diagonalKernelSum ≤
    Real.exp (1 / 2 : ℝ) *
      (Real.exp (-(1 / 8 : ℝ)) / (1 - Real.exp (-(1 / 8 : ℝ))) ^ 2) := by
  have hq : ‖Real.exp (-(1 / 8 : ℝ))‖ < 1 := exp_neg_norm_lt_one (by norm_num)
  have hmajor := (hasSum_coe_mul_geometric_of_norm_lt_one hq).mul_left
    (Real.exp (1 / 2 : ℝ))
  have hle := diagonalKernel_summable.tsum_le_tsum diagonalKernel_le_geometric hmajor.summable
  simpa only [diagonalKernelSum, hmajor.tsum_eq] using hle

/-! ## Counting an inclusive central band -/

def centralBand (N B : ℝ) : Finset ℕ := Finset.Icc ⌈N⌉₊ ⌊B⌋₊

lemma mem_centralBand {N B : ℝ} (hB : 0 ≤ B) (n : ℕ) :
    n ∈ centralBand N B ↔ N ≤ (n : ℝ) ∧ (n : ℝ) ≤ B := by
  rw [centralBand, Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff hB]

/-- Counting integers in a band with arbitrary real endpoints. -/
theorem card_centralBand_le {N B : ℝ} (hN : 0 ≤ N) (hNB : N ≤ B) :
    ((centralBand N B).card : ℝ) ≤ B - N + 1 := by
  have hsub : ⌈N⌉₊ ≤ ⌊B⌋₊ + 1 :=
    (Nat.ceil_mono hNB).trans (Nat.ceil_le_floor_add_one B)
  rw [centralBand, Nat.card_Icc, Nat.cast_sub hsub, Nat.cast_add, Nat.cast_one]
  linarith [Nat.floor_le (hN.trans hNB), Nat.le_ceil N]

theorem card_centralBand_mul_le {N t : ℝ} (hN : 0 ≤ N) (ht : 1 ≤ t) :
    ((centralBand N (N * t)).card : ℝ) ≤ N * (t - 1) + 1 := by
  have hNB : N ≤ N * t := by nlinarith
  have h := card_centralBand_le hN hNB
  nlinarith

theorem card_centralBand_exp_le {N s₀ : ℝ} (hN : 0 ≤ N) (hs : 0 ≤ s₀) :
    ((centralBand N (N * Real.exp (2 * s₀))).card : ℝ) ≤
      N * (Real.exp (2 * s₀) - 1) + 1 :=
  card_centralBand_mul_le hN (Real.one_le_exp_iff.mpr (by positivity))

#print axioms integerCrossoverTerm_summable
#print axioms tsum_integerCrossoverTerm_le
#print axioms diagonalKernel_summable
#print axioms diagonalKernelSum_le
#print axioms card_centralBand_le

end ThetaTrial.Paper.ThetaDerivPrimeSums
