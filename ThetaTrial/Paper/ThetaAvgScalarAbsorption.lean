import ThetaTrial.Paper.Definitions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-! Elementary inequalities that absorb the constants and the factorial in the
polynomial tail estimate. -/

noncomputable section
open Real

namespace ThetaTrial.Paper

def thetaAvgScalarAmplitude (B A a : ℝ) (k : ℕ) : ℝ :=
  B * A ^ (k + 1) * (k + 1).factorial * (scaleZ a) ^ (2 * k) *
    Real.exp (16 * a - scaleT a)

def thetaAvgNormalizedAmplitude (B A c a : ℝ) (k : ℕ) : ℝ :=
  (2 * Real.sqrt (scaleZ a) / Real.sqrt c) * thetaAvgScalarAmplitude B A a k

theorem thetaAvg_factorial_exp_le (k : ℕ) :
    ((k + 1).factorial : ℝ) ≤
      Real.exp ((k : ℝ) * Real.log ((k : ℝ) + 1) + k) := by
  have hp : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hf : ((k + 1).factorial : ℝ) ≤ ((k : ℝ) + 1) ^ (k + 1) := by
    exact_mod_cast Nat.factorial_le_pow (k + 1)
  have hl : Real.log ((k : ℝ) + 1) ≤ k := by
    linarith [Real.log_le_sub_one_of_pos hp]
  calc
    _ ≤ ((k : ℝ) + 1) ^ (k + 1) := hf
    _ = Real.exp (((k : ℝ) + 1) * Real.log ((k : ℝ) + 1)) := by
      rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by push_cast; rfl,
        Real.exp_nat_mul, Real.exp_log (by positivity)]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem thetaAvg_pos_le_exp_abs_log {x : ℝ} (hx : 0 < x) : x ≤ Real.exp |Real.log x| := by
  simpa only [Real.exp_log hx] using Real.exp_le_exp.mpr (le_abs_self (Real.log x))

theorem thetaAvg_pow_le_exp_abs_log {x : ℝ} (hx : 0 < x) (n : ℕ) :
    x ^ n ≤ Real.exp (|Real.log x| * n) := by
  have h := pow_le_pow_left₀ hx.le (thetaAvg_pos_le_exp_abs_log hx) n
  simpa only [← Real.exp_nat_mul, mul_comm] using h

theorem thetaAvgNormalizedAmplitude_eq (B A c a : ℝ) (k : ℕ) :
    thetaAvgNormalizedAmplitude B A c a k =
      (2 * B * Real.sqrt Real.pi / Real.sqrt c) * A ^ (k + 1) *
        Real.pi ^ (2 * k) * (k + 1).factorial *
        Real.exp (17 * a + 4 * (k : ℝ) * a - scaleT a) := by
  have hz : (scaleZ a) ^ (2 * k) = Real.pi ^ (2 * k) * Real.exp (4 * (k : ℝ) * a) := by
    rw [scaleZ, mul_pow, ← Real.exp_nat_mul]
    push_cast
    congr 2
    ring
  have hs : Real.sqrt (scaleZ a) = Real.sqrt Real.pi * Real.exp a := by
    have he : Real.exp (2 * a) = (Real.exp a) ^ 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [scaleZ, Real.sqrt_mul Real.pi_pos.le, he, Real.sqrt_sq (Real.exp_pos a).le]
  have he : Real.exp a * Real.exp (4 * (k : ℝ) * a) *
      Real.exp (16 * a - scaleT a) = Real.exp (17 * a + 4 * (k : ℝ) * a - scaleT a) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  unfold thetaAvgNormalizedAmplitude thetaAvgScalarAmplitude
  rw [hz, hs]
  calc
    _ = ((2 * B * Real.sqrt Real.pi / Real.sqrt c) * A ^ (k + 1) *
        Real.pi ^ (2 * k) * (k + 1).factorial) *
          (Real.exp a * Real.exp (4 * (k : ℝ) * a) * Real.exp (16 * a - scaleT a)) := by ring
    _ = _ := by rw [he]

def thetaAvgAbsorptionConstant (B A c : ℝ) : ℝ :=
  |Real.log (2 * B * Real.sqrt Real.pi / Real.sqrt c)| +
    2 * |Real.log A| + 2 * |Real.log Real.pi| + 18

theorem thetaAvgAbsorptionConstant_pos (B A c : ℝ) : 0 < thetaAvgAbsorptionConstant B A c := by
  unfold thetaAvgAbsorptionConstant
  positivity

/-- One uniform exponent absorbs every fixed constant and the factorial. -/
theorem thetaAvgNormalizedAmplitude_le {B A c a : ℝ} (hB : 0 < B)
    (hA : 0 < A) (hc : 0 < c) (ha : 1 ≤ a) (k : ℕ) :
    thetaAvgNormalizedAmplitude B A c a k ≤
      Real.exp ((k : ℝ) * (Real.log ((k : ℝ) + 1) + 4 * a) +
        thetaAvgAbsorptionConstant B A c * ((k : ℝ) + a) - scaleT a) := by
  let D := 2 * B * Real.sqrt Real.pi / Real.sqrt c
  have hD : 0 < D := by dsimp [D]; positivity
  rw [thetaAvgNormalizedAmplitude_eq]
  change D * _ * _ * _ * _ ≤ _
  calc
    _ ≤ Real.exp |Real.log D| * Real.exp (|Real.log A| * (k + 1 : ℕ)) *
        Real.exp (|Real.log Real.pi| * (2 * k : ℕ)) *
        Real.exp ((k : ℝ) * Real.log ((k : ℝ) + 1) + k) *
        Real.exp (17 * a + 4 * (k : ℝ) * a - scaleT a) := by
      gcongr
      · exact thetaAvg_pos_le_exp_abs_log hD
      · exact thetaAvg_pow_le_exp_abs_log hA (k + 1)
      · exact thetaAvg_pow_le_exp_abs_log Real.pi_pos (2 * k)
      · exact thetaAvg_factorial_exp_le k
    _ ≤ _ := by
      simp only [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      push_cast
      unfold thetaAvgAbsorptionConstant
      dsimp [D]
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith [abs_nonneg (Real.log (2 * B * Real.sqrt Real.pi / Real.sqrt c)),
        abs_nonneg (Real.log A), abs_nonneg (Real.log Real.pi),
        mul_nonneg (abs_nonneg (Real.log (2 * B * Real.sqrt Real.pi / Real.sqrt c)))
          (show 0 ≤ a - 1 by linarith),
        mul_nonneg (abs_nonneg (Real.log A)) (show 0 ≤ a - 1 by linarith),
        mul_nonneg (abs_nonneg (Real.log Real.pi)) (show 0 ≤ a - 1 by linarith)]

theorem thetaAvgNormalizedAmplitude_sq {B A c a : ℝ} (hc : 0 < c) (k : ℕ) :
    (thetaAvgNormalizedAmplitude B A c a k) ^ 2 =
      (4 * scaleZ a / c) * (thetaAvgScalarAmplitude B A a k) ^ 2 := by
  have hZ : 0 < scaleZ a := mul_pos Real.pi_pos (Real.exp_pos _)
  unfold thetaAvgNormalizedAmplitude
  rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hZ.le, Real.sq_sqrt hc.le]
  norm_num

/-- Under the paper's degree condition, the tail carries at most a quarter of
the norm. -/
theorem thetaAvg_amplitude_small_of_degree {B A c a : ℝ} (hB : 0 < B)
    (hA : 0 < A) (hc : 0 < c) (ha : 1 ≤ a) (k : ℕ)
    (hdegree : (k : ℝ) * (Real.log ((k : ℝ) + 1) + 4 * a) +
      thetaAvgAbsorptionConstant B A c * ((k : ℝ) + a) ≤ scaleT a) :
    (thetaAvgScalarAmplitude B A a k) ^ 2 ≤ c / (4 * scaleZ a) := by
  have hZ : 0 < scaleZ a := mul_pos Real.pi_pos (Real.exp_pos _)
  have hn0 : 0 ≤ thetaAvgNormalizedAmplitude B A c a k := by
    unfold thetaAvgNormalizedAmplitude thetaAvgScalarAmplitude
    positivity
  have hn : thetaAvgNormalizedAmplitude B A c a k ≤ 1 :=
    (thetaAvgNormalizedAmplitude_le hB hA hc ha k).trans
      (Real.exp_le_one_iff.mpr (by linarith))
  have hs := pow_le_pow_left₀ hn0 hn 2
  rw [thetaAvgNormalizedAmplitude_sq hc, one_pow] at hs
  have hs' : 4 * scaleZ a * (thetaAvgScalarAmplitude B A a k) ^ 2 ≤ c := by
    rw [div_mul_eq_mul_div] at hs
    simpa only [one_mul] using (div_le_iff₀ hc).mp hs
  apply (le_div_iff₀ (by positivity : 0 < 4 * scaleZ a)).mpr
  nlinarith

def thetaAvgEnergyAbsorptionConstant (B A c H : ℝ) : ℝ :=
  2 * thetaAvgAbsorptionConstant B A c + |Real.log H|

theorem thetaAvgEnergyAbsorptionConstant_pos (B A c H : ℝ) :
    0 < thetaAvgEnergyAbsorptionConstant B A c H := by
  unfold thetaAvgEnergyAbsorptionConstant
  linarith [thetaAvgAbsorptionConstant_pos B A c, abs_nonneg (Real.log H)]

/-- The energy prefactor has the precise paper exponential
shape. This bound does not need the degree restriction. -/
theorem thetaAvg_energy_amplitude_bound {B A c H a : ℝ} (hB : 0 < B)
    (hA : 0 < A) (hc : 0 < c) (hH : 0 < H) (ha : 1 ≤ a) (k : ℕ) :
    (4 * scaleZ a / c) * H * (thetaAvgScalarAmplitude B A a k) ^ 2 ≤
      Real.exp (-2 * scaleT a + 8 * (k : ℝ) * a +
        2 * (k : ℝ) * Real.log ((k : ℝ) + 1) +
        thetaAvgEnergyAbsorptionConstant B A c H * ((k : ℝ) + a)) := by
  have hZ : 0 < scaleZ a := mul_pos Real.pi_pos (Real.exp_pos _)
  have hn0 : 0 ≤ thetaAvgNormalizedAmplitude B A c a k := by
    unfold thetaAvgNormalizedAmplitude thetaAvgScalarAmplitude
    positivity
  have hn := thetaAvgNormalizedAmplitude_le hB hA hc ha k
  have hs := pow_le_pow_left₀ hn0 hn 2
  rw [← Real.exp_nat_mul] at hs
  norm_num only [Nat.cast_ofNat] at hs
  have hka : 1 ≤ (k : ℝ) + a := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hh : H ≤ Real.exp (|Real.log H| * ((k : ℝ) + a)) :=
    (thetaAvg_pos_le_exp_abs_log hH).trans (Real.exp_le_exp.mpr
      (le_mul_of_one_le_right (abs_nonneg _) hka))
  calc
    _ = H * (thetaAvgNormalizedAmplitude B A c a k) ^ 2 := by
      rw [thetaAvgNormalizedAmplitude_sq hc]
      ring
    _ ≤ Real.exp (|Real.log H| * ((k : ℝ) + a)) *
        Real.exp (2 * ((k : ℝ) * (Real.log ((k : ℝ) + 1) + 4 * a) +
          thetaAvgAbsorptionConstant B A c * ((k : ℝ) + a) - scaleT a)) :=
      mul_le_mul hh hs (sq_nonneg _) (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      unfold thetaAvgEnergyAbsorptionConstant
      ring

theorem thetaAvg_scaled_amplitude_small_of_degree {B A c a E : ℝ} (hB : 0 < B)
    (hA : 0 < A) (hc : 0 < c) (ha : 1 ≤ a) (hE : 0 ≤ E) (k : ℕ)
    (hdegree : (k : ℝ) * (Real.log ((k : ℝ) + 1) + 4 * a) +
      thetaAvgAbsorptionConstant B A c * ((k : ℝ) + a) ≤ scaleT a) :
    (thetaAvgScalarAmplitude B A a k * Real.sqrt E) ^ 2 ≤ (c / (4 * scaleZ a)) * E := by
  rw [mul_pow, Real.sq_sqrt hE]
  exact mul_le_mul_of_nonneg_right
    (thetaAvg_amplitude_small_of_degree hB hA hc ha k hdegree) hE

/-- Constants independent of the degree and of the window, with an explicit
valid lower threshold a₁=1. -/
theorem thetaAvg_scalar_absorption {B A c H : ℝ} (hB : 0 < B)
    (hA : 0 < A) (hc : 0 < c) (hH : 0 < H) :
    ∃ C₁ > 0, ∃ C₂ > 0, ∃ a₁ : ℝ, 1 ≤ a₁ ∧ ∀ a ≥ a₁, ∀ k : ℕ,
      (((k : ℝ) * (Real.log ((k : ℝ) + 1) + 4 * a) + C₁ * ((k : ℝ) + a) ≤ scaleT a →
        (thetaAvgScalarAmplitude B A a k) ^ 2 ≤ c / (4 * scaleZ a)) ∧
      ((4 * scaleZ a / c) * H * (thetaAvgScalarAmplitude B A a k) ^ 2 ≤
        Real.exp (-2 * scaleT a + 8 * (k : ℝ) * a +
          2 * (k : ℝ) * Real.log ((k : ℝ) + 1) + C₂ * ((k : ℝ) + a)))) := by
  refine ⟨thetaAvgAbsorptionConstant B A c, thetaAvgAbsorptionConstant_pos B A c,
    thetaAvgEnergyAbsorptionConstant B A c H, thetaAvgEnergyAbsorptionConstant_pos B A c H,
    1, le_rfl, ?_⟩
  intro a ha k
  exact ⟨thetaAvg_amplitude_small_of_degree hB hA hc ha k,
    thetaAvg_energy_amplitude_bound hB hA hc hH ha k⟩

end ThetaTrial.Paper
