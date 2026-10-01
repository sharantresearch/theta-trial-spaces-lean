import ThetaTrial.Paper.Definitions
import ThetaTrial.Paper.ThetaDerivPrimeSums

/-!
# A fixed constant for the prime-tail factor

This file bounds the explicit numerical factor assembled from the three
prime majorants. The constant is independent of the cutoff and central width.
-/

noncomputable section

namespace ThetaTrial.Paper

open ThetaDerivPrimeSums

def primeTailFactor (a s₀ : ℝ) : ℝ :=
  2 * Real.exp (-3 * scaleT a / 8) * diagonalKernelSum +
    Real.exp (-a) * (2 * a + 2 * s₀) *
      (Real.exp (2 * a) * Real.exp (2 * s₀) - Real.exp (2 * a) + 1) +
    2 * Real.exp (-a) * exponentialTailBound (Real.pi / 4) (2 * a)

def primeTailConstant : ℝ :=
  2 * diagonalKernelSum + 8 * Real.exp (2 : ℝ) + 4 +
    2 * exponentialTailBound (Real.pi / 4) 2

lemma exponentialTailBound_nonneg {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B) :
    0 ≤ exponentialTailBound c B := by
  have hd : 0 < 1 - Real.exp (-c) := by
    have := Real.exp_lt_one_iff.mpr (show -c < 0 by linarith)
    linarith
  unfold exponentialTailBound
  positivity

alias prime_exponentialTailBound_nonneg := exponentialTailBound_nonneg

lemma primeTailConstant_nonneg : 0 ≤ primeTailConstant := by
  have hD := diagonalKernelSum_nonneg
  have hG := exponentialTailBound_nonneg
    (show 0 < Real.pi / 4 by positivity) (show (0 : ℝ) ≤ 2 by norm_num)
  unfold primeTailConstant
  positivity

lemma primeTailFactor_nonneg {a s₀ : ℝ} (ha : 0 ≤ a) (hs0 : 0 ≤ s₀) :
    0 ≤ primeTailFactor a s₀ := by
  have hD := diagonalKernelSum_nonneg
  have hG := exponentialTailBound_nonneg
    (show 0 < Real.pi / 4 by positivity) (show 0 ≤ 2 * a by positivity)
  have hb : 0 ≤ Real.exp (2 * a) * Real.exp (2 * s₀) - Real.exp (2 * a) + 1 := by
    have he : 1 ≤ Real.exp (2 * s₀) := Real.one_le_exp_iff.mpr (by positivity)
    have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (2 * a)).le
    nlinarith
  unfold primeTailFactor
  exact add_nonneg (add_nonneg (by positivity)
    (mul_nonneg (by positivity) hb)) (by positivity)

lemma prime_exp_two_mul_sub_one_le {s₀ : ℝ} (hs0 : 0 ≤ s₀) (hs1 : s₀ ≤ 1) :
    Real.exp (2 * s₀) - 1 ≤ 2 * Real.exp (2 : ℝ) * s₀ := by
  have hb : 1 - 2 * s₀ ≤ Real.exp (-(2 * s₀)) := by
    linarith [Real.add_one_le_exp (-(2 * s₀))]
  have hm := mul_le_mul_of_nonneg_left hb (Real.exp_pos (2 * s₀)).le
  have he : Real.exp (2 * s₀) * Real.exp (-(2 * s₀)) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [he] at hm
  have hmono : Real.exp (2 * s₀) ≤ Real.exp (2 : ℝ) :=
    Real.exp_le_exp.mpr (by linarith)
  have hm' := mul_le_mul_of_nonneg_left hmono (show 0 ≤ 2 * s₀ by positivity)
  nlinarith

lemma prime_scaleT_lower {a : ℝ} (ha : 1 ≤ a) : 8 * a / 3 ≤ scaleT a := by
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.one_le_pi_div_two]
  have hexp : 2 * a ≤ Real.exp (2 * a) := by
    linarith [Real.add_one_le_exp (2 * a)]
  have hp := mul_le_mul_of_nonneg_right hpi (Real.exp_pos (2 * a)).le
  unfold scaleT scaleZ
  nlinarith

lemma prime_exp_scaleT_le {a : ℝ} (ha : 1 ≤ a) :
    Real.exp (-3 * scaleT a / 8) ≤ Real.exp (-a) := by
  apply Real.exp_le_exp.mpr
  linarith [prime_scaleT_lower ha]

lemma prime_exponentialTailBound_linear {a : ℝ} (ha : 1 ≤ a) :
    exponentialTailBound (Real.pi / 4) (2 * a) ≤
      a * exponentialTailBound (Real.pi / 4) 2 := by
  have hd : 0 < 1 - Real.exp (-(Real.pi / 4)) := by
    have := Real.exp_lt_one_iff.mpr (show -(Real.pi / 4) < 0 from neg_neg_of_pos (by positivity))
    linarith
  have hnum : 2 * a + 1 ≤ a * (2 + 1) := by linarith
  have hfirst := div_le_div_of_nonneg_right hnum hd.le
  have hsecond : Real.exp (-(Real.pi / 4)) / (1 - Real.exp (-(Real.pi / 4))) ^ 2 ≤
      a * (Real.exp (-(Real.pi / 4)) / (1 - Real.exp (-(Real.pi / 4))) ^ 2) := by
    exact le_mul_of_one_le_left (by positivity) ha
  unfold exponentialTailBound
  calc
    _ ≤ a * (2 + 1) / (1 - Real.exp (-(Real.pi / 4))) +
        a * (Real.exp (-(Real.pi / 4)) / (1 - Real.exp (-(Real.pi / 4))) ^ 2) :=
      add_le_add hfirst hsecond
    _ = _ := by ring

/-- Uniform prime-tail factor bound with one explicit numerical constant. -/
theorem primeTailFactor_le {a s₀ : ℝ} (ha : 1 ≤ a) (hs0 : 0 ≤ s₀) (hs1 : s₀ ≤ 1) :
    primeTailFactor a s₀ ≤
      primeTailConstant * (1 + Real.exp (2 * a) * s₀) * a * Real.exp (-a) := by
  let R : ℝ := (1 + Real.exp (2 * a) * s₀) * a * Real.exp (-a)
  have ha0 : 0 ≤ a := by linarith
  have hX : 0 ≤ Real.exp (2 * a) * s₀ := by positivity
  have he0 : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
  have hR1 : a * Real.exp (-a) ≤ R := by
    dsimp [R]
    nlinarith [mul_nonneg hX (mul_nonneg ha0 he0)]
  have hR0 : Real.exp (-a) ≤ R := by
    have he := mul_le_mul_of_nonneg_right ha he0
    simp only [one_mul] at he
    exact he.trans hR1
  have hdiag : 2 * Real.exp (-3 * scaleT a / 8) * diagonalKernelSum ≤
      (2 * diagonalKernelSum) * R := by
    have he := (prime_exp_scaleT_le ha).trans hR0
    have hm := mul_le_mul_of_nonneg_left he
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) diagonalKernelSum_nonneg)
    nlinarith
  have hbracket : Real.exp (2 * a) * Real.exp (2 * s₀) - Real.exp (2 * a) + 1 ≤
      2 * Real.exp (2 : ℝ) * (Real.exp (2 * a) * s₀) + 1 := by
    have hm := mul_le_mul_of_nonneg_left (prime_exp_two_mul_sub_one_le hs0 hs1)
      (Real.exp_pos (2 * a)).le
    nlinarith
  have hbracket0 : 0 ≤ Real.exp (2 * a) * Real.exp (2 * s₀) - Real.exp (2 * a) + 1 := by
    have he : 1 ≤ Real.exp (2 * s₀) := Real.one_le_exp_iff.mpr (by positivity)
    have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (2 * a)).le
    nlinarith
  have hcoeff : 2 * a + 2 * s₀ ≤ 4 * a := by linarith
  have hmiddle : Real.exp (-a) * (2 * a + 2 * s₀) *
      (Real.exp (2 * a) * Real.exp (2 * s₀) - Real.exp (2 * a) + 1) ≤
        (8 * Real.exp (2 : ℝ) + 4) * R := by
    have hm := mul_le_mul hcoeff hbracket hbracket0 (show 0 ≤ 4 * a by positivity)
    have hm' := mul_le_mul_of_nonneg_left hm he0
    have hp : 8 * Real.exp (2 : ℝ) * (Real.exp (2 * a) * s₀) + 4 ≤
        (8 * Real.exp (2 : ℝ) + 4) * (1 + Real.exp (2 * a) * s₀) := by
      nlinarith [Real.exp_pos (2 : ℝ)]
    have hp' := mul_le_mul_of_nonneg_right hp (mul_nonneg ha0 he0)
    dsimp [R]
    nlinarith
  have hG0 : 0 ≤ exponentialTailBound (Real.pi / 4) 2 :=
    exponentialTailBound_nonneg (by positivity) (by norm_num)
  have htail : 2 * Real.exp (-a) * exponentialTailBound (Real.pi / 4) (2 * a) ≤
      (2 * exponentialTailBound (Real.pi / 4) 2) * R := by
    have hm := mul_le_mul_of_nonneg_left (prime_exponentialTailBound_linear ha)
      (show 0 ≤ 2 * Real.exp (-a) by positivity)
    have hm' := mul_le_mul_of_nonneg_left hR1
      (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hG0)
    nlinarith
  unfold primeTailFactor primeTailConstant
  have hsum := add_le_add (add_le_add hdiag hmiddle) htail
  dsimp [R] at hsum
  nlinarith

#print axioms primeTailConstant_nonneg
#print axioms primeTailFactor_nonneg
#print axioms primeTailFactor_le

end ThetaTrial.Paper
