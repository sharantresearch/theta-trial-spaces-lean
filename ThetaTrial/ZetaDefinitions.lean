import ThetaTrial.Xi
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Tactic.Linarith

/-!
# Zeros of zeta and Xi, and the critical strip

The nontrivial zeros of zeta, defined by the same three conditions as in
Mathlib's `RiemannHypothesis`, and their description through the entire
function `Xi`. That zeros lie in the open strip uses Mathlib's
`riemannZeta_ne_zero_of_one_le_re`.
-/

noncomputable section

namespace ThetaTrial

open Complex Set

/-- The nontrivial zeros of zeta, defined as in Mathlib's `RiemannHypothesis`. -/
def NontrivialZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ (¬ ∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1

theorem xi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : xi s ≠ 0 := by
  by_cases hs1 : s = 1
  · simp [hs1]
  have hpos : 0 < s.re := lt_of_lt_of_le zero_lt_one hs
  have hs0 : s ≠ 0 := by
    intro h
    simp [h] at hpos
  rw [xi_eq_gamma_zeta_of_re_pos hpos hs1]
  exact mul_ne_zero
    (mul_ne_zero (div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) (by norm_num))
      (Gammaℝ_ne_zero_of_re_pos hpos))
    (riemannZeta_ne_zero_of_one_le_re hs)

theorem xi_ne_zero_of_re_le_zero {s : ℂ} (hs : s.re ≤ 0) : xi s ≠ 0 := by
  rw [← xi_one_sub s]
  apply xi_ne_zero_of_one_le_re
  simp only [sub_re, one_re]
  linarith

/-- Every zero of the entire xi is strictly inside the critical strip. -/
theorem xi_zero_strict_strip {s : ℂ} (hs : xi s = 0) : 0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra h
    exact xi_ne_zero_of_re_le_zero (le_of_not_gt h) hs
  · by_contra h
    exact xi_ne_zero_of_one_le_re (le_of_not_gt h) hs

theorem NontrivialZetaZero.ne_zero {s : ℂ} (hs : NontrivialZetaZero s) : s ≠ 0 := by
  intro h
  have hz := hs.1
  simp [h, riemannZeta_zero] at hz

theorem NontrivialZetaZero.gamma_ne_zero {s : ℂ} (hs : NontrivialZetaZero s) :
    Gammaℝ s ≠ 0 := by
  rw [Ne, Gammaℝ_eq_zero_iff]
  rintro ⟨n, hn⟩
  cases n with
  | zero => exact hs.ne_zero (by simpa using hn)
  | succ n =>
      apply hs.2.1
      refine ⟨n, ?_⟩
      simpa [Nat.cast_add, Nat.cast_one, neg_mul] using hn

/-- A nontrivial zero of zeta is a zero of the entire xi extension. -/
theorem NontrivialZetaZero.xi_eq_zero {s : ℂ} (hs : NontrivialZetaZero s) : xi s = 0 := by
  rw [xi_eq_gamma_zeta_of_ne_zero hs.ne_zero hs.2.2 hs.gamma_ne_zero, hs.1]
  simp

/-- The two notions of zero agree. -/
theorem xi_eq_zero_iff_nontrivialZetaZero (s : ℂ) : xi s = 0 ↔ NontrivialZetaZero s := by
  refine ⟨fun hs => ?_, NontrivialZetaZero.xi_eq_zero⟩
  obtain ⟨hpos, hlt⟩ := xi_zero_strict_strip hs
  have hs0 : s ≠ 0 := by
    intro h
    simp [h] at hpos
  have hs1 : s ≠ 1 := by
    intro h
    simp [h] at hlt
  have hfactor : s * (s - 1) / 2 * Gammaℝ s ≠ 0 :=
    mul_ne_zero (div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) (by norm_num))
      (Gammaℝ_ne_zero_of_re_pos hpos)
  have hz : riemannZeta s = 0 := by
    rw [xi_eq_gamma_zeta_of_re_pos hpos hs1] at hs
    exact (mul_eq_zero.mp hs).resolve_left hfactor
  refine ⟨hz, ?_, hs1⟩
  rintro ⟨n, hn⟩
  have hre := congrArg Complex.re hn
  simp only [mul_re, neg_re, re_ofNat, add_re, natCast_re, one_re, neg_im,
    im_ofNat, add_im, natCast_im, one_im, zero_add, neg_zero, zero_mul, sub_zero] at hre
  have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- The zero set in the coordinate `1/2 - iz`. -/
def XiZeros : Set ℂ := Xi ⁻¹' {0}

@[simp] theorem mem_XiZeros {z : ℂ} : z ∈ XiZeros ↔ Xi z = 0 := Iff.rfl

end ThetaTrial
