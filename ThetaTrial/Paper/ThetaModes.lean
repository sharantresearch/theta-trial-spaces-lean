import ThetaTrial.ThetaSeries.Kernel
import ThetaTrial.Paper.Definitions
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

/-!
# Theta modes for the theta-derivative construction

`thetaPhiTerm` in `ThetaSeries` uses half the normalization of the paper;
`paperThetaMode` includes the factor two. The results below concern single
theta modes and complex polynomials (Lemma `deriv:exact-modes`).
-/

noncomputable section

open Polynomial
open scoped Polynomial

namespace ThetaTrial.Paper

/-- Index n represents the positive integer n+1. -/
def paperThetaMode (n : ℕ) (u : ℝ) : ℝ :=
  2 * ThetaTrial.ThetaSeries.thetaPhiTerm n u

theorem paperThetaMode_formula (n : ℕ) (u : ℝ) :
    paperThetaMode n u =
      (4 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u / 2) -
       6 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u / 2)) *
      Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u)) := by
  unfold paperThetaMode ThetaTrial.ThetaSeries.thetaPhiTerm
  ring

theorem paperThetaMode_summable (u : ℝ) :
    Summable (fun n => paperThetaMode n u) :=
  (ThetaTrial.ThetaSeries.thetaPhiTerm_summable u).mul_left 2

theorem paperThetaMode_tsum (u : ℝ) :
    (∑' n : ℕ, paperThetaMode n u) = 2 * ThetaTrial.ThetaSeries.thetaPhi u := by
  simp only [paperThetaMode, ThetaTrial.ThetaSeries.thetaPhi, tsum_mul_left]

theorem paperThetaMode_pos (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 < paperThetaMode n u :=
  mul_pos (by norm_num) (ThetaTrial.ThetaSeries.thetaPhiTerm_pos n hu)

private theorem exp_two_log (x : ℝ) (hx : 0 < x) :
    Real.exp (2 * Real.log x) = x ^ 2 := by
  rw [show 2 * Real.log x = Real.log x + Real.log x by ring,
    Real.exp_add, Real.exp_log hx]
  ring

theorem thetaQ_shift (n : ℕ) (u : ℝ) :
    ThetaTrial.ThetaSeries.thetaQ 0 (u + Real.log ((n : ℝ) + 1)) =
      ThetaTrial.ThetaSeries.thetaQ n u := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  simp only [ThetaTrial.ThetaSeries.thetaQ, Nat.cast_zero, zero_add, one_pow, mul_one]
  rw [show 2 * (u + Real.log ((n : ℝ) + 1)) =
      2 * u + 2 * Real.log ((n : ℝ) + 1) by ring,
    Real.exp_add, exp_two_log _ hn]
  ring

private theorem paperThetaMode_factor (n : ℕ) (u : ℝ) :
    paperThetaMode n u =
      (4 * ThetaTrial.ThetaSeries.thetaQ n u ^ 2 - 6 * ThetaTrial.ThetaSeries.thetaQ n u) *
        ThetaTrial.ThetaSeries.thetaBTerm n u := by
  have h := ThetaTrial.ThetaSeries.thetaBSecondTerm_sub_quarter n u
  dsimp [ThetaTrial.ThetaSeries.thetaBSecondTerm] at h
  dsimp [paperThetaMode]
  linear_combination -h

/-- Exact translation identity, with the amplitude written as an exponential
of a logarithm rather than as an ambiguous real power. -/
theorem paperThetaMode_shift (n : ℕ) (u : ℝ) :
    paperThetaMode n u =
      Real.exp (-Real.log ((n : ℝ) + 1) / 2) *
        paperThetaMode 0 (u + Real.log ((n : ℝ) + 1)) := by
  rw [paperThetaMode_factor, paperThetaMode_factor, thetaQ_shift]
  have hb :
      Real.exp (-Real.log ((n : ℝ) + 1) / 2) *
        ThetaTrial.ThetaSeries.thetaBTerm 0 (u + Real.log ((n : ℝ) + 1)) =
      ThetaTrial.ThetaSeries.thetaBTerm n u := by
    have hq := thetaQ_shift n u
    simp only [ThetaTrial.ThetaSeries.thetaQ] at hq
    simp only [ThetaTrial.ThetaSeries.thetaBTerm, Nat.cast_zero]
    rw [show -Real.pi * ((0 : ℝ) + 1) ^ 2 *
        Real.exp (2 * (u + Real.log ((n : ℝ) + 1))) =
        -Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u) by
          linear_combination -hq]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [← hb]
  ring

/-- Translation commutes with each ordinary derivative. -/
theorem paperThetaMode_iteratedDeriv_shift (k n : ℕ) (u : ℝ) :
    iteratedDeriv k (paperThetaMode n) u =
      Real.exp (-Real.log ((n : ℝ) + 1) / 2) *
        iteratedDeriv k (paperThetaMode 0) (u + Real.log ((n : ℝ) + 1)) := by
  have hfun : paperThetaMode n = fun v =>
      Real.exp (-Real.log ((n : ℝ) + 1) / 2) *
        paperThetaMode 0 (v + Real.log ((n : ℝ) + 1)) :=
    funext (paperThetaMode_shift n)
  rw [hfun, iteratedDeriv_const_mul_field, iteratedDeriv_comp_add_const]

/-- Polynomial operation induced by D=-i d/du after factoring
2π exp(5u/2) exp(-π exp(2u)). -/
def thetaPolyStep (R : ℂ[X]) : ℂ[X] :=
  C (2 * Complex.I) * (X * R) +
    C (-(5 / 2 : ℂ) * Complex.I) * R +
    C (-2 * Complex.I) * (X * R.derivative)

theorem thetaPolyStep_coeff_succ (R : ℂ[X]) (k : ℕ) :
    (thetaPolyStep R).coeff (k + 1) =
      (2 * Complex.I) * R.coeff k -
        Complex.I * (5 / 2 + 2 * ((k : ℂ) + 1)) * R.coeff (k + 1) := by
  simp only [thetaPolyStep, coeff_add, coeff_C_mul, coeff_X_mul,
    coeff_derivative]
  ring

theorem thetaPolyStep_natDegree_le (R : ℂ[X]) :
    (thetaPolyStep R).natDegree ≤ R.natDegree + 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  cases k with
  | zero => omega
  | succ k =>
    rw [thetaPolyStep_coeff_succ,
      coeff_eq_zero_of_natDegree_lt (by omega : R.natDegree < k),
      coeff_eq_zero_of_natDegree_lt (by omega : R.natDegree < k + 1)]
    ring

theorem thetaPolyStep_topCoeff (R : ℂ[X]) :
    (thetaPolyStep R).coeff (R.natDegree + 1) =
      2 * Complex.I * R.leadingCoeff := by
  rw [thetaPolyStep_coeff_succ, coeff_natDegree_succ_eq_zero, coeff_natDegree]
  ring

theorem thetaPolyStep_ne_zero {R : ℂ[X]} (hR : R ≠ 0) :
    thetaPolyStep R ≠ 0 := by
  intro hz
  have h := thetaPolyStep_topCoeff R
  rw [hz, coeff_zero] at h
  have hn : (2 : ℂ) * Complex.I * R.leadingCoeff ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (leadingCoeff_ne_zero.mpr hR)
  exact hn h.symm

theorem thetaPolyStep_natDegree {R : ℂ[X]} (hR : R ≠ 0) :
    (thetaPolyStep R).natDegree = R.natDegree + 1 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (thetaPolyStep_natDegree_le R)
  rw [thetaPolyStep_topCoeff]
  exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
    (leadingCoeff_ne_zero.mpr hR)

theorem thetaPolyStep_leadingCoeff {R : ℂ[X]} (hR : R ≠ 0) :
    (thetaPolyStep R).leadingCoeff = 2 * Complex.I * R.leadingCoeff := by
  rw [← coeff_natDegree, thetaPolyStep_natDegree hR, thetaPolyStep_topCoeff]

/-- The common weight for the first mode. -/
def thetaModeWeight (u : ℝ) : ℝ :=
  2 * Real.pi * Real.exp (5 * u / 2) *
    Real.exp (-ThetaTrial.ThetaSeries.thetaQ 0 u)

def thetaPolyProfile (R : ℂ[X]) (u : ℝ) : ℂ :=
  (thetaModeWeight u : ℂ) * R.eval (ThetaTrial.ThetaSeries.thetaQ 0 u : ℂ)

def thetaBasePoly : ℂ[X] := C 2 * X - C 3

theorem thetaBasePoly_profile (u : ℝ) :
    thetaPolyProfile thetaBasePoly u = (paperThetaMode 0 u : ℂ) := by
  rw [paperThetaMode, ThetaTrial.ThetaSeries.thetaPhiTerm_factor]
  simp only [thetaPolyProfile, thetaBasePoly, thetaModeWeight,
    eval_sub, eval_mul, eval_C, eval_X, ThetaTrial.ThetaSeries.thetaQ, Nat.cast_zero,
    zero_add, one_pow, mul_one]
  push_cast
  ring

theorem thetaQ_hasDerivAt (u : ℝ) :
    HasDerivAt (ThetaTrial.ThetaSeries.thetaQ 0) (2 * ThetaTrial.ThetaSeries.thetaQ 0 u) u := by
  have heq : ThetaTrial.ThetaSeries.thetaQ 0 = fun v : ℝ => Real.pi * Real.exp (2 * v) := by
    funext v
    simp [ThetaTrial.ThetaSeries.thetaQ]
  rw [heq]
  have hd := (((hasDerivAt_id u).const_mul 2).exp).const_mul Real.pi
  simpa only [mul_one,
    one_mul, id_eq, mul_assoc, mul_left_comm, mul_comm] using hd

theorem thetaModeWeight_hasDerivAt (u : ℝ) :
    HasDerivAt thetaModeWeight
      (thetaModeWeight u * (5 / 2 - 2 * ThetaTrial.ThetaSeries.thetaQ 0 u)) u := by
  have h₁ := ((((hasDerivAt_id u).const_mul 5).div_const 2).exp).const_mul
    (2 * Real.pi)
  have h₂ := ((thetaQ_hasDerivAt u).neg).exp
  convert h₁.mul h₂ using 1 <;>
    first | rfl | (dsimp [thetaModeWeight]; ring)

/-- The differential operator used by the paper. -/
def thetaD (g : ℝ → ℂ) (u : ℝ) : ℂ := -Complex.I * deriv g u

theorem thetaD_polyProfile (R : ℂ[X]) :
    thetaD (thetaPolyProfile R) = thetaPolyProfile (thetaPolyStep R) := by
  funext u
  have hp := (R.hasDerivAt (ThetaTrial.ThetaSeries.thetaQ 0 u : ℂ)).comp u
    (thetaQ_hasDerivAt u).ofReal_comp
  have hw := (thetaModeWeight_hasDerivAt u).ofReal_comp
  have hd := hw.mul hp
  change -Complex.I * deriv (thetaPolyProfile R) u = _
  rw [show deriv (thetaPolyProfile R) u = _ from hd.deriv]
  simp only [thetaPolyProfile, thetaPolyStep, eval_add, eval_mul, eval_C, eval_X,
    Function.comp_apply]
  push_cast
  ring

def thetaDerivativePoly (k : ℕ) : ℂ[X] :=
  thetaPolyStep^[k] thetaBasePoly

theorem thetaDerivativePoly_zero : thetaDerivativePoly 0 = thetaBasePoly := rfl

theorem thetaDerivativePoly_succ (k : ℕ) :
    thetaDerivativePoly (k + 1) = thetaPolyStep (thetaDerivativePoly k) := by
  simp only [thetaDerivativePoly, Function.iterate_succ_apply']

theorem thetaDerivativePoly_nonzero (k : ℕ) : thetaDerivativePoly k ≠ 0 := by
  induction k with
  | zero =>
    intro h
    have hc := congrArg (fun R : ℂ[X] => R.coeff 1) h
    norm_num [thetaDerivativePoly, thetaBasePoly] at hc
  | succ k ih => exact thetaDerivativePoly_succ k ▸ thetaPolyStep_ne_zero ih

theorem thetaDerivativePoly_natDegree (k : ℕ) :
    (thetaDerivativePoly k).natDegree = k + 1 := by
  induction k with
  | zero =>
    norm_num [thetaDerivativePoly, thetaBasePoly, natDegree_sub_C]
  | succ k ih =>
    rw [thetaDerivativePoly_succ, thetaPolyStep_natDegree
      (thetaDerivativePoly_nonzero k), ih]

theorem thetaDerivativePoly_represents (k : ℕ) :
    thetaD^[k] (fun u => (paperThetaMode 0 u : ℂ)) =
      thetaPolyProfile (thetaDerivativePoly k) := by
  induction k with
  | zero => exact funext fun u => (thetaBasePoly_profile u).symm
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, thetaD_polyProfile,
      thetaDerivativePoly_succ]

theorem thetaDerivativePoly_leadingCoeff (k : ℕ) :
    (thetaDerivativePoly k).leadingCoeff = (2 * Complex.I) ^ k * 2 := by
  induction k with
  | zero =>
    rw [← coeff_natDegree, thetaDerivativePoly_natDegree]
    norm_num [thetaDerivativePoly, thetaBasePoly]
  | succ k ih =>
    rw [thetaDerivativePoly_succ,
      thetaPolyStep_leadingCoeff (thetaDerivativePoly_nonzero k), ih, pow_succ]
    ring

/-- Finite polynomial multiplier of the first-mode derivative polynomials. -/
def thetaMultiplierPoly (P : ℂ[X]) : ℂ[X] :=
  ∑ k ∈ Finset.range (P.natDegree + 1), C (P.coeff k) * thetaDerivativePoly k

theorem thetaMultiplierPoly_natDegree_le (P : ℂ[X]) :
    (thetaMultiplierPoly P).natDegree ≤ P.natDegree + 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  simp only [thetaMultiplierPoly, finsetSum_coeff, coeff_C_mul]
  apply Finset.sum_eq_zero
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have hd : (thetaDerivativePoly k).natDegree < j := by
    rw [thetaDerivativePoly_natDegree]
    omega
  rw [coeff_eq_zero_of_natDegree_lt hd, mul_zero]

theorem thetaMultiplierPoly_topCoeff (P : ℂ[X]) :
    (thetaMultiplierPoly P).coeff (P.natDegree + 1) =
      P.leadingCoeff * ((2 * Complex.I) ^ P.natDegree * 2) := by
  simp only [thetaMultiplierPoly, finsetSum_coeff, coeff_C_mul]
  rw [Finset.sum_eq_single P.natDegree]
  · rw [coeff_natDegree]
    rw [← thetaDerivativePoly_natDegree P.natDegree, coeff_natDegree,
      thetaDerivativePoly_leadingCoeff]
  · intro k hk hne
    have hk' := Finset.mem_range.mp hk
    have hd : (thetaDerivativePoly k).natDegree < P.natDegree + 1 := by
      rw [thetaDerivativePoly_natDegree]
      omega
    rw [coeff_eq_zero_of_natDegree_lt hd, mul_zero]
  · intro hn
    exact (hn (Finset.mem_range.mpr (Nat.lt_succ_self _))).elim

theorem thetaMultiplierPoly_ne_zero {P : ℂ[X]} (hP : P ≠ 0) :
    thetaMultiplierPoly P ≠ 0 := by
  intro hz
  have h := thetaMultiplierPoly_topCoeff P
  rw [hz, coeff_zero] at h
  have hn : P.leadingCoeff * ((2 * Complex.I) ^ P.natDegree * 2) ≠ 0 :=
    mul_ne_zero (leadingCoeff_ne_zero.mpr hP)
      (mul_ne_zero (pow_ne_zero _ (mul_ne_zero (by norm_num) Complex.I_ne_zero))
        (by norm_num))
  exact hn h.symm

theorem thetaMultiplierPoly_natDegree {P : ℂ[X]} (hP : P ≠ 0) :
    (thetaMultiplierPoly P).natDegree = P.natDegree + 1 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (thetaMultiplierPoly_natDegree_le P)
  rw [thetaMultiplierPoly_topCoeff]
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr hP)
    (mul_ne_zero (pow_ne_zero _ (mul_ne_zero (by norm_num) Complex.I_ne_zero))
      (by norm_num))

/-- Applying a polynomial in the operator D to a smooth complex function. -/
def thetaPolynomialOperator (P : ℂ[X]) (g : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * (thetaD^[k] g) u

theorem thetaMultiplierPoly_represents (P : ℂ[X]) :
    thetaPolynomialOperator P (fun u => (paperThetaMode 0 u : ℂ)) =
      thetaPolyProfile (thetaMultiplierPoly P) := by
  funext u
  simp only [thetaPolynomialOperator, thetaDerivativePoly_represents,
    thetaPolyProfile, thetaMultiplierPoly, eval_finsetSum, eval_mul, eval_C]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem thetaQ_injective : Function.Injective (ThetaTrial.ThetaSeries.thetaQ 0) := by
  intro u v h
  simp only [ThetaTrial.ThetaSeries.thetaQ, Nat.cast_zero, zero_add, one_pow, mul_one] at h
  have hExp := (mul_left_cancel₀ (ne_of_gt Real.pi_pos)) h
  have huv := Real.exp_injective hExp
  linarith

theorem thetaModeWeight_pos (u : ℝ) : 0 < thetaModeWeight u := by
  unfold thetaModeWeight
  positivity

/-- The polynomial representation, as an identity of functions on the real
line. -/
theorem thetaPolyProfile_eq_zero_iff (R : ℂ[X]) :
    thetaPolyProfile R = 0 ↔ R = 0 := by
  constructor
  · intro h
    apply R.eq_zero_of_infinite_isRoot
    have hi : Function.Injective (fun u : ℝ => (ThetaTrial.ThetaSeries.thetaQ 0 u : ℂ)) :=
      Complex.ofReal_injective.comp thetaQ_injective
    apply (Set.infinite_range_of_injective hi).mono
    rintro z ⟨u, rfl⟩
    have he := congrFun h u
    change (thetaModeWeight u : ℂ) * R.eval (ThetaTrial.ThetaSeries.thetaQ 0 u : ℂ) = 0 at he
    exact (mul_eq_zero.mp he).resolve_left
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (thetaModeWeight_pos u)))
  · rintro rfl
    funext u
    simp [thetaPolyProfile]

theorem thetaPolynomialOperator_firstMode_ne_zero {P : ℂ[X]} (hP : P ≠ 0) :
    thetaPolynomialOperator P (fun u => (paperThetaMode 0 u : ℂ)) ≠ 0 := by
  rw [thetaMultiplierPoly_represents, ne_eq, thetaPolyProfile_eq_zero_iff]
  exact thetaMultiplierPoly_ne_zero hP

theorem thetaD_const_mul (c : ℂ) (g : ℝ → ℂ) :
    thetaD (fun u => c * g u) = fun u => c * thetaD g u := by
  funext u
  simp only [thetaD, deriv_const_mul_field]
  ring

theorem thetaD_translate (g : ℝ → ℂ) (a : ℝ) :
    thetaD (fun u => g (u + a)) = fun u => thetaD g (u + a) := by
  funext u
  simp only [thetaD, deriv_comp_add_const]

theorem thetaD_iterate_const_mul (k : ℕ) (c : ℂ) (g : ℝ → ℂ) :
    thetaD^[k] (fun u => c * g u) = fun u => c * (thetaD^[k] g) u := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, thetaD_const_mul]
    simp only [Function.iterate_succ_apply']

theorem thetaD_iterate_translate (k : ℕ) (g : ℝ → ℂ) (a : ℝ) :
    thetaD^[k] (fun u => g (u + a)) = fun u => (thetaD^[k] g) (u + a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, thetaD_translate]
    simp only [Function.iterate_succ_apply']

/-- Full mode translation after applying an arbitrary complex polynomial in D. -/
theorem thetaPolynomialOperator_mode_shift (P : ℂ[X]) (n : ℕ) (u : ℝ) :
    thetaPolynomialOperator P (fun v => (paperThetaMode n v : ℂ)) u =
      (Real.exp (-Real.log ((n : ℝ) + 1) / 2) : ℂ) *
        thetaPolynomialOperator P (fun v => (paperThetaMode 0 v : ℂ))
          (u + Real.log ((n : ℝ) + 1)) := by
  have hfun : (fun v => (paperThetaMode n v : ℂ)) =
      fun v => (Real.exp (-Real.log ((n : ℝ) + 1) / 2) : ℂ) *
        (paperThetaMode 0 (v + Real.log ((n : ℝ) + 1)) : ℂ) := by
    funext v
    rw [paperThetaMode_shift, Complex.ofReal_mul]
  simp only [thetaPolynomialOperator, hfun, thetaD_iterate_const_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [congrFun (thetaD_iterate_translate k
    (fun v => (paperThetaMode 0 v : ℂ)) (Real.log ((n : ℝ) + 1))) u]
  ring

theorem thetaD_eq_differentialOperator : thetaD = differentialOperator := rfl

/-- Converts the sum over a degree range into the sum over the support used in
the paper. -/
theorem thetaPolynomialOperator_eq_polynomialDerivative (P : ℂ[X]) (g : ℝ → ℂ) :
    thetaPolynomialOperator P g = polynomialDerivative P g := by
  funext u
  have h := P.sum_over_range
    (f := fun j c => c * ((differentialOperator^[j]) g) u)
    (fun j => zero_mul _)
  simpa only [Polynomial.sum_def, thetaPolynomialOperator, polynomialDerivative,
    thetaD_eq_differentialOperator] using h.symm

theorem paperThetaMode_eq_complexThetaMode (n : ℕ) (u : ℝ) :
    (paperThetaMode n u : ℂ) = complexThetaMode n (u : ℂ) := by
  rw [paperThetaMode_formula]
  simp only [complexThetaMode, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_ofNat, Complex.ofReal_natCast, Complex.ofReal_exp,
    Complex.ofReal_neg, Complex.ofReal_div]

theorem polynomialDerivative_firstMode_ne_zero {P : ℂ[X]} (hP : P ≠ 0) :
    polynomialDerivative P (fun u => (paperThetaMode 0 u : ℂ)) ≠ 0 := by
  rw [← thetaPolynomialOperator_eq_polynomialDerivative]
  exact thetaPolynomialOperator_firstMode_ne_zero hP

theorem polynomialDerivative_mode_shift (P : ℂ[X]) (n : ℕ) (u : ℝ) :
    polynomialDerivative P (fun v => (paperThetaMode n v : ℂ)) u =
      (Real.exp (-Real.log ((n : ℝ) + 1) / 2) : ℂ) *
        polynomialDerivative P (fun v => (paperThetaMode 0 v : ℂ))
          (u + Real.log ((n : ℝ) + 1)) := by
  simpa only [thetaPolynomialOperator_eq_polynomialDerivative] using
    thetaPolynomialOperator_mode_shift P n u

theorem thetaModeWeight_paper_normalization (u : ℝ) :
    thetaModeWeight u =
      (2 * Real.pi ^ (-(1 / 4 : ℝ))) *
        Real.exp (-ThetaTrial.ThetaSeries.thetaQ 0 u) *
        (ThetaTrial.ThetaSeries.thetaQ 0 u) ^ (5 / 4 : ℝ) := by
  have hy : ThetaTrial.ThetaSeries.thetaQ 0 u = Real.pi * Real.exp (2 * u) := by
    simp [ThetaTrial.ThetaSeries.thetaQ]
  have he : (Real.exp (2 * u)) ^ (5 / 4 : ℝ) = Real.exp (5 * u / 2) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have hp : Real.pi ^ (-(1 / 4 : ℝ)) * Real.pi ^ (5 / 4 : ℝ) = Real.pi := by
    rw [← Real.rpow_add Real.pi_pos]
    norm_num
  rw [thetaModeWeight, hy, Real.mul_rpow Real.pi_pos.le (Real.exp_pos _).le, he]
  linear_combination -2 * Real.exp (5 * u / 2) *
    Real.exp (-(Real.pi * Real.exp (2 * u))) * hp

/-- Exactly the polynomial R_P in the paper's factor exp(-y)y^(5/4)R_P(y). -/
def thetaPaperPolynomial (P : ℂ[X]) : ℂ[X] :=
  C ((2 * Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) * thetaMultiplierPoly P

private theorem thetaPaperPolynomial_scalar_ne_zero :
    ((2 * Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  exact ne_of_gt (mul_pos (by norm_num) (Real.rpow_pos_of_pos Real.pi_pos _))

theorem thetaPaperPolynomial_ne_zero {P : ℂ[X]} (hP : P ≠ 0) :
    thetaPaperPolynomial P ≠ 0 :=
  mul_ne_zero (C_ne_zero.mpr thetaPaperPolynomial_scalar_ne_zero)
    (thetaMultiplierPoly_ne_zero hP)

theorem thetaPaperPolynomial_natDegree {P : ℂ[X]} (hP : P ≠ 0) :
    (thetaPaperPolynomial P).natDegree = P.natDegree + 1 := by
  rw [thetaPaperPolynomial, natDegree_C_mul thetaPaperPolynomial_scalar_ne_zero,
    thetaMultiplierPoly_natDegree hP]

/-- First-mode polynomial representation with the paper normalization. -/
theorem polynomialDerivative_firstMode_representation (P : ℂ[X]) (u : ℝ) :
    polynomialDerivative P (fun v => (paperThetaMode 0 v : ℂ)) u =
      (Real.exp (-ThetaTrial.ThetaSeries.thetaQ 0 u) : ℂ) *
        ((ThetaTrial.ThetaSeries.thetaQ 0 u) ^ (5 / 4 : ℝ) : ℝ) *
        (thetaPaperPolynomial P).eval (ThetaTrial.ThetaSeries.thetaQ 0 u : ℂ) := by
  rw [← thetaPolynomialOperator_eq_polynomialDerivative,
    thetaMultiplierPoly_represents]
  simp only [thetaPolyProfile, thetaPaperPolynomial, eval_mul, eval_C]
  rw [thetaModeWeight_paper_normalization]
  push_cast
  ring

theorem polynomialDerivative_mode_shift_rpow (P : ℂ[X]) (n : ℕ) (u : ℝ) :
    polynomialDerivative P (fun v => (paperThetaMode n v : ℂ)) u =
      (((n : ℝ) + 1) ^ (-(1 / 2 : ℝ)) : ℝ) *
        polynomialDerivative P (fun v => (paperThetaMode 0 v : ℂ))
          (u + Real.log ((n : ℝ) + 1)) := by
  rw [polynomialDerivative_mode_shift]
  have he : Real.exp (-Real.log ((n : ℝ) + 1) / 2) =
      ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    congr 1
    ring
  rw [he]

/-- The first-mode profile cannot vanish on an infinite real set. -/
theorem thetaPolyProfile_zero_of_infinite {R : ℂ[X]} {S : Set ℝ}
    (hS : S.Infinite) (hzero : ∀ u ∈ S, thetaPolyProfile R u = 0) : R = 0 := by
  apply R.eq_zero_of_infinite_isRoot
  have hi : Function.Injective (fun u : ℝ => (ThetaTrial.ThetaSeries.thetaQ 0 u : ℂ)) :=
    Complex.ofReal_injective.comp thetaQ_injective
  apply (hS.image hi.injOn).mono
  rintro z ⟨u, hu, rfl⟩
  have he := hzero u hu
  change (thetaModeWeight u : ℂ) * R.eval (ThetaTrial.ThetaSeries.thetaQ 0 u : ℂ) = 0 at he
  exact (mul_eq_zero.mp he).resolve_left
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (thetaModeWeight_pos u)))

/-- Nontriviality holds on every exterior interval, not only somewhere on R. -/
theorem polynomialDerivative_firstMode_nonzero_on_tail {P : ℂ[X]}
    (hP : P ≠ 0) (a : ℝ) :
    ∃ u : ℝ, a < u ∧
      polynomialDerivative P (fun v => (paperThetaMode 0 v : ℂ)) u ≠ 0 := by
  by_contra h
  push_neg at h
  apply thetaMultiplierPoly_ne_zero hP
  apply thetaPolyProfile_zero_of_infinite (Set.Ioi_infinite a)
  intro u hu
  have he := h u hu
  rw [← thetaPolynomialOperator_eq_polynomialDerivative,
    thetaMultiplierPoly_represents] at he
  exact he

end ThetaTrial.Paper
