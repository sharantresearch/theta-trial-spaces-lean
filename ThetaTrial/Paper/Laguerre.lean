import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Concrete Laguerre polynomials and exponential integrals

This file proves the Laguerre ingredient of the theta-trial paper from the
coefficient formula. It proves orthonormality, the three-term
recurrence, the coefficient-uniform first-moment bound for every complex
polynomial of bounded degree, and the full positive-rate moment-ratio
inequality. The rate derivative follows from finite Gamma sums.
-/

noncomputable section

open MeasureTheory Set Polynomial
open scoped Polynomial

namespace ThetaTrial.Paper

def laguerrePolynomial (n : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (n + 1),
    C ((-1 : ℝ) ^ j * (n.choose j : ℝ) / (j.factorial : ℝ)) * X ^ j

theorem laguerrePolynomial_eval (n : ℕ) (x : ℝ) :
    (laguerrePolynomial n).eval x =
      ∑ j ∈ Finset.range (n + 1),
        ((-1 : ℝ) ^ j * (n.choose j : ℝ) / (j.factorial : ℝ)) * x ^ j := by
  simp [laguerrePolynomial, eval_finsetSum]

theorem laguerrePolynomial_zero : laguerrePolynomial 0 = 1 := by
  norm_num [laguerrePolynomial]

theorem laguerrePolynomial_one : laguerrePolynomial 1 = 1 - X := by
  norm_num [laguerrePolynomial, Finset.sum_range_succ]
  ring

theorem laguerrePolynomial_coeff (n k : ℕ) :
    (laguerrePolynomial n).coeff k =
      (-1 : ℝ) ^ k * (n.choose k : ℝ) / (k.factorial : ℝ) := by
  by_cases hk : k < n + 1
  · simp [laguerrePolynomial, finsetSum_coeff, coeff_C_mul, coeff_X_pow, hk]
  · have hnk : n < k := by omega
    simp [laguerrePolynomial, finsetSum_coeff, coeff_C_mul, coeff_X_pow, hk,
      Nat.choose_eq_zero_of_lt hnk]

theorem laguerrePolynomial_natDegree (n : ℕ) :
    (laguerrePolynomial n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    simp [laguerrePolynomial_coeff, Nat.choose_eq_zero_of_lt hk]
  · rw [laguerrePolynomial_coeff, Nat.choose_self, Nat.cast_one, mul_one]
    exact div_ne_zero (pow_ne_zero _ (by norm_num))
      (by exact_mod_cast Nat.factorial_ne_zero n)

theorem laguerrePolynomial_leadingCoeff (n : ℕ) :
    (laguerrePolynomial n).leadingCoeff =
      (-1 : ℝ) ^ n / (n.factorial : ℝ) := by
  rw [← coeff_natDegree, laguerrePolynomial_natDegree, laguerrePolynomial_coeff]
  simp

/-- A differential identity for the Laguerre family. -/
theorem laguerrePolynomial_derivative_succ (n : ℕ) :
    (laguerrePolynomial (n + 1)).derivative =
      (laguerrePolynomial n).derivative - laguerrePolynomial n := by
  ext k
  simp only [coeff_derivative, coeff_sub, laguerrePolynomial_coeff]
  have hc : ((n + 1).choose (k + 1) : ℝ) =
      (n.choose k : ℝ) + (n.choose (k + 1) : ℝ) := by
    exact_mod_cast Nat.choose_succ_succ n k
  have hf : ((k + 1).factorial : ℝ) =
      ((k : ℝ) + 1) * (k.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_succ k
  have hfn : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hkn : (k : ℝ) + 1 ≠ 0 := by positivity
  rw [hc, hf, pow_succ]
  field_simp
  ring

theorem laguerrePolynomial_X_derivative_succ (n : ℕ) :
    X * (laguerrePolynomial (n + 1)).derivative =
      C ((n : ℝ) + 1) * (laguerrePolynomial (n + 1) - laguerrePolynomial n) := by
  ext k
  cases k with
  | zero =>
    simp [coeff_C_mul, laguerrePolynomial_coeff]
  | succ k =>
    simp only [coeff_X_mul, coeff_derivative, coeff_C_mul, coeff_sub,
      laguerrePolynomial_coeff]
    have hc : ((n + 1).choose (k + 1) : ℝ) =
        (n.choose k : ℝ) + (n.choose (k + 1) : ℝ) := by
      exact_mod_cast Nat.choose_succ_succ n k
    have hm : ((n : ℝ) + 1) * (n.choose k : ℝ) =
        ((n + 1).choose (k + 1) : ℝ) * ((k : ℝ) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq n k
    rw [hc] at hm ⊢
    linear_combination -((-1 : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ)) * hm

/-- The Laguerre Sturm--Liouville equation, as an exact polynomial identity. -/
theorem laguerrePolynomial_ode (n : ℕ) :
    X * (laguerrePolynomial n).derivative.derivative +
      (1 - X) * (laguerrePolynomial n).derivative +
      C (n : ℝ) * laguerrePolynomial n = 0 := by
  cases n with
  | zero => simp [laguerrePolynomial_zero]
  | succ n =>
    have h := laguerrePolynomial_X_derivative_succ n
    have hd := congrArg Polynomial.derivative h
    simp only [derivative_mul, derivative_X, derivative_C, derivative_sub,
      zero_mul, zero_add, one_mul] at hd
    have hdiff : (laguerrePolynomial (n + 1)).derivative -
        (laguerrePolynomial n).derivative = -laguerrePolynomial n := by
      rw [laguerrePolynomial_derivative_succ]
      ring
    rw [hdiff] at hd
    norm_num only [Nat.cast_add, Nat.cast_one]
    linear_combination hd - h

/-- Three-term recurrence with positive indices and no truncated subtraction. -/
theorem laguerrePolynomial_three_term (n : ℕ) :
    C ((n : ℝ) + 2) * laguerrePolynomial (n + 2) =
      (C (2 * (n : ℝ) + 3) - X) * laguerrePolynomial (n + 1) -
        C ((n : ℝ) + 1) * laguerrePolynomial n := by
  have h₁ := laguerrePolynomial_X_derivative_succ (n + 1)
  have h₀ := laguerrePolynomial_X_derivative_succ n
  rw [laguerrePolynomial_derivative_succ (n + 1)] at h₁
  norm_num only [Nat.cast_add, Nat.cast_one] at h₁
  have hc₁ : C ((n : ℝ) + 1 + 1) = C ((n : ℝ) + 2) := by congr 1; ring
  have hc₂ : C (2 * (n : ℝ) + 3) =
      C ((n : ℝ) + 2) + C ((n : ℝ) + 1) := by
    rw [← C_add]
    congr 1
    ring
  rw [hc₁] at h₁
  rw [hc₂]
  linear_combination h₀ - h₁

theorem integrableOn_pow_exp_neg_mul (n : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => x ^ n * Real.exp (-(r * x))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (n : ℝ)) (b := r)
    (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg n))
    (by norm_num) hr
  simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul] using h

theorem integral_pow_exp_neg_mul (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ in Ioi 0, x ^ n * Real.exp (-(r * x))) =
      (1 / r) ^ (n + 1) * (n.factorial : ℝ) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (n : ℝ) + 1) (r := r) (by positivity) hr
  rw [add_sub_cancel_right, Real.Gamma_nat_eq_factorial] at h
  have he : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by norm_num
  rw [he, Real.rpow_natCast] at h
  simpa only [Real.rpow_natCast] using h

theorem laguerrePolynomial_exp_integrable (n : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x : ℝ =>
      (laguerrePolynomial n).eval x * Real.exp (-(r * x))) (Ioi 0) := by
  simp_rw [laguerrePolynomial_eval, Finset.sum_mul]
  apply integrable_finsetSum
  intro j hj
  simpa only [mul_assoc] using
    (integrableOn_pow_exp_neg_mul j hr).const_mul
      ((-1 : ℝ) ^ j * (n.choose j : ℝ) / (j.factorial : ℝ))

/-- Exact Laplace transform of the concrete Laguerre polynomial, at every
positive real rate. -/
theorem laguerrePolynomial_laplace (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ in Ioi 0,
      (laguerrePolynomial n).eval x * Real.exp (-(r * x))) =
      (1 / r) * (1 - 1 / r) ^ n := by
  simp_rw [laguerrePolynomial_eval, Finset.sum_mul]
  rw [integral_finsetSum]
  · have hterm (j : ℕ) :
        (∫ x : ℝ in Ioi 0,
          ((-1 : ℝ) ^ j * (n.choose j : ℝ) / (j.factorial : ℝ)) *
            x ^ j * Real.exp (-(r * x))) =
          (1 / r) * ((-(1 / r)) ^ j * (n.choose j : ℝ)) := by
      rw [show (fun x : ℝ =>
          ((-1 : ℝ) ^ j * (n.choose j : ℝ) / (j.factorial : ℝ)) *
            x ^ j * Real.exp (-(r * x))) =
          fun x : ℝ => ((-1 : ℝ) ^ j * (n.choose j : ℝ) / (j.factorial : ℝ)) *
            (x ^ j * Real.exp (-(r * x))) by funext x; ring,
        integral_const_mul, integral_pow_exp_neg_mul j hr]
      have hf : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
      rw [pow_succ, neg_pow]
      field_simp
      ring
    simp_rw [hterm]
    rw [← Finset.mul_sum]
    congr 1
    have hbin := add_pow (-(1 / r)) (1 : ℝ) n
    simpa only [one_pow, mul_one, sub_eq_add_neg, add_comm] using hbin.symm
  · intro j hj
    simpa only [mul_assoc] using
      (integrableOn_pow_exp_neg_mul j hr).const_mul
        ((-1 : ℝ) ^ j * (n.choose j : ℝ) / (j.factorial : ℝ))

/-- Orthogonality to the constant polynomial, from the Laplace transform. -/
theorem laguerrePolynomial_integral_exp (n : ℕ) :
    (∫ x : ℝ in Ioi 0, (laguerrePolynomial n).eval x * Real.exp (-x)) =
      if n = 0 then 1 else 0 := by
  have h := laguerrePolynomial_laplace n (r := (1 : ℝ)) (by norm_num)
  simpa [zero_pow_eq] using h

theorem polynomial_exp_integrable (p : ℝ[X]) :
    IntegrableOn (fun x : ℝ => p.eval x * Real.exp (-x)) (Ioi 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [eval_add, add_mul, Pi.add_apply, IntegrableOn] using! hp.add hq
  | monomial n a =>
    simpa only [eval_monomial, mul_assoc, one_mul, IntegrableOn] using!
      (integrableOn_pow_exp_neg_mul n (r := (1 : ℝ)) (by norm_num)).const_mul a

/-- Integration against the exponential weight on the positive half-line. -/
def laguerreMoment : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := ∫ x : ℝ in Ioi 0, p.eval x * Real.exp (-x)
  map_add' p q := by
    simp only [eval_add, add_mul]
    exact integral_add (polynomial_exp_integrable p) (polynomial_exp_integrable q)
  map_smul' c p := by
    simp only [smul_eq_C_mul, eval_mul, eval_C, smul_eq_mul, mul_assoc,
      integral_const_mul, RingHom.id_apply]

theorem laguerreMoment_apply (p : ℝ[X]) :
    laguerreMoment p = ∫ x : ℝ in Ioi 0, p.eval x * Real.exp (-x) := rfl

theorem laguerreMoment_monomial (n : ℕ) (a : ℝ) :
    laguerreMoment (monomial n a) = a * (n.factorial : ℝ) := by
  rw [laguerreMoment_apply]
  simp only [eval_monomial, mul_assoc, integral_const_mul]
  congr 1
  simpa only [one_div_one, one_pow, one_mul] using
    integral_pow_exp_neg_mul n (r := (1 : ℝ)) (by norm_num)

theorem laguerreMoment_C_mul (c : ℝ) (p : ℝ[X]) :
    laguerreMoment (C c * p) = c * laguerreMoment p := by
  simp only [laguerreMoment_apply, eval_mul, eval_C, mul_assoc, integral_const_mul]

theorem laguerreMoment_C (c : ℝ) : laguerreMoment (C c) = c := by
  simpa only [monomial_zero_left, Nat.factorial_zero, Nat.cast_one, mul_one] using
    laguerreMoment_monomial 0 c

/-- Weighted integration by parts for every polynomial, proved by
Gamma moments including the endpoint term. -/
theorem laguerreMoment_derivative (p : ℝ[X]) :
    laguerreMoment p.derivative = laguerreMoment p - p.coeff 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [derivative_add, map_add, coeff_add, hp, hq]
    ring
  | monomial n a =>
    cases n with
    | zero =>
      simp [laguerreMoment_C]
    | succ n =>
      rw [derivative_monomial_succ, laguerreMoment_monomial,
        laguerreMoment_monomial]
      simp only [coeff_monomial, Nat.succ_ne_zero, if_false, sub_zero,
        Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring

def laguerreDifferential (p : ℝ[X]) : ℝ[X] :=
  X * p.derivative.derivative + (1 - X) * p.derivative

theorem laguerreDifferential_symmetric (p q : ℝ[X]) :
    laguerreMoment (laguerreDifferential p * q) =
      laguerreMoment (p * laguerreDifferential q) := by
  let W : ℝ[X] := X * (p.derivative * q - p * q.derivative)
  have hW : W.coeff 0 = 0 := by simp [W]
  have hI : laguerreMoment (W.derivative - W) = 0 := by
    rw [map_sub, laguerreMoment_derivative, hW]
    ring
  have hpoly : W.derivative - W =
      laguerreDifferential p * q - p * laguerreDifferential q := by
    simp only [W, derivative_mul, derivative_sub, derivative_X, one_mul,
      laguerreDifferential]
    ring
  rw [hpoly, map_sub] at hI
  exact sub_eq_zero.mp hI

theorem laguerreDifferential_eigenvector (n : ℕ) :
    laguerreDifferential (laguerrePolynomial n) =
      -(C (n : ℝ) * laguerrePolynomial n) := by
  have h := laguerrePolynomial_ode n
  change laguerreDifferential (laguerrePolynomial n) +
    C (n : ℝ) * laguerrePolynomial n = 0 at h
  exact eq_neg_of_add_eq_zero_left h

/-- Orthogonality of distinct Laguerre polynomials for the exponential weight. -/
theorem laguerrePolynomial_orthogonal {m n : ℕ} (hmn : m ≠ n) :
    laguerreMoment (laguerrePolynomial m * laguerrePolynomial n) = 0 := by
  have h := laguerreDifferential_symmetric (laguerrePolynomial m)
    (laguerrePolynomial n)
  rw [laguerreDifferential_eigenvector, laguerreDifferential_eigenvector] at h
  simp only [neg_mul, mul_neg, map_neg, mul_assoc] at h
  rw [laguerreMoment_C_mul] at h
  rw [show laguerrePolynomial m * (C (n : ℝ) * laguerrePolynomial n) =
      C (n : ℝ) * (laguerrePolynomial m * laguerrePolynomial n) by ring,
    laguerreMoment_C_mul] at h
  have hprod :
      ((m : ℝ) - (n : ℝ)) *
        laguerreMoment (laguerrePolynomial m * laguerrePolynomial n) = 0 := by
    linarith
  exact (mul_eq_zero.mp hprod).resolve_left
    (sub_ne_zero.mpr (by exact_mod_cast hmn))

theorem laguerrePolynomial_X_mul (n : ℕ) :
    X * laguerrePolynomial n =
      C (2 * (n : ℝ) + 1) * laguerrePolynomial n -
        C ((n : ℝ) + 1) * laguerrePolynomial (n + 1) -
          C (n : ℝ) * laguerrePolynomial (n - 1) := by
  cases n with
  | zero => simp [laguerrePolynomial_zero, laguerrePolynomial_one]
  | succ n =>
    have h := laguerrePolynomial_three_term n
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] at ⊢
    have hc₁ : C (2 * ((n : ℝ) + 1) + 1) = C (2 * (n : ℝ) + 3) := by
      congr 1
      ring
    have hc₂ : C ((n : ℝ) + 1 + 1) = C ((n : ℝ) + 2) := by
      congr 1
      ring
    rw [hc₁, hc₂]
    linear_combination h

/-- The Gram pairing, as an integral. -/
def laguerreInner (p q : ℝ[X]) : ℝ := laguerreMoment (p * q)

theorem laguerreInner_sub_left (p q r : ℝ[X]) :
    laguerreInner (p - q) r = laguerreInner p r - laguerreInner q r := by
  simp [laguerreInner, sub_mul]

theorem laguerreInner_sub_right (p q r : ℝ[X]) :
    laguerreInner p (q - r) = laguerreInner p q - laguerreInner p r := by
  simp [laguerreInner, mul_sub]

theorem laguerreInner_C_mul_left (c : ℝ) (p q : ℝ[X]) :
    laguerreInner (C c * p) q = c * laguerreInner p q := by
  simp only [laguerreInner, mul_assoc, laguerreMoment_C_mul]

theorem laguerreInner_C_mul_right (c : ℝ) (p q : ℝ[X]) :
    laguerreInner p (C c * q) = c * laguerreInner p q := by
  rw [laguerreInner, show p * (C c * q) = C c * (p * q) by ring,
    laguerreMoment_C_mul]
  rfl

theorem laguerreInner_orthogonal {m n : ℕ} (hmn : m ≠ n) :
    laguerreInner (laguerrePolynomial m) (laguerrePolynomial n) = 0 :=
  laguerrePolynomial_orthogonal hmn

theorem laguerrePolynomial_norm_succ (n : ℕ) :
    laguerreInner (laguerrePolynomial (n + 1)) (laguerrePolynomial (n + 1)) =
      laguerreInner (laguerrePolynomial n) (laguerrePolynomial n) := by
  have h : laguerreInner (X * laguerrePolynomial n) (laguerrePolynomial (n + 1)) =
      laguerreInner (laguerrePolynomial n) (X * laguerrePolynomial (n + 1)) := by
    unfold laguerreInner
    congr 1
    ring
  rw [laguerrePolynomial_X_mul n, laguerrePolynomial_X_mul (n + 1)] at h
  simp only [laguerreInner_sub_left, laguerreInner_sub_right,
    laguerreInner_C_mul_left, laguerreInner_C_mul_right] at h
  rw [laguerreInner_orthogonal (by omega : n ≠ n + 1),
    laguerreInner_orthogonal (by omega : n - 1 ≠ n + 1),
    laguerreInner_orthogonal (by omega : n ≠ n + 1 + 1)] at h
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, mul_zero,
    zero_sub, sub_zero] at h
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  nlinarith

/-- Unit squared norm of each concrete Laguerre polynomial. -/
theorem laguerrePolynomial_norm (n : ℕ) :
    laguerreInner (laguerrePolynomial n) (laguerrePolynomial n) = 1 := by
  induction n with
  | zero =>
    rw [laguerreInner, laguerrePolynomial_zero, mul_one]
    simpa only [map_one] using laguerreMoment_C 1
  | succ n ih => rw [laguerrePolynomial_norm_succ, ih]

/-- Full orthonormality, proved for the polynomial coefficients and the
Lebesgue integral used in the paper. -/
theorem laguerrePolynomial_orthonormal (m n : ℕ) :
    (∫ x : ℝ in Ioi 0,
      (laguerrePolynomial m).eval x * (laguerrePolynomial n).eval x *
        Real.exp (-x)) = if m = n then 1 else 0 := by
  have hi : (∫ x : ℝ in Ioi 0,
      (laguerrePolynomial m).eval x * (laguerrePolynomial n).eval x *
        Real.exp (-x)) =
      laguerreInner (laguerrePolynomial m) (laguerrePolynomial n) := by
    simp only [laguerreInner, laguerreMoment_apply, eval_mul]
  rw [hi]
  split_ifs with h
  · subst n
    exact laguerrePolynomial_norm m
  · exact laguerreInner_orthogonal h

theorem laguerreInner_orthonormal (m n : ℕ) :
    laguerreInner (laguerrePolynomial m) (laguerrePolynomial n) =
      if m = n then 1 else 0 := by
  by_cases h : m = n
  · subst n
    simp [laguerrePolynomial_norm]
  · simp [h, laguerreInner_orthogonal h]

theorem laguerreInner_sum_left {ι : Type*} (s : Finset ι)
    (p : ι → ℝ[X]) (q : ℝ[X]) :
    laguerreInner (∑ i ∈ s, p i) q = ∑ i ∈ s, laguerreInner (p i) q := by
  simp only [laguerreInner, Finset.sum_mul, map_sum]

theorem laguerreInner_sum_right {ι : Type*} (s : Finset ι)
    (p : ℝ[X]) (q : ι → ℝ[X]) :
    laguerreInner p (∑ i ∈ s, q i) = ∑ i ∈ s, laguerreInner p (q i) := by
  simp only [laguerreInner, Finset.mul_sum, map_sum]

def laguerreExpansion (m : ℕ) (b : ℕ → ℝ) : ℝ[X] :=
  ∑ j ∈ Finset.range (m + 1), C (b j) * laguerrePolynomial j

theorem laguerreInner_expansion_right (m n : ℕ) (b : ℕ → ℝ) :
    laguerreInner (laguerrePolynomial n) (laguerreExpansion m b) =
      if n ≤ m then b n else 0 := by
  simp only [laguerreExpansion, laguerreInner_sum_right,
    laguerreInner_C_mul_right, laguerreInner_orthonormal]
  simp [Finset.mem_range, Nat.lt_succ_iff, eq_comm]

/-- Parseval's identity for each finite Laguerre expansion. -/
theorem laguerreExpansion_norm (m : ℕ) (b : ℕ → ℝ) :
    laguerreInner (laguerreExpansion m b) (laguerreExpansion m b) =
      ∑ j ∈ Finset.range (m + 1), (b j) ^ 2 := by
  conv_lhs => lhs; rw [laguerreExpansion]
  rw [laguerreInner_sum_left]
  apply Finset.sum_congr rfl
  intro j hj
  rw [laguerreInner_C_mul_left, laguerreInner_expansion_right,
    if_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  ring

/-- The multiplication operator has its exact tridiagonal matrix in this
concrete orthonormal family. -/
theorem laguerrePolynomial_X_inner (m n : ℕ) :
    laguerreInner (X * laguerrePolynomial m) (laguerrePolynomial n) =
      (2 * (m : ℝ) + 1) * (if m = n then 1 else 0) -
        ((m : ℝ) + 1) * (if m + 1 = n then 1 else 0) -
          (m : ℝ) * (if m - 1 = n then 1 else 0) := by
  rw [laguerrePolynomial_X_mul]
  simp only [laguerreInner_sub_left, laguerreInner_C_mul_left,
    laguerreInner_orthonormal]

theorem laguerreExpansion_X_moment (m : ℕ) (b : ℕ → ℝ) :
    laguerreInner (X * laguerreExpansion m b) (laguerreExpansion m b) =
      ∑ j ∈ Finset.range (m + 1), b j *
        ((2 * (j : ℝ) + 1) * b j -
          ((j : ℝ) + 1) * (if j + 1 ≤ m then b (j + 1) else 0) -
            (j : ℝ) * b (j - 1)) := by
  conv_lhs => lhs; rhs; rw [laguerreExpansion]
  rw [Finset.mul_sum, laguerreInner_sum_left]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [show X * (C (b j) * laguerrePolynomial j) =
      C (b j) * (X * laguerrePolynomial j) by ring,
    laguerreInner_C_mul_left, laguerrePolynomial_X_mul]
  simp only [laguerreInner_sub_left, laguerreInner_C_mul_left,
    laguerreInner_expansion_right, if_pos hjm, if_pos (by omega : j - 1 ≤ m)]

theorem laguerreExpansion_X_moment_edges (m : ℕ) (b : ℕ → ℝ) :
    laguerreInner (X * laguerreExpansion m b) (laguerreExpansion m b) =
      (∑ j ∈ Finset.range (m + 1), (2 * (j : ℝ) + 1) * (b j) ^ 2) -
        2 * ∑ j ∈ Finset.range m, ((j : ℝ) + 1) * b j * b (j + 1) := by
  have hlo : ∀ k : ℕ,
      (∑ j ∈ Finset.range (k + 1), b j * (j : ℝ) * b (j - 1)) =
        ∑ j ∈ Finset.range k, ((j : ℝ) + 1) * b j * b (j + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      ring
  have hhi :
      (∑ j ∈ Finset.range (m + 1), b j * ((j : ℝ) + 1) *
        (if j + 1 ≤ m then b (j + 1) else 0)) =
        ∑ j ∈ Finset.range m, ((j : ℝ) + 1) * b j * b (j + 1) := by
    rw [Finset.sum_range_succ]
    simp only [Nat.not_succ_le_self, if_false, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    rw [if_pos (by have := Finset.mem_range.mp hj; omega)]
    ring
  rw [laguerreExpansion_X_moment]
  simp_rw [mul_sub, ← mul_assoc]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hlo m, hhi]
  have hdiag : (∑ j ∈ Finset.range (m + 1), b j * (2 * (j : ℝ) + 1) * b j) =
      ∑ j ∈ Finset.range (m + 1), (2 * (j : ℝ) + 1) * (b j) ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hdiag]
  ring

/-- A coefficient-uniform first-moment estimate for the finite real
Laguerre expansion. -/
theorem laguerreExpansion_first_moment_le (m : ℕ) (b : ℕ → ℝ) :
    laguerreInner (X * laguerreExpansion m b) (laguerreExpansion m b) ≤
      (4 * (m : ℝ) + 2) *
        laguerreInner (laguerreExpansion m b) (laguerreExpansion m b) := by
  rw [laguerreExpansion_norm, laguerreExpansion_X_moment_edges]
  let E : ℝ := ∑ j ∈ Finset.range (m + 1), (b j) ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hd : (∑ j ∈ Finset.range (m + 1), (2 * (j : ℝ) + 1) * (b j) ^ 2) ≤
      (2 * (m : ℝ) + 1) * E := by
    dsimp only [E]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hjm : (j : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    linarith
  have hleft : (∑ j ∈ Finset.range m, (b j) ^ 2) ≤ E := by
    dsimp [E]
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hright : (∑ j ∈ Finset.range m, (b (j + 1)) ^ 2) ≤ E := by
    dsimp [E]
    rw [Finset.sum_range_succ']
    exact le_add_of_nonneg_right (sq_nonneg _)
  have he : -(2 * ∑ j ∈ Finset.range m, ((j : ℝ) + 1) * b j * b (j + 1)) ≤
      (m : ℝ) * ((∑ j ∈ Finset.range m, (b j) ^ 2) +
        ∑ j ∈ Finset.range m, (b (j + 1)) ^ 2) := by
    rw [mul_add]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro j hj
    have hjm : (j : ℝ) + 1 ≤ (m : ℝ) := by
      exact_mod_cast (show j + 1 ≤ m by have := Finset.mem_range.mp hj; omega)
    have hj0 : 0 ≤ (j : ℝ) + 1 := by positivity
    have hs := mul_nonneg hj0 (sq_nonneg (b j + b (j + 1)))
    have ht := mul_nonneg (sub_nonneg.mpr hjm)
      (add_nonneg (sq_nonneg (b j)) (sq_nonneg (b (j + 1))))
    nlinarith
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have he' : -(2 * ∑ j ∈ Finset.range m, ((j : ℝ) + 1) * b j * b (j + 1)) ≤
      2 * (m : ℝ) * E := by
    calc
      _ ≤ (m : ℝ) * ((∑ j ∈ Finset.range m, (b j) ^ 2) +
          ∑ j ∈ Finset.range m, (b (j + 1)) ^ 2) := he
      _ ≤ (m : ℝ) * (E + E) := mul_le_mul_of_nonneg_left
        (add_le_add hleft hright) hm
      _ = 2 * (m : ℝ) * E := by ring
  dsimp only [E] at hd he' hE
  nlinarith

theorem laguerrePolynomial_ne_zero (n : ℕ) : laguerrePolynomial n ≠ 0 := by
  intro h
  have hc := laguerrePolynomial_coeff n 0
  rw [h] at hc
  simpa using hc

/-- The concrete Laguerre polynomials form a polynomial sequence of exact
degrees, so the finite expansions exhaust the required degree space. -/
def laguerreSequence : Polynomial.Sequence ℝ where
  elems' := laguerrePolynomial
  degree_eq' n := by
    rw [degree_eq_natDegree (laguerrePolynomial_ne_zero n),
      laguerrePolynomial_natDegree]

theorem exists_laguerreExpansion (m : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ m) :
    ∃ b : ℕ → ℝ, laguerreExpansion m b = p := by
  have hs := laguerreSequence.span_degreeLE (m := m)
    (fun i hi => isUnit_iff_ne_zero.mpr
      (leadingCoeff_ne_zero.mpr (laguerrePolynomial_ne_zero i)))
  have hset : (laguerreSequence : ℕ → ℝ[X]) '' Iic m =
      laguerrePolynomial '' (↑(Finset.range (m + 1)) : Set ℕ) := by
    congr 1
    ext n
    simp only [mem_Iic, Finset.mem_coe, Finset.mem_range]
    omega
  rw [hset] at hs
  have hp' : p ∈ Submodule.span ℝ
      (laguerrePolynomial '' (↑(Finset.range (m + 1)) : Set ℕ)) := by
    rw [hs, mem_degreeLE]
    exact degree_le_of_natDegree_le hp
  obtain ⟨b, hb⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' ℝ).mp hp'
  refine ⟨b, ?_⟩
  simpa only [laguerreExpansion, smul_eq_C_mul] using hb

/-- The first-moment estimate holds for every real polynomial of the given
degree. -/
theorem polynomial_exp_first_moment_le (m : ℕ) (p : ℝ[X])
    (hp : p.natDegree ≤ m) :
    (∫ x : ℝ in Ioi 0, x * (p.eval x) ^ 2 * Real.exp (-x)) ≤
      (4 * (m : ℝ) + 2) *
        (∫ x : ℝ in Ioi 0, (p.eval x) ^ 2 * Real.exp (-x)) := by
  obtain ⟨b, rfl⟩ := exists_laguerreExpansion m p hp
  simpa only [laguerreInner, laguerreMoment_apply, eval_mul, eval_X,
    pow_two, mul_assoc] using laguerreExpansion_first_moment_le m b

def complexCoefficientPart (p : ℂ[X]) (f : ℂ → ℝ) : ℝ[X] :=
  ∑ j ∈ Finset.range (p.natDegree + 1), C (f (p.coeff j)) * X ^ j

theorem complexCoefficientPart_natDegree_le (p : ℂ[X]) (f : ℂ → ℝ) :
    (complexCoefficientPart p f).natDegree ≤ p.natDegree := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_C_mul_le _ _).trans
    (by simpa only [natDegree_X_pow] using Nat.le_of_lt_succ (Finset.mem_range.mp hj))

theorem complexCoefficientPart_re_eval (p : ℂ[X]) (x : ℝ) :
    (complexCoefficientPart p Complex.re).eval x = (p.eval (x : ℂ)).re := by
  conv_rhs => rw [eval_eq_sum_range]
  simp [complexCoefficientPart, eval_finsetSum, Complex.mul_re,
    ← Complex.ofReal_pow]

theorem complexCoefficientPart_im_eval (p : ℂ[X]) (x : ℝ) :
    (complexCoefficientPart p Complex.im).eval x = (p.eval (x : ℂ)).im := by
  conv_rhs => rw [eval_eq_sum_range]
  simp [complexCoefficientPart, eval_finsetSum, Complex.mul_im,
    ← Complex.ofReal_pow]

/-- A real polynomial representing the squared absolute value of a complex
polynomial along the real axis. -/
def complexNormSquarePolynomial (p : ℂ[X]) : ℝ[X] :=
  complexCoefficientPart p Complex.re ^ 2 + complexCoefficientPart p Complex.im ^ 2

theorem complexNormSquarePolynomial_eval (p : ℂ[X]) (x : ℝ) :
    (complexNormSquarePolynomial p).eval x = ‖p.eval (x : ℂ)‖ ^ 2 := by
  simp only [complexNormSquarePolynomial, Polynomial.eval_add, Polynomial.eval_pow,
    complexCoefficientPart_re_eval, complexCoefficientPart_im_eval,
    Complex.sq_norm, Complex.normSq_apply]
  ring

theorem complex_polynomial_exp_first_moment_le (m : ℕ) (p : ℂ[X])
    (hp : p.natDegree ≤ m) :
    (∫ x : ℝ in Ioi 0, x * ‖p.eval (x : ℂ)‖ ^ 2 * Real.exp (-x)) ≤
      (4 * (m : ℝ) + 2) *
        (∫ x : ℝ in Ioi 0, ‖p.eval (x : ℂ)‖ ^ 2 * Real.exp (-x)) := by
  let R := complexCoefficientPart p Complex.re
  let S := complexCoefficientPart p Complex.im
  have hR := polynomial_exp_first_moment_le m R
    ((complexCoefficientPart_natDegree_le p Complex.re).trans hp)
  have hS := polynomial_exp_first_moment_le m S
    ((complexCoefficientPart_natDegree_le p Complex.im).trans hp)
  have hnorm (x : ℝ) : ‖p.eval (x : ℂ)‖ ^ 2 = (R.eval x) ^ 2 + (S.eval x) ^ 2 := by
    simpa only [complexNormSquarePolynomial, Polynomial.eval_add, Polynomial.eval_pow, R, S] using
      (complexNormSquarePolynomial_eval p x).symm
  have hR₀ : IntegrableOn (fun x : ℝ => (R.eval x) ^ 2 * Real.exp (-x)) (Ioi 0) := by
    have he : (fun x : ℝ => (R.eval x) ^ 2 * Real.exp (-x)) =
        (fun x : ℝ => (R ^ 2).eval x * Real.exp (-x)) := by
      funext x
      rw [Polynomial.eval_pow]
    rw [he]
    exact polynomial_exp_integrable (R ^ 2)
  have hS₀ : IntegrableOn (fun x : ℝ => (S.eval x) ^ 2 * Real.exp (-x)) (Ioi 0) := by
    have he : (fun x : ℝ => (S.eval x) ^ 2 * Real.exp (-x)) =
        (fun x : ℝ => (S ^ 2).eval x * Real.exp (-x)) := by
      funext x
      rw [Polynomial.eval_pow]
    rw [he]
    exact polynomial_exp_integrable (S ^ 2)
  have hR₁ : IntegrableOn (fun x : ℝ => x * (R.eval x) ^ 2 * Real.exp (-x)) (Ioi 0) := by
    have he : (fun x : ℝ => x * (R.eval x) ^ 2 * Real.exp (-x)) =
        (fun x : ℝ => (X * R ^ 2).eval x * Real.exp (-x)) := by
      funext x
      rw [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_pow]
    rw [he]
    exact polynomial_exp_integrable (X * R ^ 2)
  have hS₁ : IntegrableOn (fun x : ℝ => x * (S.eval x) ^ 2 * Real.exp (-x)) (Ioi 0) := by
    have he : (fun x : ℝ => x * (S.eval x) ^ 2 * Real.exp (-x)) =
        (fun x : ℝ => (X * S ^ 2).eval x * Real.exp (-x)) := by
      funext x
      rw [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_pow]
    rw [he]
    exact polynomial_exp_integrable (X * S ^ 2)
  simp_rw [hnorm, mul_add, add_mul]
  rw [integral_add hR₁ hS₁, integral_add hR₀ hS₀]
  linarith

def polynomialWeightedMoment (p : ℝ[X]) (t : ℕ) (r : ℝ) : ℝ :=
  ∫ x : ℝ in Ioi 0, x ^ t * p.eval x * Real.exp (-(r * x))

theorem polynomial_weighted_exp_integrable (p : ℝ[X]) (t : ℕ)
    {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => x ^ t * p.eval x * Real.exp (-(r * x))) (Ioi 0) := by
  simp_rw [Polynomial.eval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
  apply integrable_finsetSum
  intro j hj
  have he : (fun x : ℝ => x ^ t * (p.coeff j * x ^ j) * Real.exp (-(r * x))) =
      (fun x : ℝ => p.coeff j * (x ^ (j + t) * Real.exp (-(r * x)))) := by
    funext x
    rw [pow_add]
    ring
  rw [he]
  exact (integrableOn_pow_exp_neg_mul (j + t) hr).const_mul (p.coeff j)

/-- A finite Gamma-moment formula, valid at every positive rate. -/
theorem polynomialWeightedMoment_eq_sum (p : ℝ[X]) (t : ℕ)
    {r : ℝ} (hr : 0 < r) :
    polynomialWeightedMoment p t r =
      ∑ j ∈ Finset.range (p.natDegree + 1),
        p.coeff j * (1 / r) ^ (j + t + 1) * ((j + t).factorial : ℝ) := by
  unfold polynomialWeightedMoment
  simp_rw [Polynomial.eval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
  have he (j : ℕ) :
      (fun x : ℝ => x ^ t * (p.coeff j * x ^ j) * Real.exp (-(r * x))) =
      (fun x : ℝ => p.coeff j * (x ^ (j + t) * Real.exp (-(r * x)))) := by
    funext x
    rw [pow_add]
    ring
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [he, integral_const_mul, integral_pow_exp_neg_mul _ hr]
    ring
  · intro j hj
    rw [he]
    exact (integrableOn_pow_exp_neg_mul (j + t) hr).const_mul (p.coeff j)

def complexPolynomialMoment (p : ℂ[X]) (t : ℕ) (r : ℝ) : ℝ :=
  ∫ x : ℝ in Ioi 0, x ^ t * ‖p.eval (x : ℂ)‖ ^ 2 * Real.exp (-(r * x))

theorem complexPolynomialMoment_eq_real (p : ℂ[X]) (t : ℕ) (r : ℝ) :
    complexPolynomialMoment p t r =
      polynomialWeightedMoment (complexNormSquarePolynomial p) t r := by
  simp only [complexPolynomialMoment, polynomialWeightedMoment,
    complexNormSquarePolynomial_eval]

theorem complex_polynomial_weighted_exp_integrable (p : ℂ[X]) (t : ℕ)
    {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => x ^ t * ‖p.eval (x : ℂ)‖ ^ 2 *
      Real.exp (-(r * x))) (Ioi 0) := by
  have h := polynomial_weighted_exp_integrable (complexNormSquarePolynomial p) t hr
  simpa only [complexNormSquarePolynomial_eval] using h

def complexScalePolynomial (p : ℂ[X]) (r : ℝ) : ℂ[X] :=
  p.comp (C ((r⁻¹ : ℝ) : ℂ) * X)

theorem complexScalePolynomial_eval (p : ℂ[X]) (r x : ℝ) :
    (complexScalePolynomial p r).eval (x : ℂ) = p.eval ((r⁻¹ * x : ℝ) : ℂ) := by
  simp only [complexScalePolynomial, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Complex.ofReal_mul]

theorem complexScalePolynomial_natDegree_le (p : ℂ[X]) (r : ℝ) :
    (complexScalePolynomial p r).natDegree ≤ p.natDegree := by
  apply natDegree_comp_le.trans
  simpa only [natDegree_X, mul_one] using
    Nat.mul_le_mul_left p.natDegree (natDegree_C_mul_le ((r⁻¹ : ℝ) : ℂ) (X : ℂ[X]))

/-- Change of scale for polynomial moments. -/
theorem complexPolynomialMoment_scale (p : ℂ[X]) (t : ℕ)
    {r : ℝ} (hr : 0 < r) :
    complexPolynomialMoment (complexScalePolynomial p r) t 1 =
      r ^ (t + 1) * complexPolynomialMoment p t r := by
  have h := integral_comp_mul_left_Ioi
    (fun x : ℝ => (r * x) ^ t * ‖p.eval (x : ℂ)‖ ^ 2 * Real.exp (-(r * x)))
    0 (inv_pos.mpr hr)
  have he₁ : (fun x : ℝ => (r * (r⁻¹ * x)) ^ t *
      ‖p.eval ((r⁻¹ * x : ℝ) : ℂ)‖ ^ 2 * Real.exp (-(r * (r⁻¹ * x)))) =
      (fun x : ℝ => x ^ t * ‖(complexScalePolynomial p r).eval (x : ℂ)‖ ^ 2 *
        Real.exp (-(1 * x))) := by
    funext x
    rw [complexScalePolynomial_eval, mul_inv_cancel_left₀ hr.ne', one_mul]
  rw [he₁] at h
  simp only [inv_inv, mul_zero, smul_eq_mul] at h
  have he₂ : (fun x : ℝ => (r * x) ^ t * ‖p.eval (x : ℂ)‖ ^ 2 *
      Real.exp (-(r * x))) =
      (fun x : ℝ => r ^ t * (x ^ t * ‖p.eval (x : ℂ)‖ ^ 2 *
        Real.exp (-(r * x)))) := by
    funext x
    rw [mul_pow]
    ring
  rw [he₂, integral_const_mul] at h
  change complexPolynomialMoment (complexScalePolynomial p r) t 1 =
    r * (r ^ t * complexPolynomialMoment p t r) at h
  rw [h]
  ring

theorem complexPolynomialMoment_first_le (m : ℕ) (p : ℂ[X])
    (hp : p.natDegree ≤ m) {r : ℝ} (hr : 0 < r) :
    r * complexPolynomialMoment p 1 r ≤
      (4 * (m : ℝ) + 2) * complexPolynomialMoment p 0 r := by
  have h : complexPolynomialMoment (complexScalePolynomial p r) 1 1 ≤
      (4 * (m : ℝ) + 2) * complexPolynomialMoment (complexScalePolynomial p r) 0 1 := by
    simpa only [complexPolynomialMoment, pow_one, pow_zero, one_mul] using
      complex_polynomial_exp_first_moment_le m (complexScalePolynomial p r)
        ((complexScalePolynomial_natDegree_le p r).trans hp)
  rw [complexPolynomialMoment_scale p 1 hr, complexPolynomialMoment_scale p 0 hr] at h
  norm_num only [zero_add, pow_one] at h
  have h' : r * (r * complexPolynomialMoment p 1 r) ≤
      r * ((4 * (m : ℝ) + 2) * complexPolynomialMoment p 0 r) := by
    nlinarith only [h]
  exact (mul_le_mul_iff_right₀ hr).mp h'

/-- Differentiation of the explicit Gamma moment is an elementary finite
calculation; no differentiation under an integral sign is used. -/
theorem hasDerivAt_gammaMoment (n : ℕ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => (1 / s) ^ (n + 1) * (n.factorial : ℝ))
      (-((1 / r) ^ (n + 2) * ((n + 1).factorial : ℝ))) r := by
  have h := (((hasDerivAt_id r).inv hr.ne').pow (n + 1)).mul_const (n.factorial : ℝ)
  convert! h using 1 <;> try rfl
  · funext s
    simp only [one_div, Pi.pow_apply, Pi.inv_apply, id_eq]
  · simp only [Pi.inv_apply, id_eq, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
      Nat.factorial_succ, Nat.cast_mul]
    rw [show n + 2 = n + 1 + 1 by omega, pow_succ, pow_succ]
    field_simp <;> ring

theorem polynomialWeightedMoment_hasDerivAt (p : ℝ[X]) (t : ℕ)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (polynomialWeightedMoment p t)
      (-polynomialWeightedMoment p (t + 1) r) r := by
  have hsum := HasDerivAt.sum (u := Finset.range (p.natDegree + 1))
    (fun j hj => (hasDerivAt_gammaMoment (j + t) hr).const_mul (p.coeff j))
  have hd : HasDerivAt
      (fun s : ℝ => ∑ j ∈ Finset.range (p.natDegree + 1),
        p.coeff j * ((1 / s) ^ (j + t + 1) * ((j + t).factorial : ℝ)))
      (-polynomialWeightedMoment p (t + 1) r) r := by
    convert! hsum using 1 <;> try rfl
    · funext s
      simp only [Finset.sum_apply]
    · rw [polynomialWeightedMoment_eq_sum p (t + 1) hr]
      simp_rw [mul_neg, Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Nat.add_assoc, mul_assoc]
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hr] with s hs
  rw [polynomialWeightedMoment_eq_sum p t hs]
  simp only [mul_assoc]

theorem complexPolynomialMoment_hasDerivAt (p : ℂ[X]) (t : ℕ)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (complexPolynomialMoment p t)
      (-complexPolynomialMoment p (t + 1) r) r := by
  have hf : complexPolynomialMoment p t =
      polynomialWeightedMoment (complexNormSquarePolynomial p) t := by
    funext s
    exact complexPolynomialMoment_eq_real p t s
  rw [hf, complexPolynomialMoment_eq_real]
  exact polynomialWeightedMoment_hasDerivAt (complexNormSquarePolynomial p) t hr

theorem complexPolynomialMoment_zero_nonneg (p : ℂ[X]) (r : ℝ) :
    0 ≤ complexPolynomialMoment p 0 r := by
  apply integral_nonneg
  intro x
  positivity

theorem complexPolynomialMoment_zero_pos {p : ℂ[X]} (hp : p ≠ 0)
    {r : ℝ} (hr : 0 < r) : 0 < complexPolynomialMoment p 0 r := by
  have hex : ∃ x : ℝ, 0 < x ∧ p.eval (x : ℂ) ≠ 0 := by
    by_contra h
    push Not at h
    apply hp
    apply p.eq_zero_of_infinite_isRoot
    apply ((Set.Ioi_infinite (0 : ℝ)).image Complex.ofReal_injective.injOn).mono
    rintro z ⟨x, hx, rfl⟩
    exact h x hx
  obtain ⟨x, hx, hpx⟩ := hex
  let f : ℝ → ℝ := fun y => y ^ (0 : ℕ) * ‖p.eval (y : ℂ)‖ ^ 2 *
    Real.exp (-(r * y))
  have hf : Continuous f := by
    have hpoly : Continuous (fun y : ℝ => p.eval (y : ℂ)) :=
      p.continuous.comp Complex.continuous_ofReal
    unfold f
    fun_prop
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f :=
    Filter.Eventually.of_forall (fun y => by dsimp [f]; positivity)
  apply (setIntegral_pos_iff_support_of_nonneg_ae hnonneg
    (complex_polynomial_weighted_exp_integrable p 0 hr)).mpr
  apply IsOpen.measure_pos volume (hf.isOpen_support.inter isOpen_Ioi)
  refine ⟨x, ?_, hx⟩
  change x ^ (0 : ℕ) * ‖p.eval (x : ℂ)‖ ^ 2 * Real.exp (-(r * x)) ≠ 0
  exact mul_ne_zero (mul_ne_zero (by simp) (pow_ne_zero _ (norm_ne_zero_iff.mpr hpx)))
    (Real.exp_ne_zero _)

theorem complexPolynomialMoment_power_hasDerivAt (m : ℕ) (p : ℂ[X])
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => s ^ (4 * m + 6) * complexPolynomialMoment p 0 s)
      (r ^ (4 * m + 5) *
        ((4 * (m : ℝ) + 6) * complexPolynomialMoment p 0 r -
          r * complexPolynomialMoment p 1 r)) r := by
  have h := ((hasDerivAt_id r).pow (4 * m + 6)).mul
    (complexPolynomialMoment_hasDerivAt p 0 hr)
  convert! h using 1 <;> try rfl
  simp only [Pi.pow_apply, Pi.mul_apply, id_eq, zero_add,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, mul_one]
  rw [show 4 * m + 6 - 1 = 4 * m + 5 by omega,
    show 4 * m + 6 = 4 * m + 5 + 1 by omega, pow_succ]
  ring

theorem complexPolynomialMoment_power_monotone (m : ℕ) (p : ℂ[X])
    (hp : p.natDegree ≤ m) :
    MonotoneOn (fun r => r ^ (4 * m + 6) * complexPolynomialMoment p 0 r) (Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi (0 : ℝ))
  · intro r hr
    exact (complexPolynomialMoment_power_hasDerivAt m p hr).continuousAt.continuousWithinAt
  · intro r hr
    exact (complexPolynomialMoment_power_hasDerivAt m p
      (interior_subset hr)).differentiableAt.differentiableWithinAt
  · intro r hr
    have hr' : 0 < r := interior_subset hr
    rw [(complexPolynomialMoment_power_hasDerivAt m p hr').deriv]
    apply mul_nonneg (pow_nonneg hr'.le _)
    have h := complexPolynomialMoment_first_le m p hp hr'
    have h₀ := complexPolynomialMoment_zero_nonneg p r
    linarith

/-- The coefficient-uniform moment-ratio estimate from Lemma deriv:laguerre-moment
of the paper, for the complex polynomial and the integrals. -/
theorem complexPolynomialMoment_ratio_le (m : ℕ) (p : ℂ[X])
    (hp : p ≠ 0) (hm : p.natDegree ≤ m) {k₁ k₂ : ℝ}
    (hk₁ : 0 < k₁) (hk : k₁ ≤ k₂) :
    complexPolynomialMoment p 0 k₁ / complexPolynomialMoment p 0 k₂ ≤
      (k₂ / k₁) ^ (4 * m + 6) := by
  have hk₂ : 0 < k₂ := lt_of_lt_of_le hk₁ hk
  have h := complexPolynomialMoment_power_monotone m p hm hk₁ hk₂ hk
  apply (div_le_iff₀ (complexPolynomialMoment_zero_pos hp hk₂)).mpr
  rw [div_pow, div_mul_eq_mul_div]
  apply (le_div_iff₀ (pow_pos hk₁ (4 * m + 6))).mpr
  nlinarith only [h]

/-- Integral form of the paper's coefficient-uniform Laguerre lemma. -/
theorem thetaDeriv_laguerre_moment_ratio (m : ℕ) (p : ℂ[X])
    (hp : p ≠ 0) (hm : p.natDegree ≤ m) {k₁ k₂ : ℝ}
    (hk₁ : 0 < k₁) (hk : k₁ ≤ k₂) :
    (∫ x : ℝ in Ioi 0, ‖p.eval (x : ℂ)‖ ^ 2 * Real.exp (-(k₁ * x))) /
      (∫ x : ℝ in Ioi 0, ‖p.eval (x : ℂ)‖ ^ 2 * Real.exp (-(k₂ * x))) ≤
        (k₂ / k₁) ^ (4 * m + 6) := by
  simpa only [complexPolynomialMoment, pow_zero, one_mul] using
    complexPolynomialMoment_ratio_le m p hp hm hk₁ hk

end ThetaTrial.Paper
