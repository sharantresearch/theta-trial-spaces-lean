import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import ThetaTrial.Paper.Laguerre
import Mathlib.Tactic

/-!
Coefficient estimates used in the polynomial trial spaces. The degree dependence
is explicit; finite-dimensional norm equivalence alone would not suffice here.
We use Chebyshev polynomials of the second kind, whose weight is bounded by one.
-/

noncomputable section
open Polynomial Polynomial.Chebyshev MeasureTheory Real Set
open scoped BigOperators

namespace ThetaTrial.Paper.CoefficientBounds

def U (n : ℕ) : ℝ[X] := Polynomial.Chebyshev.U ℝ n

def chebyshevUSequence : Polynomial.Sequence ℝ where
  elems' := U
  degree_eq' n := by simpa [U] using degree_U_natCast ℝ n

theorem U_degree (n : ℕ) : (U n).natDegree = n :=
  natDegree_U_natCast ℝ n

def weightedInner (p q : ℝ[X]) : ℝ :=
  ∫ x, (1 - x ^ 2) * p.eval x * q.eval x ∂measureT

theorem weighted_integrable (p q : ℝ[X]) :
    Integrable (fun x : ℝ => (1 - x ^ 2) * p.eval x * q.eval x) measureT :=
  integrable_measureT (by fun_prop)

theorem weightedInner_U (n m : ℕ) :
    weightedInner (U n) (U m) = if n = m then π / 2 else 0 := by
  unfold weightedInner
  rw [integral_measureT_eq_integral_cos]
  have he (θ : ℝ) :
      (1 - cos θ ^ 2) * (U n).eval (cos θ) * (U m).eval (cos θ) =
        (cos (((n : ℤ) - (m : ℤ) : ℤ) * θ) -
          cos (((n : ℤ) + (m : ℤ) + 2 : ℤ) * θ)) / 2 := by
    have hn := U_real_cos θ (n : ℤ)
    have hm := U_real_cos θ (m : ℤ)
    have hs := sin_sq_add_cos_sq θ
    have hp := two_mul_sin_mul_sin ((n + 1 : ℤ) * θ) ((m + 1 : ℤ) * θ)
    have hsq : 1 - cos θ ^ 2 = sin θ ^ 2 := by linarith
    rw [hsq]
    calc
      sin θ ^ 2 * (U n).eval (cos θ) * (U m).eval (cos θ) =
          ((U n).eval (cos θ) * sin θ) * ((U m).eval (cos θ) * sin θ) := by ring
      _ = sin (((n : ℤ) + 1) * θ) * sin (((m : ℤ) + 1) * θ) := by
        rw [show (U n).eval (cos θ) * sin θ = _ from hn,
          show (U m).eval (cos θ) * sin θ = _ from hm]
      _ = _ := by
        rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
        convert hp using 1 <;> push_cast <;> ring_nf
  simp_rw [he]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    ((by fun_prop : Continuous (fun θ : ℝ => cos (((n : ℤ) - (m : ℤ) : ℤ) * θ))).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun θ : ℝ => cos (((n : ℤ) + (m : ℤ) + 2 : ℤ) * θ))).intervalIntegrable _ _)]
  have hcos (j : ℤ) :
      (∫ θ in (0 : ℝ)..π, cos ((j : ℝ) * θ)) =
        ∫ x, (T ℝ j).eval x ∂measureT := by
    rw [integral_measureT_eq_integral_cos]
    simp
  rw [hcos, hcos,
    integral_eval_T_real_measureT_of_ne_zero (n := (n : ℤ) + (m : ℤ) + 2) (by omega)]
  by_cases h : n = m
  · subst m
    rw [sub_self, integral_eval_T_real_measureT_zero]
    simp
  · rw [integral_eval_T_real_measureT_of_ne_zero (by omega)]
    simp [h]

theorem exists_U_expansion (k : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ k) :
    ∃ b : Fin (k + 1) → ℝ, p = ∑ i : Fin (k + 1), b i • U i := by
  have hmem : p ∈ Submodule.span ℝ (chebyshevUSequence '' Iic k) := by
    rw [chebyshevUSequence.span_degreeLE (fun i hi =>
      isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr
        (chebyshevUSequence.ne_zero i)))]
    exact (Polynomial.mem_degreeLE).2 (Polynomial.degree_le_of_natDegree_le hp)
  have hrange : chebyshevUSequence '' Iic k = range (fun i : Fin (k + 1) => U i) := by
    ext p
    simp only [mem_image, mem_Iic, mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, by omega⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, by omega, rfl⟩
  rw [hrange, Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨b, hb⟩ := hmem
  exact ⟨b, hb.symm⟩

theorem weightedInner_sum_left {ι : Type*} (s : Finset ι)
    (p : ι → ℝ[X]) (q : ℝ[X]) :
    weightedInner (∑ i ∈ s, p i) q = ∑ i ∈ s, weightedInner (p i) q := by
  simp only [weightedInner, eval_finsetSum, Finset.mul_sum, Finset.sum_mul]
  exact integral_finsetSum s (fun i hi => weighted_integrable (p i) q)

theorem weightedInner_sum_right {ι : Type*} (s : Finset ι)
    (p : ℝ[X]) (q : ι → ℝ[X]) :
    weightedInner p (∑ i ∈ s, q i) = ∑ i ∈ s, weightedInner p (q i) := by
  simp only [weightedInner, eval_finsetSum, Finset.mul_sum]
  exact integral_finsetSum s (fun i hi => weighted_integrable p (q i))

theorem weightedInner_smul_left (b : ℝ) (p q : ℝ[X]) :
    weightedInner (b • p) q = b * weightedInner p q := by
  simp only [weightedInner, eval_smul, smul_eq_mul]
  simp_rw [show ∀ x : ℝ, (1-x^2) * (b * p.eval x) * q.eval x =
    b * ((1-x^2) * p.eval x * q.eval x) by intro x; ring]
  exact integral_const_mul _ _

theorem weightedInner_smul_right (b : ℝ) (p q : ℝ[X]) :
    weightedInner p (b • q) = b * weightedInner p q := by
  simp only [weightedInner, eval_smul, smul_eq_mul]
  simp_rw [show ∀ x : ℝ, (1-x^2) * p.eval x * (b * q.eval x) =
    b * ((1-x^2) * p.eval x * q.eval x) by intro x; ring]
  exact integral_const_mul _ _

theorem weightedInner_expansion (k : ℕ) (b : Fin (k+1) → ℝ) :
    weightedInner (∑ i, b i • U i) (∑ i, b i • U i) =
      π / 2 * ∑ i, b i ^ 2 := by
  rw [weightedInner_sum_left]
  simp_rw [weightedInner_smul_left, weightedInner_sum_right,
    weightedInner_smul_right, weightedInner_U]
  simp only [Fin.val_inj, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem weightedInner_eq_interval (p : ℝ[X]) :
    weightedInner p p =
      ∫ x in (-1 : ℝ)..1, sqrt (1-x^2) * (p.eval x)^2 := by
  rw [weightedInner, integral_measureT]
  simp only [sqrt_inv]
  apply intervalIntegral.integral_congr
  intro x hx
  change (1-x^2) * p.eval x * p.eval x * (sqrt (1-x^2))⁻¹ =
    sqrt (1-x^2) * (p.eval x)^2
  have hx' : x ∈ Icc (-1 : ℝ) 1 := by simpa using hx
  have hpos : 0 ≤ 1-x^2 := by nlinarith [hx'.1, hx'.2]
  have hs : sqrt (1-x^2) ^ 2 = 1-x^2 := sq_sqrt hpos
  by_cases hz : sqrt (1-x^2) = 0
  · have hzero : 1-x^2 = 0 := by nlinarith
    simp [hz, hzero]
  · nth_rw 1 [← hs]
    field_simp

theorem weightedInner_le_interval_sq (p : ℝ[X]) :
    weightedInner p p ≤ ∫ x in (-1 : ℝ)..1, (p.eval x)^2 := by
  rw [weightedInner_eq_interval]
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((by fun_prop : Continuous (fun x : ℝ => sqrt (1-x^2) * (p.eval x)^2)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun x : ℝ => (p.eval x)^2)).intervalIntegrable _ _)
  intro x hx
  apply mul_le_of_le_one_left (sq_nonneg _)
  exact (sqrt_le_one).2 (by nlinarith [sq_nonneg x])

theorem U_coeff_abs_le (n j : ℕ) : |(U n).coeff j| ≤ 3 ^ n := by
  induction n using Nat.twoStepInduction generalizing j with
  | zero =>
    simp only [U, Nat.cast_zero, U_zero, coeff_one, pow_zero]
    split_ifs <;> norm_num
  | one =>
    simp only [U, Nat.cast_one, U_one]
    rw [show (2 : ℝ[X]) = Polynomial.C 2 from (Polynomial.C_ofNat 2).symm]
    simp only [coeff_C_mul, coeff_X]
    split_ifs <;> norm_num
  | more n ih₀ ih₁ =>
    have hr : U (n+2) = Polynomial.C 2 * X * U (n+1) - U n := by
      simpa only [U, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
        ← Polynomial.C_ofNat] using U_add_two ℝ (n : ℤ)
    rw [hr, coeff_sub]
    calc
      |(Polynomial.C 2 * X * U (n+1)).coeff j - (U n).coeff j| ≤
          |(Polynomial.C 2 * X * U (n+1)).coeff j| + |(U n).coeff j| := abs_sub _ _
      _ ≤ 2 * 3^(n+1) + 3^n := by
        apply add_le_add _ (ih₀ j)
        cases j with
        | zero => simp [mul_assoc, coeff_X_mul]
        | succ j =>
          simp only [mul_assoc, coeff_C_mul, coeff_X_mul, abs_mul]
          norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          exact mul_le_mul_of_nonneg_left (ih₁ j) (by norm_num)
      _ ≤ 3^(n+2) := by
        simp only [show n+2 = (n+1)+1 by omega, pow_succ]
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) n]

def intervalSq (p : ℝ[X]) : ℝ := ∫ x in (-1 : ℝ)..1, (p.eval x)^2

theorem intervalSq_nonneg (p : ℝ[X]) : 0 ≤ intervalSq p :=
  intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun x => sq_nonneg _)

theorem expansion_coefficient_abs_le (k : ℕ) (b : Fin (k+1) → ℝ)
    (p : ℝ[X]) (hp : p = ∑ i, b i • U i) (i : Fin (k+1)) :
    |b i| ≤ sqrt (intervalSq p) := by
  have hsum : b i ^ 2 ≤ ∑ j, b j ^ 2 :=
    Finset.single_le_sum (fun j hj => sq_nonneg (b j)) (Finset.mem_univ i)
  have htotal := weightedInner_le_interval_sq p
  have hnorm : weightedInner p p = π / 2 * ∑ j, b j ^ 2 := by
    rw [hp, weightedInner_expansion]
  rw [hnorm] at htotal
  have hsn : 0 ≤ ∑ j, b j ^ 2 := Finset.sum_nonneg (fun j hj => sq_nonneg _)
  have hπ : 1 ≤ π / 2 := by linarith [pi_gt_three]
  have hsq : b i ^ 2 ≤ intervalSq p := by
    exact hsum.trans ((le_mul_of_one_le_left hsn hπ).trans htotal)
  have hr := sq_sqrt (intervalSq_nonneg p)
  nlinarith [abs_nonneg (b i), sqrt_nonneg (intervalSq p), sq_abs (b i)]

theorem real_coeff_abs_le (k : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ k) (j : ℕ) :
    |p.coeff j| ≤ (k+1 : ℝ) * 3^k * sqrt (intervalSq p) := by
  obtain ⟨b, hb⟩ := exists_U_expansion k p hp
  have hcoeff : p.coeff j = ∑ i, b i * (U i).coeff j := by
    rw [hb]
    simp
  rw [hcoeff]
  calc
    |∑ i, b i * (U i).coeff j| ≤ ∑ i, |b i * (U i).coeff j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (k+1), sqrt (intervalSq p) * 3^k := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      apply mul_le_mul (expansion_coefficient_abs_le k b p hb i)
        ((U_coeff_abs_le i j).trans (pow_le_pow_right₀ (by norm_num) (by omega)))
        (abs_nonneg _) (sqrt_nonneg _)
    _ = _ := by simp; ring

theorem real_sum_abs_coeff_le (k : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ k) :
    (∑ j ∈ Finset.range (k+1), |p.coeff j|) ≤
      ((k+1 : ℝ)^2 * 3^k) * sqrt (intervalSq p) := by
  calc
    _ ≤ ∑ j ∈ Finset.range (k+1), (k+1 : ℝ) * 3^k * sqrt (intervalSq p) :=
      Finset.sum_le_sum (fun j hj => real_coeff_abs_le k p hp j)
    _ = _ := by simp; ring

theorem dimension_factor_le (k : ℕ) : (k+1 : ℝ)^2 * 3^k ≤ 12^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hquad : (k+2 : ℝ)^2 ≤ 4*(k+1 : ℝ)^2 := by nlinarith
    simp only [Nat.cast_succ]
    rw [pow_succ (3 : ℝ) k, pow_succ (12 : ℝ) k]
    calc
      (k + 1 + 1 : ℝ)^2 * (3^k*3) ≤ (4*(k+1 : ℝ)^2) * (3^k*3) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [hquad]
      _ = 12 * ((k+1 : ℝ)^2 * 3^k) := by ring
      _ ≤ 12 * 12^k := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by ring

theorem real_sum_abs_coeff_le_exponential (k : ℕ) (p : ℝ[X])
    (hp : p.natDegree ≤ k) :
    (∑ j ∈ Finset.range (k+1), |p.coeff j|) ≤ 12^k * sqrt (intervalSq p) :=
  (real_sum_abs_coeff_le k p hp).trans
    (mul_le_mul_of_nonneg_right (dimension_factor_le k) (sqrt_nonneg _))

def complexIntervalSq (p : ℂ[X]) : ℝ :=
  ∫ x in (-1 : ℝ)..1, ‖p.eval (x : ℂ)‖^2

theorem complexIntervalSq_nonneg (p : ℂ[X]) : 0 ≤ complexIntervalSq p :=
  intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun x => sq_nonneg _)

theorem complexCoefficientPart_coeff (p : ℂ[X]) (f : ℂ → ℝ) (hf : f 0 = 0)
    (j : ℕ) : (complexCoefficientPart p f).coeff j = f (p.coeff j) := by
  simp only [complexCoefficientPart, finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases hj : j < p.natDegree + 1
  · simp [hj]
  · have hz := Polynomial.coeff_eq_zero_of_natDegree_lt (show p.natDegree < j by omega)
    simp [hj, hz, hf]

theorem part_intervalSq_le (p : ℂ[X]) :
    intervalSq (complexCoefficientPart p Complex.re) ≤ complexIntervalSq p ∧
    intervalSq (complexCoefficientPart p Complex.im) ≤ complexIntervalSq p := by
  constructor
  all_goals
    unfold intervalSq complexIntervalSq
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((by fun_prop : Continuous _).intervalIntegrable _ _)
      ((by fun_prop : Continuous _).intervalIntegrable _ _)
    intro x hx
  · rw [complexCoefficientPart_re_eval, Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg (p.eval (x : ℂ)).im]
  · rw [complexCoefficientPart_im_eval, Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg (p.eval (x : ℂ)).re]

/-- Uniform complex coefficient estimate on a fixed real interval. -/
theorem complex_sum_norm_coeff_le (k : ℕ) (p : ℂ[X]) (hp : p.natDegree ≤ k) :
    (∑ j ∈ Finset.range (k+1), ‖p.coeff j‖) ≤
      2 * 12^k * sqrt (complexIntervalSq p) := by
  have hR := real_sum_abs_coeff_le_exponential k
    (complexCoefficientPart p Complex.re)
    ((complexCoefficientPart_natDegree_le _ _).trans hp)
  have hI := real_sum_abs_coeff_le_exponential k
    (complexCoefficientPart p Complex.im)
    ((complexCoefficientPart_natDegree_le _ _).trans hp)
  simp_rw [complexCoefficientPart_coeff p Complex.re rfl] at hR
  simp_rw [complexCoefficientPart_coeff p Complex.im rfl] at hI
  have hsmall := part_intervalSq_le p
  calc
    _ ≤ ∑ j ∈ Finset.range (k+1), (|(p.coeff j).re| + |(p.coeff j).im|) :=
      Finset.sum_le_sum (fun j hj => Complex.norm_le_abs_re_add_abs_im _)
    _ = _ := Finset.sum_add_distrib
    _ ≤ 12^k * sqrt (intervalSq (complexCoefficientPart p Complex.re)) +
        12^k * sqrt (intervalSq (complexCoefficientPart p Complex.im)) := add_le_add hR hI
    _ ≤ 12^k * sqrt (complexIntervalSq p) + 12^k * sqrt (complexIntervalSq p) :=
      add_le_add (mul_le_mul_of_nonneg_left (sqrt_le_sqrt hsmall.1) (by positivity))
        (mul_le_mul_of_nonneg_left (sqrt_le_sqrt hsmall.2) (by positivity))
    _ = _ := by ring

def complexIntervalSqAt (d : ℝ) (p : ℂ[X]) : ℝ :=
  ∫ x in -d..d, ‖p.eval (x : ℂ)‖^2

theorem complexIntervalSqAt_nonneg {d : ℝ} (hd : 0 ≤ d) (p : ℂ[X]) :
    0 ≤ complexIntervalSqAt d p :=
  intervalIntegral.integral_nonneg_of_forall (by linarith) (fun x => sq_nonneg _)

theorem complexIntervalSq_scale {d : ℝ} (hd : d ≠ 0) (p : ℂ[X]) :
    complexIntervalSq (p.comp (Polynomial.C (d : ℂ) * X)) =
      d⁻¹ * complexIntervalSqAt d p := by
  unfold complexIntervalSq complexIntervalSqAt
  simp only [eval_comp, eval_mul, eval_C, eval_X, ← Complex.ofReal_mul]
  simpa only [mul_neg, mul_one, smul_eq_mul] using
    (intervalIntegral.integral_comp_mul_left
      (fun x : ℝ => ‖p.eval (x : ℂ)‖^2) hd (a := -1) (b := 1))

theorem scaled_coeff_sum_le {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (k : ℕ) (p : ℂ[X]) (hp : p.natDegree ≤ k) :
    (∑ j ∈ Finset.range (k+1), ‖p.coeff j‖) ≤
      ((2 / sqrt d) * (12 / d)^k) * sqrt (complexIntervalSqAt d p) := by
  let q := p.comp (Polynomial.C (d : ℂ) * X)
  have hq : q.natDegree ≤ k := by
    have hc : (Polynomial.C (d : ℂ) * (X : ℂ[X])).natDegree ≤ 1 :=
      (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    exact (Polynomial.natDegree_comp_le).trans
      ((Nat.mul_le_mul_left p.natDegree hc).trans (by simpa using hp))
  have hnorm (j : ℕ) : ‖q.coeff j‖ = ‖p.coeff j‖ * d^j := by
    dsimp [q]
    rw [comp_C_mul_X_coeff, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hd]
  have hsmall : d^k * (∑ j ∈ Finset.range (k+1), ‖p.coeff j‖) ≤
      ∑ j ∈ Finset.range (k+1), ‖q.coeff j‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [hnorm, mul_comm (d^k)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hd.le hd1 hjk) (norm_nonneg _)
  have hbound := hsmall.trans (complex_sum_norm_coeff_le k q hq)
  have hs : complexIntervalSq q = d⁻¹ * complexIntervalSqAt d p :=
    complexIntervalSq_scale hd.ne' p
  rw [hs, sqrt_mul (inv_nonneg.mpr hd.le), sqrt_inv] at hbound
  apply (mul_le_mul_iff_right₀ (pow_pos hd k)).mp
  convert hbound using 1 <;> simp only [div_pow] <;> field_simp [hd.ne'] <;> ring

/-- One degree-independent base controls all complex polynomial coefficients
on any fixed symmetric interval inside `[-1,1]`. -/
theorem uniform_interval_coefficient_bound {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    ∃ A ≥ (1 : ℝ), ∀ k : ℕ, ∀ p : ℂ[X], p.natDegree ≤ k →
      (∑ j ∈ Finset.range (k+1), ‖p.coeff j‖) ≤
        A^(k+1) * sqrt (complexIntervalSqAt d p) := by
  refine ⟨24/d, ?_, ?_⟩
  · apply (le_div_iff₀ hd).mpr
    linarith
  intro k p hp
  apply (scaled_coeff_sum_le hd hd1 k p hp).trans
  apply mul_le_mul_of_nonneg_right _ (sqrt_nonneg _)
  have hs : d ≤ sqrt d := by
    nlinarith [sq_sqrt hd.le, sqrt_nonneg d]
  have hfac : 2 / sqrt d ≤ 24 / d := by
    apply (div_le_div_iff₀ (sqrt_pos.mpr hd) hd).mpr
    nlinarith
  have hbase : 12 / d ≤ 24 / d := div_le_div_of_nonneg_right (by norm_num) hd.le
  calc
    (2 / sqrt d) * (12/d)^k ≤ (24/d) * (24/d)^k :=
      mul_le_mul hfac (pow_le_pow_left₀ (by positivity) hbase k)
        (by positivity) (by positivity)
    _ = (24/d)^(k+1) := by rw [pow_succ]; ring

end ThetaTrial.Paper.CoefficientBounds
