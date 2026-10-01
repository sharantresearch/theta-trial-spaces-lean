import ThetaTrial.Paper.Laguerre
import ThetaTrial.Paper.ThetaModes
import ThetaTrial.Paper.ThetaDerivativeSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Concentration of the theta polynomial profiles

The first step concerns the positive density `(Y+x)^(3/2) exp(-2x) |q(x)|²`
on `x > 0`. The moment input is the Laguerre estimate of Lemma
`deriv:laguerre-moment`.
-/

noncomputable section

open MeasureTheory Set Polynomial
open scoped Polynomial

namespace ThetaTrial.Paper

def firstModePolynomialDensity (Y : ℝ) (q : ℂ[X]) (x : ℝ) : ℝ :=
  (Y + x) ^ (3 / 2 : ℝ) * ‖q.eval (x : ℂ)‖ ^ 2 * Real.exp (-(2 * x))

theorem firstMode_power_lower {Y x : ℝ} (hY : 6 ≤ Y) (hx : 0 ≤ x) :
    Y ^ (3 / 2 : ℝ) ≤ (Y + x) ^ (3 / 2 : ℝ) := by
  exact Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)

theorem firstMode_power_upper {Y x : ℝ} (hY : 6 ≤ Y) (hx : 0 ≤ x) :
    (Y + x) ^ (3 / 2 : ℝ) ≤ Y ^ (3 / 2 : ℝ) * Real.exp (x / 4) := by
  have hYpos : 0 < Y := by linarith
  have hYx : 0 < Y + x := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hYx hYpos)
  rw [Real.log_div hYx.ne' hYpos.ne'] at hlog
  have hfrac : (Y + x) / Y - 1 = x / Y := by field_simp; ring
  rw [hfrac] at hlog
  have hr : (3 / 2 : ℝ) * (x / Y) ≤ x / 4 := by
    apply (mul_le_mul_iff_right₀ hYpos).mp
    have hmul := mul_nonneg (sub_nonneg.mpr hY) hx
    field_simp
    nlinarith
  rw [Real.rpow_def_of_pos hYx, Real.rpow_def_of_pos hYpos, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem firstModePolynomialDensity_nonneg {Y x : ℝ} (hY : 6 ≤ Y)
    (hx : 0 ≤ x) (q : ℂ[X]) : 0 ≤ firstModePolynomialDensity Y q x := by
  unfold firstModePolynomialDensity
  positivity

theorem firstModePolynomialDensity_lower {Y x : ℝ} (hY : 6 ≤ Y)
    (hx : 0 ≤ x) (q : ℂ[X]) :
    Y ^ (3 / 2 : ℝ) * (‖q.eval (x : ℂ)‖ ^ 2 * Real.exp (-(2 * x))) ≤
      firstModePolynomialDensity Y q x := by
  unfold firstModePolynomialDensity
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_right (firstMode_power_lower hY hx) (by positivity)

theorem firstModePolynomialDensity_exp_upper {Y x : ℝ} (hY : 6 ≤ Y)
    (hx : 0 ≤ x) (q : ℂ[X]) :
    Real.exp x * firstModePolynomialDensity Y q x ≤
      Y ^ (3 / 2 : ℝ) * (‖q.eval (x : ℂ)‖ ^ 2 * Real.exp (-((3 / 4 : ℝ) * x))) := by
  have h := mul_le_mul_of_nonneg_right (firstMode_power_upper hY hx)
    (by positivity : 0 ≤ Real.exp x * ‖q.eval (x : ℂ)‖ ^ 2 * Real.exp (-(2 * x)))
  have he : Real.exp (x / 4) * (Real.exp x * Real.exp (-(2 * x))) =
      Real.exp (-((3 / 4 : ℝ) * x)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp x * firstModePolynomialDensity Y q x =
        (Y + x) ^ (3 / 2 : ℝ) *
          (Real.exp x * ‖q.eval (x : ℂ)‖ ^ 2 * Real.exp (-(2 * x))) := by
      unfold firstModePolynomialDensity
      ring
    _ ≤ (Y ^ (3 / 2 : ℝ) * Real.exp (x / 4)) *
        (Real.exp x * ‖q.eval (x : ℂ)‖ ^ 2 * Real.exp (-(2 * x))) := h
    _ = Y ^ (3 / 2 : ℝ) * (‖q.eval (x : ℂ)‖ ^ 2 *
        (Real.exp (x / 4) * (Real.exp x * Real.exp (-(2 * x))))) := by ring
    _ = _ := by rw [he]

theorem firstModePolynomialDensity_continuous (Y : ℝ) (q : ℂ[X]) :
    Continuous (firstModePolynomialDensity Y q) := by
  have hpoly : Continuous (fun x : ℝ => q.eval (x : ℂ)) :=
    q.continuous.comp Complex.continuous_ofReal
  have hp : Continuous (fun x : ℝ => (Y + x) ^ (3 / 2 : ℝ)) :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).comp
      (continuous_const.add continuous_id)
  unfold firstModePolynomialDensity
  fun_prop

theorem firstModePolynomialDensity_exp_integrable {Y : ℝ} (hY : 6 ≤ Y)
    (q : ℂ[X]) :
    IntegrableOn (fun x : ℝ => Real.exp x * firstModePolynomialDensity Y q x) (Ioi 0) := by
  have hbase : IntegrableOn (fun x : ℝ =>
      ‖q.eval (x : ℂ)‖ ^ 2 * Real.exp (-((3 / 4 : ℝ) * x))) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using
      complex_polynomial_weighted_exp_integrable q 0 (r := (3 / 4 : ℝ)) (by norm_num)
  apply (hbase.const_mul (Y ^ (3 / 2 : ℝ))).mono'
    ((Real.continuous_exp.mul (firstModePolynomialDensity_continuous Y q)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos x).le
    (firstModePolynomialDensity_nonneg hY hx.le q))]
  exact firstModePolynomialDensity_exp_upper hY hx.le q

theorem firstModePolynomialDensity_integrable {Y : ℝ} (hY : 6 ≤ Y)
    (q : ℂ[X]) : IntegrableOn (firstModePolynomialDensity Y q) (Ioi 0) := by
  apply (firstModePolynomialDensity_exp_integrable hY q).mono'
    (firstModePolynomialDensity_continuous Y q).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (firstModePolynomialDensity_nonneg hY hx.le q)]
  have he : 1 ≤ Real.exp x := Real.one_le_exp hx.le
  simpa only [one_mul] using mul_le_mul_of_nonneg_right he
    (firstModePolynomialDensity_nonneg hY hx.le q)

theorem firstModePolynomialDensity_mass_lower {Y : ℝ} (hY : 6 ≤ Y)
    (q : ℂ[X]) :
    Y ^ (3 / 2 : ℝ) * complexPolynomialMoment q 0 2 ≤
      ∫ x : ℝ in Ioi 0, firstModePolynomialDensity Y q x := by
  have hi : IntegrableOn (fun x : ℝ =>
      ‖q.eval (x : ℂ)‖ ^ 2 * Real.exp (-(2 * x))) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using
      complex_polynomial_weighted_exp_integrable q 0 (r := (2 : ℝ)) (by norm_num)
  have h := setIntegral_mono_on (hi.const_mul (Y ^ (3 / 2 : ℝ)))
    (firstModePolynomialDensity_integrable hY q) measurableSet_Ioi
    (fun x hx => firstModePolynomialDensity_lower hY hx.le q)
  simpa only [integral_const_mul, complexPolynomialMoment, pow_zero, one_mul] using h

theorem firstModePolynomialDensity_mass_pos {Y : ℝ} (hY : 6 ≤ Y)
    {q : ℂ[X]} (hq : q ≠ 0) :
    0 < ∫ x : ℝ in Ioi 0, firstModePolynomialDensity Y q x := by
  apply lt_of_lt_of_le _ (firstModePolynomialDensity_mass_lower hY q)
  exact mul_pos (Real.rpow_pos_of_pos (by linarith) _)
    (complexPolynomialMoment_zero_pos hq (by norm_num))

theorem firstModePolynomialDensity_exp_mass_upper {Y : ℝ} (hY : 6 ≤ Y)
    (q : ℂ[X]) :
    (∫ x : ℝ in Ioi 0, Real.exp x * firstModePolynomialDensity Y q x) ≤
      Y ^ (3 / 2 : ℝ) * complexPolynomialMoment q 0 (3 / 4) := by
  have hi : IntegrableOn (fun x : ℝ =>
      ‖q.eval (x : ℂ)‖ ^ 2 * Real.exp (-((3 / 4 : ℝ) * x))) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using
      complex_polynomial_weighted_exp_integrable q 0 (r := (3 / 4 : ℝ)) (by norm_num)
  have h := setIntegral_mono_on (firstModePolynomialDensity_exp_integrable hY q)
    (hi.const_mul (Y ^ (3 / 2 : ℝ))) measurableSet_Ioi
    (fun x hx => firstModePolynomialDensity_exp_upper hY hx.le q)
  simpa only [integral_const_mul, complexPolynomialMoment, pow_zero, one_mul] using h

theorem firstModePolynomialDensity_exp_mass_le {Y : ℝ} (hY : 6 ≤ Y)
    (m : ℕ) (q : ℂ[X]) (hq : q ≠ 0) (hm : q.natDegree ≤ m) :
    (∫ x : ℝ in Ioi 0, Real.exp x * firstModePolynomialDensity Y q x) ≤
      (8 / 3 : ℝ) ^ (4 * m + 6) *
        ∫ x : ℝ in Ioi 0, firstModePolynomialDensity Y q x := by
  have hratio := complexPolynomialMoment_ratio_le m q hq hm
    (k₁ := (3 / 4 : ℝ)) (k₂ := 2) (by norm_num) (by norm_num)
  norm_num only [show (2 : ℝ) / (3 / 4) = 8 / 3 by norm_num] at hratio
  have hI := (div_le_iff₀ (complexPolynomialMoment_zero_pos hq (r := 2)
    (by norm_num))).mp hratio
  have hYp : 0 ≤ Y ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  calc
    _ ≤ Y ^ (3 / 2 : ℝ) * complexPolynomialMoment q 0 (3 / 4) :=
      firstModePolynomialDensity_exp_mass_upper hY q
    _ ≤ Y ^ (3 / 2 : ℝ) *
        ((8 / 3 : ℝ) ^ (4 * m + 6) * complexPolynomialMoment q 0 2) :=
      mul_le_mul_of_nonneg_left hI hYp
    _ = (8 / 3 : ℝ) ^ (4 * m + 6) *
        (Y ^ (3 / 2 : ℝ) * complexPolynomialMoment q 0 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (firstModePolynomialDensity_mass_lower hY q)
      (by positivity)

theorem firstModePolynomialDensity_tail_le {Y z : ℝ} (hY : 6 ≤ Y)
    (hz : 0 ≤ z) (m : ℕ) (q : ℂ[X]) (hq : q ≠ 0) (hm : q.natDegree ≤ m) :
    (∫ x : ℝ in Ioi z, firstModePolynomialDensity Y q x) ≤
      (Real.exp (-z) * (8 / 3 : ℝ) ^ (4 * m + 6)) *
        ∫ x : ℝ in Ioi 0, firstModePolynomialDensity Y q x := by
  have hsub : Ioi z ⊆ Ioi (0 : ℝ) := fun x hx => lt_of_le_of_lt hz hx
  have hD := firstModePolynomialDensity_integrable hY q
  have hE := firstModePolynomialDensity_exp_integrable hY q
  have hpoint : ∀ x ∈ Ioi z, firstModePolynomialDensity Y q x ≤
      Real.exp (-z) * (Real.exp x * firstModePolynomialDensity Y q x) := by
    intro x hx
    have hd := firstModePolynomialDensity_nonneg hY (hsub hx).le q
    change z < x at hx
    have he : 1 ≤ Real.exp (-z) * Real.exp x := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    simpa only [one_mul, mul_assoc] using mul_le_mul_of_nonneg_right he hd
  have hmono : (∫ x : ℝ in Ioi z, Real.exp x * firstModePolynomialDensity Y q x) ≤
      ∫ x : ℝ in Ioi 0, Real.exp x * firstModePolynomialDensity Y q x := by
    apply setIntegral_mono_set hE
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (Real.exp_pos x).le (firstModePolynomialDensity_nonneg hY hx.le q)
    · exact Filter.Eventually.of_forall hsub
  calc
    _ ≤ ∫ x : ℝ in Ioi z,
        Real.exp (-z) * (Real.exp x * firstModePolynomialDensity Y q x) :=
      setIntegral_mono_on (hD.mono_set hsub)
        ((hE.mono_set hsub).const_mul _) measurableSet_Ioi hpoint
    _ = Real.exp (-z) *
        ∫ x : ℝ in Ioi z, Real.exp x * firstModePolynomialDensity Y q x := by
      rw [integral_const_mul]
    _ ≤ Real.exp (-z) *
        ∫ x : ℝ in Ioi 0, Real.exp x * firstModePolynomialDensity Y q x :=
      mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le
    _ ≤ Real.exp (-z) * ((8 / 3 : ℝ) ^ (4 * m + 6) *
        ∫ x : ℝ in Ioi 0, firstModePolynomialDensity Y q x) :=
      mul_le_mul_of_nonneg_left (firstModePolynomialDensity_exp_mass_le hY m q hq hm)
        (Real.exp_pos _).le
    _ = _ := by ring

theorem laguerre_ratio_constant_le_exp (m : ℕ) :
    (8 / 3 : ℝ) ^ (4 * m + 6) ≤ Real.exp (10 * ((m : ℝ) + 1)) := by
  have hlog : Real.log (8 / 3 : ℝ) ≤ 5 / 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8 / 3)
    norm_num at h ⊢
    exact h
  have hexp : (8 / 3 : ℝ) ^ (4 * m + 6) =
      Real.exp (((4 * m + 6 : ℕ) : ℝ) * Real.log (8 / 3 : ℝ)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 8 / 3)]
  rw [hexp]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (4 * m + 6) :
    (0 : ℝ) ≤ ((4 * m + 6 : ℕ) : ℝ))
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h ⊢
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith

/-- Normalized first-mode survival bound, with the explicit absolute
choice K=40. The degree parameter is m, and the paper's M is m+1. -/
theorem firstModePolynomialDensity_survival {Y z : ℝ} (hY : 6 ≤ Y)
    (m : ℕ) (q : ℂ[X]) (hq : q ≠ 0) (hm : q.natDegree ≤ m)
    (hz : 40 * ((m : ℝ) + 1) ≤ z) :
    (∫ x : ℝ in Ioi z, firstModePolynomialDensity Y q x) /
      (∫ x : ℝ in Ioi 0, firstModePolynomialDensity Y q x) ≤
        Real.exp (-((3 / 4 : ℝ) * z)) := by
  have hz₀ : 0 ≤ z := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  have hconst : Real.exp (-z) * (8 / 3 : ℝ) ^ (4 * m + 6) ≤
      Real.exp (-((3 / 4 : ℝ) * z)) := by
    calc
      _ ≤ Real.exp (-z) * Real.exp (10 * ((m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (laguerre_ratio_constant_le_exp m) (Real.exp_pos _).le
      _ = Real.exp (-z + 10 * ((m : ℝ) + 1)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  apply (div_le_iff₀ (firstModePolynomialDensity_mass_pos hY hq)).mpr
  exact (firstModePolynomialDensity_tail_le hY hz₀ m q hq hm).trans
    (mul_le_mul_of_nonneg_right hconst (firstModePolynomialDensity_mass_pos hY hq).le)

def translateComplexPolynomial (R : ℂ[X]) (Y : ℝ) : ℂ[X] :=
  R.comp (X + C (Y : ℂ))

theorem translateComplexPolynomial_eval (R : ℂ[X]) (Y x : ℝ) :
    (translateComplexPolynomial R Y).eval (x : ℂ) = R.eval ((Y + x : ℝ) : ℂ) := by
  simp only [translateComplexPolynomial, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C, Complex.ofReal_add]
  congr 1
  ring

theorem translateComplexPolynomial_natDegree (R : ℂ[X]) (Y : ℝ) :
    (translateComplexPolynomial R Y).natDegree = R.natDegree := by
  simp only [translateComplexPolynomial, natDegree_comp, natDegree_X_add_C, mul_one]

theorem translateComplexPolynomial_ne_zero {R : ℂ[X]} (hR : R ≠ 0) (Y : ℝ) :
    translateComplexPolynomial R Y ≠ 0 := by
  exact comp_X_add_C_ne_zero_iff.mpr hR

theorem thetaQ_zero_strictMono : StrictMono (ThetaTrial.ThetaSeries.thetaQ 0) := by
  intro u v huv
  simp only [ThetaTrial.ThetaSeries.thetaQ, Nat.cast_zero, zero_add, one_pow, mul_one]
  apply mul_lt_mul_of_pos_left _ Real.pi_pos
  exact Real.exp_lt_exp.mpr (by linarith)

theorem thetaQ_zero_pos (u : ℝ) : 0 < ThetaTrial.ThetaSeries.thetaQ 0 u := by
  simp only [ThetaTrial.ThetaSeries.thetaQ, Nat.cast_zero, zero_add, one_pow, mul_one]
  positivity

theorem thetaQ_zero_image_Ioi (a : ℝ) :
    ThetaTrial.ThetaSeries.thetaQ 0 '' Ioi a = Ioi (ThetaTrial.ThetaSeries.thetaQ 0 a) := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact thetaQ_zero_strictMono hu
  · intro hy
    have hypos : 0 < y := lt_trans (thetaQ_zero_pos a) hy
    let u : ℝ := Real.log (y / Real.pi) / 2
    have hu : ThetaTrial.ThetaSeries.thetaQ 0 u = y := by
      simp only [ThetaTrial.ThetaSeries.thetaQ, Nat.cast_zero, zero_add, one_pow, mul_one, u]
      rw [show 2 * (Real.log (y / Real.pi) / 2) = Real.log (y / Real.pi) by ring,
        Real.exp_log (div_pos hypos Real.pi_pos)]
      field_simp
    refine ⟨u, ?_, hu⟩
    apply thetaQ_zero_strictMono.lt_iff_lt.mp
    rw [hu]
    exact hy

def firstModeYDensity (R : ℂ[X]) (y : ℝ) : ℝ :=
  y ^ (3 / 2 : ℝ) * ‖R.eval (y : ℂ)‖ ^ 2 * Real.exp (-(2 * y))

theorem firstModeYDensity_translate (R : ℂ[X]) (Y x : ℝ) :
    firstModeYDensity R (Y + x) = Real.exp (-(2 * Y)) *
      firstModePolynomialDensity Y (translateComplexPolynomial R Y) x := by
  simp only [firstModeYDensity, firstModePolynomialDensity, translateComplexPolynomial_eval]
  rw [show -(2 * (Y + x)) = -(2 * Y) + -(2 * x) by ring, Real.exp_add]
  ring

theorem firstModeYDensity_tail_translate (R : ℂ[X]) (Y z : ℝ) :
    (∫ y : ℝ in Ioi (Y + z), firstModeYDensity R y) = Real.exp (-(2 * Y)) *
      ∫ x : ℝ in Ioi z, firstModePolynomialDensity Y (translateComplexPolynomial R Y) x := by
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioi z)
    measurableSet_Ioi
    (fun x hx => ((hasDerivAt_id x).const_add Y).hasDerivWithinAt)
    (show Set.InjOn (fun x : ℝ => Y + x) (Ioi z) from fun x hx y hy hxy =>
      add_left_cancel hxy) (firstModeYDensity R)
  simp only [id_eq, image_const_add_Ioi, abs_one, one_smul, firstModeYDensity_translate,
    integral_const_mul] at h
  exact h

/-- Exact density after the theta change of variables, including the Jacobian. -/
theorem firstMode_normSquare_jacobian (P : ℂ[X]) (u : ℝ) :
    (2 * ThetaTrial.ThetaSeries.thetaQ 0 u) *
        firstModeYDensity (thetaPaperPolynomial P) (ThetaTrial.ThetaSeries.thetaQ 0 u) =
      2 * ‖polynomialDerivative P (fun v => (paperThetaMode 0 v : ℂ)) u‖ ^ 2 := by
  let y := ThetaTrial.ThetaSeries.thetaQ 0 u
  have hy : 0 < y := thetaQ_zero_pos u
  have hpow : (y ^ (5 / 4 : ℝ)) ^ (2 : ℕ) = y * y ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_mul_natCast hy.le]
    have he : (5 / 4 : ℝ) * (2 : ℕ) = 1 + 3 / 2 := by norm_num
    rw [he, Real.rpow_add hy, Real.rpow_one]
  have hexp : Real.exp (-y) ^ (2 : ℕ) = Real.exp (-(2 * y)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [polynomialDerivative_firstMode_representation]
  change (2 * y) * firstModeYDensity (thetaPaperPolynomial P) y =
    2 * ‖(Real.exp (-y) : ℂ) * (y ^ (5 / 4 : ℝ) : ℝ) *
      (thetaPaperPolynomial P).eval (y : ℂ)‖ ^ 2
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), abs_of_nonneg (Real.rpow_nonneg hy.le _), mul_pow]
  rw [hpow, hexp]
  unfold firstModeYDensity
  ring

theorem firstMode_normSquare_tail_change (P : ℂ[X]) (a : ℝ) :
    (∫ u : ℝ in Ioi a,
      ‖polynomialDerivative P (fun v => (paperThetaMode 0 v : ℂ)) u‖ ^ 2) =
      (1 / 2 : ℝ) * ∫ y : ℝ in Ioi (ThetaTrial.ThetaSeries.thetaQ 0 a),
        firstModeYDensity (thetaPaperPolynomial P) y := by
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioi a)
    measurableSet_Ioi (fun u hu => (thetaQ_hasDerivAt u).hasDerivWithinAt)
    thetaQ_injective.injOn (firstModeYDensity (thetaPaperPolynomial P))
  rw [thetaQ_zero_image_Ioi] at h
  have he (u : ℝ) : |2 * ThetaTrial.ThetaSeries.thetaQ 0 u| •
      firstModeYDensity (thetaPaperPolynomial P) (ThetaTrial.ThetaSeries.thetaQ 0 u) =
      2 * ‖polynomialDerivative P (fun v => (paperThetaMode 0 v : ℂ)) u‖ ^ 2 := by
    rw [abs_of_pos (mul_pos (by norm_num) (thetaQ_zero_pos u)), smul_eq_mul]
    exact firstMode_normSquare_jacobian P u
  simp_rw [he] at h
  rw [integral_const_mul] at h
  linarith

theorem thetaQ_zero_add (a s : ℝ) :
    ThetaTrial.ThetaSeries.thetaQ 0 (a + s) = ThetaTrial.ThetaSeries.thetaQ 0 a * Real.exp (2 * s) := by
  simp only [ThetaTrial.ThetaSeries.thetaQ, Nat.cast_zero, zero_add, one_pow, mul_one]
  rw [show 2 * (a + s) = 2 * a + 2 * s by ring, Real.exp_add]
  ring

theorem firstMode_normSquare_tail_density (P : ℂ[X]) (Y b z : ℝ)
    (hb : ThetaTrial.ThetaSeries.thetaQ 0 b = Y + z) :
    (∫ u : ℝ in Ioi b,
      ‖polynomialDerivative P (fun v => (paperThetaMode 0 v : ℂ)) u‖ ^ 2) =
      ((1 / 2 : ℝ) * Real.exp (-(2 * Y))) *
        ∫ x : ℝ in Ioi z,
          firstModePolynomialDensity Y (translateComplexPolynomial (thetaPaperPolynomial P) Y) x := by
  rw [firstMode_normSquare_tail_change, hb, firstModeYDensity_tail_translate]
  ring

theorem firstMode_normSquare_tail_pos (P : ℂ[X]) (hP : P ≠ 0) (a : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a) :
    0 < ∫ u : ℝ in Ioi a,
      ‖polynomialDerivative P (fun v => (paperThetaMode 0 v : ℂ)) u‖ ^ 2 := by
  rw [firstMode_normSquare_tail_density P (ThetaTrial.ThetaSeries.thetaQ 0 a) a 0 (by simp)]
  apply mul_pos (by positivity)
  exact firstModePolynomialDensity_mass_pos ha
    (translateComplexPolynomial_ne_zero (thetaPaperPolynomial_ne_zero hP) _)

/-- The first-mode tail bound for the polynomial differential operator,
including its exact polynomial normalization and the theta Jacobian. -/
theorem firstMode_derivative_survival (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a s : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hs : 40 * ((d : ℝ) + 2) ≤
      ThetaTrial.ThetaSeries.thetaQ 0 a * (Real.exp (2 * s) - 1)) :
    (∫ u : ℝ in Ioi (a + s),
      ‖polynomialDerivative P (fun v => (paperThetaMode 0 v : ℂ)) u‖ ^ 2) /
      (∫ u : ℝ in Ioi a,
        ‖polynomialDerivative P (fun v => (paperThetaMode 0 v : ℂ)) u‖ ^ 2) ≤
      Real.exp (-((3 / 4 : ℝ) *
        (ThetaTrial.ThetaSeries.thetaQ 0 a * (Real.exp (2 * s) - 1)))) := by
  let Y := ThetaTrial.ThetaSeries.thetaQ 0 a
  let z := Y * (Real.exp (2 * s) - 1)
  let q := translateComplexPolynomial (thetaPaperPolynomial P) Y
  have hcut : ThetaTrial.ThetaSeries.thetaQ 0 (a + s) = Y + z := by
    rw [thetaQ_zero_add]
    dsimp [Y, z]
    ring
  rw [firstMode_normSquare_tail_density P Y (a + s) z hcut,
    firstMode_normSquare_tail_density P Y a 0 (by simp [Y]),
    mul_div_mul_left _ _ (by positivity : (1 / 2 : ℝ) * Real.exp (-(2 * Y)) ≠ 0)]
  apply firstModePolynomialDensity_survival ha (d + 1) q
  · exact translateComplexPolynomial_ne_zero (thetaPaperPolynomial_ne_zero hP) Y
  · rw [translateComplexPolynomial_natDegree, thetaPaperPolynomial_natDegree hP]
    omega
  · simpa only [Nat.cast_add, Nat.cast_one, show (1 : ℝ) + 1 = 2 by norm_num,
      add_assoc] using hs

theorem polynomialDerivative_mode_normSquare_shift (P : ℂ[X]) (n : ℕ) (u : ℝ) :
    ‖polynomialDerivative P (fun v => (paperThetaMode n v : ℂ)) u‖ ^ 2 =
      (((n : ℝ) + 1)⁻¹) *
        ‖polynomialDerivative P (fun v => (paperThetaMode 0 v : ℂ))
          (u + Real.log ((n : ℝ) + 1))‖ ^ 2 := by
  rw [polynomialDerivative_mode_shift, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, ← Real.exp_nat_mul]
  have he : (2 : ℝ) * (-Real.log ((n : ℝ) + 1) / 2) =
      -Real.log ((n : ℝ) + 1) := by ring
  norm_num only [Nat.cast_ofNat]
  rw [he, Real.exp_neg, Real.exp_log (by positivity)]

/-- Exact L² mode translation, before taking square roots. -/
theorem polynomialDerivative_mode_tail_shift (P : ℂ[X]) (n : ℕ) (b : ℝ) :
    (∫ u : ℝ in Ioi b,
      ‖polynomialDerivative P (fun v => (paperThetaMode n v : ℂ)) u‖ ^ 2) =
      (((n : ℝ) + 1)⁻¹) *
        ∫ u : ℝ in Ioi (b + Real.log ((n : ℝ) + 1)),
          ‖polynomialDerivative P (fun v => (paperThetaMode 0 v : ℂ)) u‖ ^ 2 := by
  simp_rw [polynomialDerivative_mode_normSquare_shift P n]
  rw [integral_const_mul]
  congr 1
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioi b)
    measurableSet_Ioi
    (fun x hx => ((hasDerivAt_id x).add_const (Real.log ((n : ℝ) + 1))).hasDerivWithinAt)
    (show Set.InjOn (fun x : ℝ => x + Real.log ((n : ℝ) + 1)) (Ioi b) from
      fun x hx y hy hxy => add_right_cancel hxy)
    (fun u : ℝ => ‖polynomialDerivative P (fun v => (paperThetaMode 0 v : ℂ)) u‖ ^ 2)
  simpa only [id_eq, image_add_const_Ioi, abs_one, one_smul] using h.symm

def thetaModeOffset (n : ℕ) (a s : ℝ) : ℝ :=
  ThetaTrial.ThetaSeries.thetaQ 0 a * (((n : ℝ) + 1) ^ 2 * Real.exp (2 * s) - 1)

theorem thetaModeOffset_eq_shift (n : ℕ) (a s : ℝ) :
    thetaModeOffset n a s = ThetaTrial.ThetaSeries.thetaQ 0 a *
      (Real.exp (2 * (s + Real.log ((n : ℝ) + 1))) - 1) := by
  unfold thetaModeOffset
  rw [show 2 * (s + Real.log ((n : ℝ) + 1)) =
      2 * s + 2 * Real.log ((n : ℝ) + 1) by ring, Real.exp_add]
  have he : Real.exp (2 * Real.log ((n : ℝ) + 1)) = ((n : ℝ) + 1) ^ (2 : ℕ) := by
    have h := Real.exp_nat_mul (Real.log ((n : ℝ) + 1)) 2
    simpa only [Nat.cast_ofNat, Real.exp_log (by positivity : (0 : ℝ) < (n : ℝ) + 1)] using h
  rw [he]
  ring

/-- Coefficient-uniform squared L² estimate for every theta mode. -/
theorem polynomialDerivative_mode_tail_bound (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (n : ℕ) (a s : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hs : 40 * ((d : ℝ) + 2) ≤ thetaModeOffset n a s) :
    (∫ u : ℝ in Ioi (a + s),
      ‖polynomialDerivative P (fun v => (paperThetaMode n v : ℂ)) u‖ ^ 2) ≤
      (((n : ℝ) + 1)⁻¹ * Real.exp (-((3 / 4 : ℝ) * thetaModeOffset n a s))) *
        ∫ u : ℝ in Ioi a,
          ‖polynomialDerivative P (fun v => (paperThetaMode 0 v : ℂ)) u‖ ^ 2 := by
  rw [polynomialDerivative_mode_tail_shift]
  have h := firstMode_derivative_survival d P hP hdegree a
    (s + Real.log ((n : ℝ) + 1)) ha
    (by simpa only [← thetaModeOffset_eq_shift] using hs)
  rw [← thetaModeOffset_eq_shift] at h
  have h' := (div_le_iff₀ (firstMode_normSquare_tail_pos P hP a ha)).mp h
  have h'' := mul_le_mul_of_nonneg_left h' (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹)
  simpa only [add_assoc, mul_assoc] using h''

theorem thetaPolyProfile_continuous (R : ℂ[X]) : Continuous (thetaPolyProfile R) := by
  have hq : Continuous (ThetaTrial.ThetaSeries.thetaQ 0) :=
    continuous_iff_continuousAt.mpr (fun u => (thetaQ_hasDerivAt u).continuousAt)
  have hp : Continuous (fun u : ℝ => R.eval (ThetaTrial.ThetaSeries.thetaQ 0 u : ℂ)) :=
    R.continuous.comp (Complex.continuous_ofReal.comp hq)
  unfold thetaPolyProfile thetaModeWeight
  fun_prop

theorem polynomialDerivative_firstMode_continuous (P : ℂ[X]) :
    Continuous (polynomialDerivative P (fun v => (paperThetaMode 0 v : ℂ))) := by
  rw [← thetaPolynomialOperator_eq_polynomialDerivative, thetaMultiplierPoly_represents]
  exact thetaPolyProfile_continuous _

theorem polynomialDerivative_mode_continuous (P : ℂ[X]) (n : ℕ) :
    Continuous (polynomialDerivative P (fun v => (paperThetaMode n v : ℂ))) := by
  have he : polynomialDerivative P (fun v => (paperThetaMode n v : ℂ)) =
      fun u => (Real.exp (-Real.log ((n : ℝ) + 1) / 2) : ℂ) *
        polynomialDerivative P (fun v => (paperThetaMode 0 v : ℂ))
          (u + Real.log ((n : ℝ) + 1)) := by
    funext u
    exact polynomialDerivative_mode_shift P n u
  rw [he]
  exact continuous_const.mul ((polynomialDerivative_firstMode_continuous P).comp
    (continuous_id.add continuous_const))

theorem polynomialDerivative_mode_tail_pos (P : ℂ[X]) (hP : P ≠ 0)
    (n : ℕ) (b : ℝ) (hb : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 b) :
    0 < ∫ u : ℝ in Ioi b,
      ‖polynomialDerivative P (fun v => (paperThetaMode n v : ℂ)) u‖ ^ 2 := by
  rw [polynomialDerivative_mode_tail_shift]
  have hn : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg
    (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hb' : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 (b + Real.log ((n : ℝ) + 1)) :=
    hb.trans (thetaQ_zero_strictMono.monotone (by linarith))
  exact mul_pos (by positivity) (firstMode_normSquare_tail_pos P hP _ hb')

theorem polynomialDerivative_mode_memLp (P : ℂ[X]) (hP : P ≠ 0)
    (n : ℕ) (b : ℝ) (hb : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 b) :
    MemLp (polynomialDerivative P (fun v => (paperThetaMode n v : ℂ))) 2
      (volume.restrict (Ioi b)) := by
  apply (memLp_two_iff_integrable_sq_norm
    (polynomialDerivative_mode_continuous P n).aestronglyMeasurable).mpr
  exact Integrable.of_integral_ne_zero (polynomialDerivative_mode_tail_pos P hP n b hb).ne'

def thetaModeTailLp (P : ℂ[X]) (hP : P ≠ 0) (n : ℕ) (b : ℝ)
    (hb : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 b) : Lp ℂ 2 (volume.restrict (Ioi b)) :=
  (polynomialDerivative_mode_memLp P hP n b hb).toLp
    (polynomialDerivative P (fun v => (paperThetaMode n v : ℂ)))

theorem complex_L2_integral_norm_sq {μ : Measure ℝ} (f : Lp ℂ 2 μ) :
    (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) = ‖f‖ ^ 2 := by
  apply Complex.ofRealLI.injective
  have h := (L2.inner_def (𝕜 := ℂ) f f).symm
  simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using h

theorem thetaModeTailLp_norm_sq (P : ℂ[X]) (hP : P ≠ 0) (n : ℕ) (b : ℝ)
    (hb : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 b) :
    ‖thetaModeTailLp P hP n b hb‖ ^ 2 =
      ∫ u : ℝ in Ioi b,
        ‖polynomialDerivative P (fun v => (paperThetaMode n v : ℂ)) u‖ ^ 2 := by
  rw [← complex_L2_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (polynomialDerivative_mode_memLp P hP n b hb)] with u hu
  rw [show thetaModeTailLp P hP n b hb u =
    polynomialDerivative P (fun v => (paperThetaMode n v : ℂ)) u from hu]

theorem thetaModeTailLp_norm_le_exp (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (n : ℕ) (a s : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hb : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 (a + s))
    (hs : 40 * ((d : ℝ) + 2) ≤ thetaModeOffset n a s) :
    ‖thetaModeTailLp P hP n (a + s) hb‖ ≤
      Real.exp (-((3 / 8 : ℝ) * thetaModeOffset n a s)) *
        ‖thetaModeTailLp P hP 0 a ha‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, thetaModeTailLp_norm_sq, thetaModeTailLp_norm_sq]
  have he : Real.exp (-((3 / 8 : ℝ) * thetaModeOffset n a s)) ^ (2 : ℕ) =
      Real.exp (-((3 / 4 : ℝ) * thetaModeOffset n a s)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [he]
  have h := polynomialDerivative_mode_tail_bound d P hP hdegree n a s ha hs
  have hn : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have he' : ((n : ℝ) + 1)⁻¹ *
      Real.exp (-((3 / 4 : ℝ) * thetaModeOffset n a s)) ≤
      Real.exp (-((3 / 4 : ℝ) * thetaModeOffset n a s)) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
  exact h.trans (mul_le_mul_of_nonneg_right he' (by
    apply integral_nonneg
    intro u
    positivity))

theorem thetaModeOffset_ge_base (n : ℕ) (a s : ℝ) (hs : 0 ≤ s) :
    thetaModeOffset 0 a s + ThetaTrial.ThetaSeries.thetaQ 0 a *
      (((n : ℝ) + 1) ^ 2 - 1) ≤ thetaModeOffset n a s := by
  have hn : 0 ≤ ((n : ℝ) + 1) ^ 2 - 1 := by
    have := Nat.cast_nonneg (α := ℝ) n
    nlinarith
  have he : 0 ≤ Real.exp (2 * s) - 1 := by
    have := Real.one_le_exp (by linarith : (0 : ℝ) ≤ 2 * s)
    linarith
  have h := mul_nonneg (thetaQ_zero_pos a).le (mul_nonneg hn he)
  simp only [thetaModeOffset, Nat.cast_zero, zero_add, one_pow, one_mul]
  nlinarith

theorem thetaMode_envelope_geometric (n : ℕ) {Y : ℝ} (hY : 6 ≤ Y) :
    Real.exp (-((3 / 8 : ℝ) * Y * (((n : ℝ) + 1) ^ 2 - 1))) ≤
      (1 / 4 : ℝ) ^ n := by
  have hquad : 3 * (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 - 1 := by
    cases n with
    | zero => norm_num
    | succ n =>
      norm_num only [Nat.cast_add, Nat.cast_one]
      have := Nat.cast_nonneg (α := ℝ) n
      nlinarith
  have hsmall : Real.exp (-((9 / 8 : ℝ) * Y)) ≤ 1 / 4 := by
    rw [Real.exp_neg]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    have h := Real.add_one_le_exp ((9 / 8 : ℝ) * Y)
    nlinarith
  calc
    _ ≤ Real.exp ((n : ℝ) * (-((9 / 8 : ℝ) * Y))) := by
      apply Real.exp_le_exp.mpr
      have := mul_nonneg (by linarith : 0 ≤ Y) (sub_nonneg.mpr hquad)
      nlinarith
    _ = Real.exp (-((9 / 8 : ℝ) * Y)) ^ n := Real.exp_nat_mul _ _
    _ ≤ (1 / 4 : ℝ) ^ n := pow_le_pow_left₀ (Real.exp_pos _).le hsmall n

theorem thetaModeTailLp_norm_le_geometric (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (n : ℕ) (a s : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hb : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 (a + s)) (hs₀ : 0 ≤ s)
    (hs : 40 * ((d : ℝ) + 2) ≤ thetaModeOffset n a s) :
    ‖thetaModeTailLp P hP n (a + s) hb‖ ≤
      (Real.exp (-((3 / 8 : ℝ) * thetaModeOffset 0 a s)) *
        ‖thetaModeTailLp P hP 0 a ha‖) * (1 / 4 : ℝ) ^ n := by
  have he : Real.exp (-((3 / 8 : ℝ) * thetaModeOffset n a s)) ≤
      Real.exp (-((3 / 8 : ℝ) * thetaModeOffset 0 a s)) * (1 / 4 : ℝ) ^ n := by
    calc
      _ ≤ Real.exp (-((3 / 8 : ℝ) *
          (thetaModeOffset 0 a s + ThetaTrial.ThetaSeries.thetaQ 0 a * (((n : ℝ) + 1) ^ 2 - 1)))) := by
        apply Real.exp_le_exp.mpr
        have h := thetaModeOffset_ge_base n a s hs₀
        linarith
      _ = Real.exp (-((3 / 8 : ℝ) * thetaModeOffset 0 a s)) *
          Real.exp (-((3 / 8 : ℝ) * ThetaTrial.ThetaSeries.thetaQ 0 a * (((n : ℝ) + 1) ^ 2 - 1))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (thetaMode_envelope_geometric n ha) (Real.exp_pos _).le
  have h := (thetaModeTailLp_norm_le_exp d P hP hdegree n a s ha hb hs).trans
    (mul_le_mul_of_nonneg_right he (norm_nonneg _))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

theorem thetaModeTailLp_base_norm_le_geometric (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (n : ℕ) (a : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a) :
    ‖thetaModeTailLp P hP n a ha‖ ≤
      ‖thetaModeTailLp P hP 0 a ha‖ * (1 / 4 : ℝ) ^ n := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hquad : (3 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 - 1 := by nlinarith
    have hstep : 3 * ThetaTrial.ThetaSeries.thetaQ 0 a ≤ thetaModeOffset n a 0 := by
      simp only [thetaModeOffset, mul_zero, Real.exp_zero, mul_one]
      nlinarith [mul_nonneg (thetaQ_zero_pos a).le (sub_nonneg.mpr hquad)]
    have h := thetaModeTailLp_norm_le_geometric d P hP hdegree n a 0 ha
      (by simpa only [add_zero] using ha) (by norm_num) (hsize.trans hstep)
    have he : ‖thetaModeTailLp P hP n (a + 0) (by simpa only [add_zero] using ha)‖ =
        ‖thetaModeTailLp P hP n a ha‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [thetaModeTailLp_norm_sq, thetaModeTailLp_norm_sq, add_zero]
    rw [he] at h
    simpa only [add_zero, thetaModeOffset, Nat.cast_zero, zero_add, one_pow,
      mul_zero, Real.exp_zero, mul_one, sub_self, neg_zero, one_mul] using h

theorem summable_norm_of_quarter_bound {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → E) (C : ℝ) (hf : ∀ n, ‖f n‖ ≤ C * (1 / 4 : ℝ) ^ n) :
    Summable (fun n => ‖f n‖) := by
  have hgeom : Summable (fun n : ℕ => C * (1 / 4 : ℝ) ^ n) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left C
  exact hgeom.of_nonneg_of_le (fun n => norm_nonneg _) hf

theorem norm_tsum_le_four_thirds_of_quarter_bound {E : Type*}
    [NormedAddCommGroup E] [CompleteSpace E] (f : ℕ → E) (C : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ C * (1 / 4 : ℝ) ^ n) :
    ‖∑' n, f n‖ ≤ (4 / 3 : ℝ) * C := by
  have hnorm := summable_norm_of_quarter_bound f C hf
  have hgeom : Summable (fun n : ℕ => C * (1 / 4 : ℝ) ^ n) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left C
  calc
    _ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, C * (1 / 4 : ℝ) ^ n := hnorm.tsum_le_tsum hf hgeom
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)]
      ring

def thetaModesTailLp (P : ℂ[X]) (hP : P ≠ 0) (a : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a) : Lp ℂ 2 (volume.restrict (Ioi a)) :=
  ∑' n : ℕ, thetaModeTailLp P hP n a ha

theorem thetaModeTailLp_summable_norm (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a) :
    Summable (fun n : ℕ => ‖thetaModeTailLp P hP n a ha‖) :=
  summable_norm_of_quarter_bound _ _
    (fun n => thetaModeTailLp_base_norm_le_geometric d P hP hdegree n a ha hsize)

theorem thetaModesTailLp_norm_upper (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a) :
    ‖thetaModesTailLp P hP a ha‖ ≤ (4 / 3 : ℝ) * ‖thetaModeTailLp P hP 0 a ha‖ :=
  norm_tsum_le_four_thirds_of_quarter_bound _ _
    (fun n => thetaModeTailLp_base_norm_le_geometric d P hP hdegree n a ha hsize)

theorem thetaModesTailLp_norm_lower (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a) :
    (2 / 3 : ℝ) * ‖thetaModeTailLp P hP 0 a ha‖ ≤ ‖thetaModesTailLp P hP a ha‖ := by
  let f : ℕ → Lp ℂ 2 (volume.restrict (Ioi a)) := fun n => thetaModeTailLp P hP n a ha
  have hsum : Summable f := (thetaModeTailLp_summable_norm d P hP hdegree a ha hsize).of_norm
  have hrest : ‖∑' n : ℕ, f (n + 1)‖ ≤ (1 / 3 : ℝ) * ‖f 0‖ := by
    have h := norm_tsum_le_four_thirds_of_quarter_bound (fun n => f (n + 1))
      (‖f 0‖ / 4) (fun n => by
        have hn := thetaModeTailLp_base_norm_le_geometric d P hP hdegree (n + 1) a ha hsize
        simpa only [f, pow_succ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, one_mul] using hn)
    nlinarith
  have he : f 0 = (∑' n, f n) - ∑' n, f (n + 1) := by
    rw [hsum.tsum_eq_zero_add]
    abel
  have htri : ‖f 0‖ ≤ ‖∑' n, f n‖ + ‖∑' n, f (n + 1)‖ := by
    rw [he]
    exact norm_sub_le _ _
  change (2 / 3 : ℝ) * ‖f 0‖ ≤ ‖∑' n, f n‖
  linarith

theorem thetaModesTailLp_decay (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a s : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hb : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 (a + s)) (hs₀ : 0 ≤ s)
    (hs : 40 * ((d : ℝ) + 2) ≤ thetaModeOffset 0 a s) :
    ‖thetaModesTailLp P hP (a + s) hb‖ ≤
      (4 / 3 : ℝ) * Real.exp (-((3 / 8 : ℝ) * thetaModeOffset 0 a s)) *
        ‖thetaModeTailLp P hP 0 a ha‖ := by
  have h := norm_tsum_le_four_thirds_of_quarter_bound
    (fun n => thetaModeTailLp P hP n (a + s) hb)
    (Real.exp (-((3 / 8 : ℝ) * thetaModeOffset 0 a s)) * ‖thetaModeTailLp P hP 0 a ha‖)
    (fun n => thetaModeTailLp_norm_le_geometric d P hP hdegree n a s ha hb hs₀ (by
      have hoff := thetaModeOffset_ge_base n a s hs₀
      have hn : 0 ≤ ((n : ℝ) + 1) ^ 2 - 1 := by
        have := Nat.cast_nonneg (α := ℝ) n
        nlinarith
      have hpos := mul_nonneg (thetaQ_zero_pos a).le hn
      linarith))
  simpa only [thetaModesTailLp, mul_assoc] using h

theorem thetaModesTailLp_norm_pos (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a) :
    0 < ‖thetaModesTailLp P hP a ha‖ := by
  have hfirst : 0 < ‖thetaModeTailLp P hP 0 a ha‖ := by
    have hsq := firstMode_normSquare_tail_pos P hP a ha
    rw [← thetaModeTailLp_norm_sq P hP 0 a ha] at hsq
    nlinarith [norm_nonneg (thetaModeTailLp P hP 0 a ha)]
  have h := thetaModesTailLp_norm_lower d P hP hdegree a ha hsize
  linarith

theorem thetaModesTailLp_survival (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a s : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hb : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 (a + s)) (hs₀ : 0 ≤ s)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hs : 40 * ((d : ℝ) + 2) ≤ thetaModeOffset 0 a s) :
    ‖thetaModesTailLp P hP (a + s) hb‖ ^ 2 / ‖thetaModesTailLp P hP a ha‖ ^ 2 ≤
      Real.exp (-(thetaModeOffset 0 a s / 2)) := by
  let offset := thetaModeOffset 0 a s
  let E := Real.exp (-((3 / 8 : ℝ) * offset))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hupper := thetaModesTailLp_decay d P hP hdegree a s ha hb hs₀ hs
  have hlower := thetaModesTailLp_norm_lower d P hP hdegree a ha hsize
  have hB : ‖thetaModesTailLp P hP (a + s) hb‖ ≤
      2 * E * ‖thetaModesTailLp P hP a ha‖ := by
    have hmul := mul_nonneg hE (sub_nonneg.mpr hlower)
    dsimp only [E, offset] at hmul ⊢
    nlinarith
  have hsq : ‖thetaModesTailLp P hP (a + s) hb‖ ^ 2 ≤
      4 * E ^ 2 * ‖thetaModesTailLp P hP a ha‖ ^ 2 := by
    have hb0 := norm_nonneg (thetaModesTailLp P hP (a + s) hb)
    have ha0 := norm_nonneg (thetaModesTailLp P hP a ha)
    have h := mul_self_le_mul_self hb0 hB
    nlinarith only [h]
  have hconstant : 4 * E ^ 2 ≤ Real.exp (-(offset / 2)) := by
    have hX : 80 ≤ offset := by
      have := Nat.cast_nonneg (α := ℝ) d
      dsimp [offset]
      linarith
    have hfour : (4 : ℝ) ≤ Real.exp (offset / 4) := by
      have h := Real.add_one_le_exp (offset / 4)
      linarith
    have hEsq : E ^ (2 : ℕ) = Real.exp (-((3 / 4 : ℝ) * offset)) := by
      dsimp [E]
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
      ring
    rw [hEsq]
    calc
      _ ≤ Real.exp (offset / 4) * Real.exp (-((3 / 4 : ℝ) * offset)) :=
        mul_le_mul_of_nonneg_right hfour (Real.exp_pos _).le
      _ = Real.exp (-(offset / 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
  apply (div_le_iff₀ (sq_pos_of_pos (thetaModesTailLp_norm_pos d P hP hdegree a ha hsize))).mpr
  exact hsq.trans (mul_le_mul_of_nonneg_right hconstant (sq_nonneg _))

/-- The theta derivative is the L² sum, almost everywhere
on the chosen exterior interval. -/
theorem thetaModesTailLp_ae_eq (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a) :
    (thetaModesTailLp P hP a ha : ℝ → ℂ) =ᵐ[volume.restrict (Ioi a)]
      polynomialDerivative P (fun v => (thetaDensity v : ℂ)) := by
  have hnorm := thetaModeTailLp_summable_norm d P hP hdegree a ha hsize
  have hsum := Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hnorm)
  have hmodes : ∀ᵐ u : ℝ ∂volume.restrict (Ioi a), ∀ n : ℕ,
      thetaModeTailLp P hP n a ha u =
        polynomialDerivative P (fun v => (paperThetaMode n v : ℂ)) u := by
    apply ae_all_iff.mpr
    intro n
    exact MemLp.coeFn_toLp (polynomialDerivative_mode_memLp P hP n a ha)
  filter_upwards [hsum, hmodes] with u hu hm
  change (∑' n : ℕ, thetaModeTailLp P hP n a ha) u = _
  rw [hu, polynomialDerivative_thetaDensity_eq_tsum]
  exact tsum_congr hm

theorem polynomialDerivative_thetaDensity_memLp_tail (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a) :
    MemLp (polynomialDerivative P (fun v => (thetaDensity v : ℂ))) 2
      (volume.restrict (Ioi a)) := by
  exact (memLp_congr_ae (thetaModesTailLp_ae_eq d P hP hdegree a ha hsize)).mp
    (Lp.memLp (thetaModesTailLp P hP a ha))

theorem fullTheta_tail_square_eq_Lp (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a) :
    (∫ u : ℝ in Ioi a,
      ‖polynomialDerivative P (fun v => (thetaDensity v : ℂ)) u‖ ^ 2) =
      ‖thetaModesTailLp P hP a ha‖ ^ 2 := by
  rw [← complex_L2_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [thetaModesTailLp_ae_eq d P hP hdegree a ha hsize] with u hu
  rw [hu]

theorem fullTheta_tail_square_pos (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a) :
    0 < ∫ u : ℝ in Ioi a,
      ‖polynomialDerivative P (fun v => (thetaDensity v : ℂ)) u‖ ^ 2 := by
  rw [fullTheta_tail_square_eq_Lp d P hP hdegree a ha hsize]
  exact sq_pos_of_pos (thetaModesTailLp_norm_pos d P hP hdegree a ha hsize)

/-- Survival estimate for the full theta series, via the triangle and reverse
triangle inequalities in `L²`. -/
theorem fullTheta_derivative_survival (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a s : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a) (hs₀ : 0 ≤ s)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hs : 40 * ((d : ℝ) + 2) ≤ thetaModeOffset 0 a s) :
    (∫ u : ℝ in Ioi (a + s),
      ‖polynomialDerivative P (fun v => (thetaDensity v : ℂ)) u‖ ^ 2) /
      (∫ u : ℝ in Ioi a,
        ‖polynomialDerivative P (fun v => (thetaDensity v : ℂ)) u‖ ^ 2) ≤
      Real.exp (-(thetaModeOffset 0 a s / 2)) := by
  have hmono := thetaQ_zero_strictMono.monotone (show a ≤ a + s by linarith)
  have hb := ha.trans hmono
  have hsizeb : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 (a + s) := by
    linarith
  rw [fullTheta_tail_square_eq_Lp d P hP hdegree (a + s) hb hsizeb,
    fullTheta_tail_square_eq_Lp d P hP hdegree a ha hsize]
  exact thetaModesTailLp_survival d P hP hdegree a s ha hb hs₀ hsize hs

theorem thetaQ_zero_eq_scaleZ (a : ℝ) : ThetaTrial.ThetaSeries.thetaQ 0 a = scaleZ a := by
  simp [ThetaTrial.ThetaSeries.thetaQ, scaleZ]

def thetaDerivTailWidth (d : ℕ) (a : ℝ) : ℝ := ((d : ℝ) + 2) / scaleT a

theorem thetaDeriv_scaleT_pos (a : ℝ) : 0 < scaleT a := by
  unfold scaleT scaleZ
  positivity

theorem thetaDerivTailWidth_pos (d : ℕ) (a : ℝ) : 0 < thetaDerivTailWidth d a := by
  unfold thetaDerivTailWidth
  exact div_pos (by positivity) (thetaDeriv_scaleT_pos a)

theorem thetaDerivTailWidth_scale (d : ℕ) (a : ℝ) :
    scaleT a * thetaDerivTailWidth d a = (d : ℝ) + 2 := by
  unfold thetaDerivTailWidth
  field_simp [(thetaDeriv_scaleT_pos a).ne']

theorem thetaModeOffset_zero_ge_linear (a s : ℝ) :
    scaleT a * s ≤ thetaModeOffset 0 a s := by
  have h := Real.add_one_le_exp (2 * s)
  have hy := thetaQ_zero_pos a
  have hmul := mul_nonneg hy.le (sub_nonneg.mpr h)
  simp only [thetaModeOffset, Nat.cast_zero, zero_add, one_pow, one_mul]
  rw [scaleT, ← thetaQ_zero_eq_scaleZ]
  nlinarith

/-- The paper's full-tail bound in its natural scale, with an explicit
coefficient-uniform cutoff of forty tail widths. -/
theorem fullTheta_derivative_tail_bound (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a s : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hs : 40 * thetaDerivTailWidth d a ≤ s) :
    (∫ u : ℝ in Ioi (a + s),
      ‖polynomialDerivative P (fun v => (thetaDensity v : ℂ)) u‖ ^ 2) ≤
      (∫ u : ℝ in Ioi a,
        ‖polynomialDerivative P (fun v => (thetaDensity v : ℂ)) u‖ ^ 2) *
      Real.exp (-(scaleT a / 4 * (Real.exp (2 * s) - 1))) := by
  have hs₀ : 0 ≤ s := by have := thetaDerivTailWidth_pos d a; linarith
  have hprod : 40 * ((d : ℝ) + 2) ≤ scaleT a * s := by
    have hmul := mul_nonneg (thetaDeriv_scaleT_pos a).le (sub_nonneg.mpr hs)
    have he := thetaDerivTailWidth_scale d a
    nlinarith
  have hcut := hprod.trans (thetaModeOffset_zero_ge_linear a s)
  have h := (div_le_iff₀ (fullTheta_tail_square_pos d P hP hdegree a ha hsize)).mp
    (fullTheta_derivative_survival d P hP hdegree a s ha hs₀ hsize hcut)
  have he : thetaModeOffset 0 a s / 2 = scaleT a / 4 * (Real.exp (2 * s) - 1) := by
    simp only [thetaModeOffset, Nat.cast_zero, zero_add, one_pow, one_mul,
      scaleT, ← thetaQ_zero_eq_scaleZ]
    ring
  rw [he] at h
  simpa only [mul_comm] using h

theorem fullTheta_derivative_tail_bound_linear (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a s : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hs : 40 * thetaDerivTailWidth d a ≤ s) :
    (∫ u : ℝ in Ioi (a + s),
      ‖polynomialDerivative P (fun v => (thetaDensity v : ℂ)) u‖ ^ 2) ≤
      (∫ u : ℝ in Ioi a,
        ‖polynomialDerivative P (fun v => (thetaDensity v : ℂ)) u‖ ^ 2) *
      Real.exp (-(scaleT a * s / 2)) := by
  apply (fullTheta_derivative_tail_bound d P hP hdegree a s ha hsize hs).trans
  apply mul_le_mul_of_nonneg_left _ (fullTheta_tail_square_pos d P hP hdegree a ha hsize).le
  apply Real.exp_le_exp.mpr
  have h := mul_nonneg (thetaDeriv_scaleT_pos a).le
    (sub_nonneg.mpr (Real.add_one_le_exp (2 * s)))
  nlinarith

theorem polynomialDerivative_thetaDensity_continuous (P : ℂ[X]) :
    Continuous (polynomialDerivative P (fun u => (thetaDensity u : ℂ))) := by
  change Continuous (fun u => ∑ j ∈ P.support,
    P.coeff j * ((differentialOperator^[j]) (fun v => (thetaDensity v : ℂ))) u)
  simp_rw [differentialOperator_iterate]
  apply continuous_finset_sum
  intro j hj
  exact continuous_const.mul (continuous_const.mul
    (RadicalApproximation.thetaDensity_contDiff.continuous_iteratedDeriv j (by simp)))

def thetaDerivOffsetSource (P : ℂ[X]) (a : ℝ) (s : ℝ) : ℂ :=
  polynomialDerivative P (fun u => (thetaDensity u : ℂ)) (a + s)

theorem thetaDerivOffsetSource_continuous (P : ℂ[X]) (a : ℝ) :
    Continuous (thetaDerivOffsetSource P a) :=
  (polynomialDerivative_thetaDensity_continuous P).comp (continuous_const.add continuous_id)

theorem thetaDeriv_integral_const_add_Ioi (g : ℝ → ℝ) (a z : ℝ) :
    (∫ x : ℝ in Ioi z, g (a + x)) = ∫ u : ℝ in Ioi (a + z), g u := by
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioi z)
    measurableSet_Ioi (fun x hx => ((hasDerivAt_id x).const_add a).hasDerivWithinAt)
    (show Set.InjOn (fun x : ℝ => a + x) (Ioi z) from fun x hx y hy hxy =>
      add_left_cancel hxy) g
  simpa only [id_eq, image_const_add_Ioi, abs_one, one_smul] using h.symm

theorem thetaDerivOffsetSource_tail_square (P : ℂ[X]) (a z : ℝ) :
    (∫ s : ℝ in Ioi z, ‖thetaDerivOffsetSource P a s‖ ^ 2) =
      ∫ u : ℝ in Ioi (a + z),
        ‖polynomialDerivative P (fun v => (thetaDensity v : ℂ)) u‖ ^ 2 := by
  exact thetaDeriv_integral_const_add_Ioi
    (fun u => ‖polynomialDerivative P (fun v => (thetaDensity v : ℂ)) u‖ ^ 2) a z

theorem thetaDerivOffsetSource_memLp (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a) :
    MemLp (thetaDerivOffsetSource P a) 2 (volume.restrict (Ioi 0)) := by
  apply (memLp_two_iff_integrable_sq_norm (thetaDerivOffsetSource_continuous P a).aestronglyMeasurable).mpr
  apply Integrable.of_integral_ne_zero
  rw [thetaDerivOffsetSource_tail_square, add_zero]
  exact (fullTheta_tail_square_pos d P hP hdegree a ha hsize).ne'

/-- The ordinary offset-tail inequality consumed by the layer-cake and
weighted-L1 estimates. It is proved for the theta density. -/
theorem thetaDerivOffsetSource_survival (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a s : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hs : 40 * thetaDerivTailWidth d a ≤ s) :
    (∫ u : ℝ in Ioi s, ‖thetaDerivOffsetSource P a u‖ ^ 2) ≤
      (∫ u : ℝ in Ioi 0, ‖thetaDerivOffsetSource P a u‖ ^ 2) * Real.exp (-(scaleT a * s / 2)) := by
  rw [thetaDerivOffsetSource_tail_square, thetaDerivOffsetSource_tail_square, add_zero]
  exact fullTheta_derivative_tail_bound_linear d P hP hdegree a s ha hsize hs

theorem polynomial_comp_neg_X_coeff (P : ℂ[X]) (j : ℕ) :
    (P.comp (-X)).coeff j = P.coeff j * (-1 : ℂ) ^ j := by
  have h := comp_C_mul_X_coeff (p := P) (r := (-1 : ℂ)) (n := j)
  simpa only [map_neg, map_one, neg_one_mul] using h

theorem polynomialDerivative_reflection (P : ℂ[X]) (f : ℝ → ℂ) (u : ℝ) :
    polynomialDerivative P (fun v => f (-v)) u =
      polynomialDerivative (P.comp (-X)) f (-u) := by
  rw [← thetaPolynomialOperator_eq_polynomialDerivative,
    ← thetaPolynomialOperator_eq_polynomialDerivative]
  simp only [thetaPolynomialOperator, thetaD_eq_differentialOperator,
    differentialOperator_iterate, natDegree_comp, natDegree_neg, natDegree_X, mul_one,
    polynomial_comp_neg_X_coeff, iteratedDeriv_comp_neg, Complex.real_smul,
    Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem polynomialDerivative_thetaDensity_reflection (P : ℂ[X]) (u : ℝ) :
    polynomialDerivative P (fun v => (thetaDensity v : ℂ)) (-u) =
      polynomialDerivative (P.comp (-X)) (fun v => (thetaDensity v : ℂ)) u := by
  have h := polynomialDerivative_reflection P (fun v => (thetaDensity v : ℂ)) (-u)
  simpa only [thetaDensity_neg, neg_neg] using h

theorem thetaDeriv_integral_neg_Ioi (g : ℝ → ℝ) (a : ℝ) :
    (∫ u : ℝ in Ioi a, g (-u)) = ∫ u : ℝ in Iio (-a), g u := by
  rw [integral_comp_neg_Ioi, integral_Iic_eq_integral_Iio]

theorem fullTheta_left_tail_square (P : ℂ[X]) (a : ℝ) :
    (∫ u : ℝ in Iio (-a),
      ‖polynomialDerivative P (fun v => (thetaDensity v : ℂ)) u‖ ^ 2) =
      ∫ u : ℝ in Ioi a,
        ‖polynomialDerivative (P.comp (-X)) (fun v => (thetaDensity v : ℂ)) u‖ ^ 2 := by
  rw [← thetaDeriv_integral_neg_Ioi]
  simp_rw [polynomialDerivative_thetaDensity_reflection]

def thetaDerivRightTail (P : ℂ[X]) (a : ℝ) : ℝ → ℂ :=
  (Ioi a).indicator (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))

def thetaDerivLeftTail (P : ℂ[X]) (a : ℝ) : ℝ → ℂ :=
  (Iio (-a)).indicator (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))

theorem thetaDerivRightTail_zero (P : ℂ[X]) (a u : ℝ) (hu : u ≤ a) :
    thetaDerivRightTail P a u = 0 := by
  simp [thetaDerivRightTail, Set.indicator_of_notMem, not_lt.mpr hu]

theorem thetaDerivLeftTail_zero (P : ℂ[X]) (a u : ℝ) (hu : -a ≤ u) :
    thetaDerivLeftTail P a u = 0 := by
  simp [thetaDerivLeftTail, Set.indicator_of_notMem, not_lt.mpr hu]

theorem thetaDerivLeftTail_reflection (P : ℂ[X]) (a u : ℝ) :
    thetaDerivLeftTail P a (-u) = thetaDerivRightTail (P.comp (-X)) a u := by
  by_cases hu : a < u
  · simp [thetaDerivLeftTail, thetaDerivRightTail, hu, neg_lt_neg_iff,
      polynomialDerivative_thetaDensity_reflection]
  · simp [thetaDerivLeftTail, thetaDerivRightTail, hu, neg_lt_neg_iff]

theorem thetaDerivRightTail_square (P : ℂ[X]) (a : ℝ) :
    squaredNorm (thetaDerivRightTail P a) =
      ∫ u : ℝ in Ioi a,
        ‖polynomialDerivative P (fun v => (thetaDensity v : ℂ)) u‖ ^ 2 := by
  unfold squaredNorm
  have he : (fun u => ‖thetaDerivRightTail P a u‖ ^ 2) =
      (Ioi a).indicator (fun u =>
        ‖polynomialDerivative P (fun v => (thetaDensity v : ℂ)) u‖ ^ 2) := by
    funext u
    by_cases hu : u ∈ Ioi a <;> simp [thetaDerivRightTail, hu]
  rw [he, integral_indicator measurableSet_Ioi]

theorem thetaDerivLeftTail_square (P : ℂ[X]) (a : ℝ) :
    squaredNorm (thetaDerivLeftTail P a) =
      ∫ u : ℝ in Iio (-a),
        ‖polynomialDerivative P (fun v => (thetaDensity v : ℂ)) u‖ ^ 2 := by
  unfold squaredNorm
  have he : (fun u => ‖thetaDerivLeftTail P a u‖ ^ 2) =
      (Iio (-a)).indicator (fun u =>
        ‖polynomialDerivative P (fun v => (thetaDensity v : ℂ)) u‖ ^ 2) := by
    funext u
    by_cases hu : u ∈ Iio (-a) <;> simp [thetaDerivLeftTail, hu]
  rw [he, integral_indicator measurableSet_Iio]

theorem thetaDerivLeftTail_square_reflection (P : ℂ[X]) (a : ℝ) :
    squaredNorm (thetaDerivLeftTail P a) = squaredNorm (thetaDerivRightTail (P.comp (-X)) a) := by
  rw [thetaDerivLeftTail_square, thetaDerivRightTail_square, fullTheta_left_tail_square]

theorem thetaDerivRightTail_memLp (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a) :
    MemLp (thetaDerivRightTail P a) 2 volume := by
  exact (memLp_indicator_iff_restrict measurableSet_Ioi).mpr
    (polynomialDerivative_thetaDensity_memLp_tail d P hP hdegree a ha hsize)

theorem thetaDerivLeftTail_memLp (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a) :
    MemLp (thetaDerivLeftTail P a) 2 volume := by
  apply (memLp_indicator_iff_restrict measurableSet_Iio).mpr
  apply (memLp_two_iff_integrable_sq_norm
    (polynomialDerivative_thetaDensity_continuous P).aestronglyMeasurable).mpr
  apply Integrable.of_integral_ne_zero
  rw [fullTheta_left_tail_square]
  exact (fullTheta_tail_square_pos d (P.comp (-X))
    (comp_neg_X_eq_zero_iff.not.mpr hP)
    (by simpa only [natDegree_comp, natDegree_neg, natDegree_X, mul_one] using hdegree)
    a ha hsize).ne'

theorem thetaDerivRightTail_survival (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a s : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hs : 40 * thetaDerivTailWidth d a ≤ s) :
    (∫ u : ℝ in Ioi (a + s), ‖thetaDerivRightTail P a u‖ ^ 2) ≤
      squaredNorm (thetaDerivRightTail P a) *
        Real.exp (-(scaleT a / 4 * (Real.exp (2 * s) - 1))) := by
  have hs0 : 0 ≤ s := (mul_nonneg (by norm_num : (0 : ℝ) ≤ 40)
    (thetaDerivTailWidth_pos d a).le).trans hs
  have he : (∫ u : ℝ in Ioi (a + s), ‖thetaDerivRightTail P a u‖ ^ 2) =
      ∫ u : ℝ in Ioi (a + s),
        ‖polynomialDerivative P (fun v => (thetaDensity v : ℂ)) u‖ ^ 2 := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    have hua : a < u := lt_of_le_of_lt (le_add_of_nonneg_right hs0) hu
    simp [thetaDerivRightTail, hua]
  rw [he, thetaDerivRightTail_square]
  exact fullTheta_derivative_tail_bound d P hP hdegree a s ha hsize hs

theorem thetaDerivLeftTail_survival (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a s : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hs : 40 * thetaDerivTailWidth d a ≤ s) :
    (∫ u : ℝ in Iio (-a - s), ‖thetaDerivLeftTail P a u‖ ^ 2) ≤
      squaredNorm (thetaDerivLeftTail P a) *
        Real.exp (-(scaleT a / 4 * (Real.exp (2 * s) - 1))) := by
  have he : -a - s = -(a + s) := by ring
  rw [he, ← thetaDeriv_integral_neg_Ioi, thetaDerivLeftTail_square_reflection]
  simp_rw [thetaDerivLeftTail_reflection]
  exact thetaDerivRightTail_survival d (P.comp (-X)) (comp_neg_X_eq_zero_iff.not.mpr hP)
    (by simpa only [natDegree_comp, natDegree_neg, natDegree_X, mul_one] using hdegree)
    a s ha hsize hs

end ThetaTrial.Paper
