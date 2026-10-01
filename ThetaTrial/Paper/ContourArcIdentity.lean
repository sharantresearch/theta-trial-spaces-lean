import ThetaTrial.Paper.Definitions
import ThetaTrial.Paper.ContourDeformation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section

open Complex MeasureTheory Set
open scoped Interval

namespace ThetaTrial.Paper.ContourArcIdentity

open ContourDeformation

def arcModeP (n : ℕ) (u : ℂ) : ℂ :=
  4 * (Real.pi : ℂ) ^ 2 * ((n : ℂ) + 1) ^ 4 * Complex.exp (9 * u / 2)

def arcModeQ (n : ℕ) (u : ℂ) : ℂ :=
  6 * (Real.pi : ℂ) * ((n : ℂ) + 1) ^ 2 * Complex.exp (5 * u / 2)

def arcModeA (n : ℕ) (u : ℂ) : ℂ :=
  (Real.pi : ℂ) * ((n : ℂ) + 1) ^ 2 * Complex.exp (2 * u)

/-- Principal powers agree with the exponential powers on this arc, as long
as the argument stays in the principal branch. -/
theorem exp_mul_I_cpow {θ : ℝ} (hlo : -Real.pi < θ) (hhi : θ ≤ Real.pi)
    (s : ℂ) :
    Complex.exp ((θ : ℂ) * I) ^ s = Complex.exp (((θ : ℂ) * I) * s) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _) s,
    Complex.log_exp (by simpa using hlo) (by simpa using hhi)]

theorem phase_weight_identity (Z A : ℂ) (y : ℝ) :
    Complex.exp (-2 * Z * (1 - (Real.cos (2 * y) : ℂ))) *
      Complex.exp (-A * Complex.exp (((2 * y : ℝ) : ℂ) * I)) =
    Complex.exp (-2 * Z) * Complex.exp
      (Z / Complex.exp (((2 * y : ℝ) : ℂ) * I) -
        (A - Z) * Complex.exp (((2 * y : ℝ) : ℂ) * I)) := by
  have hc : Complex.exp (((2 * y : ℝ) : ℂ) * I) +
      (Complex.exp (((2 * y : ℝ) : ℂ) * I))⁻¹ =
      2 * (Real.cos (2 * y) : ℂ) := by
    rw [← Complex.exp_neg]
    simpa only [neg_mul, Complex.ofReal_cos] using
      (Complex.two_cos (((2 * y : ℝ) : ℂ))).symm
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [div_eq_mul_inv]
  linear_combination -Z * hc

theorem weighted_mode_pullback (a : ℝ) (n : ℕ) (u : ℂ) {y : ℝ}
    (hlo : -Real.pi < 2 * y) (hhi : 2 * y ≤ Real.pi) :
    (shiftWeight a y : ℂ) * complexThetaMode n (u + I * (y : ℂ)) =
      Complex.exp (-2 * (scaleZ a : ℂ)) *
        exponentialPullback
          (thetaModeIntegrand (arcModeP n u) (arcModeQ n u)
            (scaleZ a) (arcModeA n u - scaleZ a) (arcModeA n u) 0)
          (((2 * y : ℝ) : ℂ) * I) := by
  have hp9 := exp_mul_I_cpow hlo hhi (9 / 4 : ℂ)
  have hp5 := exp_mul_I_cpow hlo hhi (5 / 4 : ℂ)
  have he9 : Complex.exp (9 * (u + I * (y : ℂ)) / 2) =
      Complex.exp (9 * u / 2) *
        Complex.exp ((((2 * y : ℝ) : ℂ) * I) * (9 / 4 : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have he5 : Complex.exp (5 * (u + I * (y : ℂ)) / 2) =
      Complex.exp (5 * u / 2) *
        Complex.exp ((((2 * y : ℝ) : ℂ) * I) * (5 / 4 : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have he2 : Complex.exp (2 * (u + I * (y : ℂ))) =
      Complex.exp (2 * u) * Complex.exp (((2 * y : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hw : (shiftWeight a y : ℂ) =
      Complex.exp (-2 * (scaleZ a : ℂ) * (1 - (Real.cos (2 * y) : ℂ))) := by
    simp only [shiftWeight, Complex.ofReal_exp, Complex.ofReal_mul,
      Complex.ofReal_neg, Complex.ofReal_ofNat, Complex.ofReal_sub, Complex.ofReal_one]
  rw [hw, complexThetaMode, he9, he5, he2]
  simp only [exponentialPullback, thetaModeIntegrand, mul_zero, zero_mul, sub_zero,
    div_mul_cancel₀ _ (Complex.exp_ne_zero _), hp9, hp5]
  have hphase := phase_weight_identity (scaleZ a : ℂ) (arcModeA n u) y
  unfold arcModeA arcModeP arcModeQ at *
  convert congrArg
    (fun v : ℂ => (4 * (Real.pi : ℂ)^2 * ((n : ℂ)+1)^4 *
      (Complex.exp (9*u/2) * Complex.exp ((((2*y : ℝ) : ℂ)*I)*(9/4 : ℂ))) -
      6 * (Real.pi : ℂ) * ((n : ℂ)+1)^2 *
      (Complex.exp (5*u/2) * Complex.exp ((((2*y : ℝ) : ℂ)*I)*(5/4 : ℂ)))) * v)
    hphase using 1 <;> ring

theorem intervalIntegral_double (H : ℝ → ℂ) (b : ℝ) :
    (∫ y : ℝ in -b..b, H (2 * y)) =
      (1 / 2 : ℂ) * ∫ θ : ℝ in -(2 * b)..(2 * b), H θ := by
  simpa only [mul_neg, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_ofNat, one_div] using
    (intervalIntegral.integral_comp_mul_left H (a := -b) (b := b)
      (c := 2) (by norm_num))

/-- The identity on the original arc, for an arbitrary complex centre. -/
theorem original_arc_identity (a : ℝ) (n : ℕ) (u : ℂ) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : 2 * b < Real.pi) :
    (∫ y : ℝ in -b..b,
      (shiftWeight a y : ℂ) * complexThetaMode n (u + I * (y : ℂ))) =
      Complex.exp (-2 * (scaleZ a : ℂ)) / (2 * I) *
        circularArc
          (thetaModeIntegrand (arcModeP n u) (arcModeQ n u)
            (scaleZ a) (arcModeA n u - scaleZ a) (arcModeA n u) 0)
          0 (2 * b) := by
  let H : ℝ → ℂ := fun θ => exponentialPullback
    (thetaModeIntegrand (arcModeP n u) (arcModeQ n u)
      (scaleZ a) (arcModeA n u - scaleZ a) (arcModeA n u) 0)
    ((θ : ℂ) * I)
  have hi : (∫ y : ℝ in -b..b,
      (shiftWeight a y : ℂ) * complexThetaMode n (u + I * (y : ℂ))) =
      ∫ y : ℝ in -b..b, Complex.exp (-2 * (scaleZ a : ℂ)) * H (2 * y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hy' : -b ≤ y ∧ y ≤ b := by
      simpa only [uIcc_of_le (by linarith : -b ≤ b), mem_Icc] using hy
    exact weighted_mode_pullback a n u (by linarith) (by linarith)
  rw [hi, intervalIntegral.integral_const_mul, intervalIntegral_double]
  simp only [circularArc, Complex.ofReal_zero, zero_add]
  change Complex.exp (-2 * (scaleZ a : ℂ)) * ((1 / 2 : ℂ) *
      (∫ θ : ℝ in -(2 * b)..(2 * b), H θ)) =
    Complex.exp (-2 * (scaleZ a : ℂ)) / (2 * I) *
      (I * ∫ θ : ℝ in -(2 * b)..(2 * b), H θ)
  field_simp

/-- The complex-centre exponent equals the real-centre coefficient times
the exact exponential perturbation. -/
theorem arcModeA_add (n : ℕ) (u h : ℂ) :
    arcModeA n (u + h) = arcModeA n u * Complex.exp (2 * h) := by
  unfold arcModeA
  rw [mul_add, Complex.exp_add]
  ring

theorem integrand_perturbation_identity (p q Z A h : ℂ) :
    thetaModeIntegrand p q Z (A * Complex.exp (2 * h) - Z)
      (A * Complex.exp (2 * h)) 0 =
    thetaModeIntegrand p q Z (A - Z) A (Complex.exp (2 * h) - 1) := by
  funext ζ
  unfold thetaModeIntegrand
  congr 3
  ring

/-- Exact original arc with the paper's perturbation at real centre x. -/
theorem original_arc_identity_perturbed (a x : ℝ) (n : ℕ) (h : ℂ) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : 2 * b < Real.pi) :
    (∫ y : ℝ in -b..b,
      (shiftWeight a y : ℂ) * complexThetaMode n ((x : ℂ) + h + I * (y : ℂ))) =
      Complex.exp (-2 * (scaleZ a : ℂ)) / (2 * I) *
        circularArc
          (thetaModeIntegrand (arcModeP n ((x : ℂ) + h))
            (arcModeQ n ((x : ℂ) + h)) (scaleZ a)
            (arcModeA n x - scaleZ a) (arcModeA n x)
            (Complex.exp (2 * h) - 1)) 0 (2 * b) := by
  rw [original_arc_identity a n ((x : ℂ) + h) hb0 hb, arcModeA_add,
    integrand_perturbation_identity]

theorem arcModeA_real (n : ℕ) (x : ℝ) :
    arcModeA n (x : ℂ) =
      ((Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * x) : ℝ) : ℂ) := by
  simp [arcModeA, Complex.ofReal_exp]

theorem arcModeP_real (n : ℕ) (x : ℝ) (h : ℂ) :
    arcModeP n ((x : ℂ) + h) =
      ((4 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 : ℝ) : ℂ) *
        Complex.exp (((9 / 2 : ℝ) : ℂ) * ((x : ℂ) + h)) := by
  unfold arcModeP
  push_cast
  congr 1
  congr 1
  ring

theorem arcModeQ_real (n : ℕ) (x : ℝ) (h : ℂ) :
    arcModeQ n ((x : ℂ) + h) =
      ((6 * Real.pi * ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) *
        Complex.exp (((5 / 2 : ℝ) : ℂ) * ((x : ℂ) + h)) := by
  unfold arcModeQ
  push_cast
  congr 1
  congr 1
  ring

theorem shiftWidth_arc_bounds {a : ℝ} (ha : 16 ≤ scaleZ a) :
    0 ≤ shiftWidth a ∧ 2 * shiftWidth a < Real.pi / 2 := by
  have hi : (scaleZ a)⁻¹ ≤ (16 : ℝ)⁻¹ := inv_anti₀ (by norm_num) ha
  have hp : 0 < (scaleZ a)⁻¹ := inv_pos.mpr (by linarith)
  norm_num at hi
  unfold shiftWidth
  constructor <;> nlinarith [Real.pi_gt_three]

/-- The paper arc: Z = scaleZ a, b = shiftWidth a,
with the polynomial derivative taken before any later cutoff. -/
theorem shifted_mode_original_arc {a : ℝ} (ha : 16 ≤ scaleZ a)
    (x : ℝ) (n : ℕ) (h : ℂ) :
    (∫ y : ℝ in -shiftWidth a..shiftWidth a,
      (shiftWeight a y : ℂ) * complexThetaMode n ((x : ℂ) + h + I * (y : ℂ))) =
      Complex.exp (-2 * (scaleZ a : ℂ)) / (2 * I) *
        circularArc
          (thetaModeIntegrand (arcModeP n ((x : ℂ) + h))
            (arcModeQ n ((x : ℂ) + h)) (scaleZ a)
            (arcModeA n x - scaleZ a) (arcModeA n x)
            (Complex.exp (2 * h) - 1)) 0 (2 * shiftWidth a) := by
  have hb := shiftWidth_arc_bounds ha
  exact original_arc_identity_perturbed a x n h hb.1 (by linarith [Real.pi_pos])

/-- The same identity for the set integral over the closed interval used in
`shiftedAverage`. -/
theorem shifted_mode_original_arc_Icc {a : ℝ} (ha : 16 ≤ scaleZ a)
    (x : ℝ) (n : ℕ) (h : ℂ) :
    (∫ y : ℝ in Icc (-shiftWidth a) (shiftWidth a),
      (shiftWeight a y : ℂ) * complexThetaMode n ((x : ℂ) + h + I * (y : ℂ))) =
      Complex.exp (-2 * (scaleZ a : ℂ)) / (2 * I) *
        circularArc
          (thetaModeIntegrand (arcModeP n ((x : ℂ) + h))
            (arcModeQ n ((x : ℂ) + h)) (scaleZ a)
            (arcModeA n x - scaleZ a) (arcModeA n x)
            (Complex.exp (2 * h) - 1)) 0 (2 * shiftWidth a) := by
  have hb : -shiftWidth a ≤ shiftWidth a := by
    linarith [(shiftWidth_arc_bounds ha).1]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hb]
  exact shifted_mode_original_arc ha x n h

end ThetaTrial.Paper.ContourArcIdentity
