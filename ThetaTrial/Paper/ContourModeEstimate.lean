import ThetaTrial.Paper.Contour
import ThetaTrial.Paper.ContourDeformation
import ThetaTrial.Paper.ContourArcIdentity
import ThetaTrial.Paper.ShiftedAverageBound
import ThetaTrial.Paper.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.GCongr

/-!
# Single-mode contour estimates

Quantitative bounds for the contour integrals of the individual theta modes.
-/

noncomputable section
open Complex MeasureTheory Set
open scoped Interval

namespace ThetaTrial.Paper.ContourModeEstimate

open ThetaTrial.Paper.Contour ThetaTrial.Paper.ContourDeformation

def modeA (N x : ℝ) : ℝ := Real.pi * N ^ 2 * Real.exp (2 * x)

def modeP (N x : ℝ) (h : ℂ) : ℂ :=
  ((4 * Real.pi ^ 2 * N ^ 4 : ℝ) : ℂ) *
    Complex.exp (((9 / 2 : ℝ) : ℂ) * ((x : ℂ) + h))

def modeQ (N x : ℝ) (h : ℂ) : ℂ :=
  ((6 * Real.pi * N ^ 2 : ℝ) : ℂ) *
    Complex.exp (((5 / 2 : ℝ) : ℂ) * ((x : ℂ) + h))

def modePrefactor (N x : ℝ) (h ζ : ℂ) : ℂ :=
  modeP N x h * ζ ^ ((9 / 4 : ℝ) : ℂ) -
    modeQ N x h * ζ ^ ((5 / 4 : ℝ) : ℂ)

def prefactorConstant : ℝ :=
  (4 * Real.pi ^ 2 + 6 * Real.pi) * Real.exp (9 / 2)

def prefactorEnvelope (N x Z : ℝ) : ℝ :=
  prefactorConstant * N ^ 4 * Real.exp (9 * x / 2) * Z ^ (9 / 4 : ℝ)

def modeIntegrand (N x Z : ℝ) (h : ℂ) : ℂ → ℂ :=
  thetaModeIntegrand (modeP N x h) (modeQ N x h)
    (Z : ℂ) ((modeA N x - Z : ℝ) : ℂ) (modeA N x : ℂ)
    (Complex.exp (2 * h) - 1)

theorem prefactorEnvelope_nonneg (N x : ℝ) {Z : ℝ} (hZ : 0 ≤ Z) :
    0 ≤ prefactorEnvelope N x Z := by
  unfold prefactorEnvelope prefactorConstant
  positivity

/-- Both theta prefactors are controlled by the same fixed
constant, uniformly on the entire deformed contour. -/
theorem modePrefactor_norm_le {N x Z : ℝ} {h ζ : ℂ}
    (hN : 1 ≤ N) (hx : 0 ≤ x) (hZ : 1 ≤ Z)
    (hh : ‖h‖ ≤ 1) (_hζlo : 1 ≤ ‖ζ‖) (hζhi : ‖ζ‖ ≤ Z) :
    ‖modePrefactor N x h ζ‖ ≤ prefactorEnvelope N x Z := by
  have hN0 : 0 ≤ N := by linarith
  have hZ0 : 0 ≤ Z := by linarith
  have hre : h.re ≤ 1 := (Complex.re_le_norm h).trans hh
  have he9 :
      ‖Complex.exp (((9 / 2 : ℝ) : ℂ) * ((x : ℂ) + h))‖ ≤
        Real.exp (9 / 2) * Real.exp (9 * x / 2) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, zero_mul, sub_zero]
    nlinarith
  have he5 :
      ‖Complex.exp (((5 / 2 : ℝ) : ℂ) * ((x : ℂ) + h))‖ ≤
        Real.exp (9 / 2) * Real.exp (9 * x / 2) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, zero_mul, sub_zero]
    nlinarith
  have hp9 : ‖ζ ^ ((9 / 4 : ℝ) : ℂ)‖ ≤ Z ^ (9 / 4 : ℝ) := by
    rw [Complex.norm_cpow_real]
    exact Real.rpow_le_rpow (norm_nonneg ζ) hζhi (by norm_num)
  have hp5 : ‖ζ ^ ((5 / 4 : ℝ) : ℂ)‖ ≤ Z ^ (9 / 4 : ℝ) := by
    rw [Complex.norm_cpow_real]
    exact (Real.rpow_le_rpow (norm_nonneg ζ) hζhi (by norm_num : (0 : ℝ) ≤ 5 / 4)).trans
      (Real.rpow_le_rpow_of_exponent_le hZ (by norm_num))
  have hn2 : N ^ 2 ≤ N ^ 4 := by
    have hs : 1 ≤ N ^ 2 := by nlinarith
    nlinarith [sq_nonneg (N ^ 2 - 1)]
  have hp :
      ‖modeP N x h * ζ ^ ((9 / 4 : ℝ) : ℂ)‖ ≤
        (4 * Real.pi ^ 2 * N ^ 4) *
          (Real.exp (9 / 2) * Real.exp (9 * x / 2)) * Z ^ (9 / 4 : ℝ) := by
    simp only [modeP, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_pow, abs_of_nonneg Real.pi_pos.le, abs_of_nonneg hN0,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    gcongr
  have hq :
      ‖modeQ N x h * ζ ^ ((5 / 4 : ℝ) : ℂ)‖ ≤
        (6 * Real.pi * N ^ 4) *
          (Real.exp (9 / 2) * Real.exp (9 * x / 2)) * Z ^ (9 / 4 : ℝ) := by
    simp only [modeQ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_pow, abs_of_nonneg Real.pi_pos.le, abs_of_nonneg hN0,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
    gcongr
  calc
    ‖modePrefactor N x h ζ‖ ≤
        ‖modeP N x h * ζ ^ ((9 / 4 : ℝ) : ℂ)‖ +
        ‖modeQ N x h * ζ ^ ((5 / 4 : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add hp hq
    _ = prefactorEnvelope N x Z := by unfold prefactorEnvelope prefactorConstant; ring

/-- The pullback includes the factor `1/ζ` and the Jacobian `exp(w)`. -/
theorem mode_pullback (N x Z : ℝ) (h w : ℂ) :
    exponentialPullback (modeIntegrand N x Z h) w =
      modePrefactor N x h (Complex.exp w) *
        Complex.exp (modePhase Z (modeA N x - Z) h (Complex.exp w)) := by
  unfold exponentialPullback modeIntegrand thetaModeIntegrand
  rw [div_mul_cancel₀ _ (Complex.exp_ne_zero w)]
  simp only [modePrefactor, modePhase, sub_add_cancel, Complex.ofReal_div,
    Complex.ofReal_ofNat]

theorem exp_log_polar (s θ : ℝ) :
    Complex.exp ((s : ℂ) + (θ : ℂ) * Complex.I) =
      sectorPoint (Real.exp s) θ := by
  simp only [Complex.exp_add, sectorPoint, Complex.ofReal_exp]

def contourEnvelope (N x Z : ℝ) : ℝ :=
  prefactorEnvelope N x Z * Real.exp (7 - modeA N x / Z)

theorem contourEnvelope_nonneg (N x : ℝ) {Z : ℝ} (hZ : 0 ≤ Z) :
    0 ≤ contourEnvelope N x Z :=
  mul_nonneg (prefactorEnvelope_nonneg N x hZ) (Real.exp_nonneg _)

theorem shiftBoundary_bounds {Z : ℝ} (hZ : 16 ≤ Z) :
    0 < shiftBoundary Z ∧ 2 * shiftBoundary Z < Real.pi / 2 := by
  have hZpos : 0 < Z := by linarith
  have hi : 0 < 1 / Z := by positivity
  have himax : 1 / Z ≤ 1 / 16 :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 16) hZ
  unfold shiftBoundary
  constructor <;> nlinarith [Real.pi_gt_three]

/-- A proved bound on the logarithmically parameterized radial integrand. -/
theorem ray_pullback_norm_le {N x Z s θ : ℝ} {h : ℂ}
    (hZ : 16 ≤ Z) (hN : 1 ≤ N) (hx : 0 ≤ x)
    (hA : Z ≤ modeA N x) (hh : ‖h‖ ≤ discRadius Z)
    (hs : s ∈ Icc 0 (Real.log Z)) (hθ : |θ| = 2 * shiftBoundary Z) :
    ‖exponentialPullback (modeIntegrand N x Z h)
        ((s : ℂ) + (θ : ℂ) * Complex.I)‖ ≤ contourEnvelope N x Z := by
  have hZpos : 0 < Z := by linarith
  have hρlo : 1 ≤ Real.exp s := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hs.1
  have hρhi : Real.exp s ≤ Z := by
    simpa only [Real.exp_log hZpos] using Real.exp_le_exp.mpr hs.2
  have hnorm := sectorPoint_norm (Real.exp_nonneg s) θ
  have hp := modePrefactor_norm_le hN hx (by linarith : 1 ≤ Z)
    (hh.trans ((discRadius_bounds hZ).2.1.trans (by norm_num : (1 / 4 : ℝ) ≤ 1)))
    (hnorm.symm ▸ hρlo) (hnorm.symm ▸ hρhi)
  have he := mode_ray_exp_norm_le hZ hA hρlo hρhi hθ hh
  rw [mode_pullback, exp_log_polar, norm_mul]
  exact mul_le_mul hp he (norm_nonneg _) (prefactorEnvelope_nonneg N x hZpos.le)

/-- The full outer-arc integrand has the same bound; the sharper phase
constant 6 is enlarged to 7 only at this final comparison. -/
theorem arc_pullback_norm_le {N x Z θ : ℝ} {h : ℂ}
    (hZ : 16 ≤ Z) (hN : 1 ≤ N) (hx : 0 ≤ x)
    (hA : Z ≤ modeA N x) (hh : ‖h‖ ≤ discRadius Z)
    (hθ : |θ| ≤ 2 * shiftBoundary Z) :
    ‖exponentialPullback (modeIntegrand N x Z h)
        ((Real.log Z : ℝ) + (θ : ℂ) * Complex.I)‖ ≤ contourEnvelope N x Z := by
  have hZpos : 0 < Z := by linarith
  have hnorm := sectorPoint_norm hZpos.le θ
  have hp := modePrefactor_norm_le hN hx (by linarith : 1 ≤ Z)
    (hh.trans ((discRadius_bounds hZ).2.1.trans (by norm_num : (1 / 4 : ℝ) ≤ 1)))
    (by rw [hnorm]; linarith) (by rw [hnorm])
  have he := (mode_arc_exp_norm_le hZ hA hθ hh).trans
    (Real.exp_le_exp.mpr (by linarith : 6 - modeA N x / Z ≤ 7 - modeA N x / Z))
  rw [mode_pullback, exp_log_polar, Real.exp_log hZpos, norm_mul]
  exact mul_le_mul hp he (norm_nonneg _) (prefactorEnvelope_nonneg N x hZpos.le)

/-- The lower or upper ray integral is bounded using the proved
pointwise estimate and the parameter length log Z. -/
theorem radial_integral_norm_le {N x Z θ : ℝ} {h : ℂ}
    (hZ : 16 ≤ Z) (hN : 1 ≤ N) (hx : 0 ≤ x)
    (hA : Z ≤ modeA N x) (hh : ‖h‖ ≤ discRadius Z)
    (hθ : |θ| = 2 * shiftBoundary Z) :
    ‖∫ s : ℝ in 0..Real.log Z,
        exponentialPullback (modeIntegrand N x Z h)
          ((s : ℂ) + (θ : ℂ) * Complex.I)‖ ≤
      contourEnvelope N x Z * Real.log Z := by
  have hlog : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun s hs => ray_pullback_norm_le hZ hN hx hA hh
      (uIcc_of_le hlog ▸ (uIoc_subset_uIcc hs)) hθ)
  simpa only [sub_zero, abs_of_nonneg hlog] using hbound

/-- The outer arc integral is bounded, including its factor i. -/
theorem outer_arc_norm_le {N x Z : ℝ} {h : ℂ}
    (hZ : 16 ≤ Z) (hN : 1 ≤ N) (hx : 0 ≤ x)
    (hA : Z ≤ modeA N x) (hh : ‖h‖ ≤ discRadius Z) :
    ‖circularArc (modeIntegrand N x Z h) (Real.log Z) (2 * shiftBoundary Z)‖ ≤
      contourEnvelope N x Z * (4 * shiftBoundary Z) := by
  have hb : 0 < shiftBoundary Z := (shiftBoundary_bounds hZ).1
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun θ : ℝ => exponentialPullback (modeIntegrand N x Z h)
      ((Real.log Z : ℝ) + (θ : ℂ) * Complex.I))
    (a := -(2 * shiftBoundary Z)) (b := 2 * shiftBoundary Z)
    (C := contourEnvelope N x Z) (by
      intro θ hθ
      have hmem := uIoc_subset_uIcc hθ
      rw [uIcc_of_le (by linarith : -(2 * shiftBoundary Z) ≤ 2 * shiftBoundary Z)] at hmem
      exact arc_pullback_norm_le hZ hN hx hA hh (abs_le.mpr hmem))
  simpa only [circularArc, norm_mul, Complex.norm_I, one_mul,
    sub_neg_eq_add, ← two_mul, show 2 * (2 * shiftBoundary Z) = 4 * shiftBoundary Z by ring,
    abs_of_pos (by positivity : 0 < 4 * shiftBoundary Z)] using hbound

/-- Bound on the deformed contour: both rays and the outer arc. -/
theorem inner_arc_norm_le {N x Z : ℝ} {h : ℂ}
    (hZ : 16 ≤ Z) (hN : 1 ≤ N) (hx : 0 ≤ x)
    (hA : Z ≤ modeA N x) (hh : ‖h‖ ≤ discRadius Z) :
    ‖circularArc (modeIntegrand N x Z h) 0 (2 * shiftBoundary Z)‖ ≤
      (2 + Real.pi) * Z * contourEnvelope N x Z := by
  have hb := shiftBoundary_bounds hZ
  have hlog : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
  have hlo := radial_integral_norm_le hZ hN hx hA hh
    (θ := -(2 * shiftBoundary Z))
    (by rw [abs_neg, abs_of_pos (mul_pos (by norm_num) hb.1)])
  have hup := radial_integral_norm_le hZ hN hx hA hh
    (θ := 2 * shiftBoundary Z) (abs_of_pos (mul_pos (by norm_num) hb.1))
  have hout := outer_arc_norm_le hZ hN hx hA hh
  have heq := thetaMode_annular_sector_deformation
    (modeP N x h) (modeQ N x h) (Z : ℂ)
    ((modeA N x - Z : ℝ) : ℂ) (modeA N x : ℂ) (Complex.exp (2 * h) - 1)
    (Real.log Z) (β := 2 * shiftBoundary Z) (by linarith) hb.2
  change circularArc (modeIntegrand N x Z h) 0 (2 * shiftBoundary Z) =
    lowerRay (modeIntegrand N x Z h) (Real.log Z) (2 * shiftBoundary Z) +
    circularArc (modeIntegrand N x Z h) (Real.log Z) (2 * shiftBoundary Z) -
    upperRay (modeIntegrand N x Z h) (Real.log Z) (2 * shiftBoundary Z) at heq
  have hlower : ‖lowerRay (modeIntegrand N x Z h) (Real.log Z)
      (2 * shiftBoundary Z)‖ ≤ contourEnvelope N x Z * Real.log Z := hlo
  have hupper : ‖upperRay (modeIntegrand N x Z h) (Real.log Z)
      (2 * shiftBoundary Z)‖ ≤ contourEnvelope N x Z * Real.log Z := hup
  have hlength : 2 * Real.log Z + 4 * shiftBoundary Z ≤ (2 + Real.pi) * Z := by
    have hlogmax := Real.log_le_self (show 0 ≤ Z by linarith)
    nlinarith [Real.pi_pos]
  have henv := contourEnvelope_nonneg N x (show 0 ≤ Z by linarith)
  rw [heq]
  calc
    ‖lowerRay (modeIntegrand N x Z h) (Real.log Z) (2 * shiftBoundary Z) +
        circularArc (modeIntegrand N x Z h) (Real.log Z) (2 * shiftBoundary Z) -
        upperRay (modeIntegrand N x Z h) (Real.log Z) (2 * shiftBoundary Z)‖ ≤
      ‖lowerRay (modeIntegrand N x Z h) (Real.log Z) (2 * shiftBoundary Z)‖ +
        ‖circularArc (modeIntegrand N x Z h) (Real.log Z) (2 * shiftBoundary Z)‖ +
        ‖upperRay (modeIntegrand N x Z h) (Real.log Z) (2 * shiftBoundary Z)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ contourEnvelope N x Z * (2 * Real.log Z + 4 * shiftBoundary Z) := by
      nlinarith [hlower, hout, hupper]
    _ ≤ contourEnvelope N x Z * ((2 + Real.pi) * Z) :=
      mul_le_mul_of_nonneg_left hlength henv
    _ = _ := by ring

def modeEstimateConstant : ℝ :=
  (2 + Real.pi) / 2 * prefactorConstant * Real.exp 7

def weightedContourMode (N x Z : ℝ) (h : ℂ) : ℂ :=
  ((Real.exp (-2 * Z) : ℝ) : ℂ) / (2 * Complex.I) *
    circularArc (modeIntegrand N x Z h) 0 (2 * shiftBoundary Z)

/-- The single-mode contour estimate, with the exact polynomial
power Z^(13/4) needed for the paper's constant 34. -/
theorem weightedContourMode_norm_le {N x Z : ℝ} {h : ℂ}
    (hZ : 16 ≤ Z) (hN : 1 ≤ N) (hx : 0 ≤ x)
    (hA : Z ≤ modeA N x) (hh : ‖h‖ ≤ discRadius Z) :
    ‖weightedContourMode N x Z h‖ ≤
      modeEstimateConstant * N ^ 4 * Real.exp (9 * x / 2) * Z ^ (13 / 4 : ℝ) *
        Real.exp (-2 * Z - modeA N x / Z) := by
  have hZpos : 0 < Z := by linarith
  have hp := inner_arc_norm_le hZ hN hx hA hh
  have hnorm :
      ‖((Real.exp (-2 * Z) : ℝ) : ℂ) / (2 * Complex.I)‖ =
        Real.exp (-2 * Z) / 2 := by
    simp only [norm_div, norm_mul, Complex.norm_two, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hpow : Z ^ (13 / 4 : ℝ) = Z * Z ^ (9 / 4 : ℝ) := by
    rw [show (13 / 4 : ℝ) = 1 + 9 / 4 by norm_num, Real.rpow_add hZpos, Real.rpow_one]
  have he :
      Real.exp (-2 * Z) * Real.exp (7 - modeA N x / Z) =
        Real.exp 7 * Real.exp (-2 * Z - modeA N x / Z) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  unfold weightedContourMode
  rw [norm_mul, hnorm]
  calc
    Real.exp (-2 * Z) / 2 *
        ‖circularArc (modeIntegrand N x Z h) 0 (2 * shiftBoundary Z)‖ ≤
      Real.exp (-2 * Z) / 2 * ((2 + Real.pi) * Z * contourEnvelope N x Z) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (2 + Real.pi) / 2 * prefactorConstant * N ^ 4 * Real.exp (9 * x / 2) *
        (Z * Z ^ (9 / 4 : ℝ)) *
        (Real.exp (-2 * Z) * Real.exp (7 - modeA N x / Z)) := by
      unfold contourEnvelope prefactorEnvelope
      ring
    _ = _ := by rw [he, hpow]; unfold modeEstimateConstant; ring

/-- The quantitative contour integral is exactly the shifted
theta mode from Definitions, including its original measure and weight. -/
theorem shifted_mode_eq_weightedContourMode {a : ℝ} (ha : 16 ≤ scaleZ a)
    (x : ℝ) (n : ℕ) (h : ℂ) :
    (∫ y : ℝ in Icc (-shiftWidth a) (shiftWidth a),
      (shiftWeight a y : ℂ) * complexThetaMode n ((x : ℂ) + h + I * (y : ℂ))) =
        weightedContourMode ((n : ℝ) + 1) x (scaleZ a) h := by
  have hid := ContourArcIdentity.shifted_mode_original_arc_Icc ha x n h
  rw [ContourArcIdentity.arcModeP_real, ContourArcIdentity.arcModeQ_real,
    ContourArcIdentity.arcModeA_real] at hid
  simpa only [weightedContourMode, modeIntegrand, modeP, modeQ, modeA,
    shiftBoundary, shiftWidth, one_div, Complex.ofReal_exp, Complex.ofReal_neg,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_sub] using hid

/-- The hypothesis `A ≥ Z` holds for every positive theta mode when `x ≥ a`. -/
theorem modeA_ge_scaleZ (n : ℕ) {a x : ℝ} (hax : a ≤ x) :
    scaleZ a ≤ modeA ((n : ℝ) + 1) x := by
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hn2 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have he : Real.exp (2 * a) ≤ Real.exp (2 * x) :=
    Real.exp_le_exp.mpr (by linarith)
  unfold scaleZ modeA
  calc
    Real.pi * Real.exp (2 * a) ≤ Real.pi * Real.exp (2 * x) :=
      mul_le_mul_of_nonneg_left he Real.pi_pos.le
    _ ≤ Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * x) := by
      have hm := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hn2 Real.pi_pos.le) (Real.exp_nonneg (2 * x))
      simpa only [mul_one] using hm

theorem modeA_div_scaleZ (N a x : ℝ) :
    modeA N x / scaleZ a = N ^ 2 * Real.exp (2 * (x - a)) := by
  unfold modeA scaleZ
  rw [show 2 * (x - a) = 2 * x - 2 * a by ring, Real.exp_sub]
  field_simp [Real.pi_ne_zero, Real.exp_ne_zero]

/-- Uniform single-mode bound on the whole Cauchy disc. -/
theorem shifted_single_mode_norm_le {a x : ℝ} (ha0 : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (hax : a ≤ x) (n : ℕ) {h : ℂ}
    (hh : ‖h‖ ≤ discRadius (scaleZ a)) :
    ‖∫ y : ℝ in Icc (-shiftWidth a) (shiftWidth a),
        (shiftWeight a y : ℂ) * complexThetaMode n ((x : ℂ) + h + I * (y : ℂ))‖ ≤
      modeEstimateConstant * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * x / 2) *
        (scaleZ a) ^ (13 / 4 : ℝ) *
        Real.exp (-2 * scaleZ a - ((n : ℝ) + 1) ^ 2 * Real.exp (2 * (x - a))) := by
  rw [shifted_mode_eq_weightedContourMode hZ x n h]
  have hb := weightedContourMode_norm_le hZ
    (show (1 : ℝ) ≤ (n : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) n])
    (ha0.trans hax) (modeA_ge_scaleZ n hax) hh
  simpa only [modeA_div_scaleZ] using hb

def gaussianModes (v : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ 4 * Real.exp (-v * ((n : ℝ) + 1) ^ 2)

theorem gaussianModes_summable {v : ℝ} (hv : 1 ≤ v) :
    Summable (gaussianModes v) := by
  unfold gaussianModes
  have hbase := Real.summable_pow_mul_exp_neg_nat_mul 4
    (show 0 < v by linarith)
  have hall : Summable (fun n : ℕ => (n : ℝ) ^ 4 * Real.exp (-v * (n : ℝ) ^ 2)) := by
    apply hbase.of_nonneg_of_le (fun _ => by positivity)
    intro n
    have hnsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      by_cases hn : n = 0
      · simp [hn]
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sub_nonneg.mpr hn1)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (show 0 ≤ v by linarith) (sub_nonneg.mpr hnsq)]
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).2 hall

theorem gaussianModes_sum_le {v : ℝ} (hv : 1 ≤ v) :
    (∑' n : ℕ, gaussianModes v n) ≤ Real.exp (-v) * modeConstant := by
  have hs := gaussianModes_summable hv
  unfold gaussianModes at hs
  have hall : Summable (fun n : ℕ => (n : ℝ) ^ 4 * Real.exp (-v * (n : ℝ) ^ 2)) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.cast_add, Nat.cast_one] using hs
  have heq := hall.tsum_eq_zero_add
  have heq' : (∑' n : ℕ, (n : ℝ) ^ 4 * Real.exp (-v * (n : ℝ) ^ 2)) =
      ∑' n : ℕ, gaussianModes v n := by
    simpa [gaussianModes] using heq
  rw [← heq']
  exact mode_sum_le hv

def singleModeIntegral (a x : ℝ) (h : ℂ) (n : ℕ) : ℂ :=
  ∫ y : ℝ in Icc (-shiftWidth a) (shiftWidth a),
    (shiftWeight a y : ℂ) * complexThetaMode n ((x : ℂ) + h + I * (y : ℂ))

def modeScaleEnvelope (a x : ℝ) : ℝ :=
  modeEstimateConstant * Real.exp (9 * x / 2) * (scaleZ a) ^ (13 / 4 : ℝ) *
    Real.exp (-2 * scaleZ a)

theorem modeScaleEnvelope_nonneg (a x : ℝ) : 0 ≤ modeScaleEnvelope a x := by
  unfold modeScaleEnvelope modeEstimateConstant prefactorConstant scaleZ
  positivity

theorem singleModeIntegral_norm_le {a x : ℝ} (ha0 : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (hax : a ≤ x) (n : ℕ) {h : ℂ}
    (hh : ‖h‖ ≤ discRadius (scaleZ a)) :
    ‖singleModeIntegral a x h n‖ ≤
      modeScaleEnvelope a x * gaussianModes (Real.exp (2 * (x - a))) n := by
  have hm := shifted_single_mode_norm_le ha0 hZ hax n hh
  change ‖singleModeIntegral a x h n‖ ≤ _ at hm
  refine hm.trans_eq ?_
  unfold modeScaleEnvelope gaussianModes
  rw [show -2 * scaleZ a - ((n : ℝ) + 1) ^ 2 * Real.exp (2 * (x - a)) =
    -2 * scaleZ a + (-Real.exp (2 * (x - a)) * ((n : ℝ) + 1) ^ 2) by ring,
    Real.exp_add]
  ring

/-- The mode integrals are summable, by the single-mode estimate. -/
theorem singleModeIntegral_summable {a x : ℝ} (ha0 : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (hax : a ≤ x) {h : ℂ}
    (hh : ‖h‖ ≤ discRadius (scaleZ a)) :
    Summable (singleModeIntegral a x h) := by
  have hv : 1 ≤ Real.exp (2 * (x - a)) := by
    simpa only [Real.exp_zero] using
      Real.exp_le_exp.mpr (show 0 ≤ 2 * (x - a) by linarith)
  exact ((gaussianModes_summable hv).mul_left (modeScaleEnvelope a x)).of_norm_bounded
    (fun n => singleModeIntegral_norm_le ha0 hZ hax n hh)

/-- Summing over all modes gives the double-exponential factor and the power
`Z^(13/4)` used in the paper. -/
theorem summed_shifted_modes_norm_le {a x : ℝ} (ha0 : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (hax : a ≤ x) {h : ℂ}
    (hh : ‖h‖ ≤ discRadius (scaleZ a)) :
    ‖∑' n : ℕ, singleModeIntegral a x h n‖ ≤
      (modeEstimateConstant * modeConstant) * Real.exp (9 * x / 2) *
        (scaleZ a) ^ (13 / 4 : ℝ) *
        Real.exp (-2 * scaleZ a - Real.exp (2 * (x - a))) := by
  have hv : 1 ≤ Real.exp (2 * (x - a)) := by
    simpa only [Real.exp_zero] using
      Real.exp_le_exp.mpr (show 0 ≤ 2 * (x - a) by linarith)
  have hmajor := (gaussianModes_summable hv).mul_left (modeScaleEnvelope a x)
  have hnorm := tsum_of_norm_bounded hmajor.hasSum
    (fun n => singleModeIntegral_norm_le ha0 hZ hax n hh)
  simp only [tsum_mul_left] at hnorm
  have hsum := mul_le_mul_of_nonneg_left (gaussianModes_sum_le hv)
    (modeScaleEnvelope_nonneg a x)
  refine (hnorm.trans hsum).trans_eq ?_
  unfold modeScaleEnvelope
  rw [show -2 * scaleZ a - Real.exp (2 * (x - a)) =
    -2 * scaleZ a + -Real.exp (2 * (x - a)) by ring, Real.exp_add]
  ring

/-- The theta average satisfies the full-disc bound.
All mode integrals, their summation, and integral–series interchange
are established by the preceding theorems. -/
theorem shiftedAverage_norm_le_disc {a x : ℝ} (ha0 : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (hax : a ≤ x) {h : ℂ}
    (hh : ‖h‖ ≤ discRadius (scaleZ a)) :
    ‖shiftedAverage a ((x : ℂ) + h)‖ ≤
      (modeEstimateConstant * modeConstant) * Real.exp (9 * x / 2) *
        (scaleZ a) ^ (13 / 4 : ℝ) *
        Real.exp (-2 * scaleZ a - Real.exp (2 * (x - a))) := by
  rw [shiftedAverage_eq_tsum_modes_disc hZ x hh]
  exact summed_shifted_modes_norm_le ha0 hZ hax hh

end ThetaTrial.Paper.ContourModeEstimate
