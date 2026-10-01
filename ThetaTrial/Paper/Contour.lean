import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Phase estimates for the contour argument

The complex phase inequalities in the proof of Lemma `avg:contour`, with
the constants 7 and 6 used in the paper, together with the Gaussian bound for
the sum over modes and the Cauchy estimates for derivatives. The contour
deformation itself is in `ContourDeformation`.
-/

noncomputable section

open Complex Metric Set

namespace ThetaTrial.Paper.Contour

/-- The exact mode phase, with κ = A - Z defined at the real centre. -/
def modePhase (Z κ : ℝ) (h ζ : ℂ) : ℂ :=
  (Z : ℂ) / ζ - (κ : ℂ) * ζ -
    ((κ + Z : ℝ) : ℂ) * (Complex.exp (2 * h) - 1) * ζ

/-- The small-disc exponential perturbation has coefficient 3, not 4. -/
theorem exp_two_sub_one_le {r : ℝ} {h : ℂ}
    (_hr : 0 ≤ r) (hrmax : r ≤ 1 / 4) (hh : ‖h‖ ≤ r) :
    ‖Complex.exp (2 * h) - 1‖ ≤ 3 * r := by
  have ht : ‖(2 : ℂ) * h‖ ≤ 2 * r := by
    simpa only [norm_mul, Complex.norm_two] using mul_le_mul_of_nonneg_left hh
      (by norm_num : (0 : ℝ) ≤ 2)
  have ht1 : ‖(2 : ℂ) * h‖ ≤ 1 := by linarith
  have he := Complex.norm_exp_sub_one_sub_id_le ht1
  have htri : ‖Complex.exp (2 * h) - 1‖ ≤
      ‖Complex.exp (2 * h) - 1 - 2 * h‖ + ‖(2 : ℂ) * h‖ := by
    calc
      ‖Complex.exp (2 * h) - 1‖ =
          ‖(Complex.exp (2 * h) - 1 - 2 * h) + 2 * h‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  have ht0 := norm_nonneg ((2 : ℂ) * h)
  have hsq := mul_le_mul_of_nonneg_left (show ‖(2 : ℂ) * h‖ ≤ 1 / 2 by linarith) ht0
  nlinarith

/-- Splitting A = κ + Z keeps the perturbation constant uniform
on both radial segments and the outer arc. -/
theorem perturbation_le {Z κ r ρ : ℝ} {h ζ : ℂ}
    (hZ : 0 ≤ Z) (hκ : 0 ≤ κ) (hr : 0 ≤ r) (hρ : 0 ≤ ρ)
    (hρZ : ρ ≤ Z) (hrZ : r * Z ^ 2 ≤ 1)
    (hζ : ‖ζ‖ = ρ) (he : ‖Complex.exp (2 * h) - 1‖ ≤ 3 * r) :
    ‖((κ + Z : ℝ) : ℂ) * (Complex.exp (2 * h) - 1) * ζ‖ ≤
      3 * r * κ * ρ + 3 := by
  have hA : 0 ≤ κ + Z := add_nonneg hκ hZ
  have hρterm : r * Z * ρ ≤ 1 := by
    calc
      r * Z * ρ ≤ r * Z * Z := mul_le_mul_of_nonneg_left hρZ (mul_nonneg hr hZ)
      _ = r * Z ^ 2 := by ring
      _ ≤ 1 := hrZ
  calc
    ‖((κ + Z : ℝ) : ℂ) * (Complex.exp (2 * h) - 1) * ζ‖ =
        (κ + Z) * ‖Complex.exp (2 * h) - 1‖ * ρ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA, hζ]
    _ ≤ (κ + Z) * (3 * r) * ρ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hA) hρ
    _ ≤ 3 * r * κ * ρ + 3 := by nlinarith

/-- Real part of the unperturbed phase at a point with prescribed
radius and angular cosine. -/
theorem unperturbed_re {Z κ ρ q : ℝ} {ζ : ℂ}
    (hρ : 0 < ρ) (hζnorm : ‖ζ‖ = ρ) (hζre : ζ.re = ρ * q) :
    ((Z : ℂ) / ζ - (κ : ℂ) * ζ).re =
      Z * q / ρ - κ * ρ * q := by
  simp only [Complex.sub_re, Complex.div_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, zero_div, add_zero, Complex.mul_re, sub_zero,
    Complex.normSq_eq_norm_sq, hζnorm, hζre]
  field_simp

/-- The complex perturbation is estimated through its norm. -/
theorem modePhase_re_le {Z κ r ρ q : ℝ} {h ζ : ℂ}
    (hZ : 0 ≤ Z) (hκ : 0 ≤ κ) (hr : 0 ≤ r) (hρ : 0 < ρ)
    (hρZ : ρ ≤ Z) (hrZ : r * Z ^ 2 ≤ 1)
    (hζnorm : ‖ζ‖ = ρ) (hζre : ζ.re = ρ * q)
    (he : ‖Complex.exp (2 * h) - 1‖ ≤ 3 * r) :
    (modePhase Z κ h ζ).re ≤
      Z * q / ρ - κ * ρ * q + 3 * r * κ * ρ + 3 := by
  have hp := perturbation_le hZ hκ hr hρ.le hρZ hrZ hζnorm he
  have hn := Complex.re_le_norm
    (-(((κ + Z : ℝ) : ℂ) * (Complex.exp (2 * h) - 1) * ζ))
  rw [Complex.neg_re, norm_neg] at hn
  have hb := unperturbed_re (Z := Z) (κ := κ) hρ hζnorm hζre
  unfold modePhase
  rw [Complex.sub_re, hb]
  linarith

/-- Uniform radial-segment phase estimate with the paper constant 7. -/
theorem ray_phase_le {Z κ r ρ c : ℝ} {h ζ : ℂ}
    (hZ : 1 ≤ Z) (hκ : 0 ≤ κ) (hr : 0 ≤ r)
    (hρ : 1 ≤ ρ) (hρZ : ρ ≤ Z)
    (hc : 0 ≤ c) (hcZ : c * Z ≤ 2) (hrc : 3 * r ≤ c)
    (hrZ : r * Z ^ 2 ≤ 1)
    (hζnorm : ‖ζ‖ = ρ) (hζre : ζ.re = ρ * c)
    (he : ‖Complex.exp (2 * h) - 1‖ ≤ 3 * r) :
    (modePhase Z κ h ζ).re ≤ 7 - (c - 3 * r) * (κ + Z) := by
  have hZ0 : 0 ≤ Z := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hphase := modePhase_re_le hZ0 hκ hr hρ0 hρZ hrZ hζnorm hζre he
  have hdiv : Z * c / ρ ≤ Z * c :=
    div_le_self (mul_nonneg hZ0 hc) hρ
  have hcoeff : 0 ≤ c - 3 * r := sub_nonneg.mpr hrc
  have hrad : (c - 3 * r) * κ ≤ (c - 3 * r) * κ * ρ := by
    simpa using mul_le_mul_of_nonneg_left hρ (mul_nonneg hcoeff hκ)
  have hrZ0 : 0 ≤ r * Z := mul_nonneg hr hZ0
  nlinarith

/-- Uniform outer-arc phase estimate with the paper constant 6. -/
theorem arc_phase_le {Z κ r c q : ℝ} {h ζ : ℂ}
    (hZ : 1 ≤ Z) (hκ : 0 ≤ κ) (hr : 0 ≤ r)
    (hcZ : c * Z ≤ 2) (hrc : 3 * r ≤ c)
    (hcq : c ≤ q) (hq : q ≤ 1) (hrZ : r * Z ^ 2 ≤ 1)
    (hζnorm : ‖ζ‖ = Z) (hζre : ζ.re = Z * q)
    (he : ‖Complex.exp (2 * h) - 1‖ ≤ 3 * r) :
    (modePhase Z κ h ζ).re ≤ 6 - (c - 3 * r) * (κ + Z) := by
  have hZpos : 0 < Z := by linarith
  have hphase := modePhase_re_le hZpos.le hκ hr hZpos le_rfl hrZ hζnorm hζre he
  have hdiv : Z * q / Z = q := by field_simp
  rw [hdiv] at hphase
  have hcoeff : 0 ≤ c - 3 * r := sub_nonneg.mpr hrc
  have hangular : κ * Z * c ≤ κ * Z * q :=
    mul_le_mul_of_nonneg_left hcq (mul_nonneg hκ hZpos.le)
  have hrad : (c - 3 * r) * κ ≤ (c - 3 * r) * κ * Z := by
    simpa using mul_le_mul_of_nonneg_left hZ (mul_nonneg hcoeff hκ)
  have hrZ0 : 0 ≤ r * Z := mul_nonneg hr hZpos.le
  nlinarith

/-- Radius used for the Cauchy disc. -/
def discRadius (Z : ℝ) : ℝ := (Z ^ 2)⁻¹

/-- Endpoint of the imaginary shift interval. -/
def shiftBoundary (Z : ℝ) : ℝ := Real.pi / 4 - 1 / Z

/-- Minimum angular cosine on the sector. -/
def angularFloor (Z : ℝ) : ℝ := Real.sin (2 / Z)

theorem cos_twice_shiftBoundary (Z : ℝ) :
    Real.cos (2 * shiftBoundary Z) = angularFloor Z := by
  unfold shiftBoundary angularFloor
  rw [show 2 * (Real.pi / 4 - 1 / Z) = Real.pi / 2 - 2 / Z by ring]
  exact Real.cos_pi_div_two_sub _

/-- Both uniform angular bounds are proved for the sine. -/
theorem angularFloor_bounds {Z : ℝ} (hZ : 16 ≤ Z) :
    3 / 2 ≤ angularFloor Z * Z ∧ angularFloor Z * Z ≤ 2 := by
  have hZpos : 0 < Z := by linarith
  have ht0 : 0 ≤ 2 / Z := by positivity
  have ht1 : 2 / Z ≤ 1 := (div_le_iff₀ hZpos).mpr (by linarith)
  have htZ : (2 / Z) * Z = 2 := by field_simp
  have ht2 : (2 / Z) ^ 2 ≤ 1 := by nlinarith
  have ht3 : (2 / Z) ^ 3 ≤ 2 / Z := by
    have hm := mul_le_mul_of_nonneg_right ht2 ht0
    nlinarith
  have hlo := Real.sin_ge_sub_cube ht0
  have hsinlo : 3 / 4 * (2 / Z) ≤ Real.sin (2 / Z) := by nlinarith
  have hsinu := Real.sin_le ht0
  have hmlo := mul_le_mul_of_nonneg_right hsinlo hZpos.le
  have hmup := mul_le_mul_of_nonneg_right hsinu hZpos.le
  unfold angularFloor
  constructor <;> nlinarith

theorem discRadius_bounds {Z : ℝ} (hZ : 16 ≤ Z) :
    0 < discRadius Z ∧ discRadius Z ≤ 1 / 4 ∧
      discRadius Z * Z ^ 2 = 1 := by
  have hZpos : 0 < Z := by linarith
  have hsqpos : 0 < Z ^ 2 := sq_pos_of_pos hZpos
  have hr : 0 < discRadius Z := inv_pos.mpr hsqpos
  have heq : discRadius Z * Z ^ 2 = 1 := inv_mul_cancel₀ (ne_of_gt hsqpos)
  have hsquare : 4 ≤ Z ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsquare hr.le
  exact ⟨hr, by nlinarith, heq⟩

/-- The effective angular decay remains at least one after multiplying
by Z, with the radius and the angular floor. -/
theorem effective_floor {Z : ℝ} (hZ : 16 ≤ Z) :
    1 ≤ (angularFloor Z - 3 * discRadius Z) * Z := by
  obtain ⟨hc, _⟩ := angularFloor_bounds hZ
  obtain ⟨hr, _, heq⟩ := discRadius_bounds hZ
  have hZ0 : 0 ≤ Z := by linarith
  have hmul := mul_le_mul_of_nonneg_left (show (6 : ℝ) ≤ Z by linarith)
    (mul_nonneg hr.le hZ0)
  nlinarith

/-- A concrete point on the radial segments or outer arc. -/
def sectorPoint (ρ θ : ℝ) : ℂ :=
  (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

theorem sectorPoint_norm {ρ : ℝ} (hρ : 0 ≤ ρ) (θ : ℝ) :
    ‖sectorPoint ρ θ‖ = ρ := by
  simp [sectorPoint, Complex.norm_exp_ofReal_mul_I, abs_of_nonneg hρ]

theorem sectorPoint_re (ρ θ : ℝ) :
    (sectorPoint ρ θ).re = ρ * Real.cos θ := by
  simp [sectorPoint, Complex.mul_re, Complex.exp_ofReal_mul_I_re]

/-- The mode phase is exactly the cancelled theta/weight exponent. -/
theorem modePhase_eq_cancelled (Z A : ℝ) (h ζ : ℂ) :
    modePhase Z (A - Z) h ζ =
      (Z : ℂ) / ζ + (Z : ℂ) * ζ -
        (A : ℂ) * Complex.exp (2 * h) * ζ := by
  simp only [modePhase, sub_add_cancel, Complex.ofReal_sub]
  ring

/-- Uniform radial estimate for `Z ≥ 16`. The parameter `A` may be any mode
size `n² Z_x ≥ Z`. -/
theorem mode_ray_phase_le_of_cos {Z A ρ θ : ℝ} {h : ℂ}
    (hZ : 16 ≤ Z) (hA : Z ≤ A) (hρ : 1 ≤ ρ) (hρZ : ρ ≤ Z)
    (hθ : Real.cos θ = angularFloor Z)
    (hh : ‖h‖ ≤ discRadius Z) :
    (modePhase Z (A - Z) h (sectorPoint ρ θ)).re ≤
      7 - A / Z := by
  have hZpos : 0 < Z := by linarith
  obtain ⟨hr, hrmax, hrZ⟩ := discRadius_bounds hZ
  obtain ⟨hcZlo, hcZup⟩ := angularFloor_bounds hZ
  have heff := effective_floor hZ
  have hcoeff : 0 ≤ angularFloor Z - 3 * discRadius Z :=
    nonneg_of_mul_nonneg_left (by linarith : 0 ≤
      (angularFloor Z - 3 * discRadius Z) * Z) hZpos
  have hc : 0 ≤ angularFloor Z := by linarith
  have hre : (sectorPoint ρ θ).re = ρ * angularFloor Z := by
    rw [sectorPoint_re, hθ]
  have hp := ray_phase_le (by linarith : 1 ≤ Z) (sub_nonneg.mpr hA) hr.le hρ hρZ
    hc hcZup (by linarith) (le_of_eq hrZ)
    (sectorPoint_norm (by linarith : 0 ≤ ρ) _) hre
    (exp_two_sub_one_le hr.le hrmax hh)
  have hrecip : 1 / Z ≤ angularFloor Z - 3 * discRadius Z :=
    (div_le_iff₀ hZpos).mpr heff
  have hmul := mul_le_mul_of_nonneg_right hrecip
    (show 0 ≤ A by linarith)
  have hratio : (1 / Z) * A = A / Z := by ring
  rw [hratio] at hmul
  simpa only [sub_add_cancel] using hp.trans (by nlinarith :
    7 - (angularFloor Z - 3 * discRadius Z) * (A - Z + Z) ≤ 7 - A / Z)

/-- This covers both radial segments, including the negative angle. -/
theorem mode_ray_phase_le {Z A ρ θ : ℝ} {h : ℂ}
    (hZ : 16 ≤ Z) (hA : Z ≤ A) (hρ : 1 ≤ ρ) (hρZ : ρ ≤ Z)
    (hθ : |θ| = 2 * shiftBoundary Z) (hh : ‖h‖ ≤ discRadius Z) :
    (modePhase Z (A - Z) h (sectorPoint ρ θ)).re ≤ 7 - A / Z := by
  apply mode_ray_phase_le_of_cos hZ hA hρ hρZ _ hh
  rw [← Real.cos_abs, hθ, cos_twice_shiftBoundary]

/-- Geometric membership in the entire sector implies its cosine bound. -/
theorem angularFloor_le_cos {Z θ : ℝ} (hZ : 0 < Z)
    (hθ : |θ| ≤ 2 * shiftBoundary Z) :
    angularFloor Z ≤ Real.cos θ := by
  have htop : 2 * shiftBoundary Z ≤ Real.pi := by
    unfold shiftBoundary
    have hi : 0 ≤ 1 / Z := by positivity
    nlinarith [Real.pi_pos]
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) htop hθ
  simpa only [Real.cos_abs, cos_twice_shiftBoundary] using hcos

/-- Uniform outer-arc estimate.  Membership in the angular sector is
recorded by the exact cosine inequality, not by a supplied phase bound. -/
theorem mode_arc_phase_le {Z A θ : ℝ} {h : ℂ}
    (hZ : 16 ≤ Z) (hA : Z ≤ A)
    (hθ : angularFloor Z ≤ Real.cos θ) (hh : ‖h‖ ≤ discRadius Z) :
    (modePhase Z (A - Z) h (sectorPoint Z θ)).re ≤ 6 - A / Z := by
  have hZpos : 0 < Z := by linarith
  obtain ⟨hr, hrmax, hrZ⟩ := discRadius_bounds hZ
  obtain ⟨_, hcZup⟩ := angularFloor_bounds hZ
  have heff := effective_floor hZ
  have hcoeff : 0 ≤ angularFloor Z - 3 * discRadius Z :=
    nonneg_of_mul_nonneg_left (by linarith : 0 ≤
      (angularFloor Z - 3 * discRadius Z) * Z) hZpos
  have hp := arc_phase_le (by linarith : 1 ≤ Z) (sub_nonneg.mpr hA) hr.le
    hcZup (by linarith) hθ (Real.cos_le_one θ) (le_of_eq hrZ)
    (sectorPoint_norm hZpos.le θ) (sectorPoint_re Z θ)
    (exp_two_sub_one_le hr.le hrmax hh)
  have hrecip : 1 / Z ≤ angularFloor Z - 3 * discRadius Z :=
    (div_le_iff₀ hZpos).mpr heff
  have hmul := mul_le_mul_of_nonneg_right hrecip
    (show 0 ≤ A by linarith)
  have hratio : (1 / Z) * A = A / Z := by ring
  rw [hratio] at hmul
  simpa only [sub_add_cancel] using hp.trans (by nlinarith :
    6 - (angularFloor Z - 3 * discRadius Z) * (A - Z + Z) ≤ 6 - A / Z)

/-- The outer arc, with its geometric angular condition. -/
theorem mode_arc_phase_le_of_mem_sector {Z A θ : ℝ} {h : ℂ}
    (hZ : 16 ≤ Z) (hA : Z ≤ A)
    (hθ : |θ| ≤ 2 * shiftBoundary Z) (hh : ‖h‖ ≤ discRadius Z) :
    (modePhase Z (A - Z) h (sectorPoint Z θ)).re ≤ 6 - A / Z :=
  mode_arc_phase_le hZ hA
    (angularFloor_le_cos (by linarith : 0 < Z) hθ) hh

/-- Exponential decay on either radial segment. -/
theorem mode_ray_exp_norm_le {Z A ρ θ : ℝ} {h : ℂ}
    (hZ : 16 ≤ Z) (hA : Z ≤ A) (hρ : 1 ≤ ρ) (hρZ : ρ ≤ Z)
    (hθ : |θ| = 2 * shiftBoundary Z) (hh : ‖h‖ ≤ discRadius Z) :
    ‖Complex.exp (modePhase Z (A - Z) h (sectorPoint ρ θ))‖ ≤
      Real.exp (7 - A / Z) := by
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr (mode_ray_phase_le hZ hA hρ hρZ hθ hh)

/-- Exponential decay on the full outer arc. -/
theorem mode_arc_exp_norm_le {Z A θ : ℝ} {h : ℂ}
    (hZ : 16 ≤ Z) (hA : Z ≤ A)
    (hθ : |θ| ≤ 2 * shiftBoundary Z) (hh : ‖h‖ ≤ discRadius Z) :
    ‖Complex.exp (modePhase Z (A - Z) h (sectorPoint Z θ))‖ ≤
      Real.exp (6 - A / Z) := by
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr (mode_arc_phase_le_of_mem_sector hZ hA hθ hh)

/-- The fourth-moment Gaussian majorant is summable. -/
theorem summable_mode_majorant :
    Summable (fun n : ℕ => (n : ℝ) ^ 4 * Real.exp (-((n : ℝ) ^ 2 - 1))) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ 4 * Real.exp (-(n : ℝ))) := by
    simpa using Real.summable_pow_mul_exp_neg_nat_mul 4 (by norm_num : (0 : ℝ) < 1)
  apply (hbase.mul_left (Real.exp 1)).of_nonneg_of_le (fun _ => by positivity)
  intro n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    by_cases hn : n = 0
    · simp [hn]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hn1)]
  have he : Real.exp (-((n : ℝ) ^ 2 - 1)) ≤ Real.exp (1 - n) :=
    Real.exp_le_exp.mpr (by linarith)
  calc
    (n : ℝ) ^ 4 * Real.exp (-((n : ℝ) ^ 2 - 1)) ≤
        (n : ℝ) ^ 4 * Real.exp (1 - n) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = Real.exp 1 * ((n : ℝ) ^ 4 * Real.exp (-(n : ℝ))) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring

/-- The exact, finite all-mode constant used in the contour proof. -/
def modeConstant : ℝ :=
  ∑' n : ℕ, (n : ℝ) ^ 4 * Real.exp (-((n : ℝ) ^ 2 - 1))

/-- Uniform Gaussian mode summation, with the n=0 term identically zero. -/
theorem mode_sum_le {v : ℝ} (hv : 1 ≤ v) :
    (∑' n : ℕ, (n : ℝ) ^ 4 * Real.exp (-v * (n : ℝ) ^ 2)) ≤
      Real.exp (-v) * modeConstant := by
  have hmajor := summable_mode_majorant.mul_left (Real.exp (-v))
  have hpoint (n : ℕ) :
      (n : ℝ) ^ 4 * Real.exp (-v * (n : ℝ) ^ 2) ≤
        Real.exp (-v) * ((n : ℝ) ^ 4 * Real.exp (-((n : ℝ) ^ 2 - 1))) := by
    by_cases hn : n = 0
    · simp [hn]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have he : Real.exp (-v * (n : ℝ) ^ 2) ≤
        Real.exp (-v - ((n : ℝ) ^ 2 - 1)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hv) (sub_nonneg.mpr hsq)]
    calc
      (n : ℝ) ^ 4 * Real.exp (-v * (n : ℝ) ^ 2) ≤
          (n : ℝ) ^ 4 * Real.exp (-v - ((n : ℝ) ^ 2 - 1)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = Real.exp (-v) * ((n : ℝ) ^ 4 * Real.exp (-((n : ℝ) ^ 2 - 1))) := by
        rw [sub_eq_add_neg, Real.exp_add]
        ring
  have hsum := hmajor.of_nonneg_of_le (fun _ => by positivity) hpoint
  have hle := hsum.tsum_le_tsum hpoint hmajor
  simpa only [tsum_mul_left, modeConstant] using hle

/-- The closed Cauchy disc stays strictly inside the residual strip. -/
theorem cauchy_disc_subset_strip {Z : ℝ} (hZ : 16 ≤ Z) (x : ℝ) :
    closedBall (x : ℂ) (discRadius Z) ⊆ {z : ℂ | |z.im| < 1 / Z} := by
  have hZpos : 0 < Z := by linarith
  obtain ⟨hr, _, hrZ⟩ := discRadius_bounds hZ
  have hmul := mul_lt_mul_of_pos_left (show (1 : ℝ) < Z by linarith)
    (mul_pos hr hZpos)
  have hrlt : discRadius Z < 1 / Z := (lt_div_iff₀ hZpos).mpr (by nlinarith)
  intro z hz
  have hnorm : ‖z - (x : ℂ)‖ ≤ discRadius Z := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have him := Complex.abs_im_le_norm (z - (x : ℂ))
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at him
  exact lt_of_le_of_lt (him.trans hnorm) hrlt

/-- Cauchy estimates for a holomorphic function that is bounded on a disc. -/
theorem cauchy_derivative_of_disc_bound {f : ℂ → ℂ} {x : ℂ} {Z B : ℝ}
    (hZ : 0 < Z)
    (hf : DifferentiableOn ℂ f (closedBall x ((Z ^ 2)⁻¹)))
    (hB : ∀ z ∈ closedBall x ((Z ^ 2)⁻¹), ‖f z‖ ≤ B) (j : ℕ) :
    ‖iteratedDeriv j f x‖ ≤ j.factorial * Z ^ (2 * j) * B := by
  have hr : 0 < (Z ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos hZ)
  have hbound := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hr
    (hf.diffContOnCl_ball Subset.rfl)
    (fun z hz => hB z (sphere_subset_closedBall hz))
  convert hbound using 1
  simp only [inv_pow, div_inv_eq_mul, pow_mul]
  ring

/-- Cauchy estimates for the derivatives, given holomorphy on the strip and a
bound on the disc. -/
theorem cauchy_derivative_of_strip_and_disc_bound
    {f : ℂ → ℂ} {x Z B : ℝ} (hZ : 16 ≤ Z)
    (hf : DifferentiableOn ℂ f {z : ℂ | |z.im| < 1 / Z})
    (hB : ∀ h : ℂ, ‖h‖ ≤ discRadius Z → ‖f ((x : ℂ) + h)‖ ≤ B)
    (j : ℕ) :
    ‖iteratedDeriv j f (x : ℂ)‖ ≤ j.factorial * Z ^ (2 * j) * B := by
  apply cauchy_derivative_of_disc_bound (by linarith : 0 < Z)
    (hf.mono (cauchy_disc_subset_strip hZ x))
  intro z hz
  have hnorm : ‖z - (x : ℂ)‖ ≤ discRadius Z := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, discRadius] using hz
  simpa only [add_sub_cancel] using hB (z - (x : ℂ)) hnorm

end ThetaTrial.Paper.Contour
