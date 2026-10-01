import ThetaTrial.Paper.Multiplier
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! Concentration estimates for the finite von Mises averaging weight. -/

noncomputable section
open MeasureTheory Set Real

namespace ThetaTrial.Paper

def shiftMass (a : ℝ) : ℝ :=
  ∫ y : ℝ in Icc (-shiftWidth a) (shiftWidth a), shiftWeight a y

theorem shiftWeight_continuous (a : ℝ) : Continuous (shiftWeight a) := by
  unfold shiftWeight
  fun_prop

theorem shiftWidth_ge_quarter {a : ℝ} (ha : 16 ≤ scaleZ a) :
    1 / 4 ≤ shiftWidth a := by
  have hZ : 0 < scaleZ a := by linarith
  have hi : (scaleZ a)⁻¹ ≤ (1 / 16 : ℝ) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<16) ha
  unfold shiftWidth
  linarith [Real.pi_gt_three]

theorem inv_sqrt_scale_le_quarter {a : ℝ} (ha : 16 ≤ scaleZ a) :
    (Real.sqrt (scaleZ a))⁻¹ ≤ 1 / 4 := by
  have hs : 4 ≤ Real.sqrt (scaleZ a) := by
    exact (Real.le_sqrt (by norm_num) (by linarith)).mpr (by norm_num; exact ha)
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<4) hs

/-- A fixed positive weight survives on the natural Z^(-1/2) window. -/
theorem shiftWeight_lower_central {a y : ℝ} (ha : 16 ≤ scaleZ a)
    (hy : |y| ≤ (Real.sqrt (scaleZ a))⁻¹) :
    Real.exp (-4) ≤ shiftWeight a y := by
  have hZ : 0 < scaleZ a := by linarith
  have hs : 0 < Real.sqrt (scaleZ a) := Real.sqrt_pos.2 hZ
  have hy' : |y| * Real.sqrt (scaleZ a) ≤ 1 := by
    exact (le_div_iff₀ hs).mp (by simpa only [one_div] using hy)
  have hsq : scaleZ a * y ^ 2 ≤ 1 := by
    have hh := sq_le_sq₀ (by positivity : 0 ≤ |y| * Real.sqrt (scaleZ a))
      (by norm_num : (0 : ℝ) ≤ 1) |>.2 hy'
    simpa [mul_pow, Real.sq_sqrt hZ.le, sq_abs, mul_comm] using hh
  have hc := Real.one_sub_sq_div_two_le_cos (x := 2 * y)
  unfold shiftWeight
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hZ.le (show 0 ≤ 2 * y ^ 2 - (1 - Real.cos (2 * y)) by nlinarith)]

/-- Quantitative lower bound for the mass, with an absolute constant. -/
theorem shiftMass_lower {a : ℝ} (ha : 16 ≤ scaleZ a) :
    2 * Real.exp (-4) / Real.sqrt (scaleZ a) ≤ shiftMass a := by
  let r := (Real.sqrt (scaleZ a))⁻¹
  have hr : 0 < r := by dsimp [r]; positivity
  have hrb : r ≤ shiftWidth a :=
    (inv_sqrt_scale_le_quarter ha).trans (shiftWidth_ge_quarter ha)
  have hw : IntegrableOn (shiftWeight a) (Icc (-shiftWidth a) (shiftWidth a)) :=
    (shiftWeight_continuous a).continuousOn.integrableOn_Icc
  have hsub : Icc (-r) r ⊆ Icc (-shiftWidth a) (shiftWidth a) := by
    intro y hy
    exact ⟨by linarith [hy.1], hy.2.trans hrb⟩
  have hmono := setIntegral_mono_set hw
    (Filter.Eventually.of_forall (fun y => (shiftWeight_pos a y).le))
    (Filter.Eventually.of_forall hsub)
  have hlocal : (∫ _y : ℝ in Icc (-r) r, Real.exp (-4)) ≤
      ∫ y : ℝ in Icc (-r) r, shiftWeight a y := by
    apply setIntegral_mono_on
      (continuous_const.continuousOn.integrableOn_Icc)
      ((shiftWeight_continuous a).continuousOn.integrableOn_Icc) measurableSet_Icc
    intro y hy
    exact shiftWeight_lower_central ha (abs_le.mpr hy)
  calc
    2 * Real.exp (-4) / Real.sqrt (scaleZ a) =
        ∫ _y : ℝ in Icc (-r) r, Real.exp (-4) := by
      rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith : -r ≤ r)]
      simp only [smul_eq_mul]
      dsimp [r]
      ring
    _ ≤ ∫ y : ℝ in Icc (-r) r, shiftWeight a y := hlocal
    _ ≤ shiftMass a := hmono

/-- The weight admits a Gaussian upper bound on its support. -/
theorem shiftWeight_le_gaussian {a y : ℝ} (ha : 16 ≤ scaleZ a)
    (hy : y ∈ Icc (-shiftWidth a) (shiftWidth a)) :
    shiftWeight a y ≤ Real.exp (-(16 * scaleZ a / Real.pi ^ 2) * y ^ 2) := by
  have hZ : 0 < scaleZ a := by linarith
  have hb : shiftWidth a ≤ Real.pi / 4 := by
    unfold shiftWidth
    exact sub_le_self _ (inv_nonneg.mpr hZ.le)
  have hyabs : |y| ≤ Real.pi / 4 := (abs_le.mpr hy).trans hb
  have h2y : |2 * y| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [Real.pi_pos]
  have hc := Real.cos_le_one_sub_mul_cos_sq h2y
  unfold shiftWeight
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2 * scaleZ a by positivity)
  calc
    -2 * scaleZ a * (1 - Real.cos (2 * y)) ≤
        -2 * scaleZ a + 2 * scaleZ a * (1 - 2 / Real.pi ^ 2 * (2 * y) ^ 2) := by
      linarith [hm]
    _ = _ := by ring

theorem shiftWeight_le_simple_gaussian {a y : ℝ} (ha : 16 ≤ scaleZ a)
    (hy : y ∈ Icc (-shiftWidth a) (shiftWidth a)) :
    shiftWeight a y ≤ Real.exp (-scaleZ a * y ^ 2) := by
  apply (shiftWeight_le_gaussian ha hy).trans
  apply Real.exp_le_exp.mpr
  have hp2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hcoef : scaleZ a ≤ 16 * scaleZ a / Real.pi ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hp2 (by linarith : 0 ≤ scaleZ a)]
  nlinarith [mul_le_mul_of_nonneg_right hcoef (sq_nonneg y)]

theorem shiftMass_upper {a : ℝ} (ha : 16 ≤ scaleZ a) :
    shiftMass a ≤ Real.sqrt (Real.pi / scaleZ a) := by
  have hZ : 0 < scaleZ a := by linarith
  have hg := integrable_exp_neg_mul_sq hZ
  calc
    shiftMass a ≤ ∫ y : ℝ in Icc (-shiftWidth a) (shiftWidth a),
        Real.exp (-scaleZ a * y ^ 2) := by
      apply setIntegral_mono_on
        ((shiftWeight_continuous a).continuousOn.integrableOn_Icc)
        hg.integrableOn measurableSet_Icc
      exact fun y hy => shiftWeight_le_simple_gaussian ha hy
    _ ≤ ∫ y : ℝ, Real.exp (-scaleZ a * y ^ 2) :=
      setIntegral_le_integral hg (Filter.Eventually.of_forall (fun y => (Real.exp_pos _).le))
    _ = _ := integral_gaussian _

theorem abs_mul_gaussian_le {Z y : ℝ} (hZ : 0 < Z) :
    |y| * Real.exp (-Z * y ^ 2) ≤
      (Real.sqrt Z)⁻¹ * Real.exp (-(Z / 2) * y ^ 2) := by
  have hs : 0 < Real.sqrt Z := Real.sqrt_pos.2 hZ
  have hsq := Real.sq_sqrt hZ.le
  have ht : |y| * Real.sqrt Z ≤ 1 + Z / 2 * y ^ 2 := by
    nlinarith [sq_nonneg (|y| * Real.sqrt Z - 1), sq_abs y]
  have he : |y| * Real.sqrt Z ≤ Real.exp (Z / 2 * y ^ 2) :=
    ht.trans (by simpa only [add_comm] using Real.add_one_le_exp (Z / 2 * y ^ 2))
  have hy : |y| ≤ (Real.sqrt Z)⁻¹ * Real.exp (Z / 2 * y ^ 2) := by
    simpa only [div_eq_mul_inv, mul_comm] using (le_div_iff₀ hs).mpr he
  calc
    |y| * Real.exp (-Z * y ^ 2) ≤
        ((Real.sqrt Z)⁻¹ * Real.exp (Z / 2 * y ^ 2)) * Real.exp (-Z * y ^ 2) :=
      mul_le_mul_of_nonneg_right hy (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- The absolute first moment needed by the interior Taylor estimate. -/
theorem shiftWeight_first_moment {a : ℝ} (ha : 16 ≤ scaleZ a) :
    (∫ y : ℝ in Icc (-shiftWidth a) (shiftWidth a), |y| * shiftWeight a y) ≤
      Real.sqrt (2 * Real.pi) / scaleZ a := by
  have hZ : 0 < scaleZ a := by linarith
  have hg := (integrable_exp_neg_mul_sq (half_pos hZ)).const_mul
    ((Real.sqrt (scaleZ a))⁻¹)
  calc
    (∫ y : ℝ in Icc (-shiftWidth a) (shiftWidth a), |y| * shiftWeight a y) ≤
        ∫ y : ℝ in Icc (-shiftWidth a) (shiftWidth a),
          (Real.sqrt (scaleZ a))⁻¹ * Real.exp (-(scaleZ a / 2) * y ^ 2) := by
      apply setIntegral_mono_on
        (((continuous_abs.mul (shiftWeight_continuous a)).continuousOn).integrableOn_Icc)
        hg.integrableOn measurableSet_Icc
      intro y hy
      exact (mul_le_mul_of_nonneg_left (shiftWeight_le_simple_gaussian ha hy)
        (abs_nonneg y)).trans (abs_mul_gaussian_le hZ)
    _ ≤ ∫ y : ℝ, (Real.sqrt (scaleZ a))⁻¹ *
        Real.exp (-(scaleZ a / 2) * y ^ 2) :=
      setIntegral_le_integral hg (Filter.Eventually.of_forall (fun y => by positivity))
    _ = Real.sqrt (2 * Real.pi) / scaleZ a := by
      rw [integral_const_mul, integral_gaussian]
      rw [show Real.pi / (scaleZ a / 2) = (2 * Real.pi) / scaleZ a by ring,
        Real.sqrt_div (by positivity)]
      have hs : Real.sqrt (scaleZ a) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hZ)
      field_simp
      nlinarith [Real.sq_sqrt hZ.le]

/-- Away from the fixed central strip the weight is exponentially small. -/
theorem shiftWeight_outer {a y : ℝ} (ha : 16 ≤ scaleZ a)
    (hy : y ∈ Icc (-shiftWidth a) (shiftWidth a))
    (hyouter : Real.pi / 8 ≤ |y|) :
    shiftWeight a y ≤ Real.exp (-(Real.pi ^ 2 / 64) * scaleZ a) := by
  apply (shiftWeight_le_simple_gaussian ha hy).trans
  apply Real.exp_le_exp.mpr
  have hs : (Real.pi / 8) ^ 2 ≤ y ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (by positivity) (abs_nonneg y)).mpr hyouter
  nlinarith [mul_le_mul_of_nonneg_left hs (by linarith : 0 ≤ scaleZ a)]

end ThetaTrial.Paper
