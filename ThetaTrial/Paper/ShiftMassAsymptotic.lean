import ThetaTrial.Paper.ShiftWeightMass

/-! The leading mass of the von Mises weight. The Taylor error and the
endpoint tails are bounded directly by Gaussian integrals. -/

noncomputable section
open MeasureTheory Set Real Filter

namespace ThetaTrial.Paper

theorem exp_sub_le_difference_mul_exp (x y : ℝ) :
    Real.exp x - Real.exp y ≤ (x - y) * Real.exp x := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (y - x))
    (Real.exp_pos x).le
  rw [← Real.exp_add, sub_add_cancel] at h
  nlinarith

theorem sq_sub_sin_sq_le_fourth (y : ℝ) : y ^ 2 - Real.sin y ^ 2 ≤ y ^ 4 := by
  have habs4 : |y| ^ 4 = y ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_mul, sq_abs]
  calc
    y ^ 2 - Real.sin y ^ 2 = (y - Real.sin y) * (y + Real.sin y) := by ring
    _ ≤ |(y - Real.sin y) * (y + Real.sin y)| := le_abs_self _
    _ = |y - Real.sin y| * |y + Real.sin y| := abs_mul _ _
    _ ≤ (|y| ^ 3 / 6) * (2 * |y|) := by
      apply mul_le_mul (Real.abs_sub_sin_le y) ?_ (abs_nonneg _) (by positivity)
      exact (abs_add_le _ _).trans (by linarith [Real.abs_sin_le_abs (x := y)])
    _ = |y| ^ 4 / 3 := by ring
    _ ≤ y ^ 4 := by rw [habs4]; nlinarith [sq_nonneg (y ^ 2)]

theorem quartic_mul_gaussian_le {Z y : ℝ} (hZ : 0 < Z) :
    y ^ 4 * Real.exp (-Z * y ^ 2) ≤
      (8 / Z ^ 2) * Real.exp (-(Z / 2) * y ^ 2) := by
  have he := Real.pow_div_factorial_le_exp (Z / 2 * y ^ 2) (by positivity) 2
  norm_num at he
  have hy : y ^ 4 ≤ (8 * Real.exp (Z / 2 * y ^ 2)) / Z ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hZ)).mpr
    nlinarith [he]
  calc
    _ ≤ ((8 * Real.exp (Z / 2 * y ^ 2)) / Z ^ 2) * Real.exp (-Z * y ^ 2) :=
      mul_le_mul_of_nonneg_right hy (Real.exp_pos _).le
    _ = (8 / Z ^ 2) * Real.exp (-(Z / 2) * y ^ 2) := by
      rw [show 8 * Real.exp (Z / 2 * y ^ 2) / Z ^ 2 =
        (8 / Z ^ 2) * Real.exp (Z / 2 * y ^ 2) by ring,
        mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem shiftWeight_sub_gaussian_bound {a y : ℝ} (ha : 16 ≤ scaleZ a)
    (hy : y ∈ Icc (-shiftWidth a) (shiftWidth a)) :
    0 ≤ shiftWeight a y - Real.exp (-4 * scaleZ a * y ^ 2) ∧
    shiftWeight a y - Real.exp (-4 * scaleZ a * y ^ 2) ≤
      (32 / scaleZ a) * Real.exp (-(scaleZ a / 2) * y ^ 2) := by
  have hZ : 0 < scaleZ a := by linarith
  refine ⟨sub_nonneg.mpr (shiftWeight_gaussian_lower a y), ?_⟩
  have hexp := exp_sub_le_difference_mul_exp
    (-2 * scaleZ a * (1 - Real.cos (2 * y))) (-4 * scaleZ a * y ^ 2)
  have htrig : -2 * scaleZ a * (1 - Real.cos (2 * y)) - (-4 * scaleZ a * y ^ 2) =
      4 * scaleZ a * (y ^ 2 - Real.sin y ^ 2) := by
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq y]
  rw [htrig] at hexp
  change shiftWeight a y - Real.exp (-4 * scaleZ a * y ^ 2) ≤
    (4 * scaleZ a * (y ^ 2 - Real.sin y ^ 2)) * shiftWeight a y at hexp
  calc
    _ ≤ (4 * scaleZ a * (y ^ 2 - Real.sin y ^ 2)) * shiftWeight a y := hexp
    _ ≤ (4 * scaleZ a * y ^ 4) * shiftWeight a y := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sq_sub_sin_sq_le_fourth y) (by positivity))
        (shiftWeight_pos a y).le
    _ ≤ (4 * scaleZ a * y ^ 4) * Real.exp (-scaleZ a * y ^ 2) :=
      mul_le_mul_of_nonneg_left (shiftWeight_le_simple_gaussian ha hy) (by positivity)
    _ ≤ (4 * scaleZ a) * ((8 / (scaleZ a) ^ 2) *
        Real.exp (-(scaleZ a / 2) * y ^ 2)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (quartic_mul_gaussian_le hZ) (by positivity)
    _ = _ := by field_simp; ring

theorem gaussian_endpoint_tail_bound {a y : ℝ} (ha : 16 ≤ scaleZ a)
    (hy : y ∉ Icc (-shiftWidth a) (shiftWidth a)) :
    Real.exp (-4 * scaleZ a * y ^ 2) ≤
      (8 / scaleZ a) * Real.exp (-2 * scaleZ a * y ^ 2) := by
  have hZ : 0 < scaleZ a := by linarith
  have hyabs : 1 / 4 ≤ |y| := by
    have hb := shiftWidth_ge_quarter ha
    have hnot : ¬ |y| ≤ shiftWidth a := fun h => hy (abs_le.mp h)
    linarith [lt_of_not_ge hnot]
  have hy2 : 1 / 16 ≤ y ^ 2 := by
    have hh := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) (abs_nonneg y)).mpr hyabs
    rw [sq_abs] at hh
    norm_num at hh
    exact hh
  have he : scaleZ a / 8 ≤ Real.exp (2 * scaleZ a * y ^ 2) := by
    have ht := mul_le_mul_of_nonneg_left hy2 (show 0 ≤ 2 * scaleZ a by positivity)
    linarith [Real.add_one_le_exp (2 * scaleZ a * y ^ 2)]
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-2 * scaleZ a * y ^ 2)).le
  rw [← Real.exp_add, show 2 * scaleZ a * y ^ 2 + -2 * scaleZ a * y ^ 2 = 0 by ring,
    Real.exp_zero] at hm
  have hsmall : Real.exp (-2 * scaleZ a * y ^ 2) ≤ 8 / scaleZ a := by
    apply (le_div_iff₀ hZ).mpr
    nlinarith
  calc
    Real.exp (-4 * scaleZ a * y ^ 2) =
        Real.exp (-2 * scaleZ a * y ^ 2) * Real.exp (-2 * scaleZ a * y ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le

theorem shiftMass_gaussian_error_bound {a : ℝ} (ha : 16 ≤ scaleZ a) :
    |shiftMass a - Real.sqrt (Real.pi / (4 * scaleZ a))| ≤
      (32 / scaleZ a) * Real.sqrt (Real.pi / (scaleZ a / 2)) +
      (8 / scaleZ a) * Real.sqrt (Real.pi / (2 * scaleZ a)) := by
  let J := Icc (-shiftWidth a) (shiftWidth a)
  let g : ℝ → ℝ := fun y => Real.exp (-(4 * scaleZ a) * y ^ 2)
  let E := ∫ y : ℝ in J, shiftWeight a y - g y
  let T := ∫ y : ℝ in Jᶜ, g y
  have hZ : 0 < scaleZ a := by linarith
  have hg : Integrable g := integrable_exp_neg_mul_sq (by positivity)
  have hw : IntegrableOn (shiftWeight a) J :=
    (shiftWeight_continuous a).continuousOn.integrableOn_Icc
  have he0 : 0 ≤ E := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    simpa only [g, Pi.zero_apply, neg_mul] using (shiftWeight_sub_gaussian_bound ha hy).1
  have ht0 : 0 ≤ T := integral_nonneg (fun y => (Real.exp_pos _).le)
  have hge := (integrable_exp_neg_mul_sq (half_pos hZ)).const_mul (32 / scaleZ a)
  have hgt := (integrable_exp_neg_mul_sq (show 0 < 2 * scaleZ a by positivity)).const_mul
    (8 / scaleZ a)
  have he : E ≤ (32 / scaleZ a) * Real.sqrt (Real.pi / (scaleZ a / 2)) := by
    calc
      E ≤ ∫ y : ℝ in J, (32 / scaleZ a) * Real.exp (-(scaleZ a / 2) * y ^ 2) := by
        apply integral_mono_ae (hw.sub hg.integrableOn) hge.integrableOn
        filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
        simpa only [g, Pi.sub_apply, neg_mul] using (shiftWeight_sub_gaussian_bound ha hy).2
      _ ≤ ∫ y : ℝ, (32 / scaleZ a) * Real.exp (-(scaleZ a / 2) * y ^ 2) :=
        setIntegral_le_integral hge (ae_of_all _ (fun y => by positivity))
      _ = _ := by rw [integral_const_mul, integral_gaussian]
  have ht : T ≤ (8 / scaleZ a) * Real.sqrt (Real.pi / (2 * scaleZ a)) := by
    calc
      T ≤ ∫ y : ℝ in Jᶜ, (8 / scaleZ a) * Real.exp (-(2 * scaleZ a) * y ^ 2) := by
        apply integral_mono_ae hg.integrableOn hgt.integrableOn
        filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with y hy
        simpa only [g, neg_mul] using gaussian_endpoint_tail_bound ha hy
      _ ≤ ∫ y : ℝ, (8 / scaleZ a) * Real.exp (-(2 * scaleZ a) * y ^ 2) :=
        setIntegral_le_integral hgt (ae_of_all _ (fun y => by positivity))
      _ = _ := by rw [integral_const_mul, integral_gaussian]
  have hid : shiftMass a - Real.sqrt (Real.pi / (4 * scaleZ a)) = E - T := by
    have hs := integral_add_compl (s := J) measurableSet_Icc hg
    have hs' : (∫ y : ℝ in J, g y) + T = Real.sqrt (Real.pi / (4 * scaleZ a)) := by
      simpa only [g, integral_gaussian] using hs
    have he' : E = shiftMass a - ∫ y : ℝ in J, g y := by
      exact integral_sub hw hg.integrableOn
    linarith
  rw [hid]
  apply abs_le.mpr
  constructor <;> nlinarith [he, ht]

def shiftMassErrorConstant : ℝ :=
  32 * Real.sqrt (2 * Real.pi) + 8 * Real.sqrt (Real.pi / 2)

theorem shiftMassErrorConstant_pos : 0 < shiftMassErrorConstant := by
  unfold shiftMassErrorConstant
  positivity

/-- The sharp Gaussian leading coefficient, with a concrete relative-order error. -/
theorem shiftMass_sharp_error {a : ℝ} (ha : 16 ≤ scaleZ a) :
    |shiftMass a - Real.sqrt Real.pi / (2 * Real.sqrt (scaleZ a))| ≤
      shiftMassErrorConstant / (scaleZ a * Real.sqrt (scaleZ a)) := by
  have hZ : 0 < scaleZ a := by linarith
  have h := shiftMass_gaussian_error_bound ha
  have h0 : Real.sqrt (Real.pi / (4 * scaleZ a)) =
      Real.sqrt Real.pi / (2 * Real.sqrt (scaleZ a)) := by
    rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have h1 : Real.sqrt (Real.pi / (scaleZ a / 2)) =
      Real.sqrt (2 * Real.pi) / Real.sqrt (scaleZ a) := by
    rw [show Real.pi / (scaleZ a / 2) = (2 * Real.pi) / scaleZ a by ring,
      Real.sqrt_div (by positivity)]
  have h2 : Real.sqrt (Real.pi / (2 * scaleZ a)) =
      Real.sqrt (Real.pi / 2) / Real.sqrt (scaleZ a) := by
    rw [show Real.pi / (2 * scaleZ a) = (Real.pi / 2) / scaleZ a by ring,
      Real.sqrt_div (by positivity)]
  rw [h0, h1, h2] at h
  convert h using 1 <;> unfold shiftMassErrorConstant <;> ring

/-- An explicit form of `shiftMass = sqrt(pi)/(2 sqrt(Z)) * (1 + O(1/Z))`. -/
theorem shiftMass_sharp_relative_error {a : ℝ} (ha : 16 ≤ scaleZ a) :
    |(2 * Real.sqrt (scaleZ a) / Real.sqrt Real.pi) * shiftMass a - 1| ≤
      (2 * shiftMassErrorConstant / Real.sqrt Real.pi) / scaleZ a := by
  have hZ : 0 < scaleZ a := by linarith
  have hs : 0 < Real.sqrt (scaleZ a) := Real.sqrt_pos.mpr hZ
  have hp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hm := mul_le_mul_of_nonneg_left (shiftMass_sharp_error ha)
    (show 0 ≤ 2 * Real.sqrt (scaleZ a) / Real.sqrt Real.pi by positivity)
  have hl : (2 * Real.sqrt (scaleZ a) / Real.sqrt Real.pi) *
      |shiftMass a - Real.sqrt Real.pi / (2 * Real.sqrt (scaleZ a))| =
      |(2 * Real.sqrt (scaleZ a) / Real.sqrt Real.pi) * shiftMass a - 1| := by
    calc
      _ = |(2 * Real.sqrt (scaleZ a) / Real.sqrt Real.pi) *
          (shiftMass a - Real.sqrt Real.pi / (2 * Real.sqrt (scaleZ a)))| := by
        rw [abs_mul, abs_of_nonneg (show 0 ≤ 2 * Real.sqrt (scaleZ a) /
          Real.sqrt Real.pi by positivity)]
      _ = _ := by
        congr 1
        field_simp [ne_of_gt hs, ne_of_gt hp]
  rw [hl] at hm
  calc
    _ ≤ (2 * Real.sqrt (scaleZ a) / Real.sqrt Real.pi) *
        (shiftMassErrorConstant / (scaleZ a * Real.sqrt (scaleZ a))) := hm
    _ = _ := by field_simp [ne_of_gt hZ, ne_of_gt hs, ne_of_gt hp] <;> ring

end ThetaTrial.Paper
