import ThetaTrial.Paper.ThetaConcentration
import ThetaTrial.Paper.ThetaDerivTailMoments
import ThetaTrial.Paper.ThetaDerivPolePrimes

/-!
# Localization of the polynomial derivatives of the theta density

The survival estimate is proved in `ThetaConcentration`, and the weighted
Cauchy–Schwarz and layer-cake estimates in `ThetaDerivTailMoments`.
-/

noncomputable section
open MeasureTheory Set Polynomial
open scoped Polynomial

namespace ThetaTrial.Paper

def thetaDerivL1Constant : ℝ := Real.pi / 2 * ThetaDerivTailMoments.momentConstant 40

theorem thetaDerivL1Constant_pos : 0 < thetaDerivL1Constant := by
  unfold thetaDerivL1Constant ThetaDerivTailMoments.momentConstant
  positivity

theorem thetaDeriv_scaleT_ge_four {a : ℝ} (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a) :
    4 ≤ scaleT a := by
  rw [thetaQ_zero_eq_scaleZ] at ha
  unfold scaleT
  linarith

theorem thetaDerivTailWidth_le_one {d : ℕ} {a : ℝ}
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a) :
    thetaDerivTailWidth d a ≤ 1 := by
  rw [thetaQ_zero_eq_scaleZ] at hsize
  unfold thetaDerivTailWidth
  apply (div_le_iff₀ (thetaDeriv_scaleT_pos a)).mpr
  unfold scaleT
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  linarith

theorem thetaDerivOffsetSource_weighted_l1 (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a) :
    IntegrableOn (fun s : ℝ => Real.exp (s / 2) * ‖thetaDerivOffsetSource P a s‖) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, Real.exp (s / 2) * ‖thetaDerivOffsetSource P a s‖) ^ 2 ≤
        thetaDerivL1Constant * thetaDerivTailWidth d a * squaredNorm (thetaDerivRightTail P a) := by
  have hm := thetaDerivOffsetSource_memLp d P hP hdegree a ha hsize
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have ht : 2 ≤ scaleT a * thetaDerivTailWidth d a := by
    rw [thetaDerivTailWidth_scale]
    linarith [Nat.cast_nonneg (α := ℝ) d]
  have hb := ThetaDerivTailMoments.offset_weighted_l1_bound (thetaDerivOffsetSource P a)
    hm.aestronglyMeasurable hi (by norm_num : (0 : ℝ) ≤ 40)
    (thetaDeriv_scaleT_ge_four ha) ht (thetaDerivTailWidth_le_one hsize)
    (fun s hs => by
      simpa only [ThetaDerivTailMoments.offsetMass, div_mul_eq_mul_div] using
        thetaDerivOffsetSource_survival d P hP hdegree a s ha hsize hs)
  simpa only [thetaDerivL1Constant, ThetaDerivTailMoments.offsetMass, thetaDerivOffsetSource_tail_square,
    add_zero, thetaDerivRightTail_square] using hb

theorem thetaDerivOffsetSource_l1 (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a) :
    IntegrableOn (fun s : ℝ => ‖thetaDerivOffsetSource P a s‖) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, ‖thetaDerivOffsetSource P a s‖) ^ 2 ≤
        thetaDerivL1Constant * thetaDerivTailWidth d a * squaredNorm (thetaDerivRightTail P a) := by
  have hm := thetaDerivOffsetSource_memLp d P hP hdegree a ha hsize
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have ht : 2 ≤ scaleT a * thetaDerivTailWidth d a := by
    rw [thetaDerivTailWidth_scale]
    linarith [Nat.cast_nonneg (α := ℝ) d]
  have hb := ThetaDerivTailMoments.offset_l1_bound (thetaDerivOffsetSource P a)
    hm.aestronglyMeasurable hi (by norm_num : (0 : ℝ) ≤ 40)
    (thetaDeriv_scaleT_ge_four ha) ht (thetaDerivTailWidth_le_one hsize)
    (fun s hs => by
      simpa only [ThetaDerivTailMoments.offsetMass, div_mul_eq_mul_div] using
        thetaDerivOffsetSource_survival d P hP hdegree a s ha hsize hs)
  simpa only [thetaDerivL1Constant, ThetaDerivTailMoments.offsetMass, thetaDerivOffsetSource_tail_square,
    add_zero, thetaDerivRightTail_square] using hb

theorem thetaDeriv_integrable_const_add_Ioi (g : ℝ → ℝ) (a z : ℝ) :
    IntegrableOn g (Ioi (a + z)) ↔ IntegrableOn (fun x => g (a + x)) (Ioi z) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Ioi z)
    measurableSet_Ioi (fun x hx => ((hasDerivAt_id x).const_add a).hasDerivWithinAt)
    (show Set.InjOn (fun x : ℝ => a + x) (Ioi z) from fun x hx y hy hxy =>
      add_left_cancel hxy) g
  simpa only [id_eq, image_const_add_Ioi, abs_one, one_smul] using h

theorem thetaDerivRightTail_l1_integral (P : ℂ[X]) (a : ℝ) :
    (∫ u : ℝ, ‖thetaDerivRightTail P a u‖) = ∫ s : ℝ in Ioi 0, ‖thetaDerivOffsetSource P a s‖ := by
  have he : (fun u => ‖thetaDerivRightTail P a u‖) =
      (Ioi a).indicator (fun u => ‖polynomialDerivative P (fun v => (thetaDensity v : ℂ)) u‖) := by
    funext u
    by_cases hu : u ∈ Ioi a <;> simp [thetaDerivRightTail, hu]
  rw [he, integral_indicator measurableSet_Ioi]
  simpa only [thetaDerivOffsetSource, add_zero] using
    (thetaDeriv_integral_const_add_Ioi
      (fun u => ‖polynomialDerivative P (fun v => (thetaDensity v : ℂ)) u‖) a 0).symm

theorem thetaDerivRightTail_l1 (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a) :
    Integrable (thetaDerivRightTail P a) ∧
      (∫ u : ℝ, ‖thetaDerivRightTail P a u‖) ^ 2 ≤
        thetaDerivL1Constant * thetaDerivTailWidth d a * squaredNorm (thetaDerivRightTail P a) := by
  obtain ⟨hi, hb⟩ := thetaDerivOffsetSource_l1 d P hP hdegree a ha hsize
  refine ⟨?_, ?_⟩
  · apply (integrable_indicator_iff measurableSet_Ioi).mpr
    apply (integrable_norm_iff
      (polynomialDerivative_thetaDensity_continuous P).aestronglyMeasurable).mp
    have h := (thetaDeriv_integrable_const_add_Ioi
      (fun u => ‖polynomialDerivative P (fun v => (thetaDensity v : ℂ)) u‖) a 0).mpr hi
    simpa only [IntegrableOn, add_zero] using h
  · rw [thetaDerivRightTail_l1_integral]
    exact hb

theorem thetaDerivLeftTail_l1_integral (P : ℂ[X]) (a : ℝ) :
    (∫ u : ℝ, ‖thetaDerivLeftTail P a u‖) =
      ∫ u : ℝ, ‖thetaDerivRightTail (P.comp (-X)) a u‖ := by
  rw [← integral_neg_eq_self (fun u => ‖thetaDerivLeftTail P a u‖) volume]
  simp_rw [thetaDerivLeftTail_reflection]

theorem thetaDerivLeftTail_l1 (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a) :
    Integrable (thetaDerivLeftTail P a) ∧
      (∫ u : ℝ, ‖thetaDerivLeftTail P a u‖) ^ 2 ≤
        thetaDerivL1Constant * thetaDerivTailWidth d a * squaredNorm (thetaDerivLeftTail P a) := by
  obtain ⟨hi, hb⟩ := thetaDerivRightTail_l1 d (P.comp (-X)) (comp_neg_X_eq_zero_iff.not.mpr hP)
    (by simpa only [natDegree_comp, natDegree_neg, natDegree_X, mul_one] using hdegree)
    a ha hsize
  refine ⟨?_, ?_⟩
  · have h := (Measure.measurePreserving_neg volume).integrable_comp_of_integrable hi
    convert! h using 1
    funext u
    simpa only [Function.comp_apply, neg_neg] using thetaDerivLeftTail_reflection P a (-u)
  · rw [thetaDerivLeftTail_l1_integral, thetaDerivLeftTail_square_reflection]
    exact hb

theorem thetaDeriv_twoTailSurvival (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a : ℝ)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a) :
    TwoTailSurvival (thetaDerivRightTail P a) (thetaDerivLeftTail P a) a (scaleT a)
      (40 * thetaDerivTailWidth d a) := by
  apply twoTailSurvival_of_squared
  · intro s hs
    simpa only [neg_mul] using thetaDerivRightTail_survival d P hP hdegree a s ha hsize hs
  · intro s hs
    simpa only [neg_mul] using thetaDerivLeftTail_survival d P hP hdegree a s ha hsize hs

theorem thetaDerivRightTail_weighted_indicator (P : ℂ[X]) (a : ℝ) (ha : 0 ≤ a) :
    (fun u => Real.exp (|u| / 2) * ‖thetaDerivRightTail P a u‖) =
      (Ioi a).indicator (fun u => Real.exp (u / 2) *
        ‖polynomialDerivative P (fun v => (thetaDensity v : ℂ)) u‖) := by
  funext u
  by_cases hu : a < u
  · simp [thetaDerivRightTail, hu, abs_of_nonneg (ha.trans hu.le)]
  · simp [thetaDerivRightTail, hu]

theorem thetaDerivRightTail_weighted_translate (P : ℂ[X]) (a s : ℝ) :
    Real.exp ((a + s) / 2) *
      ‖polynomialDerivative P (fun v => (thetaDensity v : ℂ)) (a + s)‖ =
      Real.exp (a / 2) * (Real.exp (s / 2) * ‖thetaDerivOffsetSource P a s‖) := by
  rw [add_div, Real.exp_add]
  exact mul_assoc _ _ _

theorem thetaDerivRightTail_weighted_integral (P : ℂ[X]) (a : ℝ) (ha : 0 ≤ a) :
    halfWeightedL1 (thetaDerivRightTail P a) = Real.exp (a / 2) *
      ∫ s : ℝ in Ioi 0, Real.exp (s / 2) * ‖thetaDerivOffsetSource P a s‖ := by
  unfold halfWeightedL1
  rw [thetaDerivRightTail_weighted_indicator P a ha, integral_indicator measurableSet_Ioi]
  have h := thetaDeriv_integral_const_add_Ioi
    (fun u => Real.exp (u / 2) * ‖polynomialDerivative P (fun v => (thetaDensity v : ℂ)) u‖) a 0
  simp only [add_zero, thetaDerivRightTail_weighted_translate] at h
  rw [← h, integral_const_mul]

theorem thetaDerivRightTail_weighted_l1 (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a : ℝ) (ha0 : 0 ≤ a)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a) :
    Integrable (fun u : ℝ => Real.exp (|u| / 2) * ‖thetaDerivRightTail P a u‖) ∧
      halfWeightedL1 (thetaDerivRightTail P a) ^ 2 ≤
        Real.exp a * thetaDerivL1Constant * thetaDerivTailWidth d a * squaredNorm (thetaDerivRightTail P a) := by
  obtain ⟨hi, hb⟩ := thetaDerivOffsetSource_weighted_l1 d P hP hdegree a ha hsize
  refine ⟨?_, ?_⟩
  · rw [thetaDerivRightTail_weighted_indicator P a ha0]
    apply (integrable_indicator_iff measurableSet_Ioi).mpr
    have hi' : IntegrableOn (fun s : ℝ => Real.exp ((a + s) / 2) *
        ‖polynomialDerivative P (fun v => (thetaDensity v : ℂ)) (a + s)‖) (Ioi 0) := by
      simp_rw [thetaDerivRightTail_weighted_translate]
      exact hi.const_mul _
    have h := (thetaDeriv_integrable_const_add_Ioi
      (fun u => Real.exp (u / 2) * ‖polynomialDerivative P (fun v => (thetaDensity v : ℂ)) u‖) a 0).mpr hi'
    simpa only [add_zero] using h
  · rw [thetaDerivRightTail_weighted_integral P a ha0, mul_pow]
    have he : Real.exp (a / 2) ^ 2 = Real.exp a := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
      <;> ring
    rw [he]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (Real.exp_pos a).le

theorem thetaDerivLeftTail_weighted_integral (P : ℂ[X]) (a : ℝ) :
    halfWeightedL1 (thetaDerivLeftTail P a) = halfWeightedL1 (thetaDerivRightTail (P.comp (-X)) a) := by
  unfold halfWeightedL1
  rw [← integral_neg_eq_self (fun u => Real.exp (|u| / 2) * ‖thetaDerivLeftTail P a u‖) volume]
  simp_rw [abs_neg, thetaDerivLeftTail_reflection]

theorem thetaDerivLeftTail_weighted_l1 (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a : ℝ) (ha0 : 0 ≤ a)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a) :
    Integrable (fun u : ℝ => Real.exp (|u| / 2) * ‖thetaDerivLeftTail P a u‖) ∧
      halfWeightedL1 (thetaDerivLeftTail P a) ^ 2 ≤
        Real.exp a * thetaDerivL1Constant * thetaDerivTailWidth d a * squaredNorm (thetaDerivLeftTail P a) := by
  obtain ⟨hi, hb⟩ := thetaDerivRightTail_weighted_l1 d (P.comp (-X))
    (comp_neg_X_eq_zero_iff.not.mpr hP)
    (by simpa only [natDegree_comp, natDegree_neg, natDegree_X, mul_one] using hdegree)
    a ha0 ha hsize
  refine ⟨?_, ?_⟩
  · have h := (Measure.measurePreserving_neg volume).integrable_comp_of_integrable hi
    convert! h using 1
    funext u
    have he := thetaDerivLeftTail_reflection P a (-u)
    simp only [neg_neg] at he
    simp only [Function.comp_apply, abs_neg, ← he]
  · rw [thetaDerivLeftTail_weighted_integral, thetaDerivLeftTail_square_reflection]
    exact hb

theorem thetaDerivTails_norm_add (P : ℂ[X]) (a : ℝ) (ha : 0 ≤ a) (u : ℝ) :
    ‖thetaDerivRightTail P a u + thetaDerivLeftTail P a u‖ =
      ‖thetaDerivRightTail P a u‖ + ‖thetaDerivLeftTail P a u‖ := by
  by_cases hu : u ≤ a
  · simp only [thetaDerivRightTail_zero P a u hu, zero_add, norm_zero]
  · have hleft : -a ≤ u := by linarith [not_le.mp hu]
    simp only [thetaDerivLeftTail_zero P a u hleft, add_zero, norm_zero]

theorem thetaDeriv_width_exp_two (d : ℕ) (a : ℝ) :
    Real.exp (2 * a) * thetaDerivTailWidth d a = ((d : ℝ) + 2) / (2 * Real.pi) := by
  unfold thetaDerivTailWidth scaleT scaleZ
  field_simp
  <;> ring

theorem thetaDeriv_width_exp_bound (d : ℕ) (a : ℝ) :
    Real.exp a * thetaDerivTailWidth d a ≤ ((d : ℝ) + 2) * Real.exp (-a) := by
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hd : 0 ≤ (d : ℝ) + 2 := by positivity
  have hdiv : ((d : ℝ) + 2) / (2 * Real.pi) ≤ (d : ℝ) + 2 :=
    div_le_self hd hpi
  have he : Real.exp a = Real.exp (-a) * Real.exp (2 * a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, mul_assoc, thetaDeriv_width_exp_two]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hdiv (Real.exp_pos (-a)).le

theorem thetaDerivTails_weighted_l1 (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a : ℝ) (ha0 : 0 ≤ a)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a) :
    Integrable (fun u : ℝ => Real.exp (|u| / 2) *
      ‖thetaDerivRightTail P a u + thetaDerivLeftTail P a u‖) ∧
      halfWeightedL1 (fun u => thetaDerivRightTail P a u + thetaDerivLeftTail P a u) ^ 2 ≤
        (2 * thetaDerivL1Constant) * ((d : ℝ) + 2) * Real.exp (-a) *
          squaredNorm (fun u => thetaDerivRightTail P a u + thetaDerivLeftTail P a u) := by
  obtain ⟨hfi, hfb⟩ := thetaDerivRightTail_weighted_l1 d P hP hdegree a ha0 ha hsize
  obtain ⟨hgi, hgb⟩ := thetaDerivLeftTail_weighted_l1 d P hP hdegree a ha0 ha hsize
  have he : (fun u : ℝ => Real.exp (|u| / 2) *
      ‖thetaDerivRightTail P a u + thetaDerivLeftTail P a u‖) =
      fun u => Real.exp (|u| / 2) * ‖thetaDerivRightTail P a u‖ +
        Real.exp (|u| / 2) * ‖thetaDerivLeftTail P a u‖ := by
    funext u
    rw [thetaDerivTails_norm_add P a ha0, mul_add]
  have hsum : halfWeightedL1 (fun u => thetaDerivRightTail P a u + thetaDerivLeftTail P a u) =
      halfWeightedL1 (thetaDerivRightTail P a) + halfWeightedL1 (thetaDerivLeftTail P a) := by
    unfold halfWeightedL1
    rw [he, integral_add hfi hgi]
  refine ⟨by rw [he]; exact hfi.add hgi, ?_⟩
  rw [hsum, separated_squaredNorm (thetaDerivRightTail_memLp d P hP hdegree a ha hsize)
    (thetaDerivLeftTail_memLp d P hP hdegree a ha hsize) ha0
    (thetaDerivRightTail_zero P a) (thetaDerivLeftTail_zero P a)]
  have hn : 0 ≤ squaredNorm (thetaDerivRightTail P a) + squaredNorm (thetaDerivLeftTail P a) := by
    unfold squaredNorm
    positivity
  have hc := mul_le_mul_of_nonneg_right (thetaDeriv_width_exp_bound d a)
    (mul_nonneg thetaDerivL1Constant_pos.le hn)
  have hs := sq_nonneg (halfWeightedL1 (thetaDerivRightTail P a) - halfWeightedL1 (thetaDerivLeftTail P a))
  nlinarith [hfb, hgb, hc, hs]

theorem thetaDeriv_exteriorTail_eq_sum (P : ℂ[X]) (a : ℝ) (ha : 0 ≤ a) :
    exteriorTail a (polynomialDerivative P (fun u => (thetaDensity u : ℂ))) =
      fun u => thetaDerivRightTail P a u + thetaDerivLeftTail P a u := by
  funext u
  by_cases hu : u ≤ a
  · by_cases hl : -a ≤ u
    · simp [exteriorTail, thetaDerivRightTail, thetaDerivLeftTail, hu, hl, not_lt.mpr hu, not_lt.mpr hl]
    · have hlu : u < -a := not_le.mp hl
      simp [exteriorTail, thetaDerivRightTail, thetaDerivLeftTail, hu, hl, hlu, not_lt.mpr hu]
  · have hur : a < u := not_le.mp hu
    have hleft : -a ≤ u := by linarith
    simp [exteriorTail, thetaDerivRightTail, thetaDerivLeftTail, hu, hur, hleft, not_lt.mpr hleft]

def thetaDerivArithmeticConstant : ℝ := 4 * thetaDerivL1Constant + 41 * primeTailConstant

theorem thetaDerivArithmeticConstant_pos : 0 < thetaDerivArithmeticConstant := by
  unfold thetaDerivArithmeticConstant
  linarith [thetaDerivL1Constant_pos, primeTailConstant_nonneg]

theorem thetaDerivTails_pole_prime_bound (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a : ℝ) (ha1 : 1 ≤ a)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hslog : 40 * thetaDerivTailWidth d a ≤ Real.log 2) :
    |poleContribution (fun u => thetaDerivRightTail P a u + thetaDerivLeftTail P a u)| +
      |primeContribution (fun u => thetaDerivRightTail P a u + thetaDerivLeftTail P a u)| ≤
      thetaDerivArithmeticConstant * ((d : ℝ) + 2) * a * Real.exp (-a) *
        squaredNorm (fun u => thetaDerivRightTail P a u + thetaDerivLeftTail P a u) := by
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨hwi, hwb⟩ := thetaDerivTails_weighted_l1 d P hP hdegree a ha0 ha hsize
  have hwidth : Real.exp (2 * a) * (40 * thetaDerivTailWidth d a) ≤ 40 * ((d : ℝ) + 2) := by
    calc
      _ = 40 * (((d : ℝ) + 2) / (2 * Real.pi)) := by rw [← thetaDeriv_width_exp_two]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (div_le_self (by positivity) (by linarith [Real.pi_gt_three])) (by norm_num)
  have hb := pole_prime_bound_of_twoTail
    (thetaDerivRightTail_memLp d P hP hdegree a ha hsize)
    (thetaDerivLeftTail_memLp d P hP hdegree a ha hsize) ha1
    (show 0 ≤ 40 * thetaDerivTailWidth d a by positivity [thetaDerivTailWidth_pos d a]) hslog
    (show 1 ≤ (d : ℝ) + 2 by linarith [Nat.cast_nonneg (α := ℝ) d])
    (show (0 : ℝ) ≤ 40 by norm_num) (show 0 ≤ 2 * thetaDerivL1Constant by positivity [thetaDerivL1Constant_pos])
    hwidth (thetaDerivRightTail_zero P a) (thetaDerivLeftTail_zero P a)
    (thetaDeriv_twoTailSurvival d P hP hdegree a ha hsize) hwi hwb
  convert! hb using 1 <;> unfold thetaDerivArithmeticConstant <;> ring

theorem thetaDeriv_exteriorTail_square_pos (d : ℕ) (P : ℂ[X]) (hP : P ≠ 0)
    (hdegree : P.natDegree ≤ d) (a : ℝ) (ha0 : 0 ≤ a)
    (ha : 6 ≤ ThetaTrial.ThetaSeries.thetaQ 0 a)
    (hsize : 40 * ((d : ℝ) + 2) ≤ 3 * ThetaTrial.ThetaSeries.thetaQ 0 a) :
    0 < squaredNorm (exteriorTail a (polynomialDerivative P (fun u => (thetaDensity u : ℂ)))) := by
  rw [thetaDeriv_exteriorTail_eq_sum P a ha0,
    separated_squaredNorm (thetaDerivRightTail_memLp d P hP hdegree a ha hsize)
      (thetaDerivLeftTail_memLp d P hP hdegree a ha hsize) ha0
      (thetaDerivRightTail_zero P a) (thetaDerivLeftTail_zero P a)]
  have hp : 0 < squaredNorm (thetaDerivRightTail P a) := by
    rw [thetaDerivRightTail_square]
    exact fullTheta_tail_square_pos d P hP hdegree a ha hsize
  have hn : 0 ≤ squaredNorm (thetaDerivLeftTail P a) := integral_nonneg (fun u => sq_nonneg _)
  linarith

end ThetaTrial.Paper
