import ThetaTrial.Paper.ShiftedAverageBound
import ThetaTrial.Paper.ThetaStripDecay
import ThetaTrial.Paper.Multiplier
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Holomorphy and symmetries of the shifted theta average

Differentiation under the integral sign is justified by a uniform bound for
the theta derivative on a compact subset of its holomorphy strip.
-/

noncomputable section
open Complex MeasureTheory Set Filter Metric
open scoped Topology ComplexConjugate Interval

namespace ThetaTrial.Paper

theorem weighted_shift_continuousOn {a : ℝ} (ha : 16 ≤ scaleZ a)
    {u : ℂ} (hu : |u.im| < 1 / scaleZ a) {f : ℂ → ℂ}
    (hf : ContinuousOn f thetaStrip) :
    ContinuousOn (fun y : ℝ => (shiftWeight a y : ℂ) * f (u + I * (y : ℂ)))
      (Icc (-shiftWidth a) (shiftWidth a)) := by
  apply ContinuousOn.mul
  · unfold shiftWeight
    fun_prop
  · exact hf.comp (by fun_prop) (fun y hy => shifted_segment_mem_thetaStrip ha hu hy)

theorem shiftedAverage_differentiableOn {a : ℝ} (ha : 16 ≤ scaleZ a) :
    DifferentiableOn ℂ (shiftedAverage a) {z : ℂ | |z.im| < 1 / scaleZ a} := by
  let U : Set ℂ := {z : ℂ | |z.im| < 1 / scaleZ a}
  let J := Icc (-shiftWidth a) (shiftWidth a)
  have hU : IsOpen U := isOpen_lt (by fun_prop) continuous_const
  have hd := complexThetaDensity_differentiableOn_strip
  have hd' := hd.deriv isOpen_thetaStrip
  intro z hz
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  let r := ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hdisc : closedBall z r ⊆ U := by
    intro w hw
    apply hεsub
    rw [Metric.mem_ball]
    have hw' := Metric.mem_closedBall.mp hw
    dsimp [r] at hw'
    linarith
  let K := (fun p : ℂ × ℝ => p.1 + I * (p.2 : ℂ)) '' (closedBall z r ×ˢ J)
  have hK : IsCompact K :=
    ((isCompact_closedBall z r).prod (isCompact_Icc : IsCompact J)).image (by fun_prop)
  have hKstrip : K ⊆ thetaStrip := by
    rintro v ⟨⟨w, y⟩, ⟨hw, hy⟩, rfl⟩
    exact shifted_segment_mem_thetaStrip ha (hdisc hw) hy
  obtain ⟨C, hC⟩ := hK.bddAbove_image (hd'.continuousOn.norm.mono hKstrip)
  have hmeas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable
      (fun y : ℝ => (shiftWeight a y : ℂ) * complexThetaDensity (w + I * (y : ℂ)))
      (volume.restrict J) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (weighted_shift_continuousOn ha hw hd.continuousOn).aestronglyMeasurable
      measurableSet_Icc
  have hbase : Integrable
      (fun y : ℝ => (shiftWeight a y : ℂ) * complexThetaDensity (z + I * (y : ℂ)))
      (volume.restrict J) :=
    (weighted_shift_continuousOn ha hz hd.continuousOn).integrableOn_Icc
  have hdmeas : AEStronglyMeasurable
      (fun y : ℝ => (shiftWeight a y : ℂ) * deriv complexThetaDensity (z + I * (y : ℂ)))
      (volume.restrict J) :=
    (weighted_shift_continuousOn ha hz hd'.continuousOn).aestronglyMeasurable measurableSet_Icc
  have hbound : ∀ᵐ y ∂volume.restrict J, ∀ w ∈ ball z r,
      ‖(shiftWeight a y : ℂ) * deriv complexThetaDensity (w + I * (y : ℂ))‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy w hw
    calc
      _ = ‖(shiftWeight a y : ℂ)‖ * ‖deriv complexThetaDensity (w + I * (y : ℂ))‖ :=
        norm_mul _ _
      _ ≤ 1 * ‖deriv complexThetaDensity (w + I * (y : ℂ))‖ :=
        mul_le_mul_of_nonneg_right (shiftWeight_norm_le_one a y) (norm_nonneg _)
      _ ≤ C := by
        rw [one_mul]
        exact hC (mem_image_of_mem _ (mem_image_of_mem _
          (show (w, y) ∈ closedBall z r ×ˢ J from ⟨ball_subset_closedBall hw, hy⟩)))
  have hdiff : ∀ᵐ y ∂volume.restrict J, ∀ w ∈ ball z r,
      HasDerivAt (fun v : ℂ =>
        (shiftWeight a y : ℂ) * complexThetaDensity (v + I * (y : ℂ)))
        ((shiftWeight a y : ℂ) * deriv complexThetaDensity (w + I * (y : ℂ))) w := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy w hw
    have hs := shifted_segment_mem_thetaStrip ha (hdisc (ball_subset_closedBall hw)) hy
    have hder := (hd.differentiableAt (isOpen_thetaStrip.mem_nhds hs)).hasDerivAt
    simpa only [mul_one, Function.comp_def, id_eq] using!
      (hder.comp w ((hasDerivAt_id w).add_const (I * (y : ℂ)))).const_mul
        (shiftWeight a y : ℂ)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict J) (s := ball z r) (bound := fun _ => C)
    (ball_mem_nhds z hr) hmeas hbase hdmeas hbound (integrable_const _) hdiff).2.differentiableAt.differentiableWithinAt

theorem shiftedAverage_analyticOnNhd {a : ℝ} (ha : 16 ≤ scaleZ a) :
    AnalyticOnNhd ℂ (shiftedAverage a) {z : ℂ | |z.im| < 1 / scaleZ a} :=
  (shiftedAverage_differentiableOn ha).analyticOnNhd
    (isOpen_lt (by fun_prop) continuous_const)

theorem complexThetaMode_conj (n : ℕ) (z : ℂ) :
    complexThetaMode n (conj z) = conj (complexThetaMode n z) := by
  simp [complexThetaMode, ← Complex.exp_conj, Complex.conj_ofNat]

theorem complexThetaDensity_conj (z : ℂ) :
    complexThetaDensity (conj z) = conj (complexThetaDensity z) := by
  unfold complexThetaDensity
  rw [Complex.conj_tsum]
  exact tsum_congr (fun n => complexThetaMode_conj n z)

theorem setIntegral_symmetric_neg (f : ℝ → ℂ) {b : ℝ} (hb : 0 ≤ b) :
    (∫ y : ℝ in Icc (-b) b, f (-y)) = ∫ y : ℝ in Icc (-b) b, f y := by
  have hbb : -b ≤ b := by linarith
  simp only [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hbb]
  simpa only [neg_neg] using
    (intervalIntegral.integral_comp_neg (f := f) (a := -b) (b := b))

theorem shiftedAverage_conj {a : ℝ} (ha : 16 ≤ scaleZ a) (z : ℂ) :
    shiftedAverage a (conj z) = conj (shiftedAverage a z) := by
  unfold shiftedAverage
  rw [← integral_conj]
  calc
    _ = ∫ y : ℝ in Icc (-shiftWidth a) (shiftWidth a),
        conj ((shiftWeight a (-y) : ℂ) *
          complexThetaDensity (z + I * ((-y : ℝ) : ℂ))) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro y _
      dsimp only
      rw [map_mul, shiftWeight_neg, Complex.conj_ofReal,
        ← complexThetaDensity_conj]
      congr 2
      simp
    _ = _ := setIntegral_symmetric_neg
      (fun y => conj ((shiftWeight a y : ℂ) * complexThetaDensity (z + I * (y : ℂ))))
      (ContourArcIdentity.shiftWidth_arc_bounds ha).1

theorem shiftedAverage_real {a : ℝ} (ha : 16 ≤ scaleZ a) (x : ℝ) :
    (shiftedAverage a (x : ℂ)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  simpa only [Complex.conj_ofReal] using (shiftedAverage_conj ha (x : ℂ)).symm

theorem shiftedAverage_neg {a : ℝ} (ha : 16 ≤ scaleZ a) {z : ℂ}
    (hz : |z.im| < 1 / scaleZ a) :
    shiftedAverage a (-z) = shiftedAverage a z := by
  unfold shiftedAverage
  calc
    _ = ∫ y : ℝ in Icc (-shiftWidth a) (shiftWidth a),
        (shiftWeight a (-y) : ℂ) *
          complexThetaDensity (z + I * ((-y : ℝ) : ℂ)) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro y hy
      dsimp only
      rw [shiftWeight_neg]
      congr 1
      have hyneg : -y ∈ Icc (-shiftWidth a) (shiftWidth a) := by
        constructor <;> linarith [hy.1, hy.2]
      have heq : -z + I * (y : ℂ) = -(z + I * ((-y : ℝ) : ℂ)) := by
        push_cast
        ring
      rw [heq]
      exact complexThetaDensity_neg (shifted_segment_mem_thetaStrip ha hz hyneg)
    _ = _ := setIntegral_symmetric_neg
      (fun y => (shiftWeight a y : ℂ) * complexThetaDensity (z + I * (y : ℂ)))
      (ContourArcIdentity.shiftWidth_arc_bounds ha).1

end ThetaTrial.Paper
