import ThetaTrial.Paper.ThetaStrip
import ThetaTrial.Paper.Contour
import ThetaTrial.Paper.ContourArcIdentity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Mode summation for the shifted theta average

A Gaussian majorant on compact substrips, built from the theta modes, and the
resulting interchange of sum and integral used in the contour estimate.
-/

noncomputable section

open Complex MeasureTheory Set Filter Metric
open scoped Topology

namespace ThetaTrial.Paper

/-- Every compact subset of the theta strip has one summable
Gaussian majorant for all its theta modes. -/
theorem complexThetaMode_compact_majorant {K : Set ℂ} (hK : IsCompact K)
    (hstrip : K ⊆ thetaStrip) :
    ∃ M : ℕ → ℝ, Summable M ∧
      ∀ n : ℕ, ∀ z ∈ K, ‖complexThetaMode n z‖ ≤ M n := by
  obtain ⟨t, ht, htlower⟩ := hK.exists_forall_le'
    (show ContinuousOn (fun z : ℂ => (Complex.exp (2 * z)).re) K by fun_prop)
    (fun z hz => exp_two_re_pos_of_mem_thetaStrip (hstrip hz))
  obtain ⟨A, hA⟩ := hK.bddAbove_image
    (show ContinuousOn (fun z : ℂ => ‖Complex.exp (9 * z / 2)‖) K by fun_prop)
  obtain ⟨B, hB⟩ := hK.bddAbove_image
    (show ContinuousOn (fun z : ℂ => ‖Complex.exp (5 * z / 2)‖) K by fun_prop)
  let M : ℕ → ℝ := fun n =>
    (4 * Real.pi ^ 2 * A) * HurwitzKernelBounds.f_nat 4 1 t n +
      (6 * Real.pi * B) * HurwitzKernelBounds.f_nat 2 1 t n
  refine ⟨M, ?_, ?_⟩
  · exact ((HurwitzKernelBounds.summable_f_nat 4 1 ht).mul_left
      (4 * Real.pi ^ 2 * A)).add
      ((HurwitzKernelBounds.summable_f_nat 2 1 ht).mul_left (6 * Real.pi * B))
  · intro n z hz
    exact complexThetaMode_norm_le n z (htlower z hz)
      (hA (mem_image_of_mem _ hz)) (hB (mem_image_of_mem _ hz))

theorem shiftWeight_norm_le_one (a y : ℝ) : ‖(shiftWeight a y : ℂ)‖ ≤ 1 := by
  have hZ : 0 < scaleZ a := mul_pos Real.pi_pos (Real.exp_pos _)
  rw [Complex.norm_real, Real.norm_eq_abs, shiftWeight,
    abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith)
    (sub_nonneg.mpr (Real.cos_le_one _))

theorem shifted_segment_mem_thetaStrip {a : ℝ} (ha : 16 ≤ scaleZ a)
    {u : ℂ} (hu : |u.im| < 1 / scaleZ a)
    {y : ℝ} (hy : y ∈ Icc (-shiftWidth a) (shiftWidth a)) :
    u + I * (y : ℂ) ∈ thetaStrip := by
  have hyabs : |y| ≤ shiftWidth a := abs_le.mpr hy
  change |(u + I * (y : ℂ)).im| < Real.pi / 4
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
  have hs := (abs_add_le u.im y).trans (add_le_add (le_refl |u.im|) hyabs)
  unfold shiftWidth at hs
  rw [one_div] at hu
  linarith

theorem weightedThetaMode_continuous (a : ℝ) (u : ℂ) (n : ℕ) :
    Continuous (fun y : ℝ =>
      (shiftWeight a y : ℂ) * complexThetaMode n (u + I * (y : ℂ))) := by
  apply Continuous.mul
  · unfold shiftWeight
    fun_prop
  · exact (complexThetaMode_differentiable n).continuous.comp (by fun_prop)

/-- Summation of the weighted mode integrals over the closed shift interval.
The strip condition covers the Cauchy disc used in the paper. -/
theorem shiftedAverage_hasSum_modes {a : ℝ} (ha : 16 ≤ scaleZ a)
    {u : ℂ} (hu : |u.im| < 1 / scaleZ a) :
    HasSum
      (fun n : ℕ => ∫ y : ℝ in Icc (-shiftWidth a) (shiftWidth a),
        (shiftWeight a y : ℂ) * complexThetaMode n (u + I * (y : ℂ)))
      (shiftedAverage a u) := by
  let J := Icc (-shiftWidth a) (shiftWidth a)
  let K := (fun y : ℝ => u + I * (y : ℂ)) '' J
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hKstrip : K ⊆ thetaStrip := by
    rintro z ⟨y, hy, rfl⟩
    exact shifted_segment_mem_thetaStrip ha hu hy
  obtain ⟨M, hM, hbound⟩ := complexThetaMode_compact_majorant hK hKstrip
  have hbound' (n : ℕ) : ∀ᵐ y ∂volume.restrict J,
      ‖(shiftWeight a y : ℂ) * complexThetaMode n (u + I * (y : ℂ))‖ ≤ M n := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    calc
      _ = ‖(shiftWeight a y : ℂ)‖ * ‖complexThetaMode n (u + I * (y : ℂ))‖ :=
        norm_mul _ _
      _ ≤ 1 * ‖complexThetaMode n (u + I * (y : ℂ))‖ :=
        mul_le_mul_of_nonneg_right (shiftWeight_norm_le_one a y) (norm_nonneg _)
      _ ≤ M n := by
        rw [one_mul]
        exact hbound n _ (mem_image_of_mem _ hy)
  have hlim : ∀ᵐ y ∂volume.restrict J,
      HasSum (fun n : ℕ => (shiftWeight a y : ℂ) *
        complexThetaMode n (u + I * (y : ℂ)))
        ((shiftWeight a y : ℂ) * complexThetaDensity (u + I * (y : ℂ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact (complexThetaMode_summable_strip
      (shifted_segment_mem_thetaStrip ha hu hy)).hasSum.mul_left (shiftWeight a y : ℂ)
  exact MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := volume.restrict J) (fun n _ => M n)
    (fun n => (weightedThetaMode_continuous a u n).aestronglyMeasurable)
    hbound' (Eventually.of_forall (fun _ => hM)) (integrable_const _) hlim

theorem shiftedAverage_eq_tsum_modes {a : ℝ} (ha : 16 ≤ scaleZ a)
    {u : ℂ} (hu : |u.im| < 1 / scaleZ a) :
    shiftedAverage a u =
      ∑' n : ℕ, ∫ y : ℝ in Icc (-shiftWidth a) (shiftWidth a),
        (shiftWeight a y : ℂ) * complexThetaMode n (u + I * (y : ℂ)) :=
  (shiftedAverage_hasSum_modes ha hu).tsum_eq.symm

/-- The disc condition implies the strip condition, so the mode-sum identity
holds on the whole closed Cauchy disc. -/
theorem shiftedAverage_hasSum_modes_disc {a : ℝ} (ha : 16 ≤ scaleZ a)
    (x : ℝ) {h : ℂ} (hh : ‖h‖ ≤ Contour.discRadius (scaleZ a)) :
    HasSum
      (fun n : ℕ => ∫ y : ℝ in Icc (-shiftWidth a) (shiftWidth a),
        (shiftWeight a y : ℂ) * complexThetaMode n ((x : ℂ) + h + I * (y : ℂ)))
      (shiftedAverage a ((x : ℂ) + h)) := by
  apply shiftedAverage_hasSum_modes ha
  exact Contour.cauchy_disc_subset_strip ha x
    (by simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left] using hh)

theorem shiftedAverage_eq_tsum_modes_disc {a : ℝ} (ha : 16 ≤ scaleZ a)
    (x : ℝ) {h : ℂ} (hh : ‖h‖ ≤ Contour.discRadius (scaleZ a)) :
    shiftedAverage a ((x : ℂ) + h) =
      ∑' n : ℕ, ∫ y : ℝ in Icc (-shiftWidth a) (shiftWidth a),
        (shiftWeight a y : ℂ) * complexThetaMode n ((x : ℂ) + h + I * (y : ℂ)) :=
  (shiftedAverage_hasSum_modes_disc ha x hh).tsum_eq.symm

end ThetaTrial.Paper
