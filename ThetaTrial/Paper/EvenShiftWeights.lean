import ThetaTrial.Paper.ShiftedAverageAnalytic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Real even densities for the imaginary-shift construction: any integrable
real density on the symmetric interval. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set
open scoped ComplexConjugate
namespace ThetaTrial.Paper

def weightedThetaAverage (b : ℝ) (w : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ y : ℝ in Icc (-b) b, (w y : ℂ) * complexThetaDensity (z + I * (y : ℂ))

def weightedShiftMultiplier (b : ℝ) (w : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ y : ℝ in Icc (-b) b, (w y : ℂ) * Complex.exp (-z * (y : ℂ))

theorem weightedThetaAverage_conj (b : ℝ) (w : ℝ → ℝ)
    (hw : ∀ y ∈ Icc (-b) b, w (-y) = w y) (z : ℂ) :
    weightedThetaAverage b w (conj z) = conj (weightedThetaAverage b w z) := by
  unfold weightedThetaAverage
  rw [← integral_conj]
  calc
    _ = ∫ y : ℝ in Icc (-b) b,
        conj ((w (-y) : ℂ) * complexThetaDensity (z + I * ((-y : ℝ) : ℂ))) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro y hy
      dsimp only
      rw [map_mul, hw y hy, Complex.conj_ofReal, ← complexThetaDensity_conj]
      congr 2
      simp
    _ = _ := integral_neg_symmetric_interval
      (fun y => conj ((w y : ℂ) * complexThetaDensity (z + I * (y : ℂ)))) b

theorem weightedThetaAverage_real (b : ℝ) (w : ℝ → ℝ)
    (hw : ∀ y ∈ Icc (-b) b, w (-y) = w y) (u : ℝ) :
    (weightedThetaAverage b w (u : ℂ)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  simpa only [Complex.conj_ofReal] using (weightedThetaAverage_conj b w hw (u : ℂ)).symm

theorem weightedThetaAverage_even {b : ℝ} (hb : b < Real.pi / 4)
    (w : ℝ → ℝ) (hw : ∀ y ∈ Icc (-b) b, w (-y) = w y) :
    Function.Even (fun u : ℝ => weightedThetaAverage b w (u : ℂ)) := by
  intro u
  unfold weightedThetaAverage
  calc
    _ = ∫ y : ℝ in Icc (-b) b,
        (w (-y) : ℂ) * complexThetaDensity ((u : ℂ) + I * ((-y : ℝ) : ℂ)) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro y hy
      dsimp only
      rw [hw y hy]
      congr 1
      have hh : (u : ℂ) + I * ((-y : ℝ) : ℂ) ∈ thetaStrip := by
        change |(((u : ℂ) + I * ((-y : ℝ) : ℂ)).im)| < Real.pi / 4
        simpa using (abs_le.mpr hy).trans_lt hb
      have he := complexThetaDensity_neg hh
      have hearg : -((u : ℂ) + I * ((-y : ℝ) : ℂ)) = ((-u : ℝ) : ℂ) + I * (y : ℂ) := by
        push_cast
        ring
      rw [hearg] at he
      exact he
    _ = _ := integral_neg_symmetric_interval
      (fun y => (w y : ℂ) * complexThetaDensity ((u : ℂ) + I * (y : ℂ))) b

theorem weightedShiftMultiplier_neg (b : ℝ) (w : ℝ → ℝ)
    (hw : ∀ y ∈ Icc (-b) b, w (-y) = w y) (z : ℂ) :
    weightedShiftMultiplier b w (-z) = weightedShiftMultiplier b w z := by
  unfold weightedShiftMultiplier
  calc
    _ = ∫ y : ℝ in Icc (-b) b, (w (-y) : ℂ) * Complex.exp (-z * ((-y : ℝ) : ℂ)) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro y hy
      simp only [hw y hy, neg_neg, Complex.ofReal_neg, mul_neg, neg_mul]
    _ = _ := integral_neg_symmetric_interval
      (fun y => (w y : ℂ) * Complex.exp (-z * (y : ℂ))) b

theorem weightedShiftMultiplier_plus (b : ℝ) (w : ℝ → ℝ)
    (hw : ∀ y ∈ Icc (-b) b, w (-y) = w y) (z : ℂ) :
    weightedShiftMultiplier b w z =
      ∫ y : ℝ in Icc (-b) b, (w y : ℂ) * Complex.exp (z * (y : ℂ)) := by
  simpa only [weightedShiftMultiplier, neg_neg] using
    (weightedShiftMultiplier_neg b w hw z).symm

theorem weightedShiftMultiplier_integrable (b : ℝ) (w : ℝ → ℝ)
    (hi : IntegrableOn w (Icc (-b) b)) (z : ℂ) :
    IntegrableOn (fun y : ℝ => (w y : ℂ) * Complex.exp (-z * (y : ℂ))) (Icc (-b) b) := by
  have hic : IntegrableOn (fun y => (w y : ℂ)) (Icc (-b) b) := hi.ofReal
  exact hic.mul_continuousOn (by fun_prop) isCompact_Icc

theorem weightedShiftMultiplier_cosh (b : ℝ) (w : ℝ → ℝ)
    (hi : IntegrableOn w (Icc (-b) b))
    (hw : ∀ y ∈ Icc (-b) b, w (-y) = w y) (z : ℂ) :
    weightedShiftMultiplier b w z =
      ∫ y : ℝ in Icc (-b) b, (w y : ℂ) * Complex.cosh (z * (y : ℂ)) := by
  have h := integral_add (weightedShiftMultiplier_integrable b w hi z)
    (weightedShiftMultiplier_integrable b w hi (-z))
  have he : (fun y : ℝ => (w y : ℂ) * Complex.exp (-z * (y : ℂ)) +
      (w y : ℂ) * Complex.exp (-(-z) * (y : ℂ))) =
      (fun y : ℝ => (2 : ℂ) * ((w y : ℂ) * Complex.cosh (z * (y : ℂ)))) := by
    funext y
    simp only [Complex.cosh, neg_mul, neg_neg]
    ring
  rw [he, integral_const_mul] at h
  change _ = weightedShiftMultiplier b w z + weightedShiftMultiplier b w (-z) at h
  rw [weightedShiftMultiplier_neg b w hw] at h
  linear_combination -h / 2

theorem weightedShiftMultiplier_real (b : ℝ) (w : ℝ → ℝ)
    (hi : IntegrableOn w (Icc (-b) b))
    (hw : ∀ y ∈ Icc (-b) b, w (-y) = w y) (r : ℝ) :
    weightedShiftMultiplier b w (r : ℂ) =
      ((∫ y : ℝ in Icc (-b) b, w y * Real.cosh (r * y) : ℝ) : ℂ) := by
  rw [weightedShiftMultiplier_cosh b w hi hw, ← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Icc
  intro y hy
  push_cast
  rfl

theorem weightedShiftMultiplier_real_ge_zero_value (b : ℝ) (w : ℝ → ℝ)
    (hi : IntegrableOn w (Icc (-b) b))
    (hw : ∀ y ∈ Icc (-b) b, w (-y) = w y)
    (hpos : ∀ y ∈ Icc (-b) b, 0 ≤ w y) (r : ℝ) :
    (weightedShiftMultiplier b w 0).re ≤ (weightedShiftMultiplier b w (r : ℂ)).re := by
  rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by rfl,
    weightedShiftMultiplier_real b w hi hw, weightedShiftMultiplier_real b w hi hw]
  simp only [Complex.ofReal_re, zero_mul, Real.cosh_zero, mul_one]
  apply setIntegral_mono_on hi (hi.mul_continuousOn (by fun_prop) isCompact_Icc) measurableSet_Icc
  intro y hy
  exact le_mul_of_one_le_right (hpos y hy) (Real.one_le_cosh _)

end ThetaTrial.Paper
