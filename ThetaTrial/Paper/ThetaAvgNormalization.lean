import ThetaTrial.Paper.ThetaAvgEnergy
import ThetaTrial.Paper.ThetaAvgRadical

/-! Real-even normalized theta trial vectors. -/

noncomputable section
open Complex MeasureTheory Set Polynomial

namespace ThetaTrial.Paper

def thetaAvgWindowTrial (a : ℝ) : ℝ → ℂ :=
  windowCut a (fun u : ℝ => shiftedAverage a (u : ℂ))

def thetaAvgNormalizationFactor (a : ℝ) : ℝ :=
  1 / Real.sqrt (squaredNorm (thetaAvgWindowTrial a))

def thetaAvgNormalizedTrial (a : ℝ) (u : ℝ) : ℂ :=
  (thetaAvgNormalizationFactor a : ℂ) * thetaAvgWindowTrial a u

theorem polynomialDerivative_one (f : ℝ → ℂ) : polynomialDerivative (1 : ℂ[X]) f = f := by
  have hs : (1 : ℂ[X]).support = {0} := by
    simpa only [map_one] using Polynomial.support_C (by norm_num : (1 : ℂ) ≠ 0)
  funext x
  simp [polynomialDerivative, hs]

theorem squaredNorm_const_mul (c : ℂ) (f : ℝ → ℂ) :
    squaredNorm (fun u => c * f u) = ‖c‖ ^ 2 * squaredNorm f := by
  unfold squaredNorm
  simp_rw [norm_mul, mul_pow]
  exact integral_const_mul _ _

theorem InWindowFormDomain.const_mul {a : ℝ} {f : ℝ → ℂ}
    (hf : InWindowFormDomain a f) (c : ℂ) :
    InWindowFormDomain a (fun u => c * f u) := by
  refine ⟨?_, hf.2.1.const_mul c, ?_⟩
  · intro u hu
    apply hf.1
    intro hzero
    exact hu (by simp only [hzero, mul_zero])
  · have he : (fun r : ℝ => Real.log (2 + |r|) *
        ‖paperFourier (fun u => c * f u) r‖ ^ 2) =
        fun r : ℝ => ‖c‖ ^ 2 * (Real.log (2 + |r|) * ‖paperFourier f r‖ ^ 2) := by
      funext r
      rw [paperFourier_const_mul, norm_mul, mul_pow]
      ring
    rw [he]
    exact hf.2.2.const_mul _

theorem thetaAvgWindowTrial_even {a : ℝ} (hZ : 16 ≤ scaleZ a) : Function.Even (thetaAvgWindowTrial a) := by
  intro u
  have he : shiftedAverage a ((-u : ℝ) : ℂ) = shiftedAverage a (u : ℂ) := by
    have hu : |(u : ℂ).im| < 1 / scaleZ a := by
      simp only [Complex.ofReal_im, abs_zero]
      exact one_div_pos.mpr (scaleZ_pos a)
    simpa only [Complex.ofReal_neg] using shiftedAverage_neg hZ hu
  have hi : -u ∈ Icc (-a) a ↔ u ∈ Icc (-a) a := by
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  by_cases hu : u ∈ Icc (-a) a
  · simp only [thetaAvgWindowTrial, windowCut, indicator_of_mem hu, indicator_of_mem (hi.mpr hu), he]
  · simp only [thetaAvgWindowTrial, windowCut, indicator_of_notMem hu,
      indicator_of_notMem (mt hi.mp hu)]

theorem thetaAvgWindowTrial_real {a : ℝ} (hZ : 16 ≤ scaleZ a) (u : ℝ) :
    (thetaAvgWindowTrial a u).im = 0 := by
  by_cases hu : u ∈ Icc (-a) a
  · simp only [thetaAvgWindowTrial, windowCut, indicator_of_mem hu]
    exact shiftedAverage_real hZ u
  · simp [thetaAvgWindowTrial, windowCut, hu]

theorem thetaAvgNormalizedTrial_even {a : ℝ} (hZ : 16 ≤ scaleZ a) :
    Function.Even (thetaAvgNormalizedTrial a) := by
  intro u
  unfold thetaAvgNormalizedTrial
  rw [thetaAvgWindowTrial_even hZ u]

theorem thetaAvgNormalizedTrial_real {a : ℝ} (hZ : 16 ≤ scaleZ a) (u : ℝ) :
    (thetaAvgNormalizedTrial a u).im = 0 := by
  simp only [thetaAvgNormalizedTrial, Complex.mul_im, Complex.ofReal_im,
    thetaAvgWindowTrial_real hZ u, mul_zero, zero_mul, add_zero]

theorem thetaAvgNormalizationFactor_pos {a : ℝ} (hN : 0 < squaredNorm (thetaAvgWindowTrial a)) :
    0 < thetaAvgNormalizationFactor a :=
  one_div_pos.mpr (Real.sqrt_pos.mpr hN)

theorem thetaAvgNormalizationFactor_norm_sq {a : ℝ}
    (hN : 0 < squaredNorm (thetaAvgWindowTrial a)) :
    ‖(thetaAvgNormalizationFactor a : ℂ)‖ ^ 2 = 1 / squaredNorm (thetaAvgWindowTrial a) := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (thetaAvgNormalizationFactor_pos hN)]
  unfold thetaAvgNormalizationFactor
  rw [div_pow, one_pow, Real.sq_sqrt hN.le]

theorem thetaAvgNormalizedTrial_squaredNorm {a : ℝ}
    (hN : 0 < squaredNorm (thetaAvgWindowTrial a)) : squaredNorm (thetaAvgNormalizedTrial a) = 1 := by
  unfold thetaAvgNormalizedTrial
  rw [squaredNorm_const_mul, thetaAvgNormalizationFactor_norm_sq hN]
  exact one_div_mul_cancel hN.ne'

theorem thetaAvgWindowTrial_hardCutoff {a : ℝ} (ha : 0 ≤ a) (hZ : 16 ≤ scaleZ a) :
    fullWeilForm (thetaAvgWindowTrial a) =
      fullWeilForm (exteriorTail a (fun u : ℝ => shiftedAverage a (u : ℂ))) := by
  simpa only [polynomialDerivative_one, thetaAvgWindowTrial] using
    polynomialDerivative_shiftedAverage_hardCutoff ha hZ (1 : ℂ[X]) ha

end ThetaTrial.Paper
