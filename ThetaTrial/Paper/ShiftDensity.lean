import ThetaTrial.Paper.ComplexShiftMeasure
import ThetaTrial.Paper.EvenShiftWeights
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Lebesgue

/-! Identification of an arbitrary integrable real shift density with
the finite complex-measure construction. No smoothness of the density is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set
open scoped ComplexConjugate

namespace ThetaTrial.Paper.ShiftDensity

/-- The finite complex measure `w(y)dy`, restricted to the shift interval. -/
def densityMeasure (b : ℝ) (w : ℝ → ℝ) : ComplexMeasure ℝ :=
  SignedMeasure.toComplexMeasure ((volume.restrict (Icc (-b) b)).withDensityᵥ w) 0

theorem densityMeasure_eq_withDensity (b : ℝ) (w : ℝ → ℝ)
    (hw : IntegrableOn w (Icc (-b) b)) :
    densityMeasure b w = (volume.restrict (Icc (-b) b)).withDensityᵥ (fun y => (w y : ℂ)) := by
  ext s hs
  rw [densityMeasure, SignedMeasure.toComplexMeasure_apply,
    withDensityᵥ_apply hw hs, withDensityᵥ_apply hw.ofReal hs]
  rw [integral_complex_ofReal]
  rfl

theorem signed_density_jordan_pos {ν : Measure ℝ} {w : ℝ → ℝ}
    (hw : Measurable w) (hi : Integrable w ν) :
    (SignedMeasure.toJordanDecomposition (ν.withDensityᵥ w)).posPart = ν.withDensity (fun y => ENNReal.ofReal (w y)) := by
  have h := SignedMeasure.toJordanDecomposition_eq_of_eq_add_withDensity
    (s := ν.withDensityᵥ w) (t := 0) hw hi VectorMeasure.MutuallySingular.zero_left (by simp)
  simpa only [SignedMeasure.toJordanDecomposition_zero, JordanDecomposition.zero_posPart, zero_add]
    using congrArg JordanDecomposition.posPart h

theorem signed_density_jordan_neg {ν : Measure ℝ} {w : ℝ → ℝ}
    (hw : Measurable w) (hi : Integrable w ν) :
    (SignedMeasure.toJordanDecomposition (ν.withDensityᵥ w)).negPart = ν.withDensity (fun y => ENNReal.ofReal (-w y)) := by
  have h := SignedMeasure.toJordanDecomposition_eq_of_eq_add_withDensity
    (s := ν.withDensityᵥ w) (t := 0) hw hi VectorMeasure.MutuallySingular.zero_left (by simp)
  simpa only [SignedMeasure.toJordanDecomposition_zero, JordanDecomposition.zero_negPart, zero_add]
    using congrArg JordanDecomposition.negPart h

theorem integral_density_measurable (b : ℝ) (w : ℝ → ℝ)
    (hw : Measurable w) (hi : IntegrableOn w (Icc (-b) b))
    (f : ℝ → ℂ) (hf : ContinuousOn f (Icc (-b) b)) :
    ComplexShiftMeasure.integral (densityMeasure b w) b f =
      ∫ y : ℝ in Icc (-b) b, (w y : ℂ) * f y := by
  unfold ComplexShiftMeasure.integral densityMeasure
  rw [SignedMeasure.re_toComplexMeasure, SignedMeasure.im_toComplexMeasure,
    SignedMeasure.toJordanDecomposition_zero, signed_density_jordan_pos hw hi,
    signed_density_jordan_neg hw hi]
  simp only [JordanDecomposition.zero_posPart, JordanDecomposition.zero_negPart,
    Measure.restrict_zero, integral_zero_measure, sub_self, mul_zero, add_zero]
  rw [restrict_withDensity measurableSet_Icc,
    restrict_withDensity measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    inter_self]
  rw [integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
      (by simp) f,
    integral_withDensity_eq_integral_toReal_smul (show Measurable (fun y => ENNReal.ofReal (-w y)) from hw.neg.ennreal_ofReal)
      (by simp) f]
  simp only [ENNReal.toReal_ofReal', Complex.real_smul]
  have hpc : IntegrableOn (fun y => ((max (w y) 0 : ℝ) : ℂ)) (Icc (-b) b) := hi.pos_part.ofReal
  have hnc : IntegrableOn (fun y => ((max (-w y) 0 : ℝ) : ℂ)) (Icc (-b) b) := hi.neg_part.ofReal
  have hp := hpc.mul_continuousOn hf isCompact_Icc
  have hn := hnc.mul_continuousOn hf isCompact_Icc
  rw [← integral_sub hp hn]
  apply setIntegral_congr_fun measurableSet_Icc
  intro y hy
  change ((max (w y) 0 : ℝ) : ℂ) * f y - ((max (-w y) 0 : ℝ) : ℂ) * f y = _
  rw [← sub_mul, ← Complex.ofReal_sub, max_zero_sub_max_neg_zero_eq_self]

theorem integral_density (b : ℝ) (w : ℝ → ℝ)
    (hi : IntegrableOn w (Icc (-b) b)) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Icc (-b) b)) :
    ComplexShiftMeasure.integral (densityMeasure b w) b f =
      ∫ y : ℝ in Icc (-b) b, (w y : ℂ) * f y := by
  let v := hi.aestronglyMeasurable.mk w
  have hvm : Measurable v := hi.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have he : w =ᵐ[volume.restrict (Icc (-b) b)] v := hi.aestronglyMeasurable.ae_eq_mk
  have hv : IntegrableOn v (Icc (-b) b) := hi.congr he
  have hm : densityMeasure b w = densityMeasure b v := by
    unfold densityMeasure
    rw [WithDensityᵥEq.congr_ae he]
  rw [hm, integral_density_measurable b v hvm hv f hf]
  apply integral_congr_ae
  filter_upwards [he] with y hy
  rw [hy]

theorem source_density {b : ℝ} (w : ℝ → ℝ)
    (hi : IntegrableOn w (Icc (-b) b)) {z : ℂ}
    (hz : z ∈ ShiftMeasure.shiftStrip b) :
    ComplexShiftMeasure.source (densityMeasure b w) b z = weightedThetaAverage b w z := by
  simpa only [ComplexShiftMeasure.source, ComplexShiftMeasure.jet, iteratedDeriv_zero,
    weightedThetaAverage] using integral_density b w hi
      (fun y => complexThetaDensity (z + I * (y : ℂ)))
      (ShiftMeasure.shiftJet_integrand_continuousOn hz 0)

theorem source_density_real {b : ℝ} (hbpi : b < Real.pi / 4) (w : ℝ → ℝ)
    (hi : IntegrableOn w (Icc (-b) b)) (u : ℝ) :
    ComplexShiftMeasure.source (densityMeasure b w) b (u : ℂ) =
      weightedThetaAverage b w (u : ℂ) :=
  source_density w hi (ShiftMeasure.real_mem_shiftStrip hbpi u)

theorem multiplier_density (b : ℝ) (w : ℝ → ℝ)
    (hi : IntegrableOn w (Icc (-b) b)) (z : ℂ) :
    ComplexShiftMeasure.multiplier (densityMeasure b w) b z = weightedShiftMultiplier b w z := by
  exact integral_density b w hi (fun y => Complex.exp (-z * (y : ℂ))) (by fun_prop)

end ThetaTrial.Paper.ShiftDensity

#print axioms ThetaTrial.Paper.ShiftDensity.source_density_real
#print axioms ThetaTrial.Paper.ShiftDensity.multiplier_density
