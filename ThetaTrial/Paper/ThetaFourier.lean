import ThetaTrial.Paper.Definitions
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! The Fourier transform of the theta density, in the normalization of the paper. All exponential
integrability follows from the estimates in `ThetaSeries`. -/

noncomputable section
open Complex MeasureTheory Set

namespace ThetaTrial.Paper

def thetaExponential (z : ℂ) (u : ℝ) : ℂ :=
  (thetaDensity u : ℂ) * Complex.exp ((u : ℂ) * z)

theorem thetaExponential_neg (z : ℂ) (u : ℝ) :
    thetaExponential z (-u) = thetaExponential (-z) u := by
  simp [thetaExponential]

theorem thetaExponential_integrableOn_pos (z : ℂ) :
    IntegrableOn (thetaExponential z) (Ioi 0) := by
  have h := ThetaTrial.ThetaSeries.thetaPhi_mul_integrable ‖z‖
    (v := fun u : ℝ => Complex.exp ((u : ℂ) * z)) (by fun_prop) (by
      intro u hu
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      nlinarith [mul_le_mul_of_nonneg_left (Complex.re_le_norm z) hu])
  have h2 : IntegrableOn (fun u : ℝ => (2 : ℂ) *
      ((ThetaTrial.ThetaSeries.thetaPhi u : ℂ) * Complex.exp ((u : ℂ) * z))) (Ioi 0) :=
    h.const_mul (2 : ℂ)
  apply h2.congr_fun _ measurableSet_Ioi
  intro u hu
  simp [thetaExponential, thetaDensity_eq_of_nonneg hu.le, mul_assoc]

theorem thetaExponential_integrableOn_neg (z : ℂ) :
    IntegrableOn (thetaExponential z) (Iic 0) := by
  rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
  let m : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).measurableEmbedding
  rw [m.integrableOn_map_iff]
  simp_rw [Function.comp_def, thetaExponential_neg, neg_preimage, neg_Iic, neg_zero]
  exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
    (thetaExponential_integrableOn_pos (-z))

theorem thetaExponential_integrable (z : ℂ) :
    Integrable (thetaExponential z) := by
  have h := (thetaExponential_integrableOn_neg z).union
    (thetaExponential_integrableOn_pos z)
  simpa using h

theorem thetaExponential_integral (z : ℂ) :
    (∫ u : ℝ, thetaExponential z u) = ThetaTrial.xi (1 / 2 + z) := by
  have hn : (∫ u : ℝ in Iic 0, thetaExponential z u) =
      ∫ u : ℝ in Ioi 0, thetaExponential (-z) u := by
    simpa only [thetaExponential_neg, neg_neg, neg_zero] using
      (integral_comp_neg_Iic 0 (thetaExponential (-z)))
  calc
    _ = (∫ u : ℝ in Iic 0, thetaExponential z u) +
        ∫ u : ℝ in Ioi 0, thetaExponential z u := by
      rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        (thetaExponential_integrableOn_neg z) (thetaExponential_integrableOn_pos z),
        Iic_union_Ioi, Measure.restrict_univ]
    _ = ∫ u : ℝ in Ioi 0,
        thetaExponential (-z) u + thetaExponential z u := by
      rw [hn, integral_add (thetaExponential_integrableOn_pos (-z))
        (thetaExponential_integrableOn_pos z)]
    _ = ∫ u : ℝ in Ioi 0,
        (4 : ℂ) * ((ThetaTrial.ThetaSeries.thetaPhi u : ℂ) * Complex.cosh ((u : ℂ) * z)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      simp only [thetaExponential, thetaDensity_eq_of_nonneg hu.le,
        Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.cosh, mul_neg]
      ring
    _ = ThetaTrial.xi (1 / 2 + z) := by
      rw [integral_const_mul, ThetaTrial.ThetaSeries.xi_centered_eq_thetaPhi]

theorem paperFourier_theta_integrable (z : ℂ) :
    Integrable (fun u : ℝ => (thetaDensity u : ℂ) *
      Complex.exp (-I * z * (u : ℂ))) := by
  have he : (fun u : ℝ => thetaExponential (-I * z) u) =
      (fun u : ℝ => (thetaDensity u : ℂ) * Complex.exp (-I * z * (u : ℂ))) := by
    funext u
    simp [thetaExponential, mul_comm]
  rw [← he]
  exact thetaExponential_integrable (-I * z)

/-- The theta density has the paper's unnormalized Fourier transform. -/
theorem paperFourier_theta (z : ℂ) :
    paperFourier (fun u => (thetaDensity u : ℂ)) z = xiFunction z := by
  have h := thetaExponential_integral (-I * z)
  have he : (fun u : ℝ => thetaExponential (-I * z) u) =
      (fun u : ℝ => (thetaDensity u : ℂ) * Complex.exp (-I * z * (u : ℂ))) := by
    funext u
    simp [thetaExponential, mul_comm]
  rw [he] at h
  change _ = _ at h
  rw [paperFourier, h, xiFunction_eq_weilFormula]
  change ThetaTrial.xi (1 / 2 + -I * z) = ThetaTrial.xi (1 / 2 - I * z)
  congr 1
  ring

end ThetaTrial.Paper
