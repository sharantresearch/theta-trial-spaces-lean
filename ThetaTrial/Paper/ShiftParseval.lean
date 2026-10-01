import ThetaTrial.Paper.LogUncertainty
import ThetaTrial.GammaEnergy.Fourier

/-!
# Translation Parseval for L1 and L2 functions

No smoothness or compact support is needed.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace ThetaTrial.Paper.ShiftParseval

open LogUncertainty

theorem paperFourier_translate (f : ℝ → ℂ) (h r : ℝ) :
    paperFourier (fun u => f (u + h)) r =
      Complex.exp (Complex.I * ((h * r : ℝ) : ℂ)) * paperFourier f r := by
  simp only [paperFourier_eq_integral]
  have hshift : (∫ u : ℝ, f (u + h) *
      Complex.exp (-Complex.I * (r : ℂ) * (u : ℂ))) =
      ∫ u : ℝ, f u * Complex.exp (-Complex.I * (r : ℂ) * ((u - h : ℝ) : ℂ)) := by
    simpa only [add_sub_cancel_right] using
      (integral_add_right_eq_self
        (fun u : ℝ => f u * Complex.exp (-Complex.I * (r : ℂ) * ((u - h : ℝ) : ℂ))) h)
  rw [hshift]
  have heq (u : ℝ) :
      f u * Complex.exp (-Complex.I * (r : ℂ) * ((u - h : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((h * r : ℝ) : ℂ)) *
        (f u * Complex.exp (-Complex.I * (r : ℂ) * (u : ℂ))) := by
    rw [mul_left_comm, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [heq]
  exact integral_const_mul _ _

theorem paperFourier_add {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) (r : ℝ) :
    paperFourier (fun u => f u + g u) r = paperFourier f r + paperFourier g r := by
  simp only [paperFourier, Real.fourier_eq, smul_add]
  exact integral_add ((Real.fourierIntegral_convergent_iff _).mpr hf)
    ((Real.fourierIntegral_convergent_iff _).mpr hg)

theorem paperFourier_sub {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) (r : ℝ) :
    paperFourier (fun u => f u - g u) r = paperFourier f r - paperFourier g r := by
  simp only [paperFourier, Real.fourier_eq, smul_sub]
  exact integral_sub ((Real.fourierIntegral_convergent_iff _).mpr hf)
    ((Real.fourierIntegral_convergent_iff _).mpr hg)

theorem paperFourier_translate_sub {f : ℝ → ℂ}
    (hf : Integrable f) (h r : ℝ) :
    paperFourier (fun u => f (u + h) - f u) r =
      (Complex.exp (Complex.I * ((h * r : ℝ) : ℂ)) - 1) * paperFourier f r := by
  rw [paperFourier_sub (hf.comp_add_right h) hf, paperFourier_translate]
  ring

theorem paperFourier_translate_sub_norm_sq {f : ℝ → ℂ}
    (hf : Integrable f) (h r : ℝ) :
    ‖paperFourier (fun u => f (u + h) - f u) r‖ ^ 2 =
      2 * (1 - Real.cos (h * r)) * ‖paperFourier f r‖ ^ 2 := by
  rw [paperFourier_translate_sub hf, norm_mul, mul_pow,
    ThetaTrial.GammaEnergy.norm_phase_sub_one_sq]

theorem shift_memLp {f : ℝ → ℂ} (hf2 : MemLp f 2) (h : ℝ) :
    MemLp (fun u => f (u + h) - f u) 2 := by
  exact (hf2.comp_measurePreserving (measurePreserving_add_right volume h)).sub hf2

theorem shift_sq_integrable {f : ℝ → ℂ} (hf2 : MemLp f 2) (h : ℝ) :
    Integrable (fun u => ‖f (u + h) - f u‖ ^ 2) := by
  exact (shift_memLp hf2 h).integrable_norm_pow (by norm_num)

theorem cosine_density_integrable {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2) (h : ℝ) :
    Integrable (fun r => (1 - Real.cos (h * r)) * ‖paperFourier f r‖ ^ 2) := by
  have hdiff := (hf.comp_add_right h).sub hf
  have hv := ((ordinary_fourier_memLp hdiff (shift_memLp hf2 h)).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)).comp_div (by positivity : 2 * Real.pi ≠ 0)
  apply (hv.div_const 2).congr
  filter_upwards [] with r
  change ‖paperFourier (fun u => f (u + h) - f u) r‖ ^ 2 / 2 = _
  rw [paperFourier_translate_sub_norm_sq hf]
  ring

/-- The exact cosine-density expression for the physical squared shift,
with the unnormalized angular-frequency Fourier transform. -/
theorem shift_parseval {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2) (h : ℝ) :
    (∫ u : ℝ, ‖f (u + h) - f u‖ ^ 2) =
      (1 / Real.pi) * ∫ r : ℝ, (1 - Real.cos (h * r)) * ‖paperFourier f r‖ ^ 2 := by
  have hP := paperFourier_mass ((hf.comp_add_right h).sub hf) (shift_memLp hf2 h)
  change (∫ r : ℝ, ‖paperFourier (fun u => f (u + h) - f u) r‖ ^ 2) =
    (2 * Real.pi) * ∫ u : ℝ, ‖f (u + h) - f u‖ ^ 2 at hP
  simp_rw [paperFourier_translate_sub_norm_sq hf, mul_assoc, integral_const_mul] at hP
  apply (mul_left_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0))
  calc
    _ = 2 * ∫ r : ℝ, (1 - Real.cos (h * r)) * ‖paperFourier f r‖ ^ 2 := by
      simpa only [mul_assoc] using hP.symm
    _ = _ := by field_simp

#print axioms shift_parseval

end ThetaTrial.Paper.ShiftParseval
