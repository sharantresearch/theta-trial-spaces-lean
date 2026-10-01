import ThetaTrial.Paper.ShiftParseval
import Mathlib.MeasureTheory.Group.Prod

/-!
# Integrable magnitudes for noncompact cross correlations

The total cross-correlation magnitude has exactly the product of the two
L1 masses. Pointwise L2 data ensure that the ordinary correlations converge
at every translation, including translations of discontinuous functions.
-/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace ThetaTrial.Paper

def crossMagnitude (f g : ℝ → ℂ) (h : ℝ) : ℝ :=
  ∫ u : ℝ, ‖f (u + h)‖ * ‖g u‖

def crossCorrelationReal (f g : ℝ → ℂ) (h : ℝ) : ℝ :=
  ∫ u : ℝ, (f (u + h) * conj (g u)).re

theorem crossMagnitude_nonneg (f g : ℝ → ℂ) (h : ℝ) :
    0 ≤ crossMagnitude f g h :=
  integral_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem crossMagnitude_joint_integrable {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun z : ℝ × ℝ => ‖f (z.2 + z.1)‖ * ‖g z.2‖)
      (volume.prod volume) := by
  have hh :=
    (measurePreserving_add_prod (volume : Measure ℝ) volume).integrable_comp_of_integrable
      (hf.norm.mul_prod hg.norm)
  change Integrable (fun z : ℝ × ℝ => ‖f (z.1 + z.2)‖ * ‖g z.2‖)
    (volume.prod volume) at hh
  simpa only [add_comm] using hh

theorem crossMagnitude_integrable {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    Integrable (crossMagnitude f g) :=
  (crossMagnitude_joint_integrable hf hg).integral_prod_left

theorem integral_crossMagnitude {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ h : ℝ, crossMagnitude f g h) = (∫ u : ℝ, ‖f u‖) * ∫ u : ℝ, ‖g u‖ := by
  unfold crossMagnitude
  rw [integral_integral_swap (crossMagnitude_joint_integrable hf hg)]
  change (∫ u : ℝ, ∫ h : ℝ, ‖f (u + h)‖ * ‖g u‖) = _
  have ht (u : ℝ) : (∫ h : ℝ, ‖f (u + h)‖) = ∫ h : ℝ, ‖f h‖ :=
    integral_add_left_eq_self (fun h : ℝ => ‖f h‖) u
  simp_rw [integral_mul_const, ht]
  exact integral_const_mul _ _

theorem crossMagnitude_integrand_integrable {f g : ℝ → ℂ}
    (hf2 : MemLp f 2) (hg2 : MemLp g 2) (h : ℝ) :
    Integrable (fun u : ℝ => ‖f (u + h)‖ * ‖g u‖) := by
  exact (hf2.comp_measurePreserving (measurePreserving_add_right volume h)).norm.integrable_mul
    hg2.norm

theorem crossCorrelationReal_integrand_integrable {f g : ℝ → ℂ}
    (hf2 : MemLp f 2) (hg2 : MemLp g 2) (h : ℝ) :
    Integrable (fun u : ℝ => (f (u + h) * conj (g u)).re) := by
  have hfm := (hf2.comp_measurePreserving
    (measurePreserving_add_right volume h)).aestronglyMeasurable
  have hgm := Complex.continuous_conj.comp_aestronglyMeasurable hg2.aestronglyMeasurable
  apply (crossMagnitude_integrand_integrable hf2 hg2 h).mono'
    (Complex.continuous_re.comp_aestronglyMeasurable (hfm.mul hgm))
  filter_upwards [] with u
  change ‖(f (u + h) * conj (g u)).re‖ ≤ ‖f (u + h)‖ * ‖g u‖
  simpa only [Real.norm_eq_abs, norm_mul, Complex.norm_conj] using
    Complex.abs_re_le_norm (f (u + h) * conj (g u))

theorem crossCorrelationReal_abs_le {f g : ℝ → ℂ}
    (hf2 : MemLp f 2) (hg2 : MemLp g 2) (h : ℝ) :
    |crossCorrelationReal f g h| ≤ crossMagnitude f g h := by
  calc
    _ ≤ ∫ u : ℝ, ‖(f (u + h) * conj (g u)).re‖ := by
      simpa only [crossCorrelationReal, Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun u : ℝ => (f (u + h) * conj (g u)).re)
    _ ≤ _ := by
      apply integral_mono
        (crossCorrelationReal_integrand_integrable hf2 hg2 h).norm
        (crossMagnitude_integrand_integrable hf2 hg2 h)
      intro u
      simpa only [Real.norm_eq_abs, norm_mul, Complex.norm_conj] using
        Complex.abs_re_le_norm (f (u + h) * conj (g u))

#print axioms integral_crossMagnitude
#print axioms crossCorrelationReal_abs_le

end ThetaTrial.Paper
