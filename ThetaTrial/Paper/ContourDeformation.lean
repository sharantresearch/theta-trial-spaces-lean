import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Annular-sector contour deformation in logarithmic coordinates

The exponential substitution turns the annular sector into a rectangle, and
the contour identity follows from the Cauchy–Goursat theorem in Mathlib. The
final theorem applies it to the principal-power theta-mode integrand.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped Interval

namespace ThetaTrial.Paper.ContourDeformation

/-- Pullback of the one-form f(ζ) dζ by ζ = exp(w). -/
def exponentialPullback (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  f (Complex.exp w) * Complex.exp w

def lowerRay (f : ℂ → ℂ) (L β : ℝ) : ℂ :=
  ∫ s : ℝ in 0..L, exponentialPullback f ((s : ℂ) + (-β : ℝ) * Complex.I)

def upperRay (f : ℂ → ℂ) (L β : ℝ) : ℂ :=
  ∫ s : ℝ in 0..L, exponentialPullback f ((s : ℂ) + (β : ℂ) * Complex.I)

def circularArc (f : ℂ → ℂ) (s β : ℝ) : ℂ :=
  Complex.I * ∫ θ : ℝ in (-β)..β,
    exponentialPullback f ((s : ℂ) + (θ : ℂ) * Complex.I)

theorem exp_re_pos_on_rectangle {L β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : β < Real.pi / 2) {w : ℂ}
    (hw : w ∈ (uIcc 0 L) ×ℂ (uIcc (-β) β)) :
    0 < (Complex.exp w).re := by
  have hi : -β ≤ w.im ∧ w.im ≤ β := by
    simpa only [uIcc_of_le (by linarith : -β ≤ β), mem_preimage, mem_Icc] using hw.2
  rw [Complex.exp_re]
  exact mul_pos (Real.exp_pos _)
    (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)

/-- An annular-sector contour identity. The radial integrals are
parameterized by log radius, so their derivatives include exp(w).
The outer circle has radius exp(L), and the inner circle radius 1. -/
theorem annular_sector_deformation (f : ℂ → ℂ) (L : ℝ) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ : β < Real.pi / 2)
    (hf : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ f z) :
    circularArc f 0 β =
      lowerRay f L β + circularArc f L β - upperRay f L β := by
  have hd : DifferentiableOn ℂ (exponentialPullback f)
      ((uIcc 0 L) ×ℂ (uIcc (-β) β)) := by
    intro w hw
    exact (((hf (Complex.exp w) (exp_re_pos_on_rectangle hβ0 hβ hw)).comp w
      Complex.differentiable_exp.differentiableAt).mul
      Complex.differentiable_exp.differentiableAt).differentiableWithinAt
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (exponentialPullback f) ((-β : ℝ) * Complex.I) ((L : ℂ) + (β : ℂ) * Complex.I)
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, sub_zero, add_zero, zero_add] at hrect
  have heq := hrect hd
  change lowerRay f L β - upperRay f L β +
    circularArc f L β - circularArc f 0 β = 0 at heq
  linear_combination -heq

/-- Principal-power integrand after ζ = exp(2iy). The arbitrary complex
coefficients include the mode coefficients and perturbation. -/
def thetaModeIntegrand (p q Z κ A δ : ℂ) (ζ : ℂ) : ℂ :=
  (p * ζ ^ (9 / 4 : ℂ) - q * ζ ^ (5 / 4 : ℂ)) *
    Complex.exp (Z / ζ - κ * ζ - A * δ * ζ) / ζ

/-- Holomorphy of the principal powers is proved on Re ζ > 0. -/
theorem thetaModeIntegrand_differentiable (p q Z κ A δ : ℂ)
    {ζ : ℂ} (hζ : 0 < ζ.re) :
    DifferentiableAt ℂ (thetaModeIntegrand p q Z κ A δ) ζ := by
  have hne : ζ ≠ 0 := by
    intro hz
    simp only [hz, Complex.zero_re, lt_self_iff_false] at hζ
  have hslit : ζ ∈ Complex.slitPlane := Or.inl hζ
  have h9 : DifferentiableAt ℂ (fun z : ℂ => z ^ (9 / 4 : ℂ)) ζ :=
    differentiableAt_id.cpow_const hslit
  have h5 : DifferentiableAt ℂ (fun z : ℂ => z ^ (5 / 4 : ℂ)) ζ :=
    differentiableAt_id.cpow_const hslit
  have hphase : DifferentiableAt ℂ (fun z : ℂ => Z / z - κ * z - A * δ * z) ζ :=
    (((differentiableAt_const Z).div differentiableAt_id hne).sub
      (differentiableAt_id.const_mul κ)).sub
      (differentiableAt_id.const_mul (A * δ))
  exact (((h9.const_mul p).sub (h5.const_mul q)).mul hphase.cexp).div
    differentiableAt_id hne

/-- Exact contour deformation for every theta mode, including both
fractional-power prefactors and the perturbed exponential. -/
theorem thetaMode_annular_sector_deformation
    (p q Z κ A δ : ℂ) (L : ℝ) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ : β < Real.pi / 2) :
    circularArc (thetaModeIntegrand p q Z κ A δ) 0 β =
      lowerRay (thetaModeIntegrand p q Z κ A δ) L β +
      circularArc (thetaModeIntegrand p q Z κ A δ) L β -
      upperRay (thetaModeIntegrand p q Z κ A δ) L β := by
  exact annular_sector_deformation _ L hβ0 hβ
    (fun _ hz => thetaModeIntegrand_differentiable p q Z κ A δ hz)

end ThetaTrial.Paper.ContourDeformation
