import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The entire Riemann xi function

`xi(s) = s(s-1)/2 · π^(-s/2) Γ(s/2) ζ(s)` and `Xi(z) = xi(1/2 - iz)`, defined
through Mathlib's completed Riemann zeta function. Entirety and the functional
equation come from `differentiable_completedZeta₀` and
`completedRiemannZeta₀_one_sub`.

The normalization is checked against `completedRiemannZeta_eq`:
`Λ(s) = Λ₀(s) - 1/s - 1/(1-s)`, so that `s(s-1)Λ(s) = s(s-1)Λ₀(s) + 1` away from
0 and 1. Since Mathlib defines division and Gamma at their poles by
convention, the product formulas carry explicit hypotheses excluding those
points.
-/

noncomputable section

namespace ThetaTrial

open Complex

/-- The entire extension of `s(s-1) Lambda(s) / 2`, with its zeta input. -/
def xi (s : ℂ) : ℂ :=
  (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

/-- The xi function is entire: it is complex differentiable everywhere. -/
theorem xi_entire : Differentiable ℂ xi := by
  exact (((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1).div_const 2

/-- The functional equation, including the two removed poles. -/
theorem xi_one_sub (s : ℂ) : xi (1 - s) = xi s := by
  simp only [xi, completedRiemannZeta₀_one_sub]
  ring

@[simp] theorem xi_one : xi 1 = 1 / 2 := by
  simp [xi]

/-- The entire extension agrees with the completed-zeta expression off its poles. -/
theorem xi_eq_completed {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    xi s = s * (s - 1) / 2 * completedRiemannZeta s := by
  rw [xi, completedRiemannZeta_eq]
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  field_simp [hs0, h1s]
  ring

/-- Agreement with the Gamma/zeta product, away from the poles of Mathlib's
Gamma factor. -/
theorem xi_eq_gamma_zeta_of_ne_zero {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hgamma : Gammaℝ s ≠ 0) :
    xi s = s * (s - 1) / 2 *
      ((Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2)) * riemannZeta s := by
  rw [xi_eq_completed hs0 hs1, riemannZeta_def_of_ne_zero hs0]
  change s * (s - 1) / 2 * completedRiemannZeta s =
    s * (s - 1) / 2 * Gammaℝ s * (completedRiemannZeta s / Gammaℝ s)
  rw [mul_assoc, mul_div_cancel₀ _ hgamma]

/-- In the positive half-plane only the zeta pole at 1 needs exclusion. -/
theorem xi_eq_gamma_zeta_of_re_pos {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    xi s = s * (s - 1) / 2 *
      ((Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2)) * riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    simp [h] at hs
  exact xi_eq_gamma_zeta_of_ne_zero hs0 hs1 (Gammaℝ_ne_zero_of_re_pos hs)

/-- Symmetry about the center of the critical strip. -/
theorem xi_centered_even (z : ℂ) : xi (1 / 2 - z) = xi (1 / 2 + z) := by
  have h : (1 : ℂ) - (1 / 2 + z) = 1 / 2 - z := by ring
  simpa only [h] using xi_one_sub (1 / 2 + z)

/-- The centered spectral variable `z ↦ 1/2 - iz`. -/
def Xi (z : ℂ) : ℂ := xi (1 / 2 - I * z)

theorem Xi_entire : Differentiable ℂ Xi := by
  unfold Xi
  apply xi_entire.comp
  fun_prop

end ThetaTrial
