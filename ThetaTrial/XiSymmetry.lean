import ThetaTrial.Xi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Conjugation symmetry of the completed zeta and xi functions

Proved directly from Mathlib's real theta kernel and the Mellin definition of
`completedRiemannZeta₀`. In particular, the zero set of `Xi` is invariant
under conjugation.
-/

noncomputable section

namespace ThetaTrial

open Complex MeasureTheory Set
open scoped ComplexConjugate

/-- A real-valued Mellin kernel has conjugation symmetry. The integral is the
Bochner integral; this identity also respects its totalized convention. -/
theorem mellin_conj_of_real (f : ℝ → ℂ) (hf : ∀ t, conj (f t) = f t) (s : ℂ) :
    mellin f (conj s) = conj (mellin f s) := by
  rw [mellin, mellin, ← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [smul_eq_mul, map_mul, hf]
  have harg : (t : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg ht.le]
    exact Real.pi_ne_zero.symm
  have hp : (t : ℂ) ^ (conj s - 1) = conj ((t : ℂ) ^ (s - 1)) := by
    simpa only [map_sub, map_one, conj_ofReal] using cpow_conj (t : ℂ) (s - 1) harg
  rw [hp]

/-- Reality of the precise pole-removing theta kernel used by mathlib. -/
theorem riemannZeta_kernel_conj (t : ℝ) :
    conj ((HurwitzZeta.hurwitzEvenFEPair 0).f_modif t) =
      (HurwitzZeta.hurwitzEvenFEPair 0).f_modif t := by
  by_cases h1 : 1 < t <;> by_cases h01 : 0 < t ∧ t < 1 <;>
    simp [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair, Set.indicator,
      smul_eq_mul, h1, h01]

theorem completedRiemannZeta₀_conj (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  simp only [completedRiemannZeta₀, HurwitzZeta.completedHurwitzZetaEven₀,
    WeakFEPair.Λ₀, map_div₀, map_ofNat]
  rw [show conj s / 2 = conj (s / 2) by simp only [map_div₀, map_ofNat]]
  rw [mellin_conj_of_real _ riemannZeta_kernel_conj]

/-- Conjugation symmetry of the entire Riemann xi extension. -/
theorem xi_conj (s : ℂ) : xi (conj s) = conj (xi s) := by
  simp only [xi, completedRiemannZeta₀_conj, map_div₀, map_add, map_mul,
    map_sub, map_one, map_ofNat]

/-- In the coordinate `1/2 - iz`, conjugation combines conjugation of xi with
its functional equation. -/
theorem Xi_conj (z : ℂ) : Xi (conj z) = conj (Xi z) := by
  rw [Xi, Xi, ← xi_conj]
  simp only [map_sub, map_div₀, map_one, map_ofNat, map_mul, conj_I, neg_mul,
    sub_neg_eq_add]
  exact xi_centered_even (I * conj z)

end ThetaTrial
