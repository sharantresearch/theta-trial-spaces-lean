import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# A diagonal bound controls a Hermitian sesquilinear form

Real polarization bounds the real and imaginary parts on the unit ball, and
scaling gives a product-of-norms bound. The convention is conjugate-linear in
the first variable.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped ComplexConjugate

namespace ThetaTrial.Paper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma sesquilinear_re_polarization (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) (hb : b.IsSymm)
    (v w : E) :
    4 * (b v w).re = (b (v + w) (v + w)).re - (b (v - w) (v - w)).re := by
  have hs : (b w v).re = (b v w).re := by
    have h := congrArg Complex.re (hb.eq v w)
    change (conj (b v w)).re = (b w v).re at h
    simpa only [Complex.conj_re] using h.symm
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply,
    Complex.add_re, Complex.sub_re]
  rw [hs]
  ring

lemma sesquilinear_re_bound_on_unit (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) (hb : b.IsSymm)
    {C : ℝ} (hC : 0 ≤ C) (hdiag : ∀ v : E, |(b v v).re| ≤ C * ‖v‖ ^ 2)
    {v w : E} (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) : |(b v w).re| ≤ 2 * C := by
  have hp : ‖v + w‖ ^ 2 ≤ 4 := by
    nlinarith [norm_add_le v w, norm_nonneg (v + w)]
  have hm : ‖v - w‖ ^ 2 ≤ 4 := by
    nlinarith [norm_sub_le v w, norm_nonneg (v - w)]
  have hp' := (hdiag (v + w)).trans (mul_le_mul_of_nonneg_left hp hC)
  have hm' := (hdiag (v - w)).trans (mul_le_mul_of_nonneg_left hm hC)
  have hpol := sesquilinear_re_polarization b hb v w
  obtain ⟨hp0, hp1⟩ := abs_le.mp hp'
  obtain ⟨hm0, hm1⟩ := abs_le.mp hm'
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma sesquilinear_bound_on_unit (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) (hb : b.IsSymm)
    {C : ℝ} (hC : 0 ≤ C) (hdiag : ∀ v : E, |(b v v).re| ≤ C * ‖v‖ ^ 2)
    {v w : E} (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) : ‖b v w‖ ≤ 4 * C := by
  have hre := sesquilinear_re_bound_on_unit b hb hC hdiag hv hw
  have hIw : ‖Complex.I • w‖ ≤ 1 := by
    simpa only [norm_smul, Complex.norm_I, one_mul] using hw
  have him := sesquilinear_re_bound_on_unit b hb hC hdiag hv hIw
  simp only [map_smul, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_sub, abs_neg] at him
  have hn := Complex.norm_le_abs_re_add_abs_im (b v w)
  linarith

lemma sesquilinear_norm_smul (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) (c d : ℂ) (v w : E) :
    ‖b (c • v) (d • w)‖ = ‖c‖ * ‖d‖ * ‖b v w‖ := by
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
    norm_mul, Complex.norm_conj]
  ring

/-- An explicit coarse bound on a Hermitian form from its quadratic
diagonal estimate, without presupposing any continuity. -/
theorem sesquilinear_norm_le_of_diagonal (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) (hb : b.IsSymm)
    {C : ℝ} (hC : 0 ≤ C) (hdiag : ∀ v : E, |(b v v).re| ≤ C * ‖v‖ ^ 2)
    (v w : E) : ‖b v w‖ ≤ 4 * C * ‖v‖ * ‖w‖ := by
  by_cases hv : v = 0
  · simp [hv]
  by_cases hw : w = 0
  · simp [hw]
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hwp : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let v' : E := ((‖v‖⁻¹ : ℝ) : ℂ) • v
  let w' : E := ((‖w‖⁻¹ : ℝ) : ℂ) • w
  have hv' : ‖v'‖ = 1 := by
    simp [v', norm_smul, hvp.ne']
  have hw' : ‖w'‖ = 1 := by
    simp [w', norm_smul, hwp.ne']
  have hu := sesquilinear_bound_on_unit b hb hC hdiag hv'.le hw'.le
  have hs : ‖b v' w'‖ = ‖b v w‖ / (‖v‖ * ‖w‖) := by
    calc
      _ = ‖((‖v‖⁻¹ : ℝ) : ℂ)‖ * ‖((‖w‖⁻¹ : ℝ) : ℂ)‖ * ‖b v w‖ :=
        sesquilinear_norm_smul b ((‖v‖⁻¹ : ℝ) : ℂ) ((‖w‖⁻¹ : ℝ) : ℂ) v w
      _ = _ := by
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, div_eq_mul_inv,
          mul_inv]
        ring
  rw [hs] at hu
  have h := (div_le_iff₀ (mul_pos hvp hwp)).mp hu
  nlinarith

/-- The diagonal hypothesis also gives a nonnegative continuity constant. -/
theorem exists_sesquilinear_bound_of_diagonal (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) (hb : b.IsSymm)
    {C : ℝ} (hdiag : ∀ v : E, |(b v v).re| ≤ C * ‖v‖ ^ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v w : E, ‖b v w‖ ≤ K * ‖v‖ * ‖w‖ := by
  have hd : ∀ v : E, |(b v v).re| ≤ |C| * ‖v‖ ^ 2 := by
    intro v
    exact (hdiag v).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg ‖v‖))
  exact ⟨4 * |C|, mul_nonneg (by norm_num) (abs_nonneg C),
    sesquilinear_norm_le_of_diagonal b hb (abs_nonneg C) hd⟩

#print axioms sesquilinear_norm_le_of_diagonal
#print axioms exists_sesquilinear_bound_of_diagonal

end ThetaTrial.Paper
