import ThetaTrial.ZetaDefinitions
import ThetaTrial.FourierNormalization
import ThetaTrial.Imported.Zeta23.Statement.SeamClosed

/-!
# Zeros of `Xi` and of zeta

A bijection between the nontrivial zeros of zeta and the zeros of `Xi`.
Multiplicity is the analytic order, and the affine change of coordinates
preserves it.
-/

noncomputable section

namespace ThetaTrial

open Complex Set
open ThetaTrial.FourierNormalization

theorem xi_eq_zero_iff_zeta23 (s : ℂ) :
    xi s = 0 ↔ Zeta23.IsNontrivialZero s := by
  constructor
  · intro h
    exact ⟨((xi_eq_zero_iff_nontrivialZetaZero s).mp h).1, xi_zero_strict_strip h⟩
  · intro h
    exact NontrivialZetaZero.xi_eq_zero ⟨h.1, h.not_trivial⟩

theorem spectralCoord_mem_XiZeros_iff (ρ : ℂ) :
    spectralCoord ρ ∈ XiZeros ↔ Zeta23.IsNontrivialZero ρ := by
  rw [mem_XiZeros, Xi, zetaCoord_spectralCoord, xi_eq_zero_iff_zeta23]

/-- A bijection of the distinct zeros. -/
def zetaZeroEquivXiZeros : Zeta23.zetaZeroConfig.carrier ≃ XiZeros where
  toFun ρ := ⟨spectralCoord ρ, (spectralCoord_mem_XiZeros_iff ρ).2 ρ.property⟩
  invFun z := ⟨1 / 2 - I * z,
    (xi_eq_zero_iff_zeta23 _).1 (show Xi z = 0 from z.property)⟩
  left_inv ρ := Subtype.ext (zetaCoord_spectralCoord ρ)
  right_inv z := Subtype.ext (spectralCoord_zetaCoord z)

@[simp] theorem zetaZeroEquivXiZeros_apply (ρ : Zeta23.zetaZeroConfig.carrier) :
    (zetaZeroEquivXiZeros ρ : ℂ) = spectralCoord ρ := rfl

/-- The analytic multiplicity of the spectral entire function. -/
def XiMultiplicity (z : ℂ) : ℕ := (analyticOrderAt Xi z).toNat

theorem Xi_analyticOrderAt (z : ℂ) :
    analyticOrderAt Xi z = analyticOrderAt xi (1 / 2 - I * z) := by
  have ha : AnalyticAt ℂ (fun w : ℂ => 1 / 2 - I * w) z := by fun_prop
  have hd : deriv (fun w : ℂ => 1 / 2 - I * w) z = -I := by
    convert (((hasDerivAt_id z).const_mul I).const_sub (1 / 2)).deriv using 1 <;> simp
  exact analyticOrderAt_comp_of_deriv_ne_zero ha (by rw [hd]; exact neg_ne_zero.mpr I_ne_zero)

theorem XiMultiplicity_spectralCoord (ρ : ℂ) :
    XiMultiplicity (spectralCoord ρ) = (analyticOrderAt xi ρ).toNat := by
  unfold XiMultiplicity
  rw [Xi_analyticOrderAt, zetaCoord_spectralCoord]

end ThetaTrial
