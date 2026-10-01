import ThetaTrial.XiZeros.Coordinates
import ThetaTrial.Imported.Zeta23.RvM.CountByIntegral

/-
The multiplicity argument below is adapted from
`Zeta23.XiPrime.ZeroFree.analyticOrderNatAt_xi` in anthropics/formal-math,
tag v1.0, commit 3635e74826a4c1fcece7d1cd2b6fa75e43a00510.
Copyright (c) 2026 Anthropic, PBC. Released under Apache License 2.0;
see ThetaTrial/Imported/Zeta23/LICENSE and ThetaTrial/Imported/Zeta23/NOTICE.
Local change: the proof uses `ThetaTrial.xi_eq_completed` directly.
-/

/-!
# Multiplicities of the zeros of zeta and Xi

The completion factor does not vanish, so xi and zeta have the same analytic
orders at nontrivial zeros. Together with the change of coordinates in
`XiZeros.Coordinates`, this identifies the multiplicities of the zeros of `Xi`.
-/

noncomputable section

namespace ThetaTrial

open ThetaTrial.FourierNormalization

@[simp] theorem zetaZeroEquivXiZeros_multiplicity
    (ρ : Zeta23.zetaZeroConfig.carrier) :
    XiMultiplicity (zetaZeroEquivXiZeros ρ) = Zeta23.zetaZeroConfig.mult ρ := by
  rw [zetaZeroEquivXiZeros_apply, XiMultiplicity_spectralCoord]
  change analyticOrderNatAt xi (ρ : ℂ) = Zeta23.zeroMult ρ
  have h0 : (ρ : ℂ) ≠ 0 := fun h => by have := ρ.property.2.1; simp [h] at this
  have h1 : (ρ : ℂ) ≠ 1 := fun h => by have := ρ.property.2.2; simp [h] at this
  have hev : xi =ᶠ[nhds (ρ : ℂ)]
      fun s => s * (s - 1) / 2 * completedRiemannZeta s := by
    filter_upwards [isOpen_compl_singleton.mem_nhds h0,
      isOpen_compl_singleton.mem_nhds h1] with s hs0 hs1
    exact xi_eq_completed hs0 hs1
  have hΛ := Zeta23.RvM.analyticAt_completedRiemannZeta h0 h1
  have hp : AnalyticAt ℂ (fun s : ℂ => s * (s - 1) / 2) (ρ : ℂ) :=
    (by fun_prop : Differentiable ℂ (fun s : ℂ => s * (s - 1) / 2)).analyticAt ρ
  have hp0 : analyticOrderAt (fun s : ℂ => s * (s - 1) / 2) (ρ : ℂ) = 0 :=
    hp.analyticOrderAt_eq_zero.mpr
      (div_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) two_ne_zero)
  have hmul := analyticOrderAt_mul hp hΛ
  rw [show ((fun s : ℂ => s * (s - 1) / 2) * completedRiemannZeta)
      = fun s => s * (s - 1) / 2 * completedRiemannZeta s from rfl] at hmul
  rw [← Zeta23.RvM.analyticOrderNatAt_completedRiemannZeta ρ.property.2.1 h1]
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr hev, hmul, hp0, zero_add]

end ThetaTrial
