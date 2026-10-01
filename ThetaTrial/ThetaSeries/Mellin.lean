/-
The Mellin representation of the completed zeta function, starting from
Mathlib's construction; convergence comes from its functional-equation pair.
-/
import ThetaTrial.Xi
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace ThetaTrial.ThetaSeries

/-- The Jacobi theta kernel at zero characteristic. -/
def thetaKernel (t : ℝ) : ℝ := HurwitzZeta.evenKernel 0 t

/-- This equals the positive-natural-index theta tail when `t > 0`. -/
def thetaTail (t : ℝ) : ℝ := (thetaKernel t - 1) / 2

/-- Mathlib's subtraction of the constant terms at both ends. -/
def modifiedTheta : ℝ → ℂ := (HurwitzZeta.hurwitzEvenFEPair 0).f_modif

/-- The upper part of the modified kernel, with no ambiguity at `t = 1`. -/
def upperTheta : ℝ → ℂ :=
  (Ioi 1).indicator (fun t : ℝ => ((thetaKernel t - 1 : ℝ) : ℂ))

def reflectedUpperTheta (t : ℝ) : ℂ :=
  (t : ℂ) ^ (-(1 / 2 : ℂ)) • upperTheta t⁻¹

def upperMellin (w : ℂ) : ℂ := mellin upperTheta w

theorem thetaTail_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t))
      (thetaTail t) := by
  have hs := (HurwitzZeta.hasSum_nat_cosKernel₀ 0 ht).mul_left (1 / 2 : ℝ)
  simpa [thetaTail, thetaKernel, ← HurwitzZeta.evenKernel_eq_cosKernel_of_zero,
    div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hs

theorem thetaKernel_functional_equation {t : ℝ} (ht : 0 < t) :
    (thetaKernel t : ℂ) =
      (t : ℂ) ^ (-(1 / 2 : ℂ)) * (thetaKernel t⁻¹ : ℂ) := by
  have hr : thetaKernel t = t ^ (-(1 / 2 : ℝ)) * thetaKernel t⁻¹ := by
    simpa [thetaKernel, ← HurwitzZeta.evenKernel_eq_cosKernel_of_zero,
      one_div, Real.rpow_neg ht.le] using
      HurwitzZeta.evenKernel_functional_equation 0 t
  simpa only [Complex.ofReal_mul, Complex.ofReal_cpow ht.le,
    Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] using congrArg Complex.ofReal hr

theorem modifiedTheta_of_one_lt {t : ℝ} (ht : 1 < t) :
    modifiedTheta t = (thetaKernel t : ℂ) - 1 := by
  simp [modifiedTheta, WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair,
    thetaKernel, ht, not_lt.mpr ht.le]

theorem modifiedTheta_of_pos_of_lt_one {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    modifiedTheta t = (thetaKernel t : ℂ) - (t : ℂ) ^ (-(1 / 2 : ℂ)) := by
  simp [modifiedTheta, WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair,
    thetaKernel, ht, ht1, not_lt.mpr ht1.le, Complex.ofReal_cpow ht.le]

@[simp] theorem modifiedTheta_one : modifiedTheta 1 = 0 := by
  simp [modifiedTheta, WeakFEPair.f_modif]

theorem upperTheta_eq_indicator_modified :
    upperTheta = (Ioi 1).indicator modifiedTheta := by
  funext t
  by_cases ht : 1 < t
  · simp [upperTheta, ht, modifiedTheta_of_one_lt ht]
  · simp [upperTheta, ht]

/-- The lower half is the functional-equation image of the upper half. -/
theorem modifiedTheta_eq_upper_add_reflected {t : ℝ} (ht : 0 < t) :
    modifiedTheta t = upperTheta t + reflectedUpperTheta t := by
  rcases lt_trichotomy t 1 with ht1 | rfl | ht1
  · have hinv : 1 < t⁻¹ := (one_lt_inv₀ ht).2 ht1
    rw [modifiedTheta_of_pos_of_lt_one ht ht1]
    simp only [reflectedUpperTheta]
    simp [upperTheta, not_lt.mpr ht1.le, hinv, smul_eq_mul]
    rw [thetaKernel_functional_equation ht]
    ring
  · simp [upperTheta, reflectedUpperTheta]
  · have hinv : ¬1 < t⁻¹ := by
      exact not_lt.mpr ((inv_le_one₀ ht).2 ht1.le)
    simp [upperTheta, reflectedUpperTheta, ht1, hinv,
      modifiedTheta_of_one_lt ht1]

/-- Convergence of the modified Mellin integral, for every exponent. -/
theorem modifiedTheta_mellinConvergent (w : ℂ) : MellinConvergent modifiedTheta w := by
  exact ((HurwitzZeta.hurwitzEvenFEPair 0).isStrongFEPair_toStrongFEPair.hasMellin w).1

theorem upperTheta_mellinConvergent (w : ℂ) : MellinConvergent upperTheta w := by
  have hi := Integrable.indicator (modifiedTheta_mellinConvergent w)
    (s := Ioi (1 : ℝ)) measurableSet_Ioi
  have he : (fun t : ℝ => (t : ℂ) ^ (w - 1) • upperTheta t) =
      (Ioi 1).indicator (fun t : ℝ => (t : ℂ) ^ (w - 1) • modifiedTheta t) := by
    funext t
    by_cases ht : 1 < t <;> simp [upperTheta_eq_indicator_modified, ht]
  change Integrable (fun t : ℝ => (t : ℂ) ^ (w - 1) • upperTheta t)
    (volume.restrict (Ioi 0))
  rw [he]
  exact hi

theorem reflectedUpperTheta_mellinConvergent (w : ℂ) :
    MellinConvergent reflectedUpperTheta w := by
  have hd := (modifiedTheta_mellinConvergent w).sub (upperTheta_mellinConvergent w)
  change IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) • reflectedUpperTheta t) (Ioi 0)
  apply hd.congr_fun _ measurableSet_Ioi
  intro t ht
  dsimp only [Pi.sub_apply]
  rw [modifiedTheta_eq_upper_add_reflected ht, smul_add]
  abel

theorem reflectedUpperTheta_mellin (w : ℂ) :
    mellin reflectedUpperTheta w = upperMellin (1 / 2 - w) := by
  unfold reflectedUpperTheta upperMellin
  rw [mellin_cpow_smul, mellin_comp_inv]
  congr 1
  ring

theorem modifiedTheta_mellin (w : ℂ) :
    mellin modifiedTheta w = upperMellin w + upperMellin (1 / 2 - w) := by
  calc
    mellin modifiedTheta w =
        mellin (fun t => upperTheta t + reflectedUpperTheta t) w := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [modifiedTheta_eq_upper_add_reflected ht]
    _ = mellin upperTheta w + mellin reflectedUpperTheta w :=
      (hasMellin_add (upperTheta_mellinConvergent w)
        (reflectedUpperTheta_mellinConvergent w)).2
    _ = _ := by rw [reflectedUpperTheta_mellin]; rfl

theorem upperMellin_integrable (w : ℂ) :
    IntegrableOn (fun t : ℝ =>
      (t : ℂ) ^ (w - 1) * ((thetaKernel t : ℂ) - 1)) (Ioi 1) := by
  have hi := (upperTheta_mellinConvergent w).mono_set
    (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))
  exact hi.congr_fun (fun t ht => by simp [upperTheta, ht]) measurableSet_Ioi

theorem upperMellin_eq_integral (w : ℂ) :
    upperMellin w = ∫ t : ℝ in Ioi 1,
      (t : ℂ) ^ (w - 1) * ((thetaKernel t : ℂ) - 1) := by
  unfold upperMellin mellin
  have he : (fun t : ℝ => (t : ℂ) ^ (w - 1) • upperTheta t) =
      (Ioi 1).indicator (fun t : ℝ =>
        (t : ℂ) ^ (w - 1) * ((thetaKernel t : ℂ) - 1)) := by
    funext t
    by_cases ht : 1 < t <;> simp [upperTheta, ht]
  rw [he, setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))]

/-- The entire completed zeta is the sum of two convergent theta-tail Mellin integrals. -/
theorem completedZeta₀_eq_upperMellin (s : ℂ) :
    completedRiemannZeta₀ s =
      (upperMellin (s / 2) + upperMellin ((1 - s) / 2)) / 2 := by
  change mellin modifiedTheta (s / 2) / 2 = _
  rw [modifiedTheta_mellin]
  congr 3
  ring

/-- The xi identity before the two integrations by parts. -/
theorem xi_centered_eq_upperMellin (z : ℂ) :
    ThetaTrial.xi (1 / 2 + z) = 1 / 2 + (z ^ 2 - 1 / 4) / 4 *
      (upperMellin (1 / 4 + z / 2) + upperMellin (1 / 4 - z / 2)) := by
  rw [ThetaTrial.xi, completedZeta₀_eq_upperMellin]
  have hplus : ((1 / 2 : ℂ) + z) / 2 = 1 / 4 + z / 2 := by ring
  have hminus : (1 - ((1 / 2 : ℂ) + z)) / 2 = 1 / 4 - z / 2 := by ring
  rw [hplus, hminus]
  ring

end ThetaTrial.ThetaSeries
