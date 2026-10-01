/-
Gaussian majorants for theta-type sums, using the bounds in Mathlib's
`HurwitzKernelBounds`, and the resulting decay and integrability lemmas.
-/
import ThetaTrial.ThetaSeries.Series
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Asymptotics

noncomputable section

open Asymptotics Filter MeasureTheory Set
open scoped Topology

namespace ThetaTrial.ThetaSeries

def thetaGaussianMoment (k : ℕ) : ℝ := HurwitzKernelBounds.F_nat k 1 (1 / 2)

theorem thetaGaussianMoment_nonneg (k : ℕ) : 0 ≤ thetaGaussianMoment k := by
  apply tsum_nonneg
  intro n
  dsimp [HurwitzKernelBounds.f_nat]
  positivity

theorem theta_gaussian_term_decay (k n : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    ‖HurwitzKernelBounds.f_nat k 1 t n‖ ≤
      HurwitzKernelBounds.f_nat k 1 (1 / 2) n * Real.exp (-Real.pi * t / 2) := by
  have ha : 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hA : 0 ≤ ((n : ℝ) + 1) ^ 2 := sq_nonneg _
  have hAt := mul_le_mul_of_nonneg_left ht hA
  have htA := mul_le_mul_of_nonneg_right ha (show 0 ≤ t by linarith)
  have hsplit : (((n : ℝ) + 1) ^ 2 + t) / 2 ≤ ((n : ℝ) + 1) ^ 2 * t := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hsplit Real.pi_pos.le
  have he : Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t) ≤
      Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * (1 / 2)) *
        Real.exp (-Real.pi * t / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hscaled]
  rw [HurwitzKernelBounds.f_nat, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ ((n : ℝ) + 1) ^ k *
        (Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * (1 / 2)) *
          Real.exp (-Real.pi * t / 2)) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by rw [HurwitzKernelBounds.f_nat]; ring

/-- One bound valid for every natural polynomial weight, including 0, 2, and 4. -/
theorem thetaGaussianMoment_decay (k : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    ‖HurwitzKernelBounds.F_nat k 1 t‖ ≤
      thetaGaussianMoment k * Real.exp (-Real.pi * t / 2) := by
  exact tsum_of_norm_bounded
    (((HurwitzKernelBounds.summable_f_nat k 1 (by norm_num : (0 : ℝ) < 1 / 2)).hasSum).mul_right
      (Real.exp (-Real.pi * t / 2)))
    (fun n => theta_gaussian_term_decay k n ht)

def doubleExpEnvelope (a c u : ℝ) : ℝ :=
  Real.exp (a * u) * Real.exp (-c * Real.exp (2 * u))

/-- Superexponential decay beats every fixed exponential weight. -/
theorem doubleExpEnvelope_tendsto (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (doubleExpEnvelope a c) atTop (𝓝 0) := by
  have hT : Tendsto (fun u : ℝ => Real.exp (2 * u)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hd := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a / 2) c hc).comp hT
  convert hd using 1
  funext u
  dsimp [doubleExpEnvelope]
  rw [← Real.exp_mul]
  congr 2
  ring

theorem doubleExpEnvelope_isLittleO_exp_neg (a : ℝ) {c : ℝ} (hc : 0 < c) :
    (doubleExpEnvelope a c) =o[atTop] (fun u : ℝ => Real.exp (-u)) := by
  apply isLittleO_of_tendsto (fun u h => (Real.exp_ne_zero (-u) h).elim)
  have heq : (fun u : ℝ => doubleExpEnvelope a c u / Real.exp (-u)) =
      doubleExpEnvelope (a + 1) c := by
    funext u
    dsimp [doubleExpEnvelope]
    rw [div_eq_mul_inv, ← Real.exp_neg, neg_neg, mul_right_comm, ← Real.exp_add]
    congr 2
    ring
  rw [heq]
  exact doubleExpEnvelope_tendsto (a + 1) hc

theorem doubleExpEnvelope_integrable (a : ℝ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (doubleExpEnvelope a c) (Ioi 0) := by
  have hcont : Continuous (doubleExpEnvelope a c) := by
    change Continuous (fun u : ℝ => Real.exp (a * u) * Real.exp (-c * Real.exp (2 * u)))
    fun_prop
  have hlocal : LocallyIntegrableOn (doubleExpEnvelope a c) (Ici 0) :=
    hcont.continuousOn.locallyIntegrableOn measurableSet_Ici
  have hbase : IntegrableAtFilter (fun u : ℝ => Real.exp (-u)) atTop volume :=
    ⟨Ioi 0, Ioi_mem_atTop 0, integrableOn_exp_neg_Ioi 0⟩
  exact (hlocal.integrableOn_of_isBigO_atTop
    (doubleExpEnvelope_isLittleO_exp_neg a hc).isBigO hbase).mono_set Ioi_subset_Ici_self

end ThetaTrial.ThetaSeries
