import ThetaTrial.Paper.Definitions
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Tactic

/-!
# Holomorphy of the complex theta-density series

A summable Gaussian majorant exists near each point where
`re (exp (2z)) > 0`, which includes the whole theta strip. Weierstrass
convergence then gives holomorphy and the termwise derivative.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace ThetaTrial.Paper

def thetaStrip : Set ℂ := {z | |z.im| < Real.pi / 4}

theorem isOpen_thetaStrip : IsOpen thetaStrip := by
  exact isOpen_lt (by fun_prop) continuous_const

theorem exp_two_re_pos_of_mem_thetaStrip {z : ℂ} (hz : z ∈ thetaStrip) :
    0 < (Complex.exp (2 * z)).re := by
  rw [Complex.exp_re]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  change |z.im| < Real.pi / 4 at hz
  have hh := abs_lt.mp hz
  norm_num [Complex.mul_im]
  constructor <;> linarith

theorem complexThetaMode_differentiable (n : ℕ) :
    Differentiable ℂ (complexThetaMode n) := by
  unfold complexThetaMode
  fun_prop

/-- A concrete bound on each mode. Its Gaussian majorant is summable
whenever `t>0`; the prefactors are independent of the mode index. -/
theorem complexThetaMode_norm_le (n : ℕ) (z : ℂ) {t A B : ℝ}
    (ht : t ≤ (Complex.exp (2 * z)).re)
    (hA : ‖Complex.exp (9 * z / 2)‖ ≤ A)
    (hB : ‖Complex.exp (5 * z / 2)‖ ≤ B) :
    ‖complexThetaMode n z‖ ≤
      (4 * Real.pi ^ 2 * A) * HurwitzKernelBounds.f_nat 4 1 t n +
      (6 * Real.pi * B) * HurwitzKernelBounds.f_nat 2 1 t n := by
  have hn : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
    have hc : (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [hc, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hA0 : 0 ≤ A := (norm_nonneg _).trans hA
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  have hcoeff : -(Real.pi : ℂ) * ((n : ℂ) + 1) ^ 2 =
      ((-Real.pi * ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  have htail :
      ‖Complex.exp (-(Real.pi : ℂ) * ((n : ℂ) + 1) ^ 2 *
        Complex.exp (2 * z))‖ ≤
      Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t) := by
    rw [Complex.norm_exp, hcoeff, Complex.re_ofReal_mul]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left ht
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) (sq_nonneg _))
  have hpref :
      ‖4 * (Real.pi : ℂ) ^ 2 * ((n : ℂ) + 1) ^ 4 * Complex.exp (9 * z / 2) -
        6 * (Real.pi : ℂ) * ((n : ℂ) + 1) ^ 2 * Complex.exp (5 * z / 2)‖ ≤
      4 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * A +
        6 * Real.pi * ((n : ℝ) + 1) ^ 2 * B := by
    calc
      _ ≤ ‖4 * (Real.pi : ℂ) ^ 2 * ((n : ℂ) + 1) ^ 4 *
          Complex.exp (9 * z / 2)‖ +
          ‖6 * (Real.pi : ℂ) * ((n : ℂ) + 1) ^ 2 *
          Complex.exp (5 * z / 2)‖ := norm_sub_le _ _
      _ = 4 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * ‖Complex.exp (9 * z / 2)‖ +
          6 * Real.pi * ((n : ℝ) + 1) ^ 2 * ‖Complex.exp (5 * z / 2)‖ := by
        simp only [norm_mul, norm_pow, Complex.norm_ofNat, hn,
          Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hA (by positivity))
        (mul_le_mul_of_nonneg_left hB (by positivity))
  rw [complexThetaMode, norm_mul]
  calc
    _ ≤ (4 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * A +
          6 * Real.pi * ((n : ℝ) + 1) ^ 2 * B) *
        Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t) :=
      mul_le_mul hpref htail (norm_nonneg _) (by positivity)
    _ = _ := by unfold HurwitzKernelBounds.f_nat; ring

/-- A locally uniform summable majorant for every theta mode. -/
theorem complexThetaDensity_local_majorant {z : ℂ}
    (hz : 0 < (Complex.exp (2 * z)).re) :
    ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∃ M : ℕ → ℝ, Summable M ∧
        ∀ (n : ℕ) (w : ℂ), w ∈ U → ‖complexThetaMode n w‖ ≤ M n := by
  let t : ℝ := (Complex.exp (2 * z)).re / 2
  let A : ℝ := ‖Complex.exp (9 * z / 2)‖ + 1
  let B : ℝ := ‖Complex.exp (5 * z / 2)‖ + 1
  let U : Set ℂ := {w | t < (Complex.exp (2 * w)).re} ∩
    ({w | ‖Complex.exp (9 * w / 2)‖ < A} ∩
      {w | ‖Complex.exp (5 * w / 2)‖ < B})
  let M : ℕ → ℝ := fun n =>
    (4 * Real.pi ^ 2 * A) * HurwitzKernelBounds.f_nat 4 1 t n +
    (6 * Real.pi * B) * HurwitzKernelBounds.f_nat 2 1 t n
  have ht : 0 < t := by dsimp [t]; positivity
  refine ⟨U, ?_, ?_, M, ?_, ?_⟩
  · exact (isOpen_lt continuous_const (by fun_prop)).inter
      ((isOpen_lt (by fun_prop) continuous_const).inter
        (isOpen_lt (by fun_prop) continuous_const))
  · refine ⟨?_, ?_, ?_⟩
    · dsimp [t]; linarith
    · dsimp [A]; linarith
    · dsimp [B]; linarith
  · exact ((HurwitzKernelBounds.summable_f_nat 4 1 ht).mul_left
      (4 * Real.pi ^ 2 * A)).add
        ((HurwitzKernelBounds.summable_f_nat 2 1 ht).mul_left (6 * Real.pi * B))
  · intro n w hw
    exact complexThetaMode_norm_le n w hw.1.le hw.2.1.le hw.2.2.le

theorem complexThetaMode_summable_of_exp_re_pos {z : ℂ}
    (hz : 0 < (Complex.exp (2 * z)).re) :
    Summable (fun n : ℕ => complexThetaMode n z) := by
  obtain ⟨U, _, hzU, M, hM, hbound⟩ := complexThetaDensity_local_majorant hz
  exact hM.of_norm_bounded (fun n => hbound n z hzU)

theorem complexThetaDensity_differentiableAt_of_exp_re_pos {z : ℂ}
    (hz : 0 < (Complex.exp (2 * z)).re) :
    DifferentiableAt ℂ complexThetaDensity z := by
  obtain ⟨U, hU, hzU, M, hM, hbound⟩ := complexThetaDensity_local_majorant hz
  have hd := Complex.differentiableOn_tsum_of_summable_norm hM
    (fun n => (complexThetaMode_differentiable n).differentiableOn) hU hbound
  exact hd.differentiableAt (hU.mem_nhds hzU)

theorem complexThetaMode_summable_strip {z : ℂ} (hz : z ∈ thetaStrip) :
    Summable (fun n : ℕ => complexThetaMode n z) :=
  complexThetaMode_summable_of_exp_re_pos (exp_two_re_pos_of_mem_thetaStrip hz)

theorem complexThetaDensity_differentiableOn_strip :
    DifferentiableOn ℂ complexThetaDensity thetaStrip := by
  intro z hz
  exact (complexThetaDensity_differentiableAt_of_exp_re_pos
    (exp_two_re_pos_of_mem_thetaStrip hz)).differentiableWithinAt

theorem complexThetaDensity_analyticOnNhd_strip :
    AnalyticOnNhd ℂ complexThetaDensity thetaStrip :=
  complexThetaDensity_differentiableOn_strip.analyticOnNhd isOpen_thetaStrip

/-- Termwise differentiation, from normal convergence. -/
theorem complexThetaDensity_hasSum_deriv_strip {z : ℂ} (hz : z ∈ thetaStrip) :
    HasSum (fun n : ℕ => deriv (complexThetaMode n) z)
      (deriv complexThetaDensity z) := by
  obtain ⟨U, hU, hzU, M, hM, hbound⟩ := complexThetaDensity_local_majorant
    (exp_two_re_pos_of_mem_thetaStrip hz)
  exact Complex.hasSum_deriv_of_summable_norm hM
    (fun n => (complexThetaMode_differentiable n).differentiableOn) hU hbound hzU

end ThetaTrial.Paper
