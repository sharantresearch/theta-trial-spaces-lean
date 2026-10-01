/-
The theta kernel and the series for `Φ`: summability and positivity on
`u ≥ 0`, and the first two derivatives of each summand.
-/
import ThetaTrial.ThetaSeries.LogCoordinate
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

noncomputable section

open Complex MeasureTheory Set

namespace ThetaTrial.ThetaSeries

theorem thetaKernel_eq_jacobi (t : ℝ) :
    thetaKernel t = (jacobiTheta₂ 0 (Complex.I * (t : ℂ))).re := by
  have hc : (thetaKernel t : ℂ) = jacobiTheta₂ 0 (Complex.I * (t : ℂ)) := by
    simpa [thetaKernel] using HurwitzZeta.evenKernel_def 0 t
  simpa using congrArg Complex.re hc

theorem thetaKernel_differentiableAt {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ thetaKernel t := by
  have hj := (differentiableAt_jacobiTheta₂_snd 0
    (show 0 < (Complex.I * (t : ℂ)).im by simpa using ht)).real_of_complex
  have hi : DifferentiableAt ℝ (fun x : ℝ => Complex.I * (x : ℂ)) t := by fun_prop
  have hr := Complex.differentiable_re.differentiableAt.comp t (hj.comp t hi)
  simpa only [Function.comp_def, ← thetaKernel_eq_jacobi] using hr

theorem thetaB_differentiableAt (u : ℝ) : DifferentiableAt ℝ thetaB u := by
  have ht := thetaKernel_differentiableAt (Real.exp_pos (2 * u))
  unfold thetaB thetaTail
  exact (by fun_prop : DifferentiableAt ℝ (fun v : ℝ => Real.exp (v / 2)) u).mul
    (((ht.comp u (by fun_prop)).sub_const 1).div_const 2)

/-- The true theta functional equation in the logarithmic coordinate. -/
theorem thetaB_reflection (u : ℝ) :
    thetaB u - thetaB (-u) = (Real.exp (-u / 2) - Real.exp (u / 2)) / 2 := by
  have hpow : (Real.exp (2 * u)) ^ (1 / 2 : ℝ) = Real.exp u := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have hinv : 1 / Real.exp (2 * u) = Real.exp (2 * -u) := by
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  have ht : thetaKernel (Real.exp (2 * u)) =
      Real.exp (-u) * thetaKernel (Real.exp (2 * -u)) := by
    have heq := HurwitzZeta.evenKernel_functional_equation 0 (Real.exp (2 * u))
    rw [← HurwitzZeta.evenKernel_eq_cosKernel_of_zero, hpow, hinv] at heq
    simpa only [thetaKernel, one_div, ← Real.exp_neg] using heq
  have he : Real.exp (u / 2) * Real.exp (-u) = Real.exp (-u / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold thetaB thetaTail
  rw [ht]
  linear_combination (thetaKernel (Real.exp (2 * -u)) / 2) * he

/-- The boundary term is obtained from the functional equation. -/
theorem thetaB_hasDerivAt_zero : HasDerivAt thetaB (-(1 / 4 : ℝ)) 0 := by
  have hb := (thetaB_differentiableAt 0).hasDerivAt
  have hn : HasDerivAt (fun u : ℝ => thetaB (-u)) (deriv thetaB 0 * -1) 0 := by
    have hbn : HasDerivAt thetaB (deriv thetaB 0) (-(0 : ℝ)) := by simpa using hb
    convert hbn.comp (0 : ℝ) (hasDerivAt_id (0 : ℝ)).neg using 1 <;> rfl
  have hl := hb.sub hn
  have hr : HasDerivAt
      (fun u : ℝ => (Real.exp (-u / 2) - Real.exp (u / 2)) / 2) (-(1 / 2 : ℝ)) 0 := by
    convert ((((hasDerivAt_id (0 : ℝ)).neg.div_const 2).exp).sub
      (((hasDerivAt_id (0 : ℝ)).div_const 2).exp)).div_const 2 using 1 <;>
        first | rfl | norm_num
  have heq : (fun u : ℝ => thetaB u - thetaB (-u)) =
      (fun u : ℝ => (Real.exp (-u / 2) - Real.exp (u / 2)) / 2) :=
    funext thetaB_reflection
  change HasDerivAt (fun u : ℝ => thetaB u - thetaB (-u)) _ _ at hl
  rw [heq] at hl
  have hd := hl.unique hr
  have hd' : deriv thetaB 0 = -(1 / 4 : ℝ) := by linarith
  simpa [hd'] using hb

theorem thetaB_deriv_zero : deriv thetaB 0 = -(1 / 4 : ℝ) :=
  thetaB_hasDerivAt_zero.deriv

def thetaBTerm (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (u / 2) * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u))

def thetaQ (n : ℕ) (u : ℝ) : ℝ := Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u)

def thetaBPrimeTerm (n : ℕ) (u : ℝ) : ℝ := (1 / 2 - 2 * thetaQ n u) * thetaBTerm n u

def thetaBSecondTerm (n : ℕ) (u : ℝ) : ℝ :=
  (1 / 4 - 6 * thetaQ n u + 4 * (thetaQ n u) ^ 2) * thetaBTerm n u

/-- The printed summand, with n+1 making the original positive index explicit. -/
def thetaPhiTerm (n : ℕ) (u : ℝ) : ℝ :=
  (2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u / 2) -
    3 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u / 2)) *
      Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u))

def thetaPhi (u : ℝ) : ℝ := ∑' n : ℕ, thetaPhiTerm n u

theorem thetaBTerm_hasSum (u : ℝ) : HasSum (fun n => thetaBTerm n u) (thetaB u) := by
  exact (thetaTail_hasSum (Real.exp_pos (2 * u))).mul_left (Real.exp (u / 2))

theorem thetaPhiTerm_summable (u : ℝ) : Summable (fun n => thetaPhiTerm n u) := by
  have h4 := (HurwitzKernelBounds.summable_f_nat 4 1 (Real.exp_pos (2 * u))).mul_left
    (2 * Real.pi ^ 2 * Real.exp (9 * u / 2))
  have h2 := (HurwitzKernelBounds.summable_f_nat 2 1 (Real.exp_pos (2 * u))).mul_left
    (3 * Real.pi * Real.exp (5 * u / 2))
  convert h4.sub h2 using 1 <;> try rfl
  funext n
  simp only [HurwitzKernelBounds.f_nat, thetaPhiTerm]
  ring

theorem thetaPhiTerm_factor (n : ℕ) (u : ℝ) :
    thetaPhiTerm n u =
      (Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u / 2)) *
        (2 * thetaQ n u - 3) *
        Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u)) := by
  have he : Real.exp (9 * u / 2) = Real.exp (5 * u / 2) * Real.exp (2 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [thetaPhiTerm, he, thetaQ]
  ring

theorem thetaPhiTerm_pos (n : ℕ) {u : ℝ} (hu : 0 ≤ u) : 0 < thetaPhiTerm n u := by
  have hn : 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have he : 1 ≤ Real.exp (2 * u) := Real.one_le_exp_iff.mpr (by linarith)
  have hm : 1 ≤ ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u) :=
    one_le_mul_of_one_le_of_one_le hn he
  have hq : 0 < 2 * thetaQ n u - 3 := by
    have hmul := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2 * Real.pi by positivity)
    dsimp [thetaQ]
    nlinarith [Real.pi_gt_three]
  rw [thetaPhiTerm_factor]
  exact mul_pos (mul_pos (by positivity) hq) (Real.exp_pos _)

theorem thetaPhi_pos {u : ℝ} (hu : 0 ≤ u) : 0 < thetaPhi u := by
  exact (thetaPhiTerm_summable u).tsum_pos (fun n => (thetaPhiTerm_pos n hu).le)
    0 (thetaPhiTerm_pos 0 hu)

theorem thetaBTerm_hasDerivAt (n : ℕ) (u : ℝ) :
    HasDerivAt (thetaBTerm n) (thetaBPrimeTerm n u) u := by
  have hd := (((hasDerivAt_id u).div_const 2).exp).mul
    (((((hasDerivAt_id u).const_mul 2).exp).const_mul
      (-Real.pi * ((n : ℝ) + 1) ^ 2)).exp)
  convert hd using 1 <;> first | rfl | (dsimp [thetaBTerm, thetaBPrimeTerm, thetaQ]; ring)

theorem thetaBPrimeTerm_hasDerivAt (n : ℕ) (u : ℝ) :
    HasDerivAt (thetaBPrimeTerm n) (thetaBSecondTerm n u) u := by
  have hq : HasDerivAt (thetaQ n) (2 * thetaQ n u) u := by
    convert (((hasDerivAt_id u).const_mul 2).exp).const_mul
      (Real.pi * ((n : ℝ) + 1) ^ 2) using 1 <;> first | rfl | (dsimp [thetaQ]; ring)
  have hd := ((hq.const_mul 2).const_sub (1 / 2)).mul (thetaBTerm_hasDerivAt n u)
  convert hd using 1 <;> first | rfl | (dsimp [thetaBPrimeTerm, thetaBSecondTerm]; ring)

/-- The exact termwise identity behind the two integrations by parts. -/
theorem thetaBSecondTerm_sub_quarter (n : ℕ) (u : ℝ) :
    thetaBSecondTerm n u - thetaBTerm n u / 4 = 2 * thetaPhiTerm n u := by
  have h5 : Real.exp (2 * u) * Real.exp (u / 2) = Real.exp (5 * u / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h9 : Real.exp (2 * u) ^ 2 * Real.exp (u / 2) = Real.exp (9 * u / 2) := by
    rw [pow_two, mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  dsimp [thetaBSecondTerm, thetaBTerm, thetaQ, thetaPhiTerm]
  linear_combination
    (4 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 *
      Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u))) * h9 -
    (6 * Real.pi * ((n : ℝ) + 1) ^ 2 *
      Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u))) * h5

theorem thetaBPrimeTerm_summable (u : ℝ) : Summable (fun n => thetaBPrimeTerm n u) := by
  have h0 := (thetaBTerm_hasSum u).summable.mul_left (1 / 2 : ℝ)
  have h2 := (HurwitzKernelBounds.summable_f_nat 2 1 (Real.exp_pos (2 * u))).mul_left
    (2 * Real.pi * Real.exp (2 * u) * Real.exp (u / 2))
  convert h0.sub h2 using 1 <;> try rfl
  funext n
  dsimp [thetaBPrimeTerm, thetaQ, thetaBTerm, HurwitzKernelBounds.f_nat]
  ring

theorem thetaBSecondTerm_summable (u : ℝ) : Summable (fun n => thetaBSecondTerm n u) := by
  have hs := ((thetaPhiTerm_summable u).mul_left 2).add
    ((thetaBTerm_hasSum u).summable.div_const 4)
  convert hs using 1 <;> try rfl
  funext n
  linarith [thetaBSecondTerm_sub_quarter n u]

/-- A sum identity only; it is not a statement that deriv commutes with tsum. -/
theorem thetaBSecondTerm_tsum_sub_quarter (u : ℝ) :
    (∑' n, thetaBSecondTerm n u) - thetaB u / 4 = 2 * thetaPhi u := by
  rw [← (thetaBTerm_hasSum u).tsum_eq, ← tsum_div_const,
    ← (thetaBSecondTerm_summable u).tsum_sub ((thetaBTerm_hasSum u).summable.div_const 4)]
  simp_rw [thetaBSecondTerm_sub_quarter]
  rw [tsum_mul_left]
  rfl

end ThetaTrial.ThetaSeries
