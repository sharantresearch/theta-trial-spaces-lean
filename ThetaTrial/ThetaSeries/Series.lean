/-
Termwise differentiation of the theta series: local summable bounds for the
derivatives, and the resulting `HasDerivAt` statements.
-/
import ThetaTrial.ThetaSeries.Kernel
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic.GCongr

noncomputable section

open Set

namespace ThetaTrial.ThetaSeries

def thetaBPrime (u : ℝ) : ℝ := ∑' n : ℕ, thetaBPrimeTerm n u

/-- Positive Gaussian majorant for B_n on the closed unit neighborhood of c. -/
def thetaBLocalBound (c : ℝ) (n : ℕ) : ℝ :=
  Real.exp ((c + 1) / 2) *
    Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * (c - 1)))

def thetaBPrimeLocalBound (c : ℝ) (n : ℕ) : ℝ :=
  (1 / 2 + 2 * thetaQ n (c + 1)) * thetaBLocalBound c n

def thetaBSecondLocalBound (c : ℝ) (n : ℕ) : ℝ :=
  (1 / 4 + 6 * thetaQ n (c + 1) + 4 * (thetaQ n (c + 1)) ^ 2) *
    thetaBLocalBound c n

theorem thetaQ_nonneg (n : ℕ) (u : ℝ) : 0 ≤ thetaQ n u := by
  dsimp [thetaQ]
  positivity

theorem thetaQ_mono (n : ℕ) : Monotone (thetaQ n) := by
  intro u v huv
  dsimp [thetaQ]
  gcongr

theorem thetaBTerm_le_localBound (c : ℝ) (n : ℕ) {u : ℝ}
    (hu : u ∈ Icc (c - 1) (c + 1)) : thetaBTerm n u ≤ thetaBLocalBound c n := by
  dsimp [thetaBTerm, thetaBLocalBound]
  apply mul_le_mul
  · gcongr
    exact hu.2
  · apply Real.exp_le_exp.mpr
    have he : Real.exp (2 * (c - 1)) ≤ Real.exp (2 * u) := by gcongr; exact hu.1
    have hn : 0 ≤ Real.pi * ((n : ℝ) + 1) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left he hn]
  · positivity
  · positivity

theorem thetaBPrimeTerm_norm_le_localBound (c : ℝ) (n : ℕ) {u : ℝ}
    (hu : u ∈ Icc (c - 1) (c + 1)) :
    ‖thetaBPrimeTerm n u‖ ≤ thetaBPrimeLocalBound c n := by
  have hq := thetaQ_nonneg n u
  have hQ := thetaQ_nonneg n (c + 1)
  have hle := thetaQ_mono n hu.2
  have hc : |1 / 2 - 2 * thetaQ n u| ≤ 1 / 2 + 2 * thetaQ n (c + 1) := by
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [thetaBPrimeTerm, norm_mul, Real.norm_eq_abs,
    Real.norm_of_nonneg (show 0 ≤ thetaBTerm n u by dsimp [thetaBTerm]; positivity)]
  exact mul_le_mul hc (thetaBTerm_le_localBound c n hu)
    (by dsimp [thetaBTerm]; positivity) (by positivity)

theorem thetaBSecondTerm_norm_le_localBound (c : ℝ) (n : ℕ) {u : ℝ}
    (hu : u ∈ Icc (c - 1) (c + 1)) :
    ‖thetaBSecondTerm n u‖ ≤ thetaBSecondLocalBound c n := by
  have hq := thetaQ_nonneg n u
  have hQ := thetaQ_nonneg n (c + 1)
  have hle := thetaQ_mono n hu.2
  have hs : (thetaQ n u) ^ 2 ≤ (thetaQ n (c + 1)) ^ 2 :=
    (sq_le_sq₀ hq hQ).2 hle
  have hc : |1 / 4 - 6 * thetaQ n u + 4 * (thetaQ n u) ^ 2| ≤
      1 / 4 + 6 * thetaQ n (c + 1) + 4 * (thetaQ n (c + 1)) ^ 2 := by
    exact abs_le.mpr ⟨by nlinarith [sq_nonneg (thetaQ n u)], by nlinarith⟩
  rw [thetaBSecondTerm, norm_mul, Real.norm_eq_abs,
    Real.norm_of_nonneg (show 0 ≤ thetaBTerm n u by dsimp [thetaBTerm]; positivity)]
  exact mul_le_mul hc (thetaBTerm_le_localBound c n hu)
    (by dsimp [thetaBTerm]; positivity) (by positivity)

theorem thetaBPrimeLocalBound_summable (c : ℝ) : Summable (thetaBPrimeLocalBound c) := by
  have h0 := (HurwitzKernelBounds.summable_f_nat 0 1
    (Real.exp_pos (2 * (c - 1)))).mul_left (Real.exp ((c + 1) / 2) / 2)
  have h2 := (HurwitzKernelBounds.summable_f_nat 2 1
    (Real.exp_pos (2 * (c - 1)))).mul_left
      (2 * Real.pi * Real.exp (2 * (c + 1)) * Real.exp ((c + 1) / 2))
  convert h0.add h2 using 1 <;> try rfl
  funext n
  dsimp [thetaBPrimeLocalBound, thetaBLocalBound, thetaQ, HurwitzKernelBounds.f_nat]
  ring

theorem thetaBSecondLocalBound_summable (c : ℝ) : Summable (thetaBSecondLocalBound c) := by
  have h0 := (HurwitzKernelBounds.summable_f_nat 0 1
    (Real.exp_pos (2 * (c - 1)))).mul_left (Real.exp ((c + 1) / 2) / 4)
  have h2 := (HurwitzKernelBounds.summable_f_nat 2 1
    (Real.exp_pos (2 * (c - 1)))).mul_left
      (6 * Real.pi * Real.exp (2 * (c + 1)) * Real.exp ((c + 1) / 2))
  have h4 := (HurwitzKernelBounds.summable_f_nat 4 1
    (Real.exp_pos (2 * (c - 1)))).mul_left
      (4 * Real.pi ^ 2 * Real.exp (2 * (c + 1)) ^ 2 * Real.exp ((c + 1) / 2))
  convert (h0.add h2).add h4 using 1 <;> try rfl
  funext n
  dsimp [thetaBSecondLocalBound, thetaBLocalBound, thetaQ, HurwitzKernelBounds.f_nat]
  ring

/-- First derivative of the theta B function. -/
theorem thetaB_hasDerivAt_series (u : ℝ) : HasDerivAt thetaB (thetaBPrime u) u := by
  have hu : u ∈ Ioo (u - 1) (u + 1) := ⟨by linarith, by linarith⟩
  have hd := hasDerivAt_tsum_of_isPreconnected
    (thetaBPrimeLocalBound_summable u) isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => thetaBTerm_hasDerivAt n y)
    (fun n y hy => thetaBPrimeTerm_norm_le_localBound u n ⟨hy.1.le, hy.2.le⟩)
    hu (thetaBTerm_hasSum u).summable hu
  have heq : (fun y : ℝ => ∑' n : ℕ, thetaBTerm n y) = thetaB :=
    funext (fun y => (thetaBTerm_hasSum y).tsum_eq)
  rw [heq] at hd
  exact hd

theorem thetaB_deriv_eq_prime : deriv thetaB = thetaBPrime := by
  funext u
  exact (thetaB_hasDerivAt_series u).deriv

/-- Derivative of the first-derivative series, using the second local bound. -/
theorem thetaBPrime_hasDerivAt_series (u : ℝ) :
    HasDerivAt thetaBPrime (thetaB u / 4 + 2 * thetaPhi u) u := by
  have hu : u ∈ Ioo (u - 1) (u + 1) := ⟨by linarith, by linarith⟩
  have hd := hasDerivAt_tsum_of_isPreconnected
    (thetaBSecondLocalBound_summable u) isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => thetaBPrimeTerm_hasDerivAt n y)
    (fun n y hy => thetaBSecondTerm_norm_le_localBound u n ⟨hy.1.le, hy.2.le⟩)
    hu (thetaBPrimeTerm_summable u) hu
  convert hd using 1 <;> try rfl
  linarith [thetaBSecondTerm_tsum_sub_quarter u]

theorem thetaBPrime_zero : thetaBPrime 0 = -(1 / 4 : ℝ) := by
  rw [← thetaB_deriv_eq_prime]
  exact thetaB_deriv_zero

end ThetaTrial.ThetaSeries
