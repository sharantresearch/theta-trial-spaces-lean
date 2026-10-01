/- Gaussian bounds for the theta series, used for the improper integrations
by parts. -/
import ThetaTrial.ThetaSeries.DecayTools
import Mathlib.MeasureTheory.Constructions.Polish.Basic

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology

namespace ThetaTrial.ThetaSeries

def gaussianWeight (k : ℕ) (a u : ℝ) : ℝ :=
  Real.exp (a * u) * HurwitzKernelBounds.F_nat k 1 (Real.exp (2 * u))

theorem gaussianWeight_measurable (k : ℕ) (a : ℝ) : Measurable (gaussianWeight k a) := by
  have hs : Measurable (fun u : ℝ =>
      HurwitzKernelBounds.F_nat k 1 (Real.exp (2 * u))) := by
    apply Measurable.tsum
    intro n
    change Measurable (fun u : ℝ => ((n : ℝ) + 1) ^ k *
      Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u)))
    fun_prop
  exact (by fun_prop : Measurable (fun u : ℝ => Real.exp (a * u))).mul hs

theorem doubleExpEnvelope_mul_exp (a c R u : ℝ) :
    doubleExpEnvelope a c u * Real.exp (R * u) = doubleExpEnvelope (a + R) c u := by
  dsimp [doubleExpEnvelope]
  rw [mul_right_comm, ← Real.exp_add]
  congr 2
  ring

theorem gaussianWeight_norm_le (k : ℕ) (a : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    ‖gaussianWeight k a u‖ ≤
      thetaGaussianMoment k * doubleExpEnvelope a (Real.pi / 2) u := by
  have ht : 1 ≤ Real.exp (2 * u) := Real.one_le_exp_iff.mpr (by linarith)
  have hg := thetaGaussianMoment_decay k ht
  rw [gaussianWeight, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ Real.exp (a * u) *
        (thetaGaussianMoment k * Real.exp (-Real.pi * Real.exp (2 * u) / 2)) :=
      mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le
    _ = _ := by
      rw [show -Real.pi * Real.exp (2 * u) / 2 =
        -(Real.pi / 2) * Real.exp (2 * u) by ring]
      dsimp [doubleExpEnvelope]
      ring

theorem gaussianWeight_mul_norm_le (k : ℕ) (a R : ℝ) {v : ℝ → ℂ}
    (hv : ∀ u, 0 ≤ u → ‖v u‖ ≤ Real.exp (R * u)) {u : ℝ} (hu : 0 ≤ u) :
    ‖(gaussianWeight k a u : ℂ) * v u‖ ≤
      thetaGaussianMoment k * doubleExpEnvelope (a + R) (Real.pi / 2) u := by
  rw [Complex.norm_mul, Complex.norm_real]
  calc
    _ ≤ (thetaGaussianMoment k * doubleExpEnvelope a (Real.pi / 2) u) *
        Real.exp (R * u) :=
      mul_le_mul (gaussianWeight_norm_le k a hu) (hv u hu) (norm_nonneg _) (by
        exact mul_nonneg (thetaGaussianMoment_nonneg k) (by dsimp [doubleExpEnvelope]; positivity))
    _ = _ := by rw [mul_assoc, doubleExpEnvelope_mul_exp]

theorem gaussianWeight_mul_integrable (k : ℕ) (a R : ℝ) {v : ℝ → ℂ}
    (hm : Measurable v) (hv : ∀ u, 0 ≤ u → ‖v u‖ ≤ Real.exp (R * u)) :
    IntegrableOn (fun u : ℝ => (gaussianWeight k a u : ℂ) * v u) (Ioi 0) := by
  have he := (doubleExpEnvelope_integrable (a + R)
    (show 0 < Real.pi / 2 by positivity)).const_mul (thetaGaussianMoment k)
  apply Integrable.mono' he
    (((gaussianWeight_measurable k a).complex_ofReal.mul hm).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact gaussianWeight_mul_norm_le k a R hv hu.le

theorem gaussianWeight_mul_tendsto (k : ℕ) (a R : ℝ) {v : ℝ → ℂ}
    (hv : ∀ u, 0 ≤ u → ‖v u‖ ≤ Real.exp (R * u)) :
    Tendsto (fun u : ℝ => (gaussianWeight k a u : ℂ) * v u) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun u =>
    thetaGaussianMoment k * doubleExpEnvelope (a + R) (Real.pi / 2) u)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    exact gaussianWeight_mul_norm_le k a R hv hu
  · simpa using (doubleExpEnvelope_tendsto (a + R)
      (show 0 < Real.pi / 2 by positivity)).const_mul (thetaGaussianMoment k)

theorem thetaB_eq_gaussianWeight (u : ℝ) : thetaB u = gaussianWeight 0 (1 / 2) u := by
  rw [← (thetaBTerm_hasSum u).tsum_eq, gaussianWeight, HurwitzKernelBounds.F_nat,
    ← tsum_mul_left]
  apply tsum_congr
  intro n
  simp [thetaBTerm, HurwitzKernelBounds.f_nat, div_eq_mul_inv, mul_comm]

theorem thetaBPrime_eq_gaussianWeight (u : ℝ) :
    thetaBPrime u = (1 / 2) * gaussianWeight 0 (1 / 2) u -
      2 * Real.pi * gaussianWeight 2 (5 / 2) u := by
  have h0 := (thetaBTerm_hasSum u).mul_left (1 / 2 : ℝ)
  have h2 := (HurwitzKernelBounds.summable_f_nat 2 1 (Real.exp_pos (2 * u))).hasSum.mul_left
    (2 * Real.pi * Real.exp (5 * u / 2))
  have he : Real.exp (2 * u) * Real.exp (u / 2) = Real.exp (5 * u / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hterm : (fun n => (1 / 2 : ℝ) * thetaBTerm n u -
      (2 * Real.pi * Real.exp (5 * u / 2)) *
        HurwitzKernelBounds.f_nat 2 1 (Real.exp (2 * u)) n) =
      (fun n => thetaBPrimeTerm n u) := by
    funext n
    dsimp [thetaBPrimeTerm, thetaBTerm, thetaQ, HurwitzKernelBounds.f_nat]
    rw [← he]
    ring
  have hs := (h0.sub h2).tsum_eq
  rw [hterm, thetaB_eq_gaussianWeight] at hs
  change thetaBPrime u = _ at hs
  rw [hs]
  dsimp [gaussianWeight, HurwitzKernelBounds.F_nat]
  congr 1
  rw [show 5 * u / 2 = (5 / 2 : ℝ) * u by ring]
  ring

theorem thetaPhi_eq_gaussianWeight (u : ℝ) :
    thetaPhi u = 2 * Real.pi ^ 2 * gaussianWeight 4 (9 / 2) u -
      3 * Real.pi * gaussianWeight 2 (5 / 2) u := by
  have h4 := (HurwitzKernelBounds.summable_f_nat 4 1 (Real.exp_pos (2 * u))).hasSum.mul_left
    (2 * Real.pi ^ 2 * Real.exp (9 * u / 2))
  have h2 := (HurwitzKernelBounds.summable_f_nat 2 1 (Real.exp_pos (2 * u))).hasSum.mul_left
    (3 * Real.pi * Real.exp (5 * u / 2))
  have hterm : (fun n => (2 * Real.pi ^ 2 * Real.exp (9 * u / 2)) *
      HurwitzKernelBounds.f_nat 4 1 (Real.exp (2 * u)) n -
      (3 * Real.pi * Real.exp (5 * u / 2)) *
      HurwitzKernelBounds.f_nat 2 1 (Real.exp (2 * u)) n) =
      (fun n => thetaPhiTerm n u) := by
    funext n
    dsimp [HurwitzKernelBounds.f_nat, thetaPhiTerm]
    ring
  have hs := (h4.sub h2).tsum_eq
  rw [hterm] at hs
  change thetaPhi u = _ at hs
  rw [hs]
  dsimp [gaussianWeight, HurwitzKernelBounds.F_nat]
  rw [show 9 * u / 2 = (9 / 2 : ℝ) * u by ring,
    show 5 * u / 2 = (5 / 2 : ℝ) * u by ring]
  ring

theorem norm_cosh_mul_ofReal_le (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖Complex.cosh ((u : ℂ) * z)‖ ≤ Real.exp (‖z‖ * u) := by
  have hpos : ‖Complex.exp ((u : ℂ) * z)‖ ≤ Real.exp (‖z‖ * u) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith [mul_le_mul_of_nonneg_left (Complex.re_le_norm z) hu]
  have hneg : ‖Complex.exp (-((u : ℂ) * z))‖ ≤ Real.exp (‖z‖ * u) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    have hz : -z.re ≤ ‖z‖ := by simpa using Complex.re_le_norm (-z)
    nlinarith [mul_le_mul_of_nonneg_left hz hu]
  rw [Complex.cosh, Complex.norm_div, Complex.norm_ofNat]
  have hn := norm_add_le (Complex.exp ((u : ℂ) * z)) (Complex.exp (-((u : ℂ) * z)))
  linarith

theorem norm_sinh_mul_ofReal_le (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖Complex.sinh ((u : ℂ) * z)‖ ≤ Real.exp (‖z‖ * u) := by
  have hpos : ‖Complex.exp ((u : ℂ) * z)‖ ≤ Real.exp (‖z‖ * u) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith [mul_le_mul_of_nonneg_left (Complex.re_le_norm z) hu]
  have hneg : ‖Complex.exp (-((u : ℂ) * z))‖ ≤ Real.exp (‖z‖ * u) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    have hz : -z.re ≤ ‖z‖ := by simpa using Complex.re_le_norm (-z)
    nlinarith [mul_le_mul_of_nonneg_left hz hu]
  rw [Complex.sinh, Complex.norm_div, Complex.norm_ofNat]
  have hn := norm_sub_le (Complex.exp ((u : ℂ) * z)) (Complex.exp (-((u : ℂ) * z)))
  linarith

theorem thetaBPrime_mul_integrable (R : ℝ) {v : ℝ → ℂ}
    (hm : Measurable v) (hv : ∀ u, 0 ≤ u → ‖v u‖ ≤ Real.exp (R * u)) :
    IntegrableOn (fun u : ℝ => (thetaBPrime u : ℂ) * v u) (Ioi 0) := by
  have h0 := (gaussianWeight_mul_integrable 0 (1 / 2) R hm hv).const_mul (1 / 2 : ℂ)
  have h2 := (gaussianWeight_mul_integrable 2 (5 / 2) R hm hv).const_mul
    ((2 * Real.pi : ℝ) : ℂ)
  have hs : IntegrableOn (fun u : ℝ =>
      (1 / 2 : ℂ) * ((gaussianWeight 0 (1 / 2) u : ℂ) * v u) -
        ((2 * Real.pi : ℝ) : ℂ) * ((gaussianWeight 2 (5 / 2) u : ℂ) * v u)) (Ioi 0) :=
    h0.sub h2
  apply hs.congr_fun _ measurableSet_Ioi
  intro u _
  dsimp only
  rw [thetaBPrime_eq_gaussianWeight]
  push_cast
  ring

theorem thetaPhi_mul_integrable (R : ℝ) {v : ℝ → ℂ}
    (hm : Measurable v) (hv : ∀ u, 0 ≤ u → ‖v u‖ ≤ Real.exp (R * u)) :
    IntegrableOn (fun u : ℝ => (thetaPhi u : ℂ) * v u) (Ioi 0) := by
  have h4 := (gaussianWeight_mul_integrable 4 (9 / 2) R hm hv).const_mul
    ((2 * Real.pi ^ 2 : ℝ) : ℂ)
  have h2 := (gaussianWeight_mul_integrable 2 (5 / 2) R hm hv).const_mul
    ((3 * Real.pi : ℝ) : ℂ)
  have hs : IntegrableOn (fun u : ℝ =>
      ((2 * Real.pi ^ 2 : ℝ) : ℂ) * ((gaussianWeight 4 (9 / 2) u : ℂ) * v u) -
        ((3 * Real.pi : ℝ) : ℂ) * ((gaussianWeight 2 (5 / 2) u : ℂ) * v u)) (Ioi 0) :=
    h4.sub h2
  apply hs.congr_fun _ measurableSet_Ioi
  intro u _
  dsimp only
  rw [thetaPhi_eq_gaussianWeight]
  push_cast
  ring

theorem thetaB_mul_tendsto (R : ℝ) {v : ℝ → ℂ}
    (hv : ∀ u, 0 ≤ u → ‖v u‖ ≤ Real.exp (R * u)) :
    Tendsto (fun u : ℝ => (thetaB u : ℂ) * v u) atTop (𝓝 0) := by
  simpa only [thetaB_eq_gaussianWeight] using gaussianWeight_mul_tendsto 0 (1 / 2) R hv

theorem thetaBPrime_mul_tendsto (R : ℝ) {v : ℝ → ℂ}
    (hv : ∀ u, 0 ≤ u → ‖v u‖ ≤ Real.exp (R * u)) :
    Tendsto (fun u : ℝ => (thetaBPrime u : ℂ) * v u) atTop (𝓝 0) := by
  have h0 := (gaussianWeight_mul_tendsto 0 (1 / 2) R hv).const_mul (1 / 2 : ℂ)
  have h2 := (gaussianWeight_mul_tendsto 2 (5 / 2) R hv).const_mul
    ((2 * Real.pi : ℝ) : ℂ)
  have hs : Tendsto (fun u : ℝ =>
      (1 / 2 : ℂ) * ((gaussianWeight 0 (1 / 2) u : ℂ) * v u) -
        ((2 * Real.pi : ℝ) : ℂ) * ((gaussianWeight 2 (5 / 2) u : ℂ) * v u)) atTop (𝓝 0) := by
    simpa only [mul_zero, sub_zero] using h0.sub h2
  apply hs.congr'
  filter_upwards with u
  rw [thetaBPrime_eq_gaussianWeight]
  push_cast
  ring

end ThetaTrial.ThetaSeries
