import ThetaTrial.Paper.ThetaNormalization
import ThetaTrial.Paper.ThetaStrip
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic

/-!
# Evenness and closed-strip decay of the complex theta density

The identity theorem extends the proved real evenness to the connected
theta strip. Gaussian summation gives a uniform double-exponential
bound on each closed substrip; Cauchy estimates transfer it to derivatives.
-/

noncomputable section
open Set Metric Filter
open scoped Topology

namespace ThetaTrial.Paper

theorem convex_thetaStrip : Convex ℝ thetaStrip := by
  have heq : thetaStrip = Complex.imLm ⁻¹' Ioo (-(Real.pi / 4)) (Real.pi / 4) := by
    ext z
    simp [thetaStrip, abs_lt]
  rw [heq]
  exact (convex_Ioo _ _).linear_preimage Complex.imLm

theorem complexThetaDensity_neg {z : ℂ} (hz : z ∈ thetaStrip) :
    complexThetaDensity (-z) = complexThetaDensity z := by
  have hneg : AnalyticOnNhd ℂ (fun w => complexThetaDensity (-w)) thetaStrip := by
    intro w hw
    have hnw : -w ∈ thetaStrip := by simpa [thetaStrip] using hw
    exact (complexThetaDensity_analyticOnNhd_strip (-w) hnw).comp
      (analyticAt_id.neg)
  have hz0 : (0 : ℂ) ∈ thetaStrip := by
    simp only [thetaStrip, mem_ofPred_eq, Complex.zero_im, abs_zero]
    positivity
  have hclosure : (0 : ℂ) ∈ closure
      ({w | complexThetaDensity (-w) = complexThetaDensity w} \ {(0 : ℂ)}) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    refine ⟨((ε / 2 : ℝ) : ℂ), ?_, ?_⟩
    · constructor
      · change complexThetaDensity (-((ε / 2 : ℝ) : ℂ)) =
          complexThetaDensity ((ε / 2 : ℝ) : ℂ)
        simpa only [Complex.ofReal_neg] using complexThetaDensity_even_real (ε / 2)
      · simp only [mem_singleton_iff, Complex.ofReal_eq_zero]
        positivity
    · rw [dist_zero_left, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
  exact hneg.eqOn_of_preconnected_of_mem_closure
    complexThetaDensity_analyticOnNhd_strip convex_thetaStrip.isPreconnected hz0 hclosure hz

private theorem cos_lower_on_closed_strip {b : ℝ} (hb : 0 ≤ b)
    (hbpi : b < Real.pi / 4) {z : ℂ} (hz : |z.im| ≤ b) :
    Real.cos (2 * b) ≤ Real.cos (2 * z.im) := by
  have hh := Real.cos_le_cos_of_nonneg_of_le_pi
    (show 0 ≤ 2 * |z.im| by positivity)
    (show 2 * b ≤ Real.pi by linarith [Real.pi_pos])
    (show 2 * |z.im| ≤ 2 * b by linarith)
  have heq : 2 * |z.im| = |2 * z.im| := by rw [abs_mul]; norm_num
  rw [heq, Real.cos_abs] at hh
  exact hh

private theorem cosine_positive {b : ℝ} (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) :
    0 < Real.cos (2 * b) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_pos]

private theorem gaussian_split (n : ℕ) {c q : ℝ} (hc : 0 ≤ c) (hcq : c ≤ q) :
    Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * q) ≤
      Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * (c / 2)) *
        Real.exp (-Real.pi * q / 2) := by
  have hn : 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hq : 0 ≤ q := hc.trans hcq
  have h1 := mul_le_mul_of_nonneg_right hn hq
  have h2 := mul_le_mul_of_nonneg_left hcq (sq_nonneg ((n : ℝ) + 1))
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (show q + ((n : ℝ) + 1) ^ 2 * c ≤
      2 * ((n : ℝ) + 1) ^ 2 * q by nlinarith) Real.pi_pos.le
  nlinarith

theorem complexThetaDensity_right_strip_decay {b : ℝ} (hb : 0 ≤ b)
    (hbpi : b < Real.pi / 4) :
    ∃ C > 0, ∀ z : ℂ, 0 ≤ z.re → |z.im| ≤ b →
      ‖complexThetaDensity z‖ ≤ C * Real.exp (9 * z.re / 2) *
        Real.exp (-(Real.pi * Real.cos (2 * b) / 2) * Real.exp (2 * z.re)) := by
  let c := Real.cos (2 * b)
  have hc : 0 < c := cosine_positive hb hbpi
  let M : ℕ → ℝ := fun n =>
    (4 * Real.pi ^ 2) * HurwitzKernelBounds.f_nat 4 1 (c / 2) n +
    (6 * Real.pi) * HurwitzKernelBounds.f_nat 2 1 (c / 2) n
  have hM : Summable M :=
    ((HurwitzKernelBounds.summable_f_nat 4 1 (by positivity : 0 < c / 2)).mul_left
      (4 * Real.pi ^ 2)).add
      ((HurwitzKernelBounds.summable_f_nat 2 1 (by positivity : 0 < c / 2)).mul_left
        (6 * Real.pi))
  have hMpos : ∀ n, 0 < M n := by intro n; dsimp [M, HurwitzKernelBounds.f_nat]; positivity
  refine ⟨∑' n, M n, hM.tsum_pos (fun n => (hMpos n).le) 0 (hMpos 0), ?_⟩
  intro z hx hy
  let q := c * Real.exp (2 * z.re)
  have hcq : c ≤ q := by
    have h := Real.one_le_exp_iff.mpr (show 0 ≤ 2 * z.re by linarith)
    dsimp [q]
    nlinarith
  have hq : q ≤ (Complex.exp (2 * z)).re := by
    have hcos := cos_lower_on_closed_strip hb hbpi hy
    rw [Complex.exp_re]
    norm_num [Complex.mul_re, Complex.mul_im]
    dsimp [q, c]
    nlinarith [mul_le_mul_of_nonneg_left hcos (Real.exp_pos (2 * z.re)).le]
  have hA : ‖Complex.exp (9 * z / 2)‖ ≤ Real.exp (9 * z.re / 2) := by
    rw [Complex.norm_exp]
    norm_num [Complex.div_re, Complex.mul_re]
  have hB : ‖Complex.exp (5 * z / 2)‖ ≤ Real.exp (9 * z.re / 2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    norm_num [Complex.div_re, Complex.mul_re]
    linarith
  let E := Real.exp (9 * z.re / 2) * Real.exp (-Real.pi * q / 2)
  have hbound (n : ℕ) : ‖complexThetaMode n z‖ ≤ M n * E := by
    have hmode := complexThetaMode_norm_le n z hq hA hB
    have hsplit := gaussian_split n hc.le hcq
    have hcoef : 0 ≤ 4 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 +
        6 * Real.pi * ((n : ℝ) + 1) ^ 2 := by positivity
    calc
      _ ≤ (Real.exp (9 * z.re / 2) *
          (4 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 +
            6 * Real.pi * ((n : ℝ) + 1) ^ 2)) *
          Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * q) := by
        convert hmode using 1
        unfold HurwitzKernelBounds.f_nat
        ring
      _ ≤ (Real.exp (9 * z.re / 2) *
          (4 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 +
            6 * Real.pi * ((n : ℝ) + 1) ^ 2)) *
          (Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * (c / 2)) *
            Real.exp (-Real.pi * q / 2)) :=
        mul_le_mul_of_nonneg_left hsplit (mul_nonneg (Real.exp_pos _).le hcoef)
      _ = M n * E := by dsimp [M, E, HurwitzKernelBounds.f_nat]; ring
  have hs := tsum_of_norm_bounded (hM.hasSum.mul_right E) hbound
  change ‖complexThetaDensity z‖ ≤ _ at hs
  calc
    _ ≤ (∑' n, M n) * E := hs
    _ = _ := by
      dsimp [E, q, c]
      have he : -Real.pi * (Real.cos (2 * b) * Real.exp (2 * z.re)) / 2 =
          -(Real.pi * Real.cos (2 * b) / 2) * Real.exp (2 * z.re) := by ring
      rw [he]
      ring

theorem complexThetaDensity_closed_strip_decay {b : ℝ} (hb : 0 ≤ b)
    (hbpi : b < Real.pi / 4) :
    ∃ C > 0, ∃ c > 0, ∀ z : ℂ, |z.im| ≤ b →
      ‖complexThetaDensity z‖ ≤ C * Real.exp (9 * |z.re| / 2) *
        Real.exp (-c * Real.exp (2 * |z.re|)) := by
  obtain ⟨C, hC, hbound⟩ := complexThetaDensity_right_strip_decay hb hbpi
  refine ⟨C, hC, Real.pi * Real.cos (2 * b) / 2, ?_, ?_⟩
  · exact div_pos (mul_pos Real.pi_pos (cosine_positive hb hbpi)) (by norm_num)
  · intro z hz
    rcases le_total 0 z.re with hx | hx
    · simpa [abs_of_nonneg hx] using hbound z hx hz
    · have hneg := hbound (-z) (by simpa using neg_nonneg.mpr hx)
        (by simpa using hz)
      have hstrip : z ∈ thetaStrip := lt_of_le_of_lt hz hbpi
      rw [complexThetaDensity_neg hstrip] at hneg
      simpa [abs_of_nonpos hx] using hneg

private theorem coordinates_on_disc {z w : ℂ} {r : ℝ}
    (hw : w ∈ closedBall z r) :
    |w.re| ≤ |z.re| + r ∧ |z.re| - r ≤ |w.re| ∧ |w.im| ≤ |z.im| + r := by
  have hn : ‖w - z‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hw
  have hre : |w.re - z.re| ≤ r := by
    simpa only [Complex.sub_re] using (Complex.abs_re_le_norm (w - z)).trans hn
  have him : |w.im - z.im| ≤ r := by
    simpa only [Complex.sub_im] using (Complex.abs_im_le_norm (w - z)).trans hn
  have hreal := abs_le.mp ((abs_abs_sub_abs_le_abs_sub w.re z.re).trans hre)
  have himag := (abs_sub_abs_le_abs_sub w.im z.im).trans him
  constructor
  · linarith [hreal.2]
  constructor
  · linarith [hreal.1]
  · linarith

/-- Uniform decay for every fixed derivative on any closed substrip.
The positive double-exponential constant can be chosen independently of the
derivative order; the prefactor constant may depend on that order. -/
theorem complexThetaDensity_iteratedDeriv_closed_strip_decay {b : ℝ}
    (hb : 0 ≤ b) (hbpi : b < Real.pi / 4) :
    ∃ c > 0, ∀ j : ℕ, ∃ C > 0, ∀ z : ℂ, |z.im| ≤ b →
      ‖iteratedDeriv j complexThetaDensity z‖ ≤
        C * Real.exp (((9 / 2 : ℝ) + 2 * (j : ℝ)) * |z.re|) *
          Real.exp (-c * Real.exp (2 * |z.re|)) := by
  let b' : ℝ := (b + Real.pi / 4) / 2
  let r : ℝ := (Real.pi / 4 - b) / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hb' : 0 ≤ b' := by dsimp [b']; positivity
  have hb'pi : b' < Real.pi / 4 := by dsimp [b']; linarith
  have hbr : b + r = b' := by dsimp [r, b']; ring
  obtain ⟨C₀, hC₀, c₀, hc₀, hzero⟩ := complexThetaDensity_closed_strip_decay hb' hb'pi
  let C' := C₀ * Real.exp (9 * r / 2)
  let c' := c₀ * Real.exp (-2 * r)
  have hC' : 0 < C' := mul_pos hC₀ (Real.exp_pos _)
  have hc' : 0 < c' := mul_pos hc₀ (Real.exp_pos _)
  have hdisc (z : ℂ) (hz : |z.im| ≤ b) : closedBall z r ⊆ thetaStrip := by
    intro w hw
    have hcoord := coordinates_on_disc hw
    have hwy : |w.im| ≤ b' := by linarith [hcoord.2.2]
    exact lt_of_le_of_lt hwy hb'pi
  have hdiscBound (z : ℂ) (hz : |z.im| ≤ b) (w : ℂ) (hw : w ∈ closedBall z r) :
      ‖complexThetaDensity w‖ ≤ C' * Real.exp (9 * |z.re| / 2) *
        Real.exp (-c' * Real.exp (2 * |z.re|)) := by
    obtain ⟨hreup, hrelow, him⟩ := coordinates_on_disc hw
    have hwy : |w.im| ≤ b' := by linarith
    have hweight : Real.exp (9 * |w.re| / 2) ≤
        Real.exp (9 * r / 2) * Real.exp (9 * |z.re| / 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    have hinner : Real.exp (-2 * r) * Real.exp (2 * |z.re|) ≤
        Real.exp (2 * |w.re|) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    have hdecay : Real.exp (-c₀ * Real.exp (2 * |w.re|)) ≤
        Real.exp (-c' * Real.exp (2 * |z.re|)) := by
      apply Real.exp_le_exp.mpr
      dsimp [c']
      nlinarith [mul_le_mul_of_nonneg_left hinner hc₀.le]
    calc
      _ ≤ C₀ * Real.exp (9 * |w.re| / 2) *
          Real.exp (-c₀ * Real.exp (2 * |w.re|)) := hzero w hwy
      _ ≤ C₀ * (Real.exp (9 * r / 2) * Real.exp (9 * |z.re| / 2)) *
          Real.exp (-c' * Real.exp (2 * |z.re|)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hweight hC₀.le) hdecay
          (Real.exp_pos _).le (by positivity)
      _ = _ := by dsimp [C']; ring
  refine ⟨c', hc', ?_⟩
  intro j
  let C := (j.factorial : ℝ) * C' / r ^ j
  have hfac : 0 < (j.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos j)
  have hC : 0 < C := div_pos (mul_pos hfac hC') (pow_pos hr j)
  refine ⟨C, hC, ?_⟩
  intro z hz
  have hbound := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hr
    (complexThetaDensity_differentiableOn_strip.diffContOnCl_ball (hdisc z hz))
    (fun w hw => hdiscBound z hz w (sphere_subset_closedBall hw))
  have hweight : Real.exp (9 * |z.re| / 2) ≤
      Real.exp (((9 / 2 : ℝ) + 2 * (j : ℝ)) * |z.re|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) (abs_nonneg z.re)]
  calc
    _ ≤ (j.factorial : ℝ) * (C' * Real.exp (9 * |z.re| / 2) *
        Real.exp (-c' * Real.exp (2 * |z.re|))) / r ^ j := hbound
    _ = C * Real.exp (9 * |z.re| / 2) *
        Real.exp (-c' * Real.exp (2 * |z.re|)) := by dsimp [C]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hweight hC.le) (Real.exp_pos _).le

end ThetaTrial.Paper
