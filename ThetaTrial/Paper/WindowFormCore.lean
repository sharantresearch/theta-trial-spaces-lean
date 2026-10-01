import ThetaTrial.Paper.WindowFormAssembly
import ThetaTrial.Paper.FormCore

/-! Compact smooth interior functions are a core for the full Weil
form, with its proved coercive shift. -/

noncomputable section
open Complex MeasureTheory Filter
open scoped Topology

namespace ThetaTrial.Paper.WindowFormAssembly
open FormDomain

theorem shiftedForm_diagonal_bounds (a : ℝ) (p : windowFormGraph a) :
    ‖p‖ ^ 2 ≤ (shiftedForm a p p).re ∧
      (shiftedForm a p p).re ≤ 2 * shiftConstant a * ‖p‖ ^ 2 := by
  have hi : (inner ℂ (windowInclusion a p) (windowInclusion a p)).re =
      ‖windowInclusion a p‖ ^ 2 := by
    simpa only [pow_two, RCLike.re_eq_complex_re] using
      inner_self_eq_norm_mul_norm (𝕜 := ℂ) (windowInclusion a p)
  constructor
  · rw [shiftedForm_apply]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hi]
    exact rawForm_shifted_coercive a p
  · have hp := (abs_le.mp (rawForm_diagonal_bound a p)).2
    have hn := physicalInclusion_norm_le a p
    change ‖windowInclusion a p‖ ≤ ‖p‖ at hn
    have hn2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    have hs := (shiftConstant_pos a).le
    rw [shiftedForm_apply]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hi]
    change (rawForm a p p).re ≤ shiftConstant a * ‖p‖ ^ 2 at hp
    nlinarith [mul_le_mul_of_nonneg_left hn2 hs]

/-- The approximants have compact support inside the window and converge in
`L2` and in the shifted form. -/
theorem exists_smooth_full_form_core_sequence {a : ℝ} (ha : 0 < a)
    (p : windowFormGraph a) :
    ∃ u : ℕ → windowFormGraph a,
      (∀ n, u n ∈ smoothCoreVectors a) ∧
      Tendsto u atTop (𝓝 p) ∧
      Tendsto (fun n => ‖windowInclusion a (u n - p)‖) atTop (𝓝 0) ∧
      Tendsto (fun n => (shiftedForm a (u n - p) (u n - p)).re) atTop (𝓝 0) := by
  obtain ⟨u, hu, ht⟩ := exists_smoothCore_sequence ha p
  have hz : Tendsto (fun n => u n - p) atTop (𝓝 0) := by
    simpa only [sub_self] using ht.sub_const p
  refine ⟨u, hu, ht, ?_, ?_⟩
  · simpa only [map_zero, norm_zero, Function.comp_def] using
      ((windowInclusion a).continuous.continuousAt.tendsto.comp hz).norm
  · have hcont : Continuous (fun v : windowFormGraph a => (shiftedForm a v v).re) := by
      fun_prop
    simpa only [map_zero, zero_apply, Complex.zero_re, Function.comp_def] using
      hcont.continuousAt.tendsto.comp hz

#print axioms shiftedForm_diagonal_bounds
#print axioms exists_smooth_full_form_core_sequence

end ThetaTrial.Paper.WindowFormAssembly
