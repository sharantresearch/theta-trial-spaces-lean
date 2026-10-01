import ThetaTrial.Paper.TailFormBound
import Mathlib.Analysis.BoundedVariation
import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
The weighted BV norm of the paper, defined through the derivative measure.
For a BV function, Mathlib constructs the derivative as a complex vector
measure, whose total variation includes the jump atoms. Taking right limits
removes changes at single points before the Fourier estimates are applied.
-/

noncomputable section
open MeasureTheory Set Filter
open ThetaTrial.PrimeContinuity
open scoped Topology ENNReal ComplexConjugate

namespace ThetaTrial.Paper

theorem bv_ae_eq_rightLim {f : ℝ → ℂ} (hv : BoundedVariationOn f univ) :
    f =ᵐ[volume] f.rightLim := by
  filter_upwards [hv.locallyBoundedVariationOn.ae_differentiableAt] with x hx
  exact hx.continuousAt.continuousWithinAt.rightLim_eq.symm

private theorem sum_measure_adjacent_Ioc (μ : Measure ℝ) (u : ℕ → ℝ) (hu : Monotone u)
    (n : ℕ) :
    (∑ i ∈ Finset.range n, μ (Ioc (u i) (u (i + 1)))) = μ (Ioc (u 0) (u n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hd : Disjoint (Ioc (u 0) (u n)) (Ioc (u n) (u (n + 1))) := by
      apply disjoint_left.mpr
      intro x hx hy
      exact hy.1.not_ge hx.2
    rw [← measure_union hd measurableSet_Ioc,
      Ioc_union_Ioc_eq_Ioc (hu (Nat.zero_le n)) (hu (Nat.le_succ n))]

/-- Canonical partition variation is bounded by the total variation of the
derivative vector measure. No Stieltjes integration by parts is used. -/
theorem rightLim_variation_le_derivativeMeasure {f : ℝ → ℂ}
    (hv : BoundedVariationOn f univ) :
    eVariationOn f.rightLim univ ≤ hv.vectorMeasure.variation univ := by
  unfold eVariationOn
  refine iSup_le fun ⟨n, u, hu, _⟩ => ?_
  calc
    _ ≤ ∑ i ∈ Finset.range n, hv.vectorMeasure.variation (Ioc (u i) (u (i + 1))) := by
      apply Finset.sum_le_sum
      intro i _
      rw [edist_eq_enorm_sub, ← hv.vectorMeasure_Ioc (hu (Nat.le_succ i))]
      exact MeasureTheory.VectorMeasure.enorm_measure_le_variation _ _
    _ = hv.vectorMeasure.variation (Ioc (u 0) (u n)) :=
      sum_measure_adjacent_Ioc _ u hu n
    _ ≤ _ := measure_mono (subset_univ _)

/-- The weighted derivative-measure norm `M(t)` of the paper. -/
def weightedBVMeasureBudget (f : ℝ → ℂ) (hv : BoundedVariationOn f univ) : ℝ :=
  (∫ x : ℝ, ‖weightedProfile 1 f x‖) +
    ∫ x : ℝ, Real.exp |x| ∂hv.vectorMeasure.variation

theorem finite_derivativeVariation_of_weighted_moment {f : ℝ → ℂ}
    (hv : BoundedVariationOn f univ)
    (hm : Integrable (fun x : ℝ => Real.exp |x|) hv.vectorMeasure.variation) :
    IsFiniteMeasure hv.vectorMeasure.variation := by
  have hi : Integrable (fun _ : ℝ => (1 : ℝ)) hv.vectorMeasure.variation := by
    apply hm.mono' aestronglyMeasurable_const
    filter_upwards [] with x
    simp only [norm_one]
    exact Real.one_le_exp_iff.mpr (abs_nonneg x)
  exact (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℝ) ≠ 0)).mp hi

theorem weightedBVMeasureBudget_nonneg {f : ℝ → ℂ} (hv : BoundedVariationOn f univ) :
    0 ≤ weightedBVMeasureBudget f hv := by
  unfold weightedBVMeasureBudget
  exact add_nonneg (integral_nonneg (fun _ => norm_nonneg _))
    (integral_nonneg (fun _ => (Real.exp_pos _).le))

theorem rightLim_variation_toReal_le_weighted_moment {f : ℝ → ℂ}
    (hv : BoundedVariationOn f univ)
    (hm : Integrable (fun x : ℝ => Real.exp |x|) hv.vectorMeasure.variation) :
    (eVariationOn f.rightLim univ).toReal ≤
      ∫ x : ℝ, Real.exp |x| ∂hv.vectorMeasure.variation := by
  let := finite_derivativeVariation_of_weighted_moment hv hm
  have h := ENNReal.toReal_mono (measure_ne_top _ _)
    (rightLim_variation_le_derivativeMeasure hv)
  apply h.trans
  have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) hv.vectorMeasure.variation := integrable_const _
  have hi := integral_mono hconst hm (fun x => Real.one_le_exp_iff.mpr (abs_nonneg x))
  simpa only [integral_const, smul_eq_mul, mul_one, MeasureTheory.measureReal_def] using hi

private theorem weighted_mass_le_integral {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hm : Integrable (fun x : ℝ => Real.exp |x|) μ) {s : Set ℝ}
    (hs : MeasurableSet s) {x : ℝ} (hx : ∀ u ∈ s, |x| ≤ |u|) :
    Real.exp |x| * μ.real s ≤ ∫ u : ℝ, Real.exp |u| ∂μ := by
  calc
    _ = ∫ _ in s, Real.exp |x| ∂μ := by rw [setIntegral_const, smul_eq_mul, mul_comm]
    _ ≤ ∫ u in s, Real.exp |u| ∂μ := by
      apply integral_mono_ae (integrable_const _) hm.integrableOn
      filter_upwards [self_mem_ae_restrict hs] with u hu
      exact Real.exp_le_exp.mpr (hx u hu)
    _ ≤ _ := setIntegral_le_integral hm (Eventually.of_forall (fun u => (Real.exp_pos _).le))

private theorem bv_limUnder_atBot_zero {f : ℝ → ℂ} (hf : Integrable f)
    (hv : BoundedVariationOn f univ) : limUnder atBot f = 0 := by
  apply (hf.integrableAtFilter atBot).eq_zero_of_tendsto ?_ hv.tendsto_atBot_limUnder
  intro s hs
  rcases mem_atBot_sets.1 hs with ⟨b, hb⟩
  rw [← top_le_iff, ← Real.volume_Iic (a := b)]
  exact measure_mono hb

/-- Both half-line masses of the derivative measure control the
canonical representative with the full exponential weight. -/
theorem weighted_rightLim_norm_le_derivative_moment {f : ℝ → ℂ} (hf : Integrable f)
    (hv : BoundedVariationOn f univ)
    (hm : Integrable (fun x : ℝ => Real.exp |x|) hv.vectorMeasure.variation) (x : ℝ) :
    Real.exp |x| * ‖f.rightLim x‖ ≤
      ∫ u : ℝ, Real.exp |u| ∂hv.vectorMeasure.variation := by
  let := finite_derivativeVariation_of_weighted_moment hv hm
  rcases le_total 0 x with hx | hx
  · have hzero : limUnder atTop f = 0 :=
      tendsto_nhds_unique hv.tendsto_atTop_limUnder (tendsto_zero_of_integrable_bv hf hv)
    have he : hv.vectorMeasure (Ioi x) = -f.rightLim x := by
      rw [hv.vectorMeasure_Ioi x, hzero, zero_sub]
    have hn : ‖f.rightLim x‖ ≤ hv.vectorMeasure.variation.real (Ioi x) := by
      have h := MeasureTheory.VectorMeasure.norm_measure_le_variation
        (μ := hv.vectorMeasure) (E := Ioi x)
      simpa only [he, norm_neg] using h
    apply (mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le).trans
    apply weighted_mass_le_integral hm measurableSet_Ioi
    intro u hu
    rw [abs_of_nonneg hx]
    exact (le_of_lt hu).trans (le_abs_self u)
  · have he : hv.vectorMeasure (Iic x) = f.rightLim x := by
      rw [hv.vectorMeasure_Iic x, bv_limUnder_atBot_zero hf hv, sub_zero]
    have hn : ‖f.rightLim x‖ ≤ hv.vectorMeasure.variation.real (Iic x) := by
      have h := MeasureTheory.VectorMeasure.norm_measure_le_variation
        (μ := hv.vectorMeasure) (E := Iic x)
      simpa only [he] using h
    apply (mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le).trans
    apply weighted_mass_le_integral hm measurableSet_Iic
    intro u hu
    rw [abs_of_nonpos hx]
    exact (neg_le_neg hu).trans (neg_le_abs u)

theorem integrable_of_weightedProfile_one {f : ℝ → ℂ}
    (hw : Integrable (weightedProfile 1 f)) : Integrable f := by
  have hi : IntegrableOn (weightedProfile 1 f) univ := by simpa using hw
  simpa using integrableOn_of_weightedProfile_one hi

theorem paperFourier_congr_ae {f g : ℝ → ℂ} (he : f =ᵐ[volume] g) (z : ℂ) :
    paperFourier f z = paperFourier g z := by
  apply integral_congr_ae
  filter_upwards [he] with x hx
  rw [hx]

theorem weightedBVMeasure_l1_le {f : ℝ → ℂ} (hv : BoundedVariationOn f univ) :
    (∫ x : ℝ, ‖weightedProfile 1 f x‖) ≤ weightedBVMeasureBudget f hv := by
  exact le_add_of_nonneg_right (integral_nonneg (fun _ => (Real.exp_pos _).le))

theorem weightedBVMeasure_ae_norm_le {f : ℝ → ℂ} (hv : BoundedVariationOn f univ)
    (hw : Integrable (weightedProfile 1 f))
    (hm : Integrable (fun x : ℝ => Real.exp |x|) hv.vectorMeasure.variation) :
    ∀ᵐ x : ℝ, ‖weightedProfile 1 f x‖ ≤ weightedBVMeasureBudget f hv := by
  filter_upwards [bv_ae_eq_rightLim hv] with x hx
  rw [weightedProfile_norm, one_mul, hx]
  apply (weighted_rightLim_norm_le_derivative_moment
    (integrable_of_weightedProfile_one hw) hv hm x).trans
  exact le_add_of_nonneg_left (integral_nonneg (fun _ => norm_nonneg _))

/-- The weighted L2 bridge uses the derivative measure, and so is
unaffected by changing values on the null set of discontinuity points. -/
theorem weightedBVMeasure_weightedL2 {f : ℝ → ℂ} (hv : BoundedVariationOn f univ)
    (hw : Integrable (weightedProfile 1 f))
    (hm : Integrable (fun x : ℝ => Real.exp |x|) hv.vectorMeasure.variation) :
    WeightedL2 1 f := by
  apply (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).2
  apply (hw.norm.const_mul (weightedBVMeasureBudget f hv)).mono'
    (hw.aestronglyMeasurable.norm.pow 2)
  filter_upwards [weightedBVMeasure_ae_norm_le hv hw hm] with x hx
  rw [sq]
  simpa only [Pi.mul_apply, norm_mul, norm_norm] using
    mul_le_mul_of_nonneg_right hx (norm_nonneg (weightedProfile 1 f x))

theorem weightedBVMeasure_weightedNorm_le {f : ℝ → ℂ} (hv : BoundedVariationOn f univ)
    (hw : Integrable (weightedProfile 1 f))
    (hm : Integrable (fun x : ℝ => Real.exp |x|) hv.vectorMeasure.variation) :
    weightedNorm 1 f ≤ weightedBVMeasureBudget f hv := by
  have hM := weightedBVMeasureBudget_nonneg hv
  have h2 := weighted_square_integrable (weightedBVMeasure_weightedL2 hv hw hm)
  have hb : (∫ x : ℝ, ‖weightedProfile 1 f x‖ ^ 2) ≤ (weightedBVMeasureBudget f hv) ^ 2 := by
    calc
      _ ≤ ∫ x : ℝ, weightedBVMeasureBudget f hv * ‖weightedProfile 1 f x‖ := by
        apply integral_mono_ae h2 (hw.norm.const_mul _)
        filter_upwards [weightedBVMeasure_ae_norm_le hv hw hm] with x hx
        simpa only [sq] using mul_le_mul_of_nonneg_right hx (norm_nonneg _)
      _ = weightedBVMeasureBudget f hv * (∫ x : ℝ, ‖weightedProfile 1 f x‖) :=
        integral_const_mul _ _
      _ ≤ weightedBVMeasureBudget f hv * weightedBVMeasureBudget f hv :=
        mul_le_mul_of_nonneg_left (weightedBVMeasure_l1_le hv) hM
      _ = _ := (sq _).symm
  exact (Real.sqrt_le_iff).2 ⟨hM, hb⟩

/-- Fourier decay from the weighted derivative-measure norm. -/
theorem weightedBVMeasure_fourier_bound {f : ℝ → ℂ} (hv : BoundedVariationOn f univ)
    (hw : Integrable (weightedProfile 1 f))
    (hm : Integrable (fun x : ℝ => Real.exp |x|) hv.vectorMeasure.variation) (r : ℝ) :
    ‖paperFourier f r‖ * (1 + |r|) ≤
      (1 + Real.pi / 2) * weightedBVMeasureBudget f hv := by
  have hf := integrable_of_weightedProfile_one hw
  have he := bv_ae_eq_rightLim hv
  have hgi := hf.congr he
  have hgv : BoundedVariationOn f.rightLim univ := by
    have := finite_derivativeVariation_of_weighted_moment hv hm
    exact ne_top_of_le_ne_top (measure_ne_top _ _) (rightLim_variation_le_derivativeMeasure hv)
  rw [paperFourier_congr_ae he]
  apply (paperFourier_norm_mul_one_add_abs_le hgi hgv r).trans
  have hL : (∫ x : ℝ, ‖f.rightLim x‖) ≤ weightedBVMeasureBudget f hv := by
    have hei : (∫ x : ℝ, ‖f x‖) = ∫ x : ℝ, ‖f.rightLim x‖ :=
      integral_congr_ae (he.fun_comp fun z : ℂ => ‖z‖)
    rw [← hei]
    apply (integral_mono hf.norm hw.norm ?_).trans (weightedBVMeasure_l1_le hv)
    intro x
    dsimp only
    rw [weightedProfile_norm, one_mul]
    exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp_iff.mpr (abs_nonneg x))
  have hV : (eVariationOn f.rightLim univ).toReal ≤ weightedBVMeasureBudget f hv := by
    apply (rightLim_variation_toReal_le_weighted_moment hv hm).trans
    exact le_add_of_nonneg_left (integral_nonneg (fun _ => norm_nonneg _))
  have hpi := Real.pi_pos
  nlinarith

theorem weightedBVMeasure_fourier_square_bound {f : ℝ → ℂ} (hv : BoundedVariationOn f univ)
    (hw : Integrable (weightedProfile 1 f))
    (hm : Integrable (fun x : ℝ => Real.exp |x|) hv.vectorMeasure.variation) (r : ℝ) :
    ‖paperFourier f r‖ ^ 2 ≤
      ((1 + Real.pi / 2) * weightedBVMeasureBudget f hv) ^ 2 / (1 + r ^ 2) := by
  have hM : 0 ≤ (1 + Real.pi / 2) * weightedBVMeasureBudget f hv :=
    mul_nonneg (by positivity) (weightedBVMeasureBudget_nonneg hv)
  have hs := (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (by positivity)) hM).2
    (weightedBVMeasure_fourier_bound hv hw hm r)
  have hr : 1 + r ^ 2 ≤ (1 + |r|) ^ 2 := by nlinarith [sq_abs r, abs_nonneg r]
  have hp := mul_le_mul_of_nonneg_left hr (sq_nonneg ‖paperFourier f r‖)
  rw [mul_pow] at hs
  exact (le_div_iff₀ (by positivity : 0 < 1 + r ^ 2)).2 (hp.trans hs)

/-- All integrals and the prime sum converge absolutely under the weighted-BV
hypotheses. -/
theorem weightedBVMeasure_fullForm_converges {f : ℝ → ℂ} (hv : BoundedVariationOn f univ)
    (hw : Integrable (weightedProfile 1 f))
    (hm : Integrable (fun x : ℝ => Real.exp |x|) hv.vectorMeasure.variation) :
    Integrable (fun r : ℝ => gammaWeight r * Complex.normSq (paperFourier f r)) ∧
    Summable (fun n : ℕ => |(ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
      (correlation f (Real.log n)).re|) ∧
    (∀ z : ℂ, |z.im| ≤ 1 → Integrable (fun u : ℝ =>
      f u * Complex.exp (-Complex.I * z * (u : ℂ)))) ∧
    (∀ v : ℝ, Integrable (fun u : ℝ => f u * conj (f (u - v)))) := by
  have hf := integrable_of_weightedProfile_one hw
  have h2 := weightedBVMeasure_weightedL2 hv hw hm
  refine ⟨gamma_term_integrable_of_fourier_decay
    (paperFourier_continuous_real hf).aestronglyMeasurable
    (weightedBVMeasure_fourier_square_bound hv hw hm), ?_, ?_, ?_⟩
  · exact fullPrime_absolutely_summable (by norm_num : (1 / 2 : ℝ) < 1) h2
  · intro z hz
    exact paperFourier_integrable_of_weighted hf hw hz
  · intro v
    have hh := (ThetaTrial.PrimeContinuity.correlation_integrable (by norm_num : (0 : ℝ) ≤ 1)
      h2 h2 v).comp_add_right (-v)
    simpa only [← sub_eq_add_neg, sub_add_cancel] using hh

theorem weightedBVMeasure_l2_bound {f : ℝ → ℂ} (hv : BoundedVariationOn f univ)
    (hw : Integrable (weightedProfile 1 f))
    (hm : Integrable (fun x : ℝ => Real.exp |x|) hv.vectorMeasure.variation) :
    Real.sqrt (squaredNorm f) ≤ weightedBVMeasureBudget f hv := by
  have h2 := weightedBVMeasure_weightedL2 hv hw hm
  apply le_trans ?_ (weightedBVMeasure_weightedNorm_le hv hw hm)
  apply Real.sqrt_le_sqrt
  apply integral_mono ((h2.memLp (by norm_num : (0 : ℝ) ≤ 1)).norm.integrable_sq)
    (weighted_square_integrable h2)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
  rw [weightedProfile_norm, one_mul]
  exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp_iff.mpr (abs_nonneg x))

private theorem weightedBVMeasure_fullForm_triangle (f : ℝ → ℂ) :
    |fullWeilForm f| ≤
      (1 / (2 * Real.pi)) * |∫ r : ℝ, gammaWeight r * Complex.normSq (paperFourier f r)| +
      2 * |(paperFourier f (Complex.I / 2) * conj (paperFourier f (-Complex.I / 2))).re| +
      2 * |∑' n : ℕ, (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        (correlation f (Real.log n)).re| := by
  unfold fullWeilForm
  calc
    _ ≤ |(1 / (2 * Real.pi)) *
          (∫ r : ℝ, gammaWeight r * Complex.normSq (paperFourier f r)) +
        2 * (paperFourier f (Complex.I / 2) * conj (paperFourier f (-Complex.I / 2))).re| +
        |2 * ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          (correlation f (Real.log n)).re| := abs_sub _ _
    _ ≤ |(1 / (2 * Real.pi)) *
          (∫ r : ℝ, gammaWeight r * Complex.normSq (paperFourier f r))| +
        |2 * (paperFourier f (Complex.I / 2) * conj (paperFourier f (-Complex.I / 2))).re| +
        |2 * ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          (correlation f (Real.log n)).re| := add_le_add (abs_add_le _ _) le_rfl
    _ = _ := by
      simp only [abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
      norm_num

/-- The full form estimate in pre:bv, with the total variation of
the complex derivative measure, including all singular parts and jumps. -/
theorem weightedBVMeasure_fullWeilForm_abs_le {f : ℝ → ℂ} (hv : BoundedVariationOn f univ)
    (hw : Integrable (weightedProfile 1 f))
    (hm : Integrable (fun x : ℝ => Real.exp |x|) hv.vectorMeasure.variation) :
    |fullWeilForm f| ≤ tailFormConstant * (weightedBVMeasureBudget f hv) ^ 2 := by
  let M := weightedBVMeasureBudget f hv
  have hM : 0 ≤ M := weightedBVMeasureBudget_nonneg hv
  have hf := integrable_of_weightedProfile_one hw
  have hl1 : (∫ u : ℝ, ‖weightedProfile 1 f u‖) ≤ M := weightedBVMeasure_l1_le hv
  have hplus : ‖paperFourier f (Complex.I / 2)‖ ≤ M :=
    (paperFourier_norm_le_weighted_l1 hf hw (by norm_num)).trans hl1
  have hminus : ‖paperFourier f (-Complex.I / 2)‖ ≤ M :=
    (paperFourier_norm_le_weighted_l1 hf hw (by norm_num)).trans hl1
  have hpoles : |(paperFourier f (Complex.I / 2) *
      conj (paperFourier f (-Complex.I / 2))).re| ≤ M ^ 2 := by
    calc
      _ ≤ ‖paperFourier f (Complex.I / 2) * conj (paperFourier f (-Complex.I / 2))‖ :=
        Complex.abs_re_le_norm _
      _ = ‖paperFourier f (Complex.I / 2)‖ * ‖paperFourier f (-Complex.I / 2)‖ := by
        rw [norm_mul, Complex.norm_conj]
      _ ≤ M * M := mul_le_mul hplus hminus (norm_nonneg _) hM
      _ = _ := (sq M).symm
  have hprimes : |∑' n : ℕ, (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
      (correlation f (Real.log n)).re| ≤ logMajorantSum 1 * M ^ 2 := by
    apply (fullPrime_abs_le_weightedNorm (weightedBVMeasure_weightedL2 hv hw hm)).trans
    exact mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (weightedNorm_nonneg 1 f) hM).2 (weightedBVMeasure_weightedNorm_le hv hw hm))
      (logMajorantSum_nonneg 1)
  have hgamma : |∫ r : ℝ, gammaWeight r * Complex.normSq (paperFourier f r)| ≤
      ((1 + Real.pi / 2) * M) ^ 2 * gammaCauchyMass :=
    gamma_integral_abs_le_of_fourier_decay (paperFourier_continuous_real hf).aestronglyMeasurable
      (weightedBVMeasure_fourier_square_bound hv hw hm)
  apply (weightedBVMeasure_fullForm_triangle f).trans
  calc
    _ ≤ (1 / (2 * Real.pi)) * (((1 + Real.pi / 2) * M) ^ 2 * gammaCauchyMass) +
        2 * M ^ 2 + 2 * (logMajorantSum 1 * M ^ 2) := by
      exact add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hgamma (by positivity))
          (mul_le_mul_of_nonneg_left hpoles (by norm_num)))
        (mul_le_mul_of_nonneg_left hprimes (by norm_num))
    _ ≤ tailFormConstant * M ^ 2 := by
      unfold tailFormConstant
      nlinarith [sq_nonneg M]

end ThetaTrial.Paper
