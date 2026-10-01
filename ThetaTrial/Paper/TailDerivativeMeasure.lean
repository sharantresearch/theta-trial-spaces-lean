import ThetaTrial.Paper.WeightedBVMeasure
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
The derivative measure of a hard exterior cutoff: its continuous density
plus the two endpoint atoms.
-/

noncomputable section
open MeasureTheory Set Filter
open ThetaTrial.PrimeContinuity
open scoped Topology ENNReal ComplexConjugate

namespace ThetaTrial.Paper

theorem exteriorTail_rightLim {F : ℝ → ℂ} (hc : Continuous F) {a : ℝ}
    (_ha : 0 < a) (x : ℝ) :
    (exteriorTail a F).rightLim x = if x < -a then F x else if x < a then 0 else F x := by
  by_cases hxl : x < -a
  · rw [if_pos hxl]
    apply rightLim_eq_of_tendsto
    apply (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hxl)] with y hy
    simp only [exteriorTail, indicator_of_mem (show y ∈ (Icc (-a) a)ᶜ from
      fun h => not_le.mpr hy h.1)]
  · rw [if_neg hxl]
    by_cases hxr : x < a
    · rw [if_pos hxr]
      apply rightLim_eq_of_tendsto
      apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) (𝓝[>] x) (𝓝 0)).congr'
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hxr)]
        with y hy hy'
      have hym : y ∈ Icc (-a) a := ⟨(le_of_not_gt hxl).trans (le_of_lt hy), le_of_lt hy'⟩
      simp [exteriorTail, hym]
    · rw [if_neg hxr]
      apply rightLim_eq_of_tendsto
      apply (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hay : a < y := lt_of_le_of_lt (le_of_not_gt hxr) hy
      simp only [exteriorTail, indicator_of_mem (show y ∈ (Icc (-a) a)ᶜ from
        fun h => hay.not_ge h.2)]

theorem exteriorTail_leftLim_left {F : ℝ → ℂ} (hc : Continuous F) (a : ℝ) :
    (exteriorTail a F).leftLim (-a) = F (-a) := by
  apply leftLim_eq_of_tendsto
  apply (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [exteriorTail, indicator_of_mem (show y ∈ (Icc (-a) a)ᶜ from
    fun h => not_le.mpr hy h.1)]

theorem exteriorTail_leftLim_right {F : ℝ → ℂ} {a : ℝ} (ha : 0 < a) :
    (exteriorTail a F).leftLim a = 0 := by
  apply leftLim_eq_of_tendsto
  apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) (𝓝[<] a) (𝓝 0)).congr'
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show -a < a by linarith))] with y hy hy'
  simp [exteriorTail, show y ∈ Icc (-a) a from ⟨le_of_lt hy', le_of_lt hy⟩]

theorem exteriorTail_derivative_atoms {F : ℝ → ℂ} (hc : Continuous F)
    {a : ℝ} (ha : 0 < a) (hv : BoundedVariationOn (exteriorTail a F) univ) :
    hv.vectorMeasure {-a} = -F (-a) ∧ hv.vectorMeasure {a} = F a := by
  constructor
  · rw [hv.vectorMeasure_singleton, exteriorTail_rightLim hc ha,
      exteriorTail_leftLim_left hc]
    simp [show -a < a by linarith]
  · rw [hv.vectorMeasure_singleton, exteriorTail_rightLim hc ha,
      exteriorTail_leftLim_right ha]
    simp [show ¬a < -a by linarith]

/-- A single scalar control measure contains Lebesgue density and both
endpoint atoms. Taking its density variation avoids dropping cross terms
or presuming additivity of norms of vector measures. -/
def tailControlMeasure (a : ℝ) : Measure ℝ := volume + Measure.dirac (-a) + Measure.dirac a

def tailDerivativeDensity (F F' : ℝ → ℂ) (a x : ℝ) : ℂ :=
  if x = -a then -F (-a) else if x = a then F a else exteriorTail a F' x

theorem tailDerivativeDensity_ae (F F' : ℝ → ℂ) (a : ℝ) :
    tailDerivativeDensity F F' a =ᵐ[volume] exteriorTail a F' := by
  have hl : ∀ᵐ x : ℝ, x ≠ -a := by rw [ae_iff]; simp
  have hr : ∀ᵐ x : ℝ, x ≠ a := by rw [ae_iff]; simp
  filter_upwards [hl, hr] with x hxl hxr
  simp [tailDerivativeDensity, hxl, hxr]

theorem tailDerivativeDensity_integrable {F F' : ℝ → ℂ} {a : ℝ}
    (hi : IntegrableOn F' (Icc (-a) a)ᶜ) :
    Integrable (tailDerivativeDensity F F' a) (tailControlMeasure a) := by
  have hv := (exteriorTail_integrable hi).congr (tailDerivativeDensity_ae F F' a).symm
  exact (hv.add_measure (integrable_dirac (by simp))).add_measure (integrable_dirac (by simp))

theorem exteriorTail_derivative_cdf {F F' : ℝ → ℂ} (hc : Continuous F)
    {a : ℝ} (ha : 0 < a)
    (hd : ∀ x ∈ (Icc (-a) a)ᶜ, HasDerivAt F (F' x) x)
    (hi : IntegrableOn F' (Icc (-a) a)ᶜ)
    (hbot : Tendsto F atBot (𝓝 0)) (x : ℝ) :
    (∫ u in Iic x, exteriorTail a F' u) =
      if x < -a then F x else if x < a then F (-a) else F (-a) + (F x - F a) := by
  have hLi : IntegrableOn F' (Iio (-a)) := hi.mono_set (by
    intro u hu hh
    exact (not_le.mpr hu) hh.1)
  have hLic : IntegrableOn F' (Iic (-a)) :=
    (integrableOn_Iic_iff_integrableOn_Iio (f := F') (μ := volume) (b := -a)).mpr hLi
  have hL (y : ℝ) (hy : y ≤ -a) : (∫ u in Iic y, F' u) = F y := by
    simpa only [sub_zero] using integral_Iic_of_hasDerivAt_of_tendsto
      hc.continuousWithinAt (fun u hu => hd u (by
        intro hh
        exact (lt_of_lt_of_le hu hy).not_ge hh.1))
      (hLic.mono_set (Iic_subset_Iic.mpr hy)) hbot
  change (∫ u in Iic x, (Icc (-a) a)ᶜ.indicator F' u) = _
  rw [setIntegral_indicator measurableSet_Icc.compl]
  by_cases hxl : x < -a
  · rw [if_pos hxl]
    have hs : Iic x ∩ (Icc (-a) a)ᶜ = Iic x := by
      apply inter_eq_left.mpr
      intro u hu hh
      exact (lt_of_le_of_lt hu hxl).not_ge hh.1
    rw [hs]
    exact hL x hxl.le
  · rw [if_neg hxl]
    by_cases hxr : x < a
    · rw [if_pos hxr]
      have hs : Iic x ∩ (Icc (-a) a)ᶜ = Iio (-a) := by
        ext u
        constructor
        · rintro ⟨hu, hh⟩
          by_contra hul
          exact hh ⟨le_of_not_gt hul, (le_of_lt hxr).trans' hu⟩
        · intro hu
          exact ⟨hu.le.trans (le_of_not_gt hxl), fun hh => hu.not_ge hh.1⟩
      rw [hs, ← integral_Iic_eq_integral_Iio]
      exact hL (-a) le_rfl
    · rw [if_neg hxr]
      have hax : a ≤ x := le_of_not_gt hxr
      have hs : Iic x ∩ (Icc (-a) a)ᶜ = Iio (-a) ∪ Ioc a x := by
        ext u
        constructor
        · rintro ⟨hu, hh⟩
          by_cases hul : u < -a
          · exact Or.inl hul
          · exact Or.inr ⟨lt_of_not_ge (fun hau => hh ⟨le_of_not_gt hul, hau⟩), hu⟩
        · rintro (hu | hu)
          · exact ⟨hu.le.trans ((show -a ≤ a by linarith).trans hax), fun hh => hu.not_ge hh.1⟩
          · exact ⟨hu.2, fun hh => hu.1.not_ge hh.2⟩
      have hRi : IntegrableOn F' (Ioc a x) := hi.mono_set (by
        intro u hu hh
        exact hu.1.not_ge hh.2)
      have hdis : Disjoint (Iio (-a)) (Ioc a x) := disjoint_left.mpr (by
        intro u hul hur
        have hlt : -a < a := by linarith
        exact (hul.trans hlt).not_ge hur.1.le)
      rw [hs, setIntegral_union hdis measurableSet_Ioc hLi hRi,
        ← integral_Iic_eq_integral_Iio, hL (-a) le_rfl]
      congr 1
      rw [← intervalIntegral.integral_of_le hax]
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hax hc.continuousOn
      · intro u hu
        exact hd u (fun hh => hu.1.not_ge hh.2)
      · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hax).mpr hRi

private theorem vectorMeasure_ext_Iic {μ ν : VectorMeasure ℝ ℂ}
    (h : ∀ x : ℝ, μ (Iic x) = ν (Iic x)) : μ = ν := by
  apply VectorMeasure.ext_of_generateFrom (range Iic)
  · rintro _ ⟨x, rfl⟩
    exact h x
  · exact borel_eq_generateFrom_Iic ℝ
  · exact isPiSystem_Iic
  · have hu : (⋃ n : ℕ, Iic (n : ℝ)) = univ := by
      ext x
      simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
      exact exists_nat_ge x
    have hm : Monotone (fun n : ℕ => Iic (n : ℝ)) := by
      intro i j hij
      exact Iic_subset_Iic.mpr (by exact_mod_cast hij)
    have hμ := μ.tendsto_vectorMeasure_iUnion_atTop_nat hm (fun _ => measurableSet_Iic)
    have hν := ν.tendsto_vectorMeasure_iUnion_atTop_nat hm (fun _ => measurableSet_Iic)
    rw [hu] at hμ hν
    simp_rw [h] at hμ
    exact tendsto_nhds_unique hμ hν

theorem tailDerivativeDensity_cdf {F F' : ℝ → ℂ} {a : ℝ} (ha : 0 < a)
    (hi : IntegrableOn F' (Icc (-a) a)ᶜ) (x : ℝ) :
    (tailControlMeasure a).withDensityᵥ (tailDerivativeDensity F F' a) (Iic x) =
      (∫ u in Iic x, exteriorTail a F' u) +
        (if -a ≤ x then -F (-a) else 0) + (if a ≤ x then F a else 0) := by
  have hdv := (exteriorTail_integrable hi).congr (tailDerivativeDensity_ae F F' a).symm
  have hdL : Integrable (tailDerivativeDensity F F' a) (Measure.dirac (-a)) :=
    integrable_dirac (by simp)
  have hdR : Integrable (tailDerivativeDensity F F' a) (Measure.dirac a) :=
    integrable_dirac (by simp)
  rw [withDensityᵥ_apply (tailDerivativeDensity_integrable hi) measurableSet_Iic,
    ← integral_indicator measurableSet_Iic]
  unfold tailControlMeasure
  rw [integral_add_measure ((hdv.indicator measurableSet_Iic).add_measure
    (hdL.indicator measurableSet_Iic)) (hdR.indicator measurableSet_Iic),
    integral_add_measure (hdv.indicator measurableSet_Iic) (hdL.indicator measurableSet_Iic),
    integral_dirac, integral_dirac]
  have he : (∫ u : ℝ, (Iic x).indicator (tailDerivativeDensity F F' a) u) =
      ∫ u in Iic x, exteriorTail a F' u := by
    rw [integral_indicator measurableSet_Iic]
    exact integral_congr_ae ((tailDerivativeDensity_ae F F' a).filter_mono ae_restrict_le)
  rw [he]
  simp only [indicator_apply, mem_Iic, tailDerivativeDensity, ite_true,
    if_neg (show a ≠ -a by linarith)]

/-- Exact derivative vector measure of the exterior cutoff, represented
using one control measure for its ordinary density and the two atoms. -/
theorem exteriorTail_vectorMeasure_eq {F F' : ℝ → ℂ} (hc : Continuous F)
    {a : ℝ} (ha : 0 < a)
    (hd : ∀ x ∈ (Icc (-a) a)ᶜ, HasDerivAt F (F' x) x)
    (hi : IntegrableOn F' (Icc (-a) a)ᶜ)
    (hfi : IntegrableOn F (Icc (-a) a)ᶜ)
    (hv : BoundedVariationOn (exteriorTail a F) univ) :
    hv.vectorMeasure = (tailControlMeasure a).withDensityᵥ (tailDerivativeDensity F F' a) := by
  have ht := exteriorTail_integrable hfi
  have hzero : limUnder atBot (exteriorTail a F) = 0 := by
    apply (ht.integrableAtFilter atBot).eq_zero_of_tendsto ?_ hv.tendsto_atBot_limUnder
    intro s hs
    rcases mem_atBot_sets.1 hs with ⟨b, hb⟩
    rw [← top_le_iff, ← Real.volume_Iic (a := b)]
    exact measure_mono hb
  have hbot : Tendsto F atBot (𝓝 0) := by
    have hb := hv.tendsto_atBot_limUnder
    rw [hzero] at hb
    apply hb.congr'
    filter_upwards [Iio_mem_atBot (-a)] with x hx
    simp only [exteriorTail, indicator_of_mem (show x ∈ (Icc (-a) a)ᶜ from
      fun hh => hx.not_ge hh.1)]
  apply vectorMeasure_ext_Iic
  intro x
  rw [hv.vectorMeasure_Iic x, hzero, sub_zero, tailDerivativeDensity_cdf ha hi,
    exteriorTail_derivative_cdf hc ha hd hi hbot, exteriorTail_rightLim hc ha]
  by_cases hxl : x < -a
  · have hxr : x < a := hxl.trans (by linarith)
    simp [hxl, not_le.mpr hxl, not_le.mpr hxr]
  · by_cases hxr : x < a
    · simp [hxl, hxr, le_of_not_gt hxl, not_le.mpr hxr]
    · simp only [hxl, hxr, if_false, le_of_not_gt hxl, le_of_not_gt hxr, if_true]
      abel

theorem tailDerivativeDensity_weighted_integrable {F F' : ℝ → ℂ} {a : ℝ}
    (hi : IntegrableOn (weightedProfile 1 F') (Icc (-a) a)ᶜ) :
    Integrable (fun x : ℝ => Real.exp |x| * ‖tailDerivativeDensity F F' a x‖)
      (tailControlMeasure a) := by
  have hwt : Integrable (weightedProfile 1 (exteriorTail a F')) := by
    rw [weightedProfile_exteriorTail]
    exact exteriorTail_integrable hi
  have hvol : Integrable (fun x : ℝ => Real.exp |x| * ‖tailDerivativeDensity F F' a x‖) := by
    apply hwt.norm.congr
    filter_upwards [tailDerivativeDensity_ae F F' a] with x hx
    rw [weightedProfile_norm, one_mul, hx]
  exact (hvol.add_measure (integrable_dirac enorm_lt_top)).add_measure (integrable_dirac enorm_lt_top)

theorem tailDerivativeDensity_weighted_integral {F F' : ℝ → ℂ} {a : ℝ}
    (ha : 0 < a) (hi : IntegrableOn (weightedProfile 1 F') (Icc (-a) a)ᶜ) :
    (∫ x : ℝ, Real.exp |x| * ‖tailDerivativeDensity F F' a x‖ ∂tailControlMeasure a) =
      (∫ x in (Icc (-a) a)ᶜ, Real.exp |x| * ‖F' x‖) +
        Real.exp a * (‖F (-a)‖ + ‖F a‖) := by
  have hwt : Integrable (weightedProfile 1 (exteriorTail a F')) := by
    rw [weightedProfile_exteriorTail]
    exact exteriorTail_integrable hi
  have he : (fun x : ℝ => Real.exp |x| * ‖tailDerivativeDensity F F' a x‖) =ᵐ[volume]
      (fun x : ℝ => ‖weightedProfile 1 (exteriorTail a F') x‖) := by
    filter_upwards [tailDerivativeDensity_ae F F' a] with x hx
    rw [weightedProfile_norm, one_mul, hx]
  have hvol := hwt.norm.congr he.symm
  unfold tailControlMeasure
  rw [integral_add_measure (hvol.add_measure (integrable_dirac enorm_lt_top))
      (integrable_dirac enorm_lt_top),
    integral_add_measure hvol (integrable_dirac enorm_lt_top), integral_dirac, integral_dirac,
    integral_congr_ae he, weighted_exteriorTail_l1_eq]
  simp only [tailDerivativeDensity, ite_true, if_neg (show a ≠ -a by linarith),
    norm_neg, abs_neg, abs_of_pos ha, weightedProfile_norm, one_mul]
  ring

/-- Exact weighted total-variation identity. Distinct endpoints are
essential: at `a = 0` their distributional atoms cancel. -/
theorem exteriorTail_weighted_derivativeMeasure {F F' : ℝ → ℂ} (hc : Continuous F)
    {a : ℝ} (ha : 0 < a)
    (hd : ∀ x ∈ (Icc (-a) a)ᶜ, HasDerivAt F (F' x) x)
    (hi : IntegrableOn (weightedProfile 1 F) (Icc (-a) a)ᶜ)
    (hi' : IntegrableOn (weightedProfile 1 F') (Icc (-a) a)ᶜ)
    (hv : BoundedVariationOn (exteriorTail a F) univ) :
    Integrable (fun x : ℝ => Real.exp |x|) hv.vectorMeasure.variation ∧
    (∫ x : ℝ, Real.exp |x| ∂hv.vectorMeasure.variation) =
      (∫ x in (Icc (-a) a)ᶜ, Real.exp |x| * ‖F' x‖) +
        Real.exp a * (‖F (-a)‖ + ‖F a‖) := by
  have hvi := tailDerivativeDensity_integrable (F := F) (integrableOn_of_weightedProfile_one hi')
  rw [exteriorTail_vectorMeasure_eq hc ha hd (integrableOn_of_weightedProfile_one hi')
      (integrableOn_of_weightedProfile_one hi) hv,
    Measure.variation_withDensityᵥ hvi]
  have hmeas := hvi.aestronglyMeasurable.enorm
  have hfinite : ∀ᵐ x ∂tailControlMeasure a, ‖tailDerivativeDensity F F' a x‖ₑ < ∞ := by
    filter_upwards [] with x
    exact enorm_lt_top
  constructor
  · apply (integrable_withDensity_iff_integrable_smul₀' hmeas hfinite).mpr
    simpa only [toReal_enorm, smul_eq_mul, mul_comm] using
      tailDerivativeDensity_weighted_integrable (F := F) hi'
  · rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas hfinite]
    simp only [toReal_enorm, smul_eq_mul]
    simpa only [mul_comm] using tailDerivativeDensity_weighted_integral (F := F) ha hi'

/-- The weighted measure norm of the hard tail equals the weighted integrals of
the function and its derivative, plus the two endpoint jumps. -/
theorem exteriorTail_weightedBVMeasureBudget_eq {F F' : ℝ → ℂ} (hc : Continuous F)
    {a : ℝ} (ha : 0 < a)
    (hd : ∀ x ∈ (Icc (-a) a)ᶜ, HasDerivAt F (F' x) x)
    (hi : IntegrableOn (weightedProfile 1 F) (Icc (-a) a)ᶜ)
    (hi' : IntegrableOn (weightedProfile 1 F') (Icc (-a) a)ᶜ)
    (hv : BoundedVariationOn (exteriorTail a F) univ) :
    weightedBVMeasureBudget (exteriorTail a F) hv = hardTailBudget F F' a := by
  unfold weightedBVMeasureBudget hardTailBudget
  rw [weighted_exteriorTail_l1_eq,
    (exteriorTail_weighted_derivativeMeasure hc ha hd hi hi' hv).2]
  have hadd := integral_add hi.norm hi'.norm
  simp only [weightedProfile_norm, one_mul, ← mul_add] at hadd ⊢
  rw [hadd]
  ring

end ThetaTrial.Paper
