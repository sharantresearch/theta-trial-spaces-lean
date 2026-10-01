import ThetaTrial.Paper.BV
import ThetaTrial.PrimeContinuity.Weighted
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
Variation of hard exterior cutoffs. From integrability of the derivative we
obtain bounded variation and Fourier decay, with the endpoint jumps included.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace ThetaTrial.Paper

/-- A derivative-integral bound for full partition variation on an interval.
The interval may be unbounded or open. -/
theorem variation_le_integral_deriv {F F' : ℝ → ℂ} {s : Set ℝ}
    (hs : OrdConnected s) (hderiv : ∀ x ∈ s, HasDerivAt F (F' x) x)
    (hi : IntegrableOn F' s) :
    eVariationOn F s ≤ ENNReal.ofReal (∫ x in s, ‖F' x‖) := by
  have hint {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≤ y) :
      IntervalIntegrable F' volume x y := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hxy (by simp)).2
    exact hi.mono_set (hs.out hx hy)
  have hinc {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≤ y) :
      ‖F y - F x‖ ≤ ∫ t in x..y, ‖F' t‖ := by
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hderiv t (hs.out hx hy (by simpa [uIcc_of_le hxy] using ht)))
      (hint hx hy hxy)]
    exact intervalIntegral.norm_integral_le_integral_norm hxy
  unfold eVariationOn
  refine iSup_le fun ⟨n, u, hu, hus⟩ => ?_
  calc
    _ ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal
        (∫ t in u i..u (i + 1), ‖F' t‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [edist_dist, dist_eq_norm]
      exact ENNReal.ofReal_le_ofReal (hinc (hus i) (hus (i + 1)) (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n,
        ∫ t in u i..u (i + 1), ‖F' t‖) := by
      symm
      apply ENNReal.ofReal_sum_of_nonneg
      intro i _
      exact intervalIntegral.integral_nonneg (hu (Nat.le_succ i)) (fun _ _ => norm_nonneg _)
    _ = ENNReal.ofReal (∫ t in u 0..u n, ‖F' t‖) := by
      rw [intervalIntegral.sum_integral_adjacent_intervals
        (fun i _ => (hint (hus i) (hus (i + 1)) (hu (Nat.le_succ i))).norm)]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [intervalIntegral.integral_of_le (hu (Nat.zero_le n))]
      exact setIntegral_mono_set hi.norm (Filter.Eventually.of_forall (fun x => norm_nonneg (F' x)))
        (Filter.Eventually.of_forall (fun x hx =>
          hs.out (hus 0) (hus n) (Ioc_subset_Icc_self hx)))

/-- Exact pointwise variation decomposition of the hard exterior cutoff.
The two endpoint contributions are present even though the cutoff is zero
at each endpoint. -/
theorem exteriorTail_variation_eq {F : ℝ → ℂ} (hc : Continuous F)
    {a : ℝ} (ha : 0 ≤ a) :
    eVariationOn (exteriorTail a F) univ =
      eVariationOn F (Iio (-a)) + ENNReal.ofReal ‖F (-a)‖ +
      eVariationOn F (Ioi a) + ENNReal.ofReal ‖F a‖ := by
  have haa : -a ≤ a := by linarith
  have hlEq : EqOn (exteriorTail a F) F (Iio (-a)) := by
    intro x hx
    simp only [exteriorTail, indicator_of_mem (show x ∈ (Icc (-a) a)ᶜ from
      fun h => not_le.mpr hx h.1)]
  have hrEq : EqOn (exteriorTail a F) F (Ioi a) := by
    intro x hx
    simp only [exteriorTail, indicator_of_mem (show x ∈ (Icc (-a) a)ᶜ from
      fun h => not_le.mpr hx h.2)]
  have hlLim : Tendsto (exteriorTail a F) (𝓝[univ ∩ Iio (-a)] (-a)) (𝓝 (F (-a))) := by
    simp only [univ_inter]
    apply (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hlEq hx).symm
  have hrLim : Tendsto (exteriorTail a F) (𝓝[univ ∩ Ioi a] a) (𝓝 (F a)) := by
    simp only [univ_inter]
    apply (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hrEq hx).symm
  have hl := eVariationOn.eVariationOn_on_inter_Iic_eq_Iio_add_edist
    (f := exteriorTail a F) (s := univ) (a := -a)
    (by simp only [univ_inter]; infer_instance) (mem_univ _) hlLim
  have hr := eVariationOn.eVariationOn_on_inter_Ici_eq_Ioi_add_edist
    (f := exteriorTail a F) (s := univ) (a := a)
    (by simp only [univ_inter]; infer_instance) (mem_univ _) hrLim
  simp only [univ_inter] at hl hr
  rw [eVariationOn.eq_of_eqOn hlEq] at hl
  rw [eVariationOn.eq_of_eqOn hrEq] at hr
  have hm : eVariationOn (exteriorTail a F) (Icc (-a) a) = 0 := by
    rw [eVariationOn.eq_of_eqOn (f' := fun _ => (0 : ℂ)) (by
      intro x hx
      simp [exteriorTail, hx])]
    exact (eVariationOn.eq_zero_iff _).2 (fun _ _ _ _ => edist_self _)
  have hsplit := eVariationOn.union (exteriorTail a F)
    (isGreatest_Iic (a := -a)) (isLeast_Ici (a := -a))
  have hsplit' := eVariationOn.union (exteriorTail a F)
    (show IsGreatest (Icc (-a) a) a from ⟨⟨haa, le_rfl⟩, fun _ h => h.2⟩)
    (isLeast_Ici (a := a))
  rw [Iic_union_Ici] at hsplit
  rw [Icc_union_Ici_eq_Ici haa, hm, zero_add] at hsplit'
  rw [hsplit, hsplit', hl, hr]
  simp only [exteriorTail, indicator_of_notMem (show -a ∉ (Icc (-a) a)ᶜ from
      fun h => h ⟨le_rfl, haa⟩),
    indicator_of_notMem (show a ∉ (Icc (-a) a)ᶜ from fun h => h ⟨haa, le_rfl⟩),
    edist_dist, dist_zero_left, add_assoc]

/-- The derivative integral and the two explicit endpoint jumps bound the
entire variation of the hard cutoff. Only the derivative outside the window
needs to be integrable. -/
theorem exteriorTail_variation_le {F F' : ℝ → ℂ} (hc : Continuous F)
    {a : ℝ} (ha : 0 ≤ a)
    (hd : ∀ x ∈ (Icc (-a) a)ᶜ, HasDerivAt F (F' x) x)
    (hi : IntegrableOn F' (Icc (-a) a)ᶜ) :
    eVariationOn (exteriorTail a F) univ ≤ ENNReal.ofReal
      (‖F (-a)‖ + ‖F a‖ + ∫ x in (Icc (-a) a)ᶜ, ‖F' x‖) := by
  have hsL : Iio (-a) ⊆ (Icc (-a) a)ᶜ := fun x hx h => not_le.mpr hx h.1
  have hsR : Ioi a ⊆ (Icc (-a) a)ᶜ := fun x hx h => not_le.mpr hx h.2
  have hL := variation_le_integral_deriv ordConnected_Iio
    (fun x hx => hd x (hsL hx)) (hi.mono_set hsL)
  have hR := variation_le_integral_deriv ordConnected_Ioi
    (fun x hx => hd x (hsR hx)) (hi.mono_set hsR)
  have he : (Icc (-a) a)ᶜ = Iio (-a) ∪ Ioi a := by
    ext x
    simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi, not_and_or, not_le]
  have hdis : Disjoint (Iio (-a)) (Ioi a) := disjoint_left.mpr (by
    intro x hx hy
    have : -a ≤ a := by linarith
    exact (lt_of_lt_of_le hx this).not_ge (le_of_lt hy))
  have hiEq : (∫ x in (Icc (-a) a)ᶜ, ‖F' x‖) =
      (∫ x in Iio (-a), ‖F' x‖) + ∫ x in Ioi a, ‖F' x‖ := by
    rw [he, setIntegral_union hdis measurableSet_Ioi (hi.mono_set hsL).norm (hi.mono_set hsR).norm]
  rw [exteriorTail_variation_eq hc ha]
  calc
    _ ≤ ENNReal.ofReal (∫ x in Iio (-a), ‖F' x‖) + ENNReal.ofReal ‖F (-a)‖ +
        ENNReal.ofReal (∫ x in Ioi a, ‖F' x‖) + ENNReal.ofReal ‖F a‖ := by
      exact add_le_add (add_le_add (add_le_add hL le_rfl) hR) le_rfl
    _ = _ := by
      rw [hiEq]
      rw [ENNReal.ofReal_add (add_nonneg (norm_nonneg _) (norm_nonneg _))
        (add_nonneg (integral_nonneg (fun _ => norm_nonneg _))
          (integral_nonneg (fun _ => norm_nonneg _)))]
      rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
        ENNReal.ofReal_add (integral_nonneg (fun _ => norm_nonneg _))
          (integral_nonneg (fun _ => norm_nonneg _))]
      ac_rfl

theorem exteriorTail_boundedVariation {F F' : ℝ → ℂ} (hc : Continuous F)
    {a : ℝ} (ha : 0 ≤ a)
    (hd : ∀ x ∈ (Icc (-a) a)ᶜ, HasDerivAt F (F' x) x)
    (hi : IntegrableOn F' (Icc (-a) a)ᶜ) :
    BoundedVariationOn (exteriorTail a F) univ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (exteriorTail_variation_le hc ha hd hi)

theorem exteriorTail_integrable {F : ℝ → ℂ} {a : ℝ}
    (hi : IntegrableOn F (Icc (-a) a)ᶜ) : Integrable (exteriorTail a F) :=
  hi.integrable_indicator (measurableSet_Icc.compl)

theorem exteriorTail_variation_toReal_le {F F' : ℝ → ℂ} (hc : Continuous F)
    {a : ℝ} (ha : 0 ≤ a)
    (hd : ∀ x ∈ (Icc (-a) a)ᶜ, HasDerivAt F (F' x) x)
    (hi : IntegrableOn F' (Icc (-a) a)ᶜ) :
    (eVariationOn (exteriorTail a F) univ).toReal ≤
      ‖F (-a)‖ + ‖F a‖ + ∫ x in (Icc (-a) a)ᶜ, ‖F' x‖ := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (exteriorTail_variation_le hc ha hd hi)
  rwa [ENNReal.toReal_ofReal (by positivity)] at h

open ThetaTrial.PrimeContinuity

/-- Ordinary derivative of the exponentially weighted function away from zero. -/
def weightedTailDerivative (F F' : ℝ → ℂ) (x : ℝ) : ℂ :=
  if x < 0 then weightedProfile 1 F' x - weightedProfile 1 F x
  else weightedProfile 1 F' x + weightedProfile 1 F x

theorem weightedProfile_one_continuous {F : ℝ → ℂ} (hc : Continuous F) :
    Continuous (weightedProfile 1 F) := by
  unfold weightedProfile
  fun_prop

set_option backward.isDefEq.respectTransparency false in
theorem weightedProfile_one_hasDerivAt {F F' : ℝ → ℂ} {x : ℝ}
    (hx0 : x ≠ 0) (hd : HasDerivAt F (F' x) x) :
    HasDerivAt (weightedProfile 1 F) (weightedTailDerivative F F' x) x := by
  by_cases hx : x < 0
  · have hb : HasDerivAt (fun y : ℝ => (Real.exp (-y) : ℂ) * F y)
        ((-(Real.exp (-x) : ℂ)) * F x + (Real.exp (-x) : ℂ) * F' x) x := by
      simpa only [Pi.neg_apply, id_eq, mul_neg_one, Pi.smul_def', Complex.real_smul,
        Complex.ofReal_neg, add_comm] using ((hasDerivAt_id x).neg.exp).smul hd
    have he : weightedProfile 1 F =ᶠ[𝓝 x]
        (fun y : ℝ => (Real.exp (-y) : ℂ) * F y) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      simp [weightedProfile, abs_of_neg (show y < 0 from hy)]
    have hdEq : weightedTailDerivative F F' x =
        (-(Real.exp (-x) : ℂ)) * F x + (Real.exp (-x) : ℂ) * F' x := by
      simp only [weightedTailDerivative, hx, ↓reduceIte, weightedProfile, one_mul, abs_of_neg hx]
      ring
    rw [hdEq]
    exact hb.congr_of_eventuallyEq he
  · have hx' : 0 < x := lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm hx0)
    have hb : HasDerivAt (fun y : ℝ => (Real.exp y : ℂ) * F y)
        ((Real.exp x : ℂ) * F x + (Real.exp x : ℂ) * F' x) x := by
      simpa only [id_eq, mul_one, Pi.smul_def', Complex.real_smul, add_comm] using
        ((hasDerivAt_id x).exp).smul hd
    have he : weightedProfile 1 F =ᶠ[𝓝 x]
        (fun y : ℝ => (Real.exp y : ℂ) * F y) := by
      filter_upwards [Ioi_mem_nhds hx'] with y hy
      simp [weightedProfile, abs_of_pos (show 0 < y from hy)]
    have hdEq : weightedTailDerivative F F' x =
        (Real.exp x : ℂ) * F x + (Real.exp x : ℂ) * F' x := by
      simp only [weightedTailDerivative, hx, ↓reduceIte, weightedProfile, one_mul, abs_of_pos hx']
      ring
    rw [hdEq]
    exact hb.congr_of_eventuallyEq he

theorem weightedTailDerivative_integrableOn {F F' : ℝ → ℂ} {s : Set ℝ}
    (hF : IntegrableOn (weightedProfile 1 F) s)
    (hF' : IntegrableOn (weightedProfile 1 F') s) :
    IntegrableOn (weightedTailDerivative F F') s := by
  have hi := Integrable.piecewise (μ := volume.restrict s) (s := Iio 0) measurableSet_Iio
    (hF'.sub hF).integrableOn (hF'.add hF).integrableOn
  change Integrable (weightedTailDerivative F F') (volume.restrict s)
  have he : weightedTailDerivative F F' =
      (Iio 0).piecewise (weightedProfile 1 F' - weightedProfile 1 F)
        (weightedProfile 1 F' + weightedProfile 1 F) := by
    funext x
    rfl
  rw [he]
  exact hi

theorem weightedTailDerivative_norm_le (F F' : ℝ → ℂ) (x : ℝ) :
    ‖weightedTailDerivative F F' x‖ ≤
      Real.exp |x| * (‖F' x‖ + ‖F x‖) := by
  unfold weightedTailDerivative
  split_ifs <;>
    calc
      _ ≤ ‖weightedProfile 1 F' x‖ + ‖weightedProfile 1 F x‖ := by
        first | exact norm_sub_le _ _ | exact norm_add_le _ _
      _ = _ := by rw [weightedProfile_norm, weightedProfile_norm]; simp only [one_mul]; ring

/-- Multiplication by the continuous weight commutes with the hard cutoff. -/
theorem weightedProfile_exteriorTail (F : ℝ → ℂ) (a : ℝ) :
    weightedProfile 1 (exteriorTail a F) = exteriorTail a (weightedProfile 1 F) := by
  funext x
  by_cases hx : x ∈ (Icc (-a) a)ᶜ <;> simp [weightedProfile, exteriorTail, hx]

/-- Exponentially weighted hard tails are BV when `F` and `F'` are weighted
integrable. -/
theorem weighted_exteriorTail_boundedVariation {F F' : ℝ → ℂ} (hc : Continuous F)
    {a : ℝ} (ha : 0 ≤ a)
    (hd : ∀ x ∈ (Icc (-a) a)ᶜ, HasDerivAt F (F' x) x)
    (hi : IntegrableOn (weightedProfile 1 F) (Icc (-a) a)ᶜ)
    (hi' : IntegrableOn (weightedProfile 1 F') (Icc (-a) a)ᶜ) :
    BoundedVariationOn (weightedProfile 1 (exteriorTail a F)) univ := by
  rw [weightedProfile_exteriorTail]
  apply exteriorTail_boundedVariation (weightedProfile_one_continuous hc) ha
    (F' := weightedTailDerivative F F')
  · intro x hx
    apply weightedProfile_one_hasDerivAt _ (hd x hx)
    intro he
    subst x
    exact hx ⟨by linarith, ha⟩
  · exact weightedTailDerivative_integrableOn hi hi'

/-- The weighted `L2` hypothesis used for the prime terms. -/
theorem exteriorTail_weightedL2 {F F' : ℝ → ℂ} (hc : Continuous F)
    {a : ℝ} (ha : 0 ≤ a)
    (hd : ∀ x ∈ (Icc (-a) a)ᶜ, HasDerivAt F (F' x) x)
    (hi : IntegrableOn (weightedProfile 1 F) (Icc (-a) a)ᶜ)
    (hi' : IntegrableOn (weightedProfile 1 F') (Icc (-a) a)ᶜ) :
    WeightedL2 1 (exteriorTail a F) := by
  apply memLp_two_of_integrable_bv
  · rw [weightedProfile_exteriorTail]
    exact exteriorTail_integrable hi
  · exact weighted_exteriorTail_boundedVariation hc ha hd hi hi'

/-- The ordinary weighted L1 data and both endpoint costs for a hard tail. -/
def hardTailBudget (F F' : ℝ → ℂ) (a : ℝ) : ℝ :=
  Real.exp a * (‖F (-a)‖ + ‖F a‖) +
    ∫ x in (Icc (-a) a)ᶜ, Real.exp |x| * (‖F x‖ + ‖F' x‖)

theorem hardTailBudget_nonneg (F F' : ℝ → ℂ) (a : ℝ) :
    0 ≤ hardTailBudget F F' a := by
  unfold hardTailBudget
  exact add_nonneg (by positivity) (integral_nonneg (fun _ => by positivity))

theorem weighted_exteriorTail_variation_le {F F' : ℝ → ℂ} (hc : Continuous F)
    {a : ℝ} (ha : 0 ≤ a)
    (hd : ∀ x ∈ (Icc (-a) a)ᶜ, HasDerivAt F (F' x) x)
    (hi : IntegrableOn (weightedProfile 1 F) (Icc (-a) a)ᶜ)
    (hi' : IntegrableOn (weightedProfile 1 F') (Icc (-a) a)ᶜ) :
    (eVariationOn (weightedProfile 1 (exteriorTail a F)) univ).toReal ≤
      hardTailBudget F F' a := by
  have hdi := weightedTailDerivative_integrableOn hi hi'
  have hw : IntegrableOn (fun x => Real.exp |x| * (‖F x‖ + ‖F' x‖)) (Icc (-a) a)ᶜ := by
    change Integrable _ (volume.restrict (Icc (-a) a)ᶜ)
    have he : (fun x => Real.exp |x| * (‖F x‖ + ‖F' x‖)) =
        (fun x => ‖weightedProfile 1 F x‖) + (fun x => ‖weightedProfile 1 F' x‖) := by
      funext x
      simp [weightedProfile_norm, mul_add]
    rw [he]
    exact hi.norm.add hi'.norm
  have hdW : ∀ x ∈ (Icc (-a) a)ᶜ,
      HasDerivAt (weightedProfile 1 F) (weightedTailDerivative F F' x) x := by
    intro x hx
    apply weightedProfile_one_hasDerivAt _ (hd x hx)
    intro he
    subst x
    exact hx ⟨by linarith, ha⟩
  have hb : (∫ x in (Icc (-a) a)ᶜ, ‖weightedTailDerivative F F' x‖) ≤
      ∫ x in (Icc (-a) a)ᶜ, Real.exp |x| * (‖F x‖ + ‖F' x‖) := by
    apply integral_mono hdi.norm hw
    intro x
    simpa only [add_comm] using weightedTailDerivative_norm_le F F' x
  have hv := exteriorTail_variation_toReal_le (weightedProfile_one_continuous hc) ha hdW hdi
  rw [← weightedProfile_exteriorTail] at hv
  simp only [weightedProfile_norm, one_mul, abs_neg, abs_of_nonneg ha] at hv
  exact hv.trans (by dsimp [hardTailBudget]; nlinarith)

/-- An exponential pointwise envelope follows from the proved weighted BV bound. -/
theorem exteriorTail_weighted_pointwise {F F' : ℝ → ℂ} (hc : Continuous F)
    {a : ℝ} (ha : 0 ≤ a)
    (hd : ∀ x ∈ (Icc (-a) a)ᶜ, HasDerivAt F (F' x) x)
    (hi : IntegrableOn (weightedProfile 1 F) (Icc (-a) a)ᶜ)
    (hi' : IntegrableOn (weightedProfile 1 F') (Icc (-a) a)ᶜ) (x : ℝ) :
    Real.exp |x| * ‖exteriorTail a F x‖ ≤ hardTailBudget F F' a := by
  have hint : Integrable (weightedProfile 1 (exteriorTail a F)) := by
    rw [weightedProfile_exteriorTail]
    exact exteriorTail_integrable hi
  have hb := norm_le_variation hint (weighted_exteriorTail_boundedVariation hc ha hd hi hi') x
  simp only [weightedProfile_norm, one_mul] at hb
  exact hb.trans (weighted_exteriorTail_variation_le hc ha hd hi hi')

/-- Removing the exponential weight preserves ordinary integrability. -/
theorem integrableOn_of_weightedProfile_one {F : ℝ → ℂ} {s : Set ℝ}
    (hi : IntegrableOn (weightedProfile 1 F) s) : IntegrableOn F s := by
  have hc : Continuous (fun x : ℝ => (Real.exp (-(1 * |x|)) : ℂ)) := by fun_prop
  have hm : AEStronglyMeasurable F (volume.restrict s) := by
    have h := hc.aestronglyMeasurable.mul hi.aestronglyMeasurable
    simpa only [Pi.mul_def, weightedProfile_cancel] using h
  apply hi.norm.mono' hm
  filter_upwards [] with x
  rw [weightedProfile_norm, one_mul]
  exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp_iff.mpr (abs_nonneg x))

theorem weighted_exteriorTail_l1_eq (F : ℝ → ℂ) (a : ℝ) :
    (∫ x : ℝ, ‖weightedProfile 1 (exteriorTail a F) x‖) =
      ∫ x in (Icc (-a) a)ᶜ, ‖weightedProfile 1 F x‖ := by
  rw [weightedProfile_exteriorTail]
  simp only [exteriorTail, norm_indicator_eq_indicator_norm]
  exact integral_indicator measurableSet_Icc.compl

theorem weighted_exteriorTail_l1_le {F F' : ℝ → ℂ} {a : ℝ}
    (hi : IntegrableOn (weightedProfile 1 F) (Icc (-a) a)ᶜ)
    (hi' : IntegrableOn (weightedProfile 1 F') (Icc (-a) a)ᶜ) :
    (∫ x : ℝ, ‖weightedProfile 1 (exteriorTail a F) x‖) ≤ hardTailBudget F F' a := by
  rw [weighted_exteriorTail_l1_eq]
  have h : (∫ x in (Icc (-a) a)ᶜ, ‖weightedProfile 1 F x‖) ≤
      ∫ x in (Icc (-a) a)ᶜ,
        ‖weightedProfile 1 F x‖ + ‖weightedProfile 1 F' x‖ := by
    apply integral_mono hi.norm (hi.norm.add hi'.norm)
    intro x
    exact le_add_of_nonneg_right (norm_nonneg _)
  simp only [weightedProfile_norm, one_mul, ← mul_add] at h
  have hh : (∫ x in (Icc (-a) a)ᶜ, Real.exp |x| * (‖F x‖ + ‖F' x‖)) ≤
      hardTailBudget F F' a := by
    unfold hardTailBudget
    exact le_add_of_nonneg_left (by positivity)
  simpa only [weightedProfile_norm, one_mul] using h.trans hh

/-- Quantitative weighted L2 control from the ordinary derivative data. -/
theorem exteriorTail_weightedNorm_le {F F' : ℝ → ℂ} (hc : Continuous F)
    {a : ℝ} (ha : 0 ≤ a)
    (hd : ∀ x ∈ (Icc (-a) a)ᶜ, HasDerivAt F (F' x) x)
    (hi : IntegrableOn (weightedProfile 1 F) (Icc (-a) a)ᶜ)
    (hi' : IntegrableOn (weightedProfile 1 F') (Icc (-a) a)ᶜ) :
    weightedNorm 1 (exteriorTail a F) ≤ hardTailBudget F F' a := by
  have hm := hardTailBudget_nonneg F F' a
  have hint : Integrable (weightedProfile 1 (exteriorTail a F)) := by
    rw [weightedProfile_exteriorTail]
    exact exteriorTail_integrable hi
  have h2 := weighted_square_integrable (exteriorTail_weightedL2 hc ha hd hi hi')
  have hpt (x : ℝ) : ‖weightedProfile 1 (exteriorTail a F) x‖ ≤ hardTailBudget F F' a := by
    simpa only [weightedProfile_norm, one_mul] using exteriorTail_weighted_pointwise hc ha hd hi hi' x
  have hb : (∫ x : ℝ, ‖weightedProfile 1 (exteriorTail a F) x‖ ^ 2) ≤
      (hardTailBudget F F' a) ^ 2 := by
    calc
      _ ≤ ∫ x : ℝ, hardTailBudget F F' a * ‖weightedProfile 1 (exteriorTail a F) x‖ := by
        apply integral_mono h2 (hint.norm.const_mul _)
        intro x
        simpa only [sq] using mul_le_mul_of_nonneg_right (hpt x) (norm_nonneg _)
      _ = hardTailBudget F F' a * (∫ x : ℝ, ‖weightedProfile 1 (exteriorTail a F) x‖) :=
        integral_const_mul _ _
      _ ≤ hardTailBudget F F' a * hardTailBudget F F' a :=
        mul_le_mul_of_nonneg_left (weighted_exteriorTail_l1_le hi hi') hm
      _ = _ := (sq _).symm
  exact (Real.sqrt_le_iff).2 ⟨hm, hb⟩

theorem exteriorTail_l1_le_budget {F F' : ℝ → ℂ} {a : ℝ}
    (hi : IntegrableOn (weightedProfile 1 F) (Icc (-a) a)ᶜ)
    (hi' : IntegrableOn (weightedProfile 1 F') (Icc (-a) a)ᶜ) :
    (∫ x : ℝ, ‖exteriorTail a F x‖) ≤ hardTailBudget F F' a := by
  have ht := exteriorTail_integrable (integrableOn_of_weightedProfile_one hi)
  have hwt : Integrable (weightedProfile 1 (exteriorTail a F)) := by
    rw [weightedProfile_exteriorTail]
    exact exteriorTail_integrable hi
  apply le_trans (integral_mono ht.norm hwt.norm ?_) (weighted_exteriorTail_l1_le hi hi')
  intro x
  dsimp only
  rw [weightedProfile_norm, one_mul]
  exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp_iff.mpr (abs_nonneg x))

theorem exteriorTail_variation_le_budget {F F' : ℝ → ℂ} (hc : Continuous F)
    {a : ℝ} (ha : 0 ≤ a)
    (hd : ∀ x ∈ (Icc (-a) a)ᶜ, HasDerivAt F (F' x) x)
    (hi : IntegrableOn (weightedProfile 1 F) (Icc (-a) a)ᶜ)
    (hi' : IntegrableOn (weightedProfile 1 F') (Icc (-a) a)ᶜ) :
    (eVariationOn (exteriorTail a F) univ).toReal ≤ hardTailBudget F F' a := by
  have hi0 := integrableOn_of_weightedProfile_one hi'
  have hdi : (∫ x in (Icc (-a) a)ᶜ, ‖F' x‖) ≤
      ∫ x in (Icc (-a) a)ᶜ, ‖weightedProfile 1 F x‖ + ‖weightedProfile 1 F' x‖ := by
    apply integral_mono hi0.norm (hi.norm.add hi'.norm)
    intro x
    calc
      _ ≤ ‖weightedProfile 1 F' x‖ := by
        rw [weightedProfile_norm, one_mul]
        exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp_iff.mpr (abs_nonneg x))
      _ ≤ _ := le_add_of_nonneg_left (norm_nonneg _)
  simp only [weightedProfile_norm, one_mul, ← mul_add] at hdi
  have hep : ‖F (-a)‖ + ‖F a‖ ≤ Real.exp a * (‖F (-a)‖ + ‖F a‖) :=
    le_mul_of_one_le_left (add_nonneg (norm_nonneg _) (norm_nonneg _))
      (Real.one_le_exp_iff.mpr ha)
  exact (exteriorTail_variation_toReal_le hc ha hd hi0).trans (add_le_add hep hdi)

/-- Fourier decay of the hard tail, with the endpoint contributions included. -/
theorem exteriorTail_fourier_bound {F F' : ℝ → ℂ} (hc : Continuous F)
    {a : ℝ} (ha : 0 ≤ a)
    (hd : ∀ x ∈ (Icc (-a) a)ᶜ, HasDerivAt F (F' x) x)
    (hi : IntegrableOn (weightedProfile 1 F) (Icc (-a) a)ᶜ)
    (hi' : IntegrableOn (weightedProfile 1 F') (Icc (-a) a)ᶜ) (r : ℝ) :
    ‖paperFourier (exteriorTail a F) r‖ * (1 + |r|) ≤
      (1 + Real.pi / 2) * hardTailBudget F F' a := by
  have ht := exteriorTail_integrable (integrableOn_of_weightedProfile_one hi)
  have hv := exteriorTail_boundedVariation hc ha hd (integrableOn_of_weightedProfile_one hi')
  have hb := paperFourier_norm_mul_one_add_abs_le ht hv r
  have hL := exteriorTail_l1_le_budget hi hi'
  have hV := mul_le_mul_of_nonneg_left (exteriorTail_variation_le_budget hc ha hd hi hi')
    Real.pi_pos.le
  nlinarith

end ThetaTrial.Paper
