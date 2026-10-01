import ThetaTrial.Paper.ThetaConcentration
import ThetaTrial.Paper.TailVariation
import ThetaTrial.Paper.RadicalSource
import ThetaTrial.Paper.TrialFourierComplex

/-!
Regularity of `P(D)Φ` for complex polynomials `P`. The one-sided cutoffs
have jumps at their endpoints.
-/

noncomputable section
open Complex MeasureTheory Set Filter Polynomial
open ThetaTrial.PrimeContinuity
open scoped Topology ContDiff

namespace ThetaTrial.Paper

theorem thetaDensity_iteratedDeriv_contDiff (j : ℕ) :
    ContDiff ℝ ⊤ (iteratedDeriv j (fun u : ℝ => (thetaDensity u : ℂ))) := by
  rw [show iteratedDeriv j (fun u : ℝ => (thetaDensity u : ℂ)) =
    fun u : ℝ => iteratedDeriv j complexThetaDensity (u : ℂ) from
      funext (RadicalApproximation.theta_real_iteratedDeriv j)]
  rw [contDiff_iff_contDiffAt]
  intro u
  have hc : ContDiffAt ℝ ⊤ (iteratedDeriv j complexThetaDensity) (u : ℂ) :=
    (RadicalApproximation.analytic_iteratedTheta j (u : ℂ)
      (RadicalApproximation.real_mem_thetaStrip u)).contDiffAt.restrict_scalars ℝ
  simpa only [Function.comp_def, Complex.ofRealCLM_apply] using!
    hc.comp u Complex.ofRealCLM.contDiff.contDiffAt

theorem thetaDensity_iteratedDeriv_hasDerivAt (j : ℕ) (u : ℝ) :
    HasDerivAt (iteratedDeriv j (fun v : ℝ => (thetaDensity v : ℂ)))
      (iteratedDeriv (j + 1) (fun v : ℝ => (thetaDensity v : ℂ)) u) u := by
  simpa only [iteratedDeriv_succ] using
    ((RadicalApproximation.thetaDensity_contDiff.differentiable_iteratedDeriv j (by simp)) u).hasDerivAt

theorem polynomialDerivative_thetaDensity_eq (P : ℂ[X]) :
    polynomialDerivative P (fun u : ℝ => (thetaDensity u : ℂ)) =
      fun u => ∑ j ∈ P.support, (P.coeff j * (-I) ^ j) *
        iteratedDeriv j (fun v : ℝ => (thetaDensity v : ℂ)) u := by
  funext u
  simp only [polynomialDerivative, differentialOperator_iterate, mul_assoc]

theorem polynomialDerivative_thetaDensity_contDiff (P : ℂ[X]) :
    ContDiff ℝ ⊤ (polynomialDerivative P (fun u : ℝ => (thetaDensity u : ℂ))) := by
  rw [polynomialDerivative_thetaDensity_eq]
  exact ContDiff.sum (fun j _ => contDiff_const.mul (thetaDensity_iteratedDeriv_contDiff j))

theorem polynomialDerivative_thetaDensity_iteratedDeriv (P : ℂ[X]) (r : ℕ) :
    iteratedDeriv r (polynomialDerivative P (fun u : ℝ => (thetaDensity u : ℂ))) =
      fun u => ∑ j ∈ P.support, (P.coeff j * (-I) ^ j) *
        iteratedDeriv (j + r) (fun v : ℝ => (thetaDensity v : ℂ)) u := by
  induction r with
  | zero => simpa only [iteratedDeriv_zero, Nat.add_zero] using polynomialDerivative_thetaDensity_eq P
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    have hd := HasDerivAt.fun_sum (u := P.support) (fun j _ =>
      (thetaDensity_iteratedDeriv_hasDerivAt (j + r) u).const_mul (P.coeff j * (-I) ^ j))
    simpa only [Nat.add_assoc] using hd.deriv

theorem thetaDensity_iteratedDeriv_all_weights_integrable (j : ℕ) (R : ℝ) :
    Integrable (weightedProfile R (iteratedDeriv j (fun u : ℝ => (thetaDensity u : ℂ)))) := by
  apply (RadicalApproximation.theta_iteratedDeriv_weighted_integrable j R).mono'
    ((show Continuous (weightedProfile R (iteratedDeriv j (fun u : ℝ => (thetaDensity u : ℂ)))) by
      unfold weightedProfile
      exact (Complex.continuous_ofReal.comp (by fun_prop)).mul
        (thetaDensity_iteratedDeriv_contDiff j).continuous).aestronglyMeasurable)
  filter_upwards [] with u
  rw [weightedProfile_norm]

theorem polynomialDerivative_thetaDensity_iteratedDeriv_all_weights_integrable
    (P : ℂ[X]) (r : ℕ) (R : ℝ) :
    Integrable (weightedProfile R
      (iteratedDeriv r (polynomialDerivative P (fun u : ℝ => (thetaDensity u : ℂ))))) := by
  rw [polynomialDerivative_thetaDensity_iteratedDeriv]
  have he : weightedProfile R (fun u => ∑ j ∈ P.support, (P.coeff j * (-I) ^ j) *
      iteratedDeriv (j + r) (fun v : ℝ => (thetaDensity v : ℂ)) u) =
      fun u => ∑ j ∈ P.support, (P.coeff j * (-I) ^ j) *
        weightedProfile R (iteratedDeriv (j + r) (fun v : ℝ => (thetaDensity v : ℂ))) u := by
    funext u
    simp only [weightedProfile, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  exact integrable_finsetSum _ (fun j _ =>
    (thetaDensity_iteratedDeriv_all_weights_integrable (j + r) R).const_mul _)

theorem polynomialDerivative_thetaDensity_norm_weighted_integrable
    (P : ℂ[X]) (r : ℕ) (R : ℝ) :
    Integrable (fun u : ℝ => Real.exp (R * |u|) *
      ‖iteratedDeriv r (polynomialDerivative P (fun v : ℝ => (thetaDensity v : ℂ))) u‖) := by
  simpa only [weightedProfile_norm] using
    (polynomialDerivative_thetaDensity_iteratedDeriv_all_weights_integrable P r R).norm

theorem polynomialDerivative_thetaDensity_all_weights_integrable (P : ℂ[X]) (R : ℝ) :
    Integrable (weightedProfile R (polynomialDerivative P (fun u : ℝ => (thetaDensity u : ℂ)))) := by
  simpa only [iteratedDeriv_zero] using
    polynomialDerivative_thetaDensity_iteratedDeriv_all_weights_integrable P 0 R

theorem polynomialDerivative_thetaDensity_integrable (P : ℂ[X]) :
    Integrable (polynomialDerivative P (fun u : ℝ => (thetaDensity u : ℂ))) := by
  exact integrableOn_univ.mp (integrableOn_of_weightedProfile_one
    (polynomialDerivative_thetaDensity_all_weights_integrable P 1).integrableOn)

theorem polynomialDerivative_thetaDensity_deriv_integrable (P : ℂ[X]) :
    Integrable (deriv (polynomialDerivative P (fun u : ℝ => (thetaDensity u : ℂ)))) := by
  have hi : Integrable (weightedProfile 1
      (deriv (polynomialDerivative P (fun u : ℝ => (thetaDensity u : ℂ))))) := by
    simpa only [iteratedDeriv_one] using
      polynomialDerivative_thetaDensity_iteratedDeriv_all_weights_integrable P 1 1
  exact integrableOn_univ.mp (integrableOn_of_weightedProfile_one hi.integrableOn)

theorem polynomialDerivative_thetaDensity_boundedVariation (P : ℂ[X]) :
    BoundedVariationOn (polynomialDerivative P (fun u : ℝ => (thetaDensity u : ℂ))) univ := by
  have hd := (polynomialDerivative_thetaDensity_contDiff P).differentiable (by simp)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (variation_le_integral_deriv ordConnected_univ (fun u _ => (hd u).hasDerivAt)
      (polynomialDerivative_thetaDensity_deriv_integrable P).integrableOn)

theorem polynomialDerivative_thetaDensity_memLp_two (P : ℂ[X]) :
    MemLp (polynomialDerivative P (fun u : ℝ => (thetaDensity u : ℂ))) 2 volume :=
  memLp_two_of_integrable_bv (polynomialDerivative_thetaDensity_integrable P)
    (polynomialDerivative_thetaDensity_boundedVariation P)

/-- The open half-line cutoff has one ordinary endpoint jump, regardless
of whether its source vanishes at that endpoint. -/
theorem continuous_bv_indicator_Ioi {F : ℝ → ℂ} (hc : Continuous F)
    (hv : BoundedVariationOn F univ) (a : ℝ) :
    BoundedVariationOn ((Ioi a).indicator F) univ := by
  let g := (Ioi a).indicator F
  have he : EqOn g F (Ioi a) := fun x hx => indicator_of_mem hx F
  have hl : Tendsto g (𝓝[univ ∩ Ioi a] a) (𝓝 (F a)) := by
    simp only [univ_inter]
    apply (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (he hx).symm
  have hj := eVariationOn.eVariationOn_on_inter_Ici_eq_Ioi_add_edist
    (f := g) (s := univ) (a := a) (by simp only [univ_inter]; infer_instance) (mem_univ _) hl
  simp only [univ_inter] at hj
  rw [eVariationOn.eq_of_eqOn he] at hj
  have hz : eVariationOn g (Iic a) = 0 := by
    rw [eVariationOn.eq_of_eqOn (f' := fun _ => (0 : ℂ)) (by
      intro x hx
      simp [g, not_lt.mpr (show x ≤ a from hx)])]
    exact (eVariationOn.eq_zero_iff _).2 (fun _ _ _ _ => edist_self _)
  have hs := eVariationOn.union g (isGreatest_Iic (a := a)) (isLeast_Ici (a := a))
  rw [Iic_union_Ici, hz, zero_add, hj] at hs
  change eVariationOn g univ ≠ (⊤ : ENNReal)
  rw [hs]
  exact ENNReal.add_ne_top.mpr ⟨hv.mono (subset_univ _), by finiteness⟩

theorem continuous_bv_indicator_Iio {F : ℝ → ℂ} (hc : Continuous F)
    (hv : BoundedVariationOn F univ) (a : ℝ) :
    BoundedVariationOn ((Iio a).indicator F) univ := by
  let g := (Iio a).indicator F
  have he : EqOn g F (Iio a) := fun x hx => indicator_of_mem hx F
  have hl : Tendsto g (𝓝[univ ∩ Iio a] a) (𝓝 (F a)) := by
    simp only [univ_inter]
    apply (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (he hx).symm
  have hj := eVariationOn.eVariationOn_on_inter_Iic_eq_Iio_add_edist
    (f := g) (s := univ) (a := a) (by simp only [univ_inter]; infer_instance) (mem_univ _) hl
  simp only [univ_inter] at hj
  rw [eVariationOn.eq_of_eqOn he] at hj
  have hz : eVariationOn g (Ici a) = 0 := by
    rw [eVariationOn.eq_of_eqOn (f' := fun _ => (0 : ℂ)) (by
      intro x hx
      simp [g, not_lt.mpr (show a ≤ x from hx)])]
    exact (eVariationOn.eq_zero_iff _).2 (fun _ _ _ _ => edist_self _)
  have hs := eVariationOn.union g (isGreatest_Iic (a := a)) (isLeast_Ici (a := a))
  rw [Iic_union_Ici, hz, add_zero, hj] at hs
  change eVariationOn g univ ≠ (⊤ : ENNReal)
  rw [hs]
  exact ENNReal.add_ne_top.mpr ⟨hv.mono (subset_univ _), by finiteness⟩

theorem thetaDerivRightTail_boundedVariation (P : ℂ[X]) (a : ℝ) :
    BoundedVariationOn (thetaDerivRightTail P a) univ :=
  continuous_bv_indicator_Ioi (polynomialDerivative_thetaDensity_contDiff P).continuous
    (polynomialDerivative_thetaDensity_boundedVariation P) a

theorem thetaDerivLeftTail_boundedVariation (P : ℂ[X]) (a : ℝ) :
    BoundedVariationOn (thetaDerivLeftTail P a) univ :=
  continuous_bv_indicator_Iio (polynomialDerivative_thetaDensity_contDiff P).continuous
    (polynomialDerivative_thetaDensity_boundedVariation P) (-a)

theorem thetaDensity_iteratedDeriv_exponential_bound (j : ℕ) (R : ℝ) :
    ∃ M > 0, ∀ u : ℝ,
      ‖iteratedDeriv j (fun v : ℝ => (thetaDensity v : ℂ)) u‖ ≤
        M * Real.exp (-(R * |u|)) := by
  obtain ⟨c, hc, hder⟩ := complexThetaDensity_iteratedDeriv_closed_strip_decay
    (b := 0) le_rfl (by positivity)
  obtain ⟨C, hC, hb⟩ := hder j
  obtain ⟨B, hB, henv⟩ := RadicalApproximation.doubleExpEnvelope_bounded
    (R + (9 / 2 + 2 * (j : ℝ))) hc
  refine ⟨C * B, mul_pos hC hB, ?_⟩
  intro u
  have h := hb (u : ℂ) (by simp)
  simp only [Complex.ofReal_re] at h
  have hw : Real.exp (R * |u|) *
      ‖iteratedDeriv j (fun v : ℝ => (thetaDensity v : ℂ)) u‖ ≤ C * B := by
    rw [RadicalApproximation.theta_real_iteratedDeriv]
    calc
      _ ≤ Real.exp (R * |u|) *
          (C * Real.exp ((9 / 2 + 2 * (j : ℝ)) * |u|) *
            Real.exp (-c * Real.exp (2 * |u|))) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = C * ThetaTrial.ThetaSeries.doubleExpEnvelope (R + (9 / 2 + 2 * (j : ℝ))) c |u| := by
        have he : Real.exp ((R + (9 / 2 + 2 * (j : ℝ))) * |u|) =
            Real.exp (R * |u|) * Real.exp ((9 / 2 + 2 * (j : ℝ)) * |u|) := by
          rw [add_mul, Real.exp_add]
        unfold ThetaTrial.ThetaSeries.doubleExpEnvelope
        rw [he]
        ring
      _ ≤ C * B := mul_le_mul_of_nonneg_left (henv |u| (abs_nonneg u)) hC.le
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
  simpa only [mul_comm] using hw

theorem polynomialDerivative_thetaDensity_exponential_bound (P : ℂ[X]) (R : ℝ) :
    ∃ M > 0, ∀ u : ℝ,
      ‖polynomialDerivative P (fun v : ℝ => (thetaDensity v : ℂ)) u‖ ≤
        M * Real.exp (-(R * |u|)) := by
  classical
  choose M hM hb using fun j : ℕ => thetaDensity_iteratedDeriv_exponential_bound j R
  let S := ∑ j ∈ P.support, ‖P.coeff j * (-I) ^ j‖ * M j
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (hM j).le)
  refine ⟨S + 1, by positivity, ?_⟩
  intro u
  rw [polynomialDerivative_thetaDensity_eq]
  calc
    _ ≤ ∑ j ∈ P.support, ‖(P.coeff j * (-I) ^ j) *
        iteratedDeriv j (fun v : ℝ => (thetaDensity v : ℂ)) u‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ P.support,
        (‖P.coeff j * (-I) ^ j‖ * M j) * Real.exp (-(R * |u|)) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hb j u) (norm_nonneg _)
    _ = S * Real.exp (-(R * |u|)) := by rw [Finset.sum_mul]
    _ ≤ (S + 1) * Real.exp (-(R * |u|)) := by nlinarith [Real.exp_pos (-(R * |u|))]

/-- `P(D)Φ` satisfies all the hypotheses of the source class used for the
explicit formula. -/
theorem polynomialDerivative_thetaDensity_regularSource (P : ℂ[X]) :
    RadicalSource.RegularSource (polynomialDerivative P (fun u : ℝ => (thetaDensity u : ℂ))) := by
  refine ⟨(polynomialDerivative_thetaDensity_contDiff P).of_le le_top,
    ?_, ?_, ?_, polynomialDerivative_thetaDensity_exponential_bound P⟩
  · intro R
    simpa only [iteratedDeriv_zero] using polynomialDerivative_thetaDensity_norm_weighted_integrable P 0 R
  · intro R
    simpa only [iteratedDeriv_one] using polynomialDerivative_thetaDensity_norm_weighted_integrable P 1 R
  · intro R
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      polynomialDerivative_thetaDensity_norm_weighted_integrable P 2 R

theorem polynomialDerivative_thetaDensity_fourier (P : ℂ[X]) (z : ℂ) :
    paperFourier (polynomialDerivative P (fun u : ℝ => (thetaDensity u : ℂ))) z =
      xiFunction z * P.eval z := by
  rw [paperFourier_polynomialDerivative_complex RadicalApproximation.thetaDensity_contDiff
    RadicalApproximation.theta_iteratedDeriv_weighted_integrable P z, paperFourier_theta]
  ring

theorem polynomialDerivative_thetaDensity_hardCutoff (P : ℂ[X]) {a : ℝ} (ha : 0 ≤ a) :
    fullWeilForm (windowCut a (polynomialDerivative P (fun u : ℝ => (thetaDensity u : ℂ)))) =
      fullWeilForm (exteriorTail a (polynomialDerivative P (fun u : ℝ => (thetaDensity u : ℂ)))) :=
  RadicalSource.source_hardCutoff (polynomialDerivative_thetaDensity_regularSource P)
    (polynomialDerivative_thetaDensity_fourier P) ha

theorem polynomialDerivative_thetaDensity_radical (P : ℂ[X]) {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h)
    (hi : ∀ R : ℝ, Integrable (fun u : ℝ => Real.exp (R * |u|) * ‖h u‖)) :
    Radical.fullPairing (polynomialDerivative P (fun u : ℝ => (thetaDensity u : ℂ))) h = 0 :=
  RadicalSource.source_fullPairing_eq_zero (polynomialDerivative_thetaDensity_regularSource P)
    (polynomialDerivative_thetaDensity_fourier P) hm hi

end ThetaTrial.Paper
