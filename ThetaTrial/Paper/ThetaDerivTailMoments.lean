import ThetaTrial.Paper.Laguerre
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Offset moments and weighted L¹ from survival bounds

A layer-cake argument turns the tail mass estimate into moment bounds and
integrability. Zero mass is allowed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ThetaTrial.Paper.ThetaDerivTailMoments

/-- Layer-cake transfer, including integrability, from an exponential
survival estimate beyond a finite offset. -/
theorem primitive_integrable_bound_of_survival
    (μ : Measure ℝ) {A s₀ r : ℝ} (hA : 0 ≤ A) (hs₀ : 0 ≤ s₀)
    (hmass : μ univ = ENNReal.ofReal A)
    (hpos : ∀ᵐ x ∂μ, 0 ≤ x)
    (htail : ∀ s : ℝ, s₀ ≤ s → μ (Ioi s) ≤ ENNReal.ofReal (A * Real.exp (-(r * s))))
    (g : ℝ → ℝ) (hg : Continuous g) (hgn : ∀ s : ℝ, 0 ≤ s → 0 ≤ g s)
    (hgi : IntegrableOn (fun s : ℝ => g s * Real.exp (-(r * s))) (Ioi 0)) :
    Integrable (fun x : ℝ => ∫ s in 0..x, g s) μ ∧
      (∫ x : ℝ, (∫ s in 0..x, g s) ∂μ) ≤
        A * ((∫ s in 0..s₀, g s) +
          ∫ s : ℝ in Ioi 0, g s * Real.exp (-(r * s))) := by
  let G : ℝ → ℝ := fun s => (Ioc 0 s₀).indicator g s + g s * Real.exp (-(r * s))
  have hi₀ : IntegrableOn g (Ioc 0 s₀) :=
    (hg.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hGI : IntegrableOn G (Ioi 0) :=
    (hi₀.integrable_indicator measurableSet_Ioc).integrableOn.add hgi
  have hGn : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ G s := by
    intro s hs
    have hn := hgn s (le_of_lt hs)
    dsimp [G]
    exact add_nonneg (indicator_nonneg (fun t (ht : t ∈ Ioc 0 s₀) => hgn t ht.1.le) s)
      (mul_nonneg hn (Real.exp_pos _).le)
  have hprim : ∀ᵐ x ∂μ, 0 ≤ ∫ s in 0..x, g s := by
    filter_upwards [hpos] with x hx
    exact intervalIntegral.integral_nonneg hx (fun s hs => hgn s hs.1)
  have hcont : Continuous (fun x : ℝ => ∫ s in 0..x, g s) :=
    intervalIntegral.continuous_primitive (fun a b => hg.intervalIntegrable a b) 0
  have hpoint : ∀ s ∈ Ioi (0 : ℝ),
      μ (Ioi s) * ENNReal.ofReal (g s) ≤ ENNReal.ofReal (A * G s) := by
    intro s hs
    have hn := hgn s (le_of_lt hs)
    by_cases ht : s ≤ s₀
    · have hmem : s ∈ Ioc 0 s₀ := ⟨hs, ht⟩
      calc
        _ ≤ ENNReal.ofReal A * ENNReal.ofReal (g s) :=
          by gcongr; exact (measure_mono (subset_univ _)).trans_eq hmass
        _ = ENNReal.ofReal (A * g s) := (ENNReal.ofReal_mul hA).symm
        _ ≤ ENNReal.ofReal (A * G s) := by
          apply ENNReal.ofReal_le_ofReal
          dsimp [G]
          rw [indicator_of_mem hmem]
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right
            (mul_nonneg hn (Real.exp_pos _).le)) hA
    · have hmem : s ∉ Ioc 0 s₀ := by simp [ht]
      calc
        _ ≤ ENNReal.ofReal (A * Real.exp (-(r * s))) * ENNReal.ofReal (g s) :=
          by gcongr; exact htail s (le_of_lt (lt_of_not_ge ht))
        _ = ENNReal.ofReal (A * G s) := by
          rw [← ENNReal.ofReal_mul (mul_nonneg hA (Real.exp_pos _).le)]
          congr 1
          simp only [G, indicator_of_notMem hmem, zero_add]
          ring
  have hbound : (∫⁻ x : ℝ, ENNReal.ofReal (∫ s in 0..x, g s) ∂μ) ≤
      ENNReal.ofReal (A * ∫ s : ℝ in Ioi 0, G s) := by
    rw [lintegral_comp_eq_lintegral_meas_lt_mul μ hpos measurable_id.aemeasurable
      (fun t _ => hg.intervalIntegrable 0 t)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hgn t ht.le)]
    calc
      _ ≤ ∫⁻ s : ℝ in Ioi 0, ENNReal.ofReal (A * G s) :=
        lintegral_mono_ae (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs using hpoint s hs)
      _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal (hGI.const_mul A)
          (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs using mul_nonneg hA (hGn s hs)),
          integral_const_mul]
  have hint : Integrable (fun x : ℝ => ∫ s in 0..x, g s) μ :=
    ⟨hcont.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hprim).mpr
      (lt_of_le_of_lt hbound ENNReal.ofReal_lt_top)⟩
  have hGIeq : (∫ s : ℝ in Ioi 0, G s) =
      (∫ s in 0..s₀, g s) + ∫ s : ℝ in Ioi 0, g s * Real.exp (-(r * s)) := by
    change (∫ s : ℝ in Ioi 0, (Ioc 0 s₀).indicator g s +
      g s * Real.exp (-(r * s))) = _
    rw [integral_add (hi₀.integrable_indicator measurableSet_Ioc).integrableOn hgi,
      integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr Ioc_subset_Ioi_self, ← intervalIntegral.integral_of_le hs₀]
  refine ⟨hint, ?_⟩
  have hnonneg : 0 ≤ A * ∫ s : ℝ in Ioi 0, G s :=
    mul_nonneg hA (integral_nonneg_of_ae
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs using hGn s hs))
  rw [← ofReal_integral_eq_lintegral_ofReal hint hprim] at hbound
  have h := (ENNReal.ofReal_le_ofReal_iff hnonneg).mp hbound
  rwa [hGIeq] at h


theorem first_moment_of_survival
    (μ : Measure ℝ) {A s₀ r : ℝ} (hA : 0 ≤ A) (hs₀ : 0 ≤ s₀) (hr : 0 < r)
    (hmass : μ univ = ENNReal.ofReal A) (hpos : ∀ᵐ x ∂μ, 0 ≤ x)
    (htail : ∀ s : ℝ, s₀ ≤ s → μ (Ioi s) ≤ ENNReal.ofReal (A * Real.exp (-(r * s)))) :
    Integrable (fun x : ℝ => x) μ ∧
      (∫ x : ℝ, x ∂μ) ≤ A * (s₀ + 1 / r) := by
  have hgi : IntegrableOn (fun s : ℝ => 1 * Real.exp (-(r * s))) (Ioi 0) := by
    simpa only [pow_zero] using integrableOn_pow_exp_neg_mul 0 hr
  have h := primitive_integrable_bound_of_survival μ hA hs₀ hmass hpos htail
    (fun _ => 1) continuous_const (by intros; norm_num) hgi
  have he := integral_pow_exp_neg_mul 0 hr
  norm_num only [pow_zero, pow_one, Nat.factorial_zero, Nat.cast_one, mul_one] at he
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one, he] using h

theorem second_moment_of_survival
    (μ : Measure ℝ) {A s₀ r : ℝ} (hA : 0 ≤ A) (hs₀ : 0 ≤ s₀) (hr : 0 < r)
    (hmass : μ univ = ENNReal.ofReal A) (hpos : ∀ᵐ x ∂μ, 0 ≤ x)
    (htail : ∀ s : ℝ, s₀ ≤ s → μ (Ioi s) ≤ ENNReal.ofReal (A * Real.exp (-(r * s)))) :
    Integrable (fun x : ℝ => x ^ 2) μ ∧
      (∫ x : ℝ, x ^ 2 ∂μ) ≤ A * (s₀ ^ 2 + 2 / r ^ 2) := by
  have hgi : IntegrableOn (fun s : ℝ => (2 * s) * Real.exp (-(r * s))) (Ioi 0) := by
    apply ((integrableOn_pow_exp_neg_mul 1 hr).const_mul (2 : ℝ)).congr
    filter_upwards with s
    simp only [pow_one]
    ring
  have h := primitive_integrable_bound_of_survival μ hA hs₀ hmass hpos htail
    (fun s => 2 * s) (by fun_prop) (by intro s hs; positivity) hgi
  have hprim : ∀ x : ℝ, (∫ s in 0..x, 2 * s) = x ^ 2 := by
    intro x
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  have he : (∫ s : ℝ in Ioi 0, (2 * s) * Real.exp (-(r * s))) = 2 / r ^ 2 := by
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    have hh := integral_pow_exp_neg_mul 1 hr
    norm_num only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one] at hh
    rw [hh]
    ring
  simpa only [hprim, he] using h

/-- The exponentially weighted quadratic offset function. -/
def offsetWeight (τ s : ℝ) : ℝ := Real.exp s * (1 + s ^ 2 / τ ^ 2)

def offsetWeightDeriv (τ s : ℝ) : ℝ :=
  Real.exp s * (1 + 2 * s / τ ^ 2 + s ^ 2 / τ ^ 2)

theorem offsetWeight_hasDerivAt (τ s : ℝ) :
    HasDerivAt (offsetWeight τ) (offsetWeightDeriv τ s) s := by
  convert! (Real.hasDerivAt_exp s).mul
    ((hasDerivAt_const s (1 : ℝ)).add (((hasDerivAt_id s).pow 2).div_const (τ ^ 2))) using 1 <;>
    simp [offsetWeight, offsetWeightDeriv, Pi.add_apply, Pi.pow_apply] <;> ring

theorem offsetWeightDeriv_continuous (τ : ℝ) : Continuous (offsetWeightDeriv τ) := by
  unfold offsetWeightDeriv
  fun_prop

theorem offsetWeight_primitive (τ x : ℝ) :
    (∫ s in 0..x, offsetWeightDeriv τ s) = offsetWeight τ x - 1 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => offsetWeight_hasDerivAt τ s)
    ((offsetWeightDeriv_continuous τ).intervalIntegrable 0 x)
  simpa [offsetWeight] using h

private theorem weighted_polynomial_exp_integrable (τ : ℝ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun s : ℝ => (1 + 2 * s / τ ^ 2 + s ^ 2 / τ ^ 2) *
      Real.exp (-(r * s))) (Ioi 0) := by
  have h0 := integrableOn_pow_exp_neg_mul 0 hr
  have h1 := (integrableOn_pow_exp_neg_mul 1 hr).const_mul (2 / τ ^ 2)
  have h2 := (integrableOn_pow_exp_neg_mul 2 hr).const_mul (1 / τ ^ 2)
  have he : (fun s : ℝ => (1 + 2 * s / τ ^ 2 + s ^ 2 / τ ^ 2) * Real.exp (-(r * s))) =
      (fun s => s ^ 0 * Real.exp (-(r * s)) +
        (2 / τ ^ 2) * (s ^ 1 * Real.exp (-(r * s))) +
        (1 / τ ^ 2) * (s ^ 2 * Real.exp (-(r * s)))) := by
    ext s
    simp only [pow_zero, pow_one]
    ring
  rw [he]
  exact (h0.add h1).add h2

private theorem weighted_polynomial_exp_integral (τ : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ s : ℝ in Ioi 0, (1 + 2 * s / τ ^ 2 + s ^ 2 / τ ^ 2) *
      Real.exp (-(r * s))) =
      1 / r + (2 / τ ^ 2) * (1 / r) ^ 2 + (2 / τ ^ 2) * (1 / r) ^ 3 := by
  have he : (fun s : ℝ => (1 + 2 * s / τ ^ 2 + s ^ 2 / τ ^ 2) * Real.exp (-(r * s))) =
      (fun s => s ^ 0 * Real.exp (-(r * s))) +
      (fun s => (2 / τ ^ 2) * (s ^ 1 * Real.exp (-(r * s)))) +
      (fun s => (1 / τ ^ 2) * (s ^ 2 * Real.exp (-(r * s)))) := by
    ext s
    simp only [Pi.add_apply, pow_zero, pow_one]
    ring
  rw [he]
  change (∫ s : ℝ in Ioi 0, (s ^ 0 * Real.exp (-(r * s)) +
    (2 / τ ^ 2) * (s ^ 1 * Real.exp (-(r * s)))) +
    (1 / τ ^ 2) * (s ^ 2 * Real.exp (-(r * s)))) = _
  rw [integral_add (f := fun s : ℝ => s ^ 0 * Real.exp (-(r * s)) +
      (2 / τ ^ 2) * (s ^ 1 * Real.exp (-(r * s))))
    ((integrableOn_pow_exp_neg_mul 0 hr).fun_add
      ((integrableOn_pow_exp_neg_mul 1 hr).const_mul (2 / τ ^ 2)))
    ((integrableOn_pow_exp_neg_mul 2 hr).const_mul (1 / τ ^ 2)),
    integral_add (integrableOn_pow_exp_neg_mul 0 hr)
      ((integrableOn_pow_exp_neg_mul 1 hr).const_mul (2 / τ ^ 2))]
  simp only [integral_const_mul, integral_pow_exp_neg_mul _ hr]
  norm_num
  ring


private theorem weighted_polynomial_tail_bound {T τ : ℝ}
    (hT : 4 ≤ T) (hTτ : 2 ≤ T * τ) :
    (∫ s : ℝ in Ioi 0, (1 + 2 * s / τ ^ 2 + s ^ 2 / τ ^ 2) *
      Real.exp (-((T / 4) * s))) ≤ 17 := by
  have hr : 0 < T / 4 := by linarith
  have hτ : 0 < τ := by nlinarith
  have hi0 : 0 ≤ (T / 4)⁻¹ := (inv_pos.mpr hr).le
  have hi1 : (T / 4)⁻¹ ≤ 1 := by
    apply (inv_le_iff_one_le_mul₀ hr).mpr
    linarith
  have hi2 : (T / 4)⁻¹ ≤ 2 * τ := by
    apply (inv_le_iff_one_le_mul₀ hr).mpr
    nlinarith
  have hsq := mul_self_le_mul_self hi0 hi2
  have h2 : (2 / τ ^ 2) * ((T / 4)⁻¹) ^ 2 ≤ 8 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos hτ)]
    nlinarith
  have h3 : (2 / τ ^ 2) * ((T / 4)⁻¹) ^ 3 ≤ 8 := by
    calc
      _ = (T / 4)⁻¹ * ((2 / τ ^ 2) * ((T / 4)⁻¹) ^ 2) := by ring
      _ ≤ 1 * 8 := mul_le_mul hi1 h2 (by positivity) (by norm_num)
      _ = 8 := by norm_num
  rw [weighted_polynomial_exp_integral τ hr]
  simp only [one_div]
  linarith

private theorem offsetWeightDeriv_tail_le {T τ s : ℝ}
    (hT : 4 ≤ T) (hs : 0 ≤ s) :
    offsetWeightDeriv τ s * Real.exp (-((T / 2) * s)) ≤
      (1 + 2 * s / τ ^ 2 + s ^ 2 / τ ^ 2) * Real.exp (-((T / 4) * s)) := by
  have hp : 0 ≤ 1 + 2 * s / τ ^ 2 + s ^ 2 / τ ^ 2 := by positivity
  calc
    _ = (1 + 2 * s / τ ^ 2 + s ^ 2 / τ ^ 2) *
        Real.exp (s - (T / 2) * s) := by
      unfold offsetWeightDeriv
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hp

/-- Uniform exponential quadratic moment, with an explicit absolute
constant once the survival cutoff multiplier `K` is fixed. -/
theorem weighted_moment_of_survival
    (μ : Measure ℝ) {A K T τ : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hT : 4 ≤ T) (hTτ : 2 ≤ T * τ) (hτone : τ ≤ 1)
    (hmass : μ univ = ENNReal.ofReal A) (hpos : ∀ᵐ x ∂μ, 0 ≤ x)
    (htail : ∀ s : ℝ, K * τ ≤ s →
      μ (Ioi s) ≤ ENNReal.ofReal (A * Real.exp (-((T / 2) * s)))) :
    Integrable (offsetWeight τ) μ ∧
      (∫ x : ℝ, offsetWeight τ x ∂μ) ≤ A * (Real.exp K * (1 + K ^ 2) + 20) := by
  have hτ : 0 < τ := by nlinarith
  have hr : 0 < T / 4 := by linarith
  have hgNN (s : ℝ) (hs : 0 ≤ s) : 0 ≤ offsetWeightDeriv τ s := by
    unfold offsetWeightDeriv
    positivity
  have hgI : IntegrableOn
      (fun s : ℝ => offsetWeightDeriv τ s * Real.exp (-((T / 2) * s))) (Ioi 0) := by
    apply (weighted_polynomial_exp_integrable τ hr).mono'
      ((offsetWeightDeriv_continuous τ).mul (by fun_prop)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    simp only [Pi.mul_apply]
    rw [Real.norm_of_nonneg (mul_nonneg (hgNN s hs.le) (Real.exp_pos _).le)]
    exact offsetWeightDeriv_tail_le hT hs.le
  have htailI : (∫ s : ℝ in Ioi 0,
      offsetWeightDeriv τ s * Real.exp (-((T / 2) * s))) ≤ 17 := by
    apply le_trans (setIntegral_mono_on hgI (weighted_polynomial_exp_integrable τ hr)
      measurableSet_Ioi (fun s hs => offsetWeightDeriv_tail_le hT hs.le))
    exact weighted_polynomial_tail_bound hT hTτ
  obtain ⟨hprimI, hbound⟩ := primitive_integrable_bound_of_survival μ hA
    (mul_nonneg hK hτ.le) hmass hpos htail (offsetWeightDeriv τ)
    (offsetWeightDeriv_continuous τ) hgNN hgI
  haveI : IsFiniteMeasure μ := ⟨by rw [hmass]; exact ENNReal.ofReal_lt_top⟩
  have hWI : Integrable (offsetWeight τ) μ := by
    have h := hprimI.fun_add (integrable_const (1 : ℝ))
    simpa only [Pi.add_apply, offsetWeight_primitive, sub_add_cancel] using h
  have hconst : (∫ _x : ℝ, (1 : ℝ) ∂μ) = A := by
    simp [integral_const, measureReal_def, hmass, ENNReal.toReal_ofReal hA]
  have hcut : offsetWeight τ (K * τ) ≤ Real.exp K * (1 + K ^ 2) := by
    have he : Real.exp (K * τ) ≤ Real.exp K :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hp : (K * τ) ^ 2 / τ ^ 2 = K ^ 2 := by field_simp
    unfold offsetWeight
    rw [hp]
    exact mul_le_mul_of_nonneg_right he (by positivity)
  simp_rw [offsetWeight_primitive] at hbound
  rw [integral_sub hWI (integrable_const _), hconst] at hbound
  refine ⟨hWI, ?_⟩
  have hcut' := mul_le_mul_of_nonneg_left hcut hA
  have htail' := mul_le_mul_of_nonneg_left htailI hA
  nlinarith


/-- Original (possibly zero) squared tail mass. -/
def offsetMass (f : ℝ → ℂ) : ℝ := ∫ s : ℝ in Ioi 0, ‖f s‖ ^ 2

def offsetMeasure (f : ℝ → ℂ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun s => ENNReal.ofReal (‖f s‖ ^ 2))

def momentConstant (K : ℝ) : ℝ := Real.exp K * (1 + K ^ 2) + 20

theorem offsetMass_nonneg (f : ℝ → ℂ) : 0 ≤ offsetMass f :=
  integral_nonneg (fun s => sq_nonneg ‖f s‖)

theorem offsetMeasure_mass (f : ℝ → ℂ)
    (hf : IntegrableOn (fun s : ℝ => ‖f s‖ ^ 2) (Ioi 0)) :
    offsetMeasure f univ = ENNReal.ofReal (offsetMass f) := by
  rw [offsetMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall (fun s => sq_nonneg ‖f s‖))).symm

theorem offsetMeasure_tail (f : ℝ → ℂ)
    (hf : IntegrableOn (fun s : ℝ => ‖f s‖ ^ 2) (Ioi 0)) {s : ℝ} (hs : 0 ≤ s) :
    offsetMeasure f (Ioi s) = ENNReal.ofReal (∫ u : ℝ in Ioi s, ‖f u‖ ^ 2) := by
  have hsub : Ioi s ⊆ Ioi (0 : ℝ) := fun u hu => lt_of_le_of_lt hs hu
  rw [offsetMeasure, withDensity_apply _ measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, inter_eq_left.mpr hsub]
  exact (ofReal_integral_eq_lintegral_ofReal (hf.mono_set hsub)
    (Eventually.of_forall (fun u => sq_nonneg ‖f u‖))).symm

theorem offsetMeasure_nonnegative (f : ℝ → ℂ) : ∀ᵐ s ∂offsetMeasure f, 0 ≤ s := by
  have h : ∀ᵐ s : ℝ ∂volume.restrict (Ioi 0), 0 ≤ s :=
    (ae_restrict_mem measurableSet_Ioi).mono (fun _ hs => le_of_lt hs)
  exact h.filter_mono (withDensity_absolutelyContinuous _ _).ae_le

theorem integral_offsetMeasure (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (g : ℝ → ℝ) :
    (∫ s : ℝ, g s ∂offsetMeasure f) = ∫ s : ℝ in Ioi 0, g s * ‖f s‖ ^ 2 := by
  have h := integral_withDensity_eq_integral_toReal_smul₀
    (hf.norm.pow 2).aemeasurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) g
  simpa only [offsetMeasure, IntegrableOn, Pi.pow_apply, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul, mul_comm] using h

theorem integrable_offsetMeasure_iff (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (g : ℝ → ℝ) :
    Integrable g (offsetMeasure f) ↔
      IntegrableOn (fun s : ℝ => g s * ‖f s‖ ^ 2) (Ioi 0) := by
  have h := integrable_withDensity_iff_integrable_smul₀'
    (hf.norm.pow 2).aemeasurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (g := g)
  simpa only [offsetMeasure, IntegrableOn, Pi.pow_apply, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul, mul_comm] using h

/-- Ordinary density version needed by the theta tails.
Zero total mass is allowed. -/
theorem offset_weighted_sq_integrable_bound (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf₂ : IntegrableOn (fun s : ℝ => ‖f s‖ ^ 2) (Ioi 0))
    {K T τ : ℝ} (hK : 0 ≤ K) (hT : 4 ≤ T) (hTτ : 2 ≤ T * τ) (hτone : τ ≤ 1)
    (htail : ∀ s : ℝ, K * τ ≤ s →
      (∫ u : ℝ in Ioi s, ‖f u‖ ^ 2) ≤ offsetMass f * Real.exp (-((T / 2) * s))) :
    IntegrableOn (fun s : ℝ => offsetWeight τ s * ‖f s‖ ^ 2) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, offsetWeight τ s * ‖f s‖ ^ 2) ≤
        offsetMass f * momentConstant K := by
  have hτ : 0 < τ := by nlinarith
  have htail' : ∀ s : ℝ, K * τ ≤ s → offsetMeasure f (Ioi s) ≤
      ENNReal.ofReal (offsetMass f * Real.exp (-((T / 2) * s))) := by
    intro s hs
    rw [offsetMeasure_tail f hf₂ ((mul_nonneg hK hτ.le).trans hs)]
    exact ENNReal.ofReal_le_ofReal (htail s hs)
  obtain ⟨hi, hb⟩ := weighted_moment_of_survival (offsetMeasure f) (offsetMass_nonneg f)
    hK hT hTτ hτone (offsetMeasure_mass f hf₂) (offsetMeasure_nonnegative f) htail'
  refine ⟨(integrable_offsetMeasure_iff f hf _).mp hi, ?_⟩
  simpa only [integral_offsetMeasure f hf, momentConstant] using hb


/-- Weighted Cauchy–Schwarz gives both L¹ membership and the squared bound. -/
theorem weighted_cauchy_schwarz (μ : Measure ℝ) (f w : ℝ → ℝ)
    (hf : AEStronglyMeasurable f μ) (hfn : ∀ᵐ s ∂μ, 0 ≤ f s)
    (hw : Continuous w) (hwp : ∀ s : ℝ, 0 < w s)
    (hwi : Integrable (fun s => (w s)⁻¹) μ)
    (hfwi : Integrable (fun s => w s * (f s) ^ 2) μ) :
    Integrable f μ ∧ (∫ s : ℝ, f s ∂μ) ^ 2 ≤
      (∫ s : ℝ, w s * (f s) ^ 2 ∂μ) * (∫ s : ℝ, (w s)⁻¹ ∂μ) := by
  let U : ℝ → ℝ := fun s => Real.sqrt (w s) * f s
  let V : ℝ → ℝ := fun s => (Real.sqrt (w s))⁻¹
  have hUm : AEStronglyMeasurable U μ := hw.sqrt.aestronglyMeasurable.mul hf
  have hVm : AEStronglyMeasurable V μ :=
    (hw.sqrt.inv₀ (fun s => (Real.sqrt_pos.mpr (hwp s)).ne')).aestronglyMeasurable
  have hU₂ : ∀ s : ℝ, U s ^ 2 = w s * (f s) ^ 2 := by
    intro s
    dsimp [U]
    rw [mul_pow, Real.sq_sqrt (hwp s).le]
  have hV₂ : ∀ s : ℝ, V s ^ 2 = (w s)⁻¹ := by
    intro s
    dsimp [V]
    rw [inv_pow, Real.sq_sqrt (hwp s).le]
  have hUV : ∀ s : ℝ, U s * V s = f s := by
    intro s
    dsimp [U, V]
    field_simp [(Real.sqrt_pos.mpr (hwp s)).ne']
  have hU : MemLp U 2 μ := (memLp_two_iff_integrable_sq hUm).mpr (by simpa only [hU₂] using hfwi)
  have hV : MemLp V 2 μ := (memLp_two_iff_integrable_sq hVm).mpr (by simpa only [hV₂] using hwi)
  have hfi : Integrable f μ := by
    apply (hU.integrable_mul hV).congr
    filter_upwards with s
    exact hUV s
  have hUn : ∀ᵐ s ∂μ, 0 ≤ U s := hfn.mono (fun s hs => mul_nonneg (Real.sqrt_nonneg _) hs)
  have hVn : ∀ᵐ s ∂μ, 0 ≤ V s := Eventually.of_forall (fun s => inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hhold : Real.HolderConjugate 2 2 := by norm_num [Real.holderConjugate_iff]
  have hc := integral_mul_le_Lp_mul_Lq_of_nonneg hhold hUn hVn
    (by simpa using hU) (by simpa using hV)
  norm_num only [Real.rpow_two, show (1 : ℝ) / 2 = (1 / 2 : ℝ) from rfl,
    ← Real.sqrt_eq_rpow, hUV, hU₂, hV₂] at hc
  have hA : 0 ≤ ∫ s : ℝ, w s * (f s) ^ 2 ∂μ :=
    integral_nonneg (fun s => mul_nonneg (hwp s).le (sq_nonneg _))
  have hB : 0 ≤ ∫ s : ℝ, (w s)⁻¹ ∂μ := integral_nonneg (fun s => (inv_pos.mpr (hwp s)).le)
  have hsq := mul_self_le_mul_self (integral_nonneg_of_ae hfn) hc
  refine ⟨hfi, ?_⟩
  nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB]

theorem inverse_quadratic_weight_integrable {τ : ℝ} (hτ : 0 < τ) :
    IntegrableOn (fun s : ℝ => (1 + s ^ 2 / τ ^ 2)⁻¹) (Ioi 0) := by
  simpa only [div_pow] using (integrable_inv_one_add_sq.comp_div hτ.ne').integrableOn

theorem inverse_quadratic_weight_integral {τ : ℝ} (hτ : 0 < τ) :
    (∫ s : ℝ in Ioi 0, (1 + s ^ 2 / τ ^ 2)⁻¹) = Real.pi * τ / 2 := by
  have h := integral_comp_mul_left_Ioi (fun s : ℝ => (1 + s ^ 2)⁻¹) 0 (inv_pos.mpr hτ)
  simpa [mul_pow, div_eq_mul_inv, mul_comm, mul_assoc] using h

/-- The edge weighted L¹ bound used in the prime and pole estimates. -/
theorem offset_weighted_l1_bound (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf₂ : IntegrableOn (fun s : ℝ => ‖f s‖ ^ 2) (Ioi 0))
    {K T τ : ℝ} (hK : 0 ≤ K) (hT : 4 ≤ T) (hTτ : 2 ≤ T * τ) (hτone : τ ≤ 1)
    (htail : ∀ s : ℝ, K * τ ≤ s →
      (∫ u : ℝ in Ioi s, ‖f u‖ ^ 2) ≤ offsetMass f * Real.exp (-((T / 2) * s))) :
    IntegrableOn (fun s : ℝ => Real.exp (s / 2) * ‖f s‖) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, Real.exp (s / 2) * ‖f s‖) ^ 2 ≤
        (Real.pi / 2 * momentConstant K) * τ * offsetMass f := by
  have hτ : 0 < τ := by nlinarith
  obtain ⟨hwi, hwb⟩ := offset_weighted_sq_integrable_bound f hf hf₂ hK hT hTτ hτone htail
  have he (s : ℝ) : (Real.exp (s / 2) * ‖f s‖) ^ 2 = Real.exp s * ‖f s‖ ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  have hident (s : ℝ) : (1 + s ^ 2 / τ ^ 2) * (Real.exp (s / 2) * ‖f s‖) ^ 2 =
      offsetWeight τ s * ‖f s‖ ^ 2 := by rw [he]; unfold offsetWeight; ring
  have hwi' : IntegrableOn
      (fun s : ℝ => (1 + s ^ 2 / τ ^ 2) * (Real.exp (s / 2) * ‖f s‖) ^ 2) (Ioi 0) := by
    simpa only [hident] using hwi
  obtain ⟨hi, hb⟩ := weighted_cauchy_schwarz (volume.restrict (Ioi 0))
    (fun s => Real.exp (s / 2) * ‖f s‖) (fun s => 1 + s ^ 2 / τ ^ 2)
    ((by fun_prop : Continuous (fun s : ℝ => Real.exp (s / 2))).aestronglyMeasurable.mul hf.norm)
    (Eventually.of_forall (fun s => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)))
    (by fun_prop) (fun s => by positivity)
    (inverse_quadratic_weight_integrable hτ) hwi'
  refine ⟨hi, ?_⟩
  simp_rw [hident] at hb
  rw [inverse_quadratic_weight_integral hτ] at hb
  calc
    _ ≤ (∫ s : ℝ in Ioi 0, offsetWeight τ s * ‖f s‖ ^ 2) * (Real.pi * τ / 2) := hb
    _ ≤ (offsetMass f * momentConstant K) * (Real.pi * τ / 2) :=
      mul_le_mul_of_nonneg_right hwb (by positivity)
    _ = _ := by ring


/-- The same scale controls ordinary edge L¹. -/
theorem offset_l1_bound (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf₂ : IntegrableOn (fun s : ℝ => ‖f s‖ ^ 2) (Ioi 0))
    {K T τ : ℝ} (hK : 0 ≤ K) (hT : 4 ≤ T) (hTτ : 2 ≤ T * τ) (hτone : τ ≤ 1)
    (htail : ∀ s : ℝ, K * τ ≤ s →
      (∫ u : ℝ in Ioi s, ‖f u‖ ^ 2) ≤ offsetMass f * Real.exp (-((T / 2) * s))) :
    IntegrableOn (fun s : ℝ => ‖f s‖) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, ‖f s‖) ^ 2 ≤
        (Real.pi / 2 * momentConstant K) * τ * offsetMass f := by
  obtain ⟨hwi, hwb⟩ := offset_weighted_l1_bound f hf hf₂ hK hT hTτ hτone htail
  have hle : ∀ᵐ s : ℝ ∂volume.restrict (Ioi 0),
      ‖f s‖ ≤ Real.exp (s / 2) * ‖f s‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by
      have hs' : 0 < s := hs
      linarith))
  have hi : IntegrableOn (fun s : ℝ => ‖f s‖) (Ioi 0) := by
    apply hwi.mono' hf.norm
    simpa only [norm_norm] using hle
  have hib := integral_mono_ae hi hwi hle
  refine ⟨hi, ?_⟩
  have hnonneg : 0 ≤ ∫ s : ℝ in Ioi 0, ‖f s‖ := integral_nonneg (fun s => norm_nonneg _)
  nlinarith

/-- Ordinary first and second offset moments at the stated scales. -/
theorem offset_first_second_moments (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf₂ : IntegrableOn (fun s : ℝ => ‖f s‖ ^ 2) (Ioi 0))
    {K T τ : ℝ} (hK : 0 ≤ K) (hT : 4 ≤ T) (hTτ : 2 ≤ T * τ)
    (htail : ∀ s : ℝ, K * τ ≤ s →
      (∫ u : ℝ in Ioi s, ‖f u‖ ^ 2) ≤ offsetMass f * Real.exp (-((T / 2) * s))) :
    IntegrableOn (fun s : ℝ => s * ‖f s‖ ^ 2) (Ioi 0) ∧
    IntegrableOn (fun s : ℝ => s ^ 2 * ‖f s‖ ^ 2) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, s * ‖f s‖ ^ 2) ≤ ((K + 1) * τ) * offsetMass f ∧
      (∫ s : ℝ in Ioi 0, s ^ 2 * ‖f s‖ ^ 2) ≤ ((K ^ 2 + 2) * τ ^ 2) * offsetMass f := by
  have hτ : 0 < τ := by nlinarith
  have hr : 0 < T / 2 := by linarith
  have hA := offsetMass_nonneg f
  have htail' : ∀ s : ℝ, K * τ ≤ s → offsetMeasure f (Ioi s) ≤
      ENNReal.ofReal (offsetMass f * Real.exp (-((T / 2) * s))) := by
    intro s hs
    rw [offsetMeasure_tail f hf₂ ((mul_nonneg hK hτ.le).trans hs)]
    exact ENNReal.ofReal_le_ofReal (htail s hs)
  obtain ⟨hi1, hb1⟩ := first_moment_of_survival (offsetMeasure f) hA (mul_nonneg hK hτ.le) hr
    (offsetMeasure_mass f hf₂) (offsetMeasure_nonnegative f) htail'
  obtain ⟨hi2, hb2⟩ := second_moment_of_survival (offsetMeasure f) hA (mul_nonneg hK hτ.le) hr
    (offsetMeasure_mass f hf₂) (offsetMeasure_nonnegative f) htail'
  have hinv : 1 / (T / 2) ≤ τ := (div_le_iff₀ hr).mpr (by nlinarith)
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ 1 / (T / 2)) hinv
  have hp1 : K * τ + 1 / (T / 2) ≤ (K + 1) * τ := by nlinarith
  have hp2 : (K * τ) ^ 2 + 2 / (T / 2) ^ 2 ≤ (K ^ 2 + 2) * τ ^ 2 := by
    calc
      _ = K ^ 2 * τ ^ 2 + 2 * (1 / (T / 2)) ^ 2 := by ring
      _ ≤ _ := by nlinarith
  refine ⟨(integrable_offsetMeasure_iff f hf _).mp hi1,
    (integrable_offsetMeasure_iff f hf _).mp hi2, ?_, ?_⟩
  · rw [integral_offsetMeasure f hf] at hb1
    exact hb1.trans (by nlinarith [mul_le_mul_of_nonneg_left hp1 hA])
  · rw [integral_offsetMeasure f hf] at hb2
    exact hb2.trans (by nlinarith [mul_le_mul_of_nonneg_left hp2 hA])

end ThetaTrial.Paper.ThetaDerivTailMoments
