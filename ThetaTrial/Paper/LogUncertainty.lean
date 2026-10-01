import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

/-!
# The logarithmic bathtub inequality

The density argument and the Fourier inequality of Lemma
`deriv:log-uncertainty`. The final theorem allows an infinite positive
logarithmic moment: the positive part is an `ENNReal` integral and the
negative part is shown to be finite.

The ordinary Fourier integral is identified with the `L2` Fourier transform
using tempered distributions, so the results hold for all nonzero
`L1 ∩ L2` functions, including discontinuous ones.
-/

noncomputable section

open MeasureTheory Set
open scoped FourierTransform SchwartzMap ContDiff

namespace ThetaTrial.Paper.LogUncertainty

/-- The unit-mass uniform comparison density on `[-R,R]`. -/
def uniformDensity (R : ℝ) (x : ℝ) : ℝ :=
  (Icc (-R) R).indicator (fun _ => (2 * R)⁻¹) x

lemma uniformDensity_integrable (R : ℝ) : Integrable (uniformDensity R) := by
  exact (integrable_indicator_iff measurableSet_Icc).mpr
    (integrableOn_const (μ := volume) (s := Icc (-R) R)
      (C := (2 * R)⁻¹) isCompact_Icc.measure_lt_top.ne)

lemma integral_uniformDensity {R : ℝ} (hR : 0 < R) :
    (∫ x : ℝ, uniformDensity R x) = 1 := by
  unfold uniformDensity
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -R ≤ R),
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  field_simp
  ring

lemma log_uniformDensity_integrable (R : ℝ) :
    Integrable (fun x : ℝ => Real.log |x| * uniformDensity R x) := by
  have hlog : IntegrableOn Real.log (Icc (-R) R) :=
    (integrableOn_Icc_iff_integrableOn_Ioc (μ := volume) (f := Real.log)).mpr
      (intervalIntegral.intervalIntegrable_log' (a := -R) (b := R)).1
  have hi : Integrable ((Icc (-R) R).indicator
      (fun x : ℝ => Real.log x * (2 * R)⁻¹)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (hlog.mul_const ((2 * R)⁻¹))
  apply hi.congr
  filter_upwards [] with x
  by_cases hx : x ∈ Icc (-R) R <;> simp [uniformDensity, hx, Real.log_abs]

lemma integral_log_uniformDensity {R : ℝ} (hR : 0 < R) :
    (∫ x : ℝ, Real.log |x| * uniformDensity R x) = Real.log R - 1 := by
  have heq : (fun x : ℝ => Real.log |x| * uniformDensity R x) =
      (Icc (-R) R).indicator (fun x => Real.log x * (2 * R)⁻¹) := by
    ext x
    by_cases hx : x ∈ Icc (-R) R <;> simp [uniformDensity, hx, Real.log_abs]
  rw [heq, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -R ≤ R),
    intervalIntegral.integral_mul_const, integral_log, Real.log_neg_eq_log]
  field_simp
  ring

/-- The logarithmic bathtub comparison, outside the irrelevant origin. -/
lemma log_bathtub_pointwise {R x p : ℝ} (hR : 0 < R) (hx : x ≠ 0)
    (hp : 0 ≤ p) (hcap : p ≤ (2 * R)⁻¹) :
    (Real.log |x| - Real.log R) * uniformDensity R x ≤
      (Real.log |x| - Real.log R) * p := by
  by_cases hin : x ∈ Icc (-R) R
  · have hxR : |x| ≤ R := abs_le.mpr ⟨hin.1, hin.2⟩
    have hl : Real.log |x| - Real.log R ≤ 0 :=
      sub_nonpos.mpr (Real.log_le_log (abs_pos.mpr hx) hxR)
    simpa [uniformDensity, hin] using mul_le_mul_of_nonpos_left hcap hl
  · have hxR : R ≤ |x| := le_of_lt (lt_of_not_ge (fun h =>
      hin (abs_le.mp h)))
    have hl : 0 ≤ Real.log |x| - Real.log R :=
      sub_nonneg.mpr (Real.log_le_log hR hxR)
    simpa [uniformDensity, hin] using mul_nonneg hl hp

/-- A nonnegative unit-mass density bounded by `1/(2R)` has logarithmic
moment at least `log R - 1`. -/
theorem log_moment_ge {R : ℝ} (hR : 0 < R) {p : ℝ → ℝ}
    (hp : Integrable p)
    (hlogp : Integrable (fun x : ℝ => Real.log |x| * p x))
    (hnonneg : ∀ᵐ x, 0 ≤ p x)
    (hcap : ∀ᵐ x, p x ≤ (2 * R)⁻¹)
    (hmass : (∫ x : ℝ, p x) = 1) :
    Real.log R - 1 ≤ ∫ x : ℝ, Real.log |x| * p x := by
  have hu := uniformDensity_integrable R
  have hlu := log_uniformDensity_integrable R
  have hu' : Integrable (fun x : ℝ =>
      (Real.log |x| - Real.log R) * uniformDensity R x) := by
    apply (hlu.sub (hu.const_mul (Real.log R))).congr
    filter_upwards [] with x
    change Real.log |x| * uniformDensity R x - Real.log R * uniformDensity R x = _
    ring
  have hp' : Integrable (fun x : ℝ => (Real.log |x| - Real.log R) * p x) := by
    apply (hlogp.sub (hp.const_mul (Real.log R))).congr
    filter_upwards [] with x
    change Real.log |x| * p x - Real.log R * p x = _
    ring
  have hcomparison := integral_mono_ae hu' hp' (by
    filter_upwards [hnonneg, hcap, volume.ae_ne (0 : ℝ)] with x hx0 hxc hx
    exact log_bathtub_pointwise hR hx hx0 hxc)
  simp only [sub_mul] at hcomparison
  rw [integral_sub hlu (hu.const_mul (Real.log R)),
    integral_sub hlogp (hp.const_mul (Real.log R)),
    integral_const_mul, integral_const_mul,
    integral_log_uniformDensity hR, integral_uniformDensity hR, hmass] at hcomparison
  linarith

/-- The unnormalized version: a nonnegative density of mass `A`, bounded
by `B`, has the exact lower bound with radius `A/(2B)`. -/
theorem log_moment_ge_of_mass_cap {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    {v : ℝ → ℝ} (hv : Integrable v)
    (hlogv : Integrable (fun x : ℝ => Real.log |x| * v x))
    (hnonneg : ∀ᵐ x, 0 ≤ v x) (hcap : ∀ᵐ x, v x ≤ B)
    (hmass : (∫ x : ℝ, v x) = A) :
    (Real.log (A / (2 * B)) - 1) * A ≤
      ∫ x : ℝ, Real.log |x| * v x := by
  let p : ℝ → ℝ := fun x => v x / A
  have hp : Integrable p := hv.div_const A
  have hlogp : Integrable (fun x : ℝ => Real.log |x| * p x) := by
    simpa only [p, mul_div_assoc] using hlogv.div_const A
  have hp0 : ∀ᵐ x, 0 ≤ p x := by
    filter_upwards [hnonneg] with x hx
    exact div_nonneg hx hA.le
  have hpcap : ∀ᵐ x, p x ≤ (2 * (A / (2 * B)))⁻¹ := by
    filter_upwards [hcap] with x hx
    have heq : (2 * (A / (2 * B)))⁻¹ = B / A := by
      field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right hx hA.le
  have hpmass : (∫ x : ℝ, p x) = 1 := by
    simp [p, integral_div, hmass, hA.ne']
  have h := log_moment_ge (by positivity : 0 < A / (2 * B))
    hp hlogp hp0 hpcap hpmass
  simp only [p, ← mul_div_assoc, integral_div] at h
  exact (le_div_iff₀ hA).mp h

/-- The ordinary Fourier transform with the paper's `exp(-i*r*u)`
normalization, obtained from mathlib's `exp(-2*pi*i*x*u)` normalization. -/
def paperFourier (f : ℝ → ℂ) (r : ℝ) : ℂ := 𝓕 f (r / (2 * Real.pi))

lemma paperFourier_eq_integral (f : ℝ → ℂ) (r : ℝ) :
    paperFourier f r = ∫ u : ℝ, f u *
      Complex.exp (-Complex.I * (r : ℂ) * (u : ℂ)) := by
  rw [paperFourier, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
  have he : ((-2 * Real.pi * (r / (2 * Real.pi) * u) : ℝ) : ℂ) *
      Complex.I = -Complex.I * (r : ℂ) * (u : ℂ) := by
    push_cast
    field_simp
  rw [he]
  ring

lemma paperFourier_norm_le (f : ℝ → ℂ) (r : ℝ) :
    ‖paperFourier f r‖ ≤ ∫ u : ℝ, ‖f u‖ := by
  simpa only [paperFourier] using!
    VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar (volume : Measure ℝ) (innerₗ ℝ) f (r / (2 * Real.pi))

/-- The L1 Fourier Fubini identity. -/
lemma integral_fourier_mul {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∫ x : ℝ, 𝓕 f x * g x) = ∫ x : ℝ, f x * 𝓕 g x := by
  simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner hf hg

/-- For an L1 and L2 function, the ordinary Fourier integral agrees almost
everywhere with the `L2` Fourier transform. The proof compares both with
smooth compactly supported test functions. -/
theorem ordinary_fourier_ae_L2 {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    𝓕 f =ᵐ[volume] (𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) := by
  let F : Lp ℂ 2 (volume : Measure ℝ) := hf2.toLp f
  have hc : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner hf
  apply ae_eq_of_integral_contDiff_smul_eq (μ := volume) hc.locallyIntegrable
    ((Lp.memLp (𝓕 F)).locallyIntegrable (by norm_num))
  intro g hg hgc
  have hgs : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hgd : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let G : 𝓢(ℝ, ℂ) := hgs.toSchwartzMap hgd
  have hdist := congrArg (fun T : TemperedDistribution ℝ ℂ => T G)
    (Lp.fourier_toTemperedDistribution_eq F)
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
    smul_eq_mul] at hdist
  have heq : (∫ x : ℝ, (𝓕 G) x * F x) = ∫ x : ℝ, (𝓕 G) x * f x := by
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp] with x hx
    change (𝓕 G) x * (hf2.toLp f) x = _
    rw [hx]
  calc
    (∫ x : ℝ, g x • 𝓕 f x) = ∫ x : ℝ, 𝓕 f x * G x := by
      congr 1
      funext x
      simp [G, Complex.real_smul, mul_comm]
    _ = ∫ x : ℝ, f x * 𝓕 G x := integral_fourier_mul hf G.integrable
    _ = ∫ x : ℝ, 𝓕 G x * F x := by simpa only [mul_comm] using heq.symm
    _ = ∫ x : ℝ, G x * (𝓕 F) x := hdist
    _ = ∫ x : ℝ, g x • (𝓕 F) x := by rfl
    _ = _ := by rfl

theorem ordinary_fourier_memLp {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    MemLp (𝓕 f) 2 := by
  exact (memLp_congr_ae (ordinary_fourier_ae_L2 hf hf2)).mpr
    (Lp.memLp (𝓕 (hf2.toLp f)))

/-- Plancherel for the ordinary Fourier integral, under exactly L1 and L2
membership, obtained through the proved almost-everywhere identification. -/
theorem ordinary_fourier_plancherel {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    (∫ x : ℝ, ‖𝓕 f x‖ ^ 2) = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  let F : Lp ℂ 2 (volume : Measure ℝ) := hf2.toLp f
  have hi := Lp.inner_fourier_eq F F
  simp only [L2.inner_def] at hi
  have hi' : (∫ x : ℝ, ‖(𝓕 F) x‖ ^ 2) = ∫ x : ℝ, ‖F x‖ ^ 2 := by
    apply Complex.ofRealLI.injective
    simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using hi
  calc
    (∫ x : ℝ, ‖𝓕 f x‖ ^ 2) = ∫ x : ℝ, ‖(𝓕 F) x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ordinary_fourier_ae_L2 hf hf2] with x hx
      rw [hx]
    _ = ∫ x : ℝ, ‖F x‖ ^ 2 := hi'
    _ = ∫ x : ℝ, ‖f x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hf2.coeFn_toLp] with x hx
      change ‖(hf2.toLp f) x‖ ^ 2 = _
      rw [hx]

lemma paperFourier_mass {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    (∫ r : ℝ, ‖paperFourier f r‖ ^ 2) =
      (2 * Real.pi) * ∫ u : ℝ, ‖f u‖ ^ 2 := by
  have hs := Measure.integral_comp_div (fun x : ℝ => ‖𝓕 f x‖ ^ 2) (2 * Real.pi)
  simpa only [paperFourier, ordinary_fourier_plancherel hf hf2,
    abs_of_pos (by positivity : 0 < 2 * Real.pi), smul_eq_mul] using! hs

/-- The Fourier inequality of the paper for nonzero L1 and L2 functions,
under a finite logarithmic moment. -/
theorem fourier_log_uncertainty {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2)
    (hL : 0 < ∫ u : ℝ, ‖f u‖)
    (hA : 0 < ∫ u : ℝ, ‖f u‖ ^ 2)
    (hlog : Integrable (fun r : ℝ => Real.log |r| * ‖paperFourier f r‖ ^ 2)) :
    (Real.log (Real.pi * (∫ u : ℝ, ‖f u‖ ^ 2) /
        (∫ u : ℝ, ‖f u‖) ^ 2) - 1) * (∫ u : ℝ, ‖f u‖ ^ 2) ≤
      (1 / (2 * Real.pi)) * ∫ r : ℝ, Real.log |r| * ‖paperFourier f r‖ ^ 2 := by
  let A : ℝ := ∫ u : ℝ, ‖f u‖ ^ 2
  let L : ℝ := ∫ u : ℝ, ‖f u‖
  have htwo : 0 < 2 * Real.pi := by positivity
  have hv : Integrable (fun r : ℝ => ‖paperFourier f r‖ ^ 2) := by
    exact ((ordinary_fourier_memLp hf hf2).integrable_norm_pow
      (by norm_num : (2 : ℕ) ≠ 0)).comp_div htwo.ne'
  have hcap : ∀ᵐ r : ℝ, ‖paperFourier f r‖ ^ 2 ≤ L ^ 2 := by
    filter_upwards [] with r
    exact sq_le_sq₀ (norm_nonneg _) hL.le |>.mpr (paperFourier_norm_le f r)
  have h := log_moment_ge_of_mass_cap (mul_pos htwo hA) (sq_pos_of_pos hL)
    hv hlog (ae_of_all _ (fun r => sq_nonneg ‖paperFourier f r‖)) hcap
    (paperFourier_mass hf hf2)
  have heq : (2 * Real.pi * A) / (2 * L ^ 2) = Real.pi * A / L ^ 2 := by ring
  change (Real.log ((2 * Real.pi * A) / (2 * L ^ 2)) - 1) *
    (2 * Real.pi * A) ≤ _ at h
  rw [heq] at h
  have hfinal : (Real.log (Real.pi * A / L ^ 2) - 1) * A ≤
      (∫ r : ℝ, Real.log |r| * ‖paperFourier f r‖ ^ 2) / (2 * Real.pi) := by
    apply (le_div_iff₀ htwo).mpr
    nlinarith [h]
  simpa only [A, L, div_eq_mul_inv, one_mul, mul_comm] using hfinal

/-- The same inequality, assuming only that `f` is nonzero in `Lp`. -/
theorem fourier_log_uncertainty_of_ne_zero {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2)
    (hne : ¬ f =ᵐ[volume] 0)
    (hlog : Integrable (fun r : ℝ => Real.log |r| * ‖paperFourier f r‖ ^ 2)) :
    (Real.log (Real.pi * (∫ u : ℝ, ‖f u‖ ^ 2) /
        (∫ u : ℝ, ‖f u‖) ^ 2) - 1) * (∫ u : ℝ, ‖f u‖ ^ 2) ≤
      (1 / (2 * Real.pi)) * ∫ r : ℝ, Real.log |r| * ‖paperFourier f r‖ ^ 2 := by
  have hL : 0 < ∫ u : ℝ, ‖f u‖ := by
    by_contra h
    have hz : (∫ u : ℝ, ‖f u‖) = 0 :=
      le_antisymm (le_of_not_gt h) (integral_nonneg (fun u => norm_nonneg (f u)))
    have hzae := (integral_eq_zero_iff_of_nonneg
      (fun u => norm_nonneg (f u)) hf.norm).mp hz
    apply hne
    filter_upwards [hzae] with x hx
    exact norm_eq_zero.mp hx
  have hA : 0 < ∫ u : ℝ, ‖f u‖ ^ 2 := by
    by_contra h
    have hz : (∫ u : ℝ, ‖f u‖ ^ 2) = 0 :=
      le_antisymm (le_of_not_gt h) (integral_nonneg (fun u => sq_nonneg ‖f u‖))
    have hzae := (integral_eq_zero_iff_of_nonneg
      (fun u => sq_nonneg ‖f u‖)
      (hf2.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))).mp hz
    apply hne
    filter_upwards [hzae] with x hx
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)
  exact fourier_log_uncertainty hf hf2 hL hA hlog

/-- Plancherel with all normalization factors, for Schwartz inputs. -/
lemma schwartz_paperFourier_mass (f : 𝓢(ℝ, ℂ)) :
    (∫ r : ℝ, ‖paperFourier f r‖ ^ 2) =
      (2 * Real.pi) * ∫ u : ℝ, ‖f u‖ ^ 2 := by
  change (∫ r : ℝ, (fun x : ℝ => ‖𝓕 f x‖ ^ 2) (r / (2 * Real.pi))) = _
  have hs := Measure.integral_comp_div (fun x : ℝ => ‖𝓕 f x‖ ^ 2) (2 * Real.pi)
  simpa only [SchwartzMap.integral_norm_sq_fourier,
    abs_of_pos (by positivity : 0 < 2 * Real.pi), smul_eq_mul] using! hs

/-- The special case of Schwartz functions; the general `L1 ∩ L2` case is
`fourier_log_uncertainty`. -/
theorem schwartz_fourier_log_uncertainty (f : 𝓢(ℝ, ℂ))
    (hL : 0 < ∫ u : ℝ, ‖f u‖)
    (hA : 0 < ∫ u : ℝ, ‖f u‖ ^ 2)
    (hlog : Integrable (fun r : ℝ => Real.log |r| * ‖paperFourier f r‖ ^ 2)) :
    (Real.log (Real.pi * (∫ u : ℝ, ‖f u‖ ^ 2) /
        (∫ u : ℝ, ‖f u‖) ^ 2) - 1) * (∫ u : ℝ, ‖f u‖ ^ 2) ≤
      (1 / (2 * Real.pi)) * ∫ r : ℝ, Real.log |r| * ‖paperFourier f r‖ ^ 2 := by
  let A : ℝ := ∫ u : ℝ, ‖f u‖ ^ 2
  let L : ℝ := ∫ u : ℝ, ‖f u‖
  have htwo : 0 < 2 * Real.pi := by positivity
  have hv : Integrable (fun r : ℝ => ‖paperFourier f r‖ ^ 2) := by
    have hi := ((𝓕 f).memLp 2).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    exact hi.comp_div htwo.ne'
  have hcap : ∀ᵐ r : ℝ, ‖paperFourier f r‖ ^ 2 ≤ L ^ 2 := by
    filter_upwards [] with r
    exact sq_le_sq₀ (norm_nonneg _) hL.le |>.mpr (paperFourier_norm_le f r)
  have h := log_moment_ge_of_mass_cap (mul_pos htwo hA) (sq_pos_of_pos hL)
    hv hlog (ae_of_all _ (fun r => sq_nonneg ‖paperFourier f r‖)) hcap
    (schwartz_paperFourier_mass f)
  have heq : (2 * Real.pi * A) / (2 * L ^ 2) = Real.pi * A / L ^ 2 := by ring
  change (Real.log ((2 * Real.pi * A) / (2 * L ^ 2)) - 1) *
    (2 * Real.pi * A) ≤ _ at h
  rw [heq] at h
  have hfinal : (Real.log (Real.pi * A / L ^ 2) - 1) * A ≤
      (∫ r : ℝ, Real.log |r| * ‖paperFourier f r‖ ^ 2) / (2 * Real.pi) := by
    apply (le_div_iff₀ htwo).mpr
    nlinarith [h]
  simpa only [A, L, div_eq_mul_inv, one_mul, mul_comm] using hfinal

end ThetaTrial.Paper.LogUncertainty

#print axioms ThetaTrial.Paper.LogUncertainty.log_moment_ge
#print axioms ThetaTrial.Paper.LogUncertainty.log_moment_ge_of_mass_cap
#print axioms ThetaTrial.Paper.LogUncertainty.schwartz_fourier_log_uncertainty
#print axioms ThetaTrial.Paper.LogUncertainty.ordinary_fourier_plancherel
#print axioms ThetaTrial.Paper.LogUncertainty.fourier_log_uncertainty
#print axioms ThetaTrial.Paper.LogUncertainty.fourier_log_uncertainty_of_ne_zero

namespace ThetaTrial.Paper.LogUncertainty

/-- Nonnegative positive logarithmic weight. -/
def positiveLogWeight (r : ℝ) : ℝ := max (Real.log |r|) 0

/-- Nonnegative negative logarithmic weight, supported on `[-1,1]`. -/
def negativeLogWeight (r : ℝ) : ℝ := max (-Real.log |r|) 0

lemma log_weight_split (r : ℝ) :
    positiveLogWeight r - negativeLogWeight r = Real.log |r| := by
  unfold positiveLogWeight negativeLogWeight
  by_cases h : 0 ≤ Real.log |r|
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    ring
  · have hn : Real.log |r| ≤ 0 := le_of_lt (lt_of_not_ge h)
    rw [max_eq_right hn, max_eq_left (neg_nonneg.mpr hn)]
    ring

lemma negativeLogWeight_integrable : Integrable negativeLogWeight := by
  apply ((log_uniformDensity_integrable 1).const_mul (-2)).congr
  filter_upwards [] with r
  by_cases hr : r ∈ Icc (-1 : ℝ) 1
  · have hlog : Real.log |r| ≤ 0 := Real.log_nonpos (abs_nonneg r) (abs_le.mpr hr)
    simp only [negativeLogWeight, uniformDensity, Set.indicator_of_mem hr,
      max_eq_left (neg_nonneg.mpr hlog)]
    norm_num
    ring
  · have hlog : 0 ≤ Real.log |r| :=
      Real.log_nonneg (le_of_lt (lt_of_not_ge (fun h => hr (abs_le.mp h))))
    simp only [negativeLogWeight, uniformDensity, Set.indicator_of_notMem hr,
      mul_zero, max_eq_right (neg_nonpos.mpr hlog)]

lemma paperFourier_continuous {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (paperFourier f) := by
  have hc : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner hf
  exact hc.comp (continuous_id.div_const (2 * Real.pi))

lemma positiveLogDensity_measurable {f : ℝ → ℂ} (hf : Integrable f) :
    Measurable (fun r : ℝ => positiveLogWeight r * ‖paperFourier f r‖ ^ 2) := by
  have hc := paperFourier_continuous hf
  unfold positiveLogWeight
  fun_prop

lemma negativeLogDensity_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (fun r : ℝ => negativeLogWeight r * ‖paperFourier f r‖ ^ 2) := by
  have hc := paperFourier_continuous hf
  have hm : AEStronglyMeasurable
      (fun r : ℝ => negativeLogWeight r * ‖paperFourier f r‖ ^ 2) := by
    apply Measurable.aestronglyMeasurable
    unfold negativeLogWeight
    fun_prop
  apply (negativeLogWeight_integrable.mul_const ((∫ u : ℝ, ‖f u‖) ^ 2)).mono' hm
  filter_upwards [] with r
  have hw : 0 ≤ negativeLogWeight r := le_max_right _ _
  have hbound : ‖paperFourier f r‖ ^ 2 ≤ (∫ u : ℝ, ‖f u‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (integral_nonneg (fun u => norm_nonneg (f u)))).mpr
      (paperFourier_norm_le f r)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_left hbound hw

open scoped ENNReal

/-- The positive logarithmic moment, as an extended nonnegative integral. -/
def positiveLogMoment (f : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ r : ℝ, ENNReal.ofReal (positiveLogWeight r * ‖paperFourier f r‖ ^ 2)

/-- The negative logarithmic moment is always an ordinary finite integral
for L1 inputs, by `negativeLogDensity_integrable`. -/
def negativeLogMoment (f : ℝ → ℂ) : ℝ :=
  ∫ r : ℝ, negativeLogWeight r * ‖paperFourier f r‖ ^ 2

lemma signed_log_integrable_of_positiveLogMoment_ne_top {f : ℝ → ℂ}
    (hf : Integrable f) (hpfin : positiveLogMoment f ≠ ⊤) :
    Integrable (fun r : ℝ => Real.log |r| * ‖paperFourier f r‖ ^ 2) := by
  have hpos : ∀ᵐ r : ℝ, 0 ≤ positiveLogWeight r * ‖paperFourier f r‖ ^ 2 :=
    ae_of_all _ (fun r => mul_nonneg (le_max_right _ _) (sq_nonneg _))
  have hp : Integrable (fun r : ℝ => positiveLogWeight r * ‖paperFourier f r‖ ^ 2) :=
    (lintegral_ofReal_ne_top_iff_integrable
      (positiveLogDensity_measurable hf).aestronglyMeasurable hpos).mp hpfin
  apply (hp.sub (negativeLogDensity_integrable hf)).congr
  filter_upwards [] with r
  change positiveLogWeight r * ‖paperFourier f r‖ ^ 2 -
    negativeLogWeight r * ‖paperFourier f r‖ ^ 2 = _
  rw [← sub_mul, log_weight_split]

/-- The logarithmic uncertainty inequality, allowing an infinite positive
logarithmic moment: the extended moment `positive/(2*pi) - negative/(2*pi)` is
bounded below as in the paper, and its negative part is finite. -/
theorem fourier_log_uncertainty_extended {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2) (hne : ¬ f =ᵐ[volume] 0) :
    ENNReal.ofReal ((2 * Real.pi) *
      ((Real.log (Real.pi * (∫ u : ℝ, ‖f u‖ ^ 2) /
        (∫ u : ℝ, ‖f u‖) ^ 2) - 1) * (∫ u : ℝ, ‖f u‖ ^ 2)) +
      negativeLogMoment f) ≤ positiveLogMoment f := by
  by_cases htop : positiveLogMoment f = ⊤
  · simp [htop]
  have hpos : ∀ᵐ r : ℝ, 0 ≤ positiveLogWeight r * ‖paperFourier f r‖ ^ 2 :=
    ae_of_all _ (fun r => mul_nonneg (le_max_right _ _) (sq_nonneg _))
  have hp : Integrable (fun r : ℝ => positiveLogWeight r * ‖paperFourier f r‖ ^ 2) :=
    (lintegral_ofReal_ne_top_iff_integrable
      (positiveLogDensity_measurable hf).aestronglyMeasurable hpos).mp htop
  have hn := negativeLogDensity_integrable hf
  have hsplit : (∫ r : ℝ, Real.log |r| * ‖paperFourier f r‖ ^ 2) =
      (∫ r : ℝ, positiveLogWeight r * ‖paperFourier f r‖ ^ 2) - negativeLogMoment f := by
    have heq : (fun r : ℝ => Real.log |r| * ‖paperFourier f r‖ ^ 2) =
        fun r => positiveLogWeight r * ‖paperFourier f r‖ ^ 2 -
          negativeLogWeight r * ‖paperFourier f r‖ ^ 2 := by
      funext r
      rw [← sub_mul, log_weight_split]
    rw [heq, integral_sub hp hn]
    rfl
  have h := fourier_log_uncertainty_of_ne_zero hf hf2 hne
    (signed_log_integrable_of_positiveLogMoment_ne_top hf htop)
  have htwo : 0 < 2 * Real.pi := by positivity
  have hscaled := mul_le_mul_of_nonneg_left h htwo.le
  have hcancel : (2 * Real.pi) * ((1 / (2 * Real.pi)) *
      (∫ r : ℝ, Real.log |r| * ‖paperFourier f r‖ ^ 2)) =
      ∫ r : ℝ, Real.log |r| * ‖paperFourier f r‖ ^ 2 := by field_simp
  rw [hcancel, hsplit] at hscaled
  unfold positiveLogMoment
  rw [← ofReal_integral_eq_lintegral_ofReal hp hpos]
  apply ENNReal.ofReal_le_ofReal
  linarith

#print axioms negativeLogDensity_integrable
#print axioms fourier_log_uncertainty_extended

end ThetaTrial.Paper.LogUncertainty
