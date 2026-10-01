import ThetaTrial.Paper.FormDomain
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Analysis.Fourier.Convolution

/-! Smooth approximation in the logarithmic form norm. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology FourierTransform SchwartzMap ContDiff ENNReal NNReal Pointwise Convolution

namespace ThetaTrial.Paper.FormDomain

/-- Inward physical dilation, used before mollification to leave a support
margin at the two walls. -/
def inwardDilation (s : ℝ) (f : ℝ → ℂ) (u : ℝ) : ℂ := f (u / s)

theorem paperFourier_inwardDilation {s : ℝ} (hs : 0 < s) (f : ℝ → ℂ) (z : ℂ) :
    paperFourier (inwardDilation s f) z = (s : ℂ) * paperFourier f ((s : ℂ) * z) := by
  have h := Measure.integral_comp_div
    (fun u : ℝ => f u * Complex.exp (-Complex.I * ((s : ℂ) * z) * (u : ℂ))) s
  simp only [abs_of_pos hs, Complex.real_smul] at h
  unfold paperFourier inwardDilation
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with u
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have he : -Complex.I * ((s : ℂ) * z) * ((u / s : ℝ) : ℂ) =
      -Complex.I * z * (u : ℂ) := by
    push_cast
    field_simp [hsC]
  rw [he]

theorem inwardDilation_support {s a : ℝ} (hs : 0 < s) {f : ℝ → ℂ}
    (hf : Function.support f ⊆ Icc (-a) a) :
    Function.support (inwardDilation s f) ⊆ Icc (-(s * a)) (s * a) := by
  intro u hu
  have h : u / s ∈ Icc (-a) a := hf hu
  refine ⟨?_, ?_⟩
  · have hl := (le_div_iff₀ hs).mp h.1
    nlinarith
  · have hh := (div_le_iff₀ hs).mp h.2
    nlinarith

theorem InWindowFormDomain.inwardDilation_memLp {s a : ℝ} (hs : 0 < s) {f : ℝ → ℂ}
    (hf : ThetaTrial.Paper.InWindowFormDomain a f) :
    MemLp (inwardDilation s f) 2 volume := by
  have hi : Integrable (inwardDilation s f) := hf.integrable.comp_div hs.ne'
  apply (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mpr
  exact (hf.2.1.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).comp_div hs.ne'

lemma log_div_weight_le {s : ℝ} (hs : (1 : ℝ) / 2 ≤ s) (r : ℝ) :
    Real.log (2 + |r / s|) ≤ 2 * Real.log (2 + |r|) := by
  have hs0 : 0 < s := by linarith
  have hr : |r| / s ≤ 2 * |r| := by
    apply (div_le_iff₀ hs0).mpr
    nlinarith [abs_nonneg r]
  have ha : 2 + |r / s| ≤ 2 * (2 + |r|) := by
    rw [abs_div, abs_of_pos hs0]
    linarith
  have hl := Real.log_le_log (by positivity : 0 < 2 + |r / s|) ha
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : 2 + |r| ≠ 0)] at hl
  have h2 : Real.log 2 ≤ Real.log (2 + |r|) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg r])
  linarith

theorem InWindowFormDomain.inwardDilation {s a : ℝ} (hs : (1 : ℝ) / 2 ≤ s)
    {f : ℝ → ℂ} (hf : ThetaTrial.Paper.InWindowFormDomain a f) :
    ThetaTrial.Paper.InWindowFormDomain (s * a) (inwardDilation s f) := by
  have hs0 : 0 < s := by linarith
  refine ⟨inwardDilation_support hs0 hf.1, InWindowFormDomain.inwardDilation_memLp hs0 hf, ?_⟩
  have hc : Continuous (fun r : ℝ => Real.log (2 + |r / s|)) :=
    (continuous_const.add (continuous_id.div_const s).abs).log
      (fun r => ne_of_gt (by positivity : 0 < 2 + |r / s|))
  have hg : Integrable (fun r : ℝ => Real.log (2 + |r / s|) * ‖paperFourier f r‖ ^ 2) := by
    apply (hf.2.2.const_mul 2).mono'
      (hc.aestronglyMeasurable.mul hf.fourier_sq_integrable.aestronglyMeasurable)
    filter_upwards [] with r
    change ‖(Real.log (2 + |r / s|) * ‖paperFourier f r‖ ^ 2 : ℝ)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (logWindowWeight_pos (r / s)).le (sq_nonneg _))]
    have h := mul_le_mul_of_nonneg_right (log_div_weight_le hs r) (sq_nonneg ‖paperFourier f r‖)
    simpa only [mul_assoc] using h
  apply ((hg.const_mul (s ^ 2)).comp_mul_left' hs0.ne').congr
  filter_upwards [] with r
  rw [mul_div_cancel_left₀ r hs0.ne', paperFourier_inwardDilation hs0]
  simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
  push_cast
  ring

/-- The logarithmic Fourier density used in the graph norm. -/
def logDensity (f : ℝ → ℂ) (r : ℝ) : ℝ :=
  Real.log (2 + |r|) * ‖paperFourier f r‖ ^ 2

lemma logDensity_nonneg (f : ℝ → ℂ) (r : ℝ) : 0 ≤ logDensity f r :=
  mul_nonneg (logWindowWeight_pos r).le (sq_nonneg _)

lemma dilated_log_integrable {s a : ℝ} (hs : (1 : ℝ) / 2 ≤ s) {f : ℝ → ℂ}
    (hf : ThetaTrial.Paper.InWindowFormDomain a f) :
    Integrable (fun r : ℝ => Real.log (2 + |r / s|) * ‖paperFourier f r‖ ^ 2) := by
  have hc : Continuous (fun r : ℝ => Real.log (2 + |r / s|)) :=
    (continuous_const.add (continuous_id.div_const s).abs).log
      (fun r => ne_of_gt (by positivity : 0 < 2 + |r / s|))
  apply (hf.2.2.const_mul 2).mono'
    (hc.aestronglyMeasurable.mul hf.fourier_sq_integrable.aestronglyMeasurable)
  filter_upwards [] with r
  change ‖(Real.log (2 + |r / s|) * ‖paperFourier f r‖ ^ 2 : ℝ)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (logWindowWeight_pos (r / s)).le (sq_nonneg _))]
  exact (mul_le_mul_of_nonneg_right (log_div_weight_le hs r) (sq_nonneg _)).trans_eq (by ring)

/-- A dilation of ratio at least one half has logarithmic tails controlled
by the original tails at half the cutoff. -/
theorem inwardDilation_log_tail {s a R : ℝ} (hs : (1 : ℝ) / 2 ≤ s)
    (hs1 : s ≤ 1) (hR : 0 ≤ R) {f : ℝ → ℂ}
    (hf : ThetaTrial.Paper.InWindowFormDomain a f) :
    (∫ r : ℝ in {r | R ≤ |r|}, logDensity (inwardDilation s f) r) ≤
      2 * ∫ r : ℝ in {r | R / 2 ≤ |r|}, logDensity f r := by
  have hs0 : 0 < s := by linarith
  let g : ℝ → ℝ := fun r => Real.log (2 + |r / s|) * ‖paperFourier f r‖ ^ 2
  have hg : Integrable g := dilated_log_integrable hs hf
  have he (r : ℝ) : logDensity (inwardDilation s f) r = s ^ 2 * g (s * r) := by
    dsimp [logDensity, g]
    rw [mul_div_cancel_left₀ r hs0.ne', paperFourier_inwardDilation hs0]
    simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    push_cast
    ring
  simp_rw [he]
  rw [integral_const_mul]
  have hc := Measure.setIntegral_comp_smul_of_pos volume g {r : ℝ | R ≤ |r|} hs0
  simp only [smul_eq_mul, Module.finrank_self, pow_one] at hc
  rw [hc]
  have hsub : s • {r : ℝ | R ≤ |r|} ⊆ {r : ℝ | R / 2 ≤ |r|} := by
    rintro r ⟨x, hx, rfl⟩
    change R / 2 ≤ |s * x|
    rw [abs_mul, abs_of_pos hs0]
    have hx' : R ≤ |x| := hx
    nlinarith [abs_nonneg x]
  have hi : (∫ r : ℝ in s • {r : ℝ | R ≤ |r|}, g r) ≤
      2 * ∫ r : ℝ in {r | R / 2 ≤ |r|}, logDensity f r := by
    calc
      _ ≤ ∫ r : ℝ in s • {r : ℝ | R ≤ |r|}, 2 * logDensity f r := by
        apply setIntegral_mono_on hg.integrableOn (hf.2.2.const_mul 2).integrableOn
        · exact (isClosed_le continuous_const continuous_abs).measurableSet.const_smul₀ s
        · intro r hr
          dsimp [g, logDensity]
          nlinarith [mul_le_mul_of_nonneg_right (log_div_weight_le hs r) (sq_nonneg ‖paperFourier f r‖)]
      _ ≤ ∫ r : ℝ in {r | R / 2 ≤ |r|}, 2 * logDensity f r := by
        apply setIntegral_mono_set (hf.2.2.const_mul 2).integrableOn
        · exact Eventually.of_forall fun r => mul_nonneg (by norm_num) (logDensity_nonneg f r)
        · exact Eventually.of_forall fun r => hsub (a := r)
      _ = _ := integral_const_mul _ _
  have hn : 0 ≤ ∫ r : ℝ in s • {r : ℝ | R ≤ |r|}, g r :=
    integral_nonneg fun r => mul_nonneg (logWindowWeight_pos (r / s)).le (sq_nonneg _)
  have hsimp : s ^ 2 * (s⁻¹ * (∫ r : ℝ in s • {r : ℝ | R ≤ |r|}, g r)) =
      s * (∫ r : ℝ in s • {r : ℝ | R ≤ |r|}, g r) := by
    field_simp
  rw [hsimp]
  exact (mul_le_of_le_one_left hn hs1).trans hi

/-- Integrability of the logarithmic density implies that the logarithmic
energy in the tails tends to zero. -/
theorem logDensity_tail_tendsto_zero {a : ℝ} {f : ℝ → ℂ}
    (hf : ThetaTrial.Paper.InWindowFormDomain a f) :
    Tendsto (fun n : ℕ => ∫ r : ℝ in {r | (n : ℝ) ≤ |r|}, logDensity f r)
      atTop (𝓝 0) := by
  have hi : (⋂ n : ℕ, {r : ℝ | (n : ℝ) ≤ |r|}) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro r hr
    obtain ⟨n, hn⟩ := exists_nat_gt |r|
    exact (not_le.mpr hn) (mem_iInter.mp hr n)
  have hm : Antitone (fun n : ℕ => {r : ℝ | (n : ℝ) ≤ |r|}) := by
    intro n m hnm r hr
    exact le_trans (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast hnm) hr
  have ht' := tendsto_setIntegral_of_antitone (μ := volume)
    (fun n : ℕ => (isClosed_le (continuous_const : Continuous (fun _ : ℝ => (n : ℝ)))
      continuous_abs).measurableSet) hm (⟨0, hf.2.2.integrableOn⟩ :
      ∃ n : ℕ, IntegrableOn (logDensity f) {r : ℝ | (n : ℝ) ≤ |r|} volume)
  simpa only [hi, setIntegral_empty] using ht'

def fourierLogDistance (f g : ℝ → ℂ) (r : ℝ) : ℝ :=
  Real.log (2 + |r|) * ‖paperFourier f r - paperFourier g r‖ ^ 2

lemma fourierLogDistance_nonneg (f g : ℝ → ℂ) (r : ℝ) :
    0 ≤ fourierLogDistance f g r :=
  mul_nonneg (logWindowWeight_pos r).le (sq_nonneg _)

lemma fourierLogDistance_le (f g : ℝ → ℂ) (r : ℝ) :
    fourierLogDistance f g r ≤ 2 * logDensity f r + 2 * logDensity g r := by
  have ht := norm_sub_le (paperFourier f r) (paperFourier g r)
  have hq : ‖paperFourier f r - paperFourier g r‖ ^ 2 ≤
      2 * ‖paperFourier f r‖ ^ 2 + 2 * ‖paperFourier g r‖ ^ 2 := by
    nlinarith [sq_nonneg (‖paperFourier f r‖ - ‖paperFourier g r‖),
      norm_nonneg (paperFourier f r - paperFourier g r)]
  have h := mul_le_mul_of_nonneg_left hq (logWindowWeight_pos r).le
  dsimp [fourierLogDistance, logDensity]
  nlinarith

lemma continuous_paperFourier {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (fun r : ℝ => paperFourier f r) := by
  simpa only [paperFourier_eq_logUncertainty] using LogUncertainty.paperFourier_continuous hf

lemma fourierLogDistance_continuous {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    Continuous (fourierLogDistance f g) := by
  exact ((continuous_const.add continuous_abs).log (fun r => ne_of_gt (by positivity : 0 < 2 + |r|))).mul
    (((continuous_paperFourier hf).sub (continuous_paperFourier hg)).norm.pow 2)

lemma fourierLogDistance_integrable {a b : ℝ} {f g : ℝ → ℂ}
    (hf : ThetaTrial.Paper.InWindowFormDomain a f)
    (hg : ThetaTrial.Paper.InWindowFormDomain b g) :
    Integrable (fourierLogDistance f g) := by
  apply ((hf.2.2.const_mul 2).add (hg.2.2.const_mul 2)).mono'
    (fourierLogDistance_continuous hf.integrable hg.integrable).aestronglyMeasurable
  filter_upwards [] with r
  rw [Real.norm_eq_abs, abs_of_nonneg (fourierLogDistance_nonneg f g r)]
  exact fourierLogDistance_le f g r

lemma fourierLogDistance_tail_le {a b R : ℝ} {f g : ℝ → ℂ}
    (hf : ThetaTrial.Paper.InWindowFormDomain a f)
    (hg : ThetaTrial.Paper.InWindowFormDomain b g) :
    (∫ r : ℝ in {r | R ≤ |r|}, fourierLogDistance f g r) ≤
      2 * (∫ r : ℝ in {r | R ≤ |r|}, logDensity f r) +
      2 * (∫ r : ℝ in {r | R ≤ |r|}, logDensity g r) := by
  have hi := integral_mono_ae (μ := volume.restrict {r : ℝ | R ≤ |r|}) (fourierLogDistance_integrable hf hg).integrableOn
    ((hf.2.2.const_mul 2).add (hg.2.2.const_mul 2)).integrableOn
    (Eventually.of_forall (fourierLogDistance_le f g))
  dsimp only [Pi.add_apply] at hi
  rw [integral_add (hf.2.2.const_mul 2).integrableOn (hg.2.2.const_mul 2).integrableOn,
    integral_const_mul, integral_const_mul] at hi
  exact hi

lemma inwardDilation_logDistance_tail {s a R : ℝ} (hs : (1 : ℝ) / 2 ≤ s)
    (hs1 : s ≤ 1) (hR : 0 ≤ R) {f : ℝ → ℂ}
    (hf : ThetaTrial.Paper.InWindowFormDomain a f) :
    (∫ r : ℝ in {r | R ≤ |r|}, fourierLogDistance (inwardDilation s f) f r) ≤
      6 * (∫ r : ℝ in {r | R / 2 ≤ |r|}, logDensity f r) := by
  have ht := fourierLogDistance_tail_le (R := R) (InWindowFormDomain.inwardDilation hs hf) hf
  have hd := inwardDilation_log_tail hs hs1 hR hf
  have hm : (∫ r : ℝ in {r | R ≤ |r|}, logDensity f r) ≤
      (∫ r : ℝ in {r | R / 2 ≤ |r|}, logDensity f r) := by
    apply setIntegral_mono_set hf.2.2.integrableOn
      (Eventually.of_forall (logDensity_nonneg f))
    exact Eventually.of_forall fun r hr => le_trans (by linarith) hr
  linarith

lemma inwardDilation_fourier_tendsto {a : ℝ} {f : ℝ → ℂ}
    (hf : ThetaTrial.Paper.InWindowFormDomain a f) {s : ℕ → ℝ}
    (hs : ∀ n, 0 < s n) (ht : Tendsto s atTop (𝓝 1)) (r : ℝ) :
    Tendsto (fun n => paperFourier (inwardDilation (s n) f) r) atTop
      (𝓝 (paperFourier f r)) := by
  have hreal := (continuous_paperFourier hf.integrable).continuousAt.tendsto.comp
    (ht.mul_const r)
  have hcast := Complex.continuous_ofReal.continuousAt.tendsto.comp ht
  have hmul := hcast.mul hreal
  simpa only [paperFourier_inwardDilation (hs _), one_mul, Complex.ofReal_one,
    Complex.ofReal_mul, Function.comp_def] using hmul

lemma inwardDilation_local_logDistance_tendsto {a : ℝ} {f : ℝ → ℂ}
    (hf : ThetaTrial.Paper.InWindowFormDomain a f) {s : ℕ → ℝ}
    (hs : ∀ n, (1 : ℝ) / 2 ≤ s n) (hs1 : ∀ n, s n ≤ 1)
    (ht : Tendsto s atTop (𝓝 1)) (R : ℝ) :
    Tendsto (fun n => ∫ r : ℝ in Ioo (-R) R,
      fourierLogDistance (inwardDilation (s n) f) f r) atTop (𝓝 0) := by
  let M : ℝ := ∫ x : ℝ, ‖f x‖
  have hM : 0 ≤ M := integral_nonneg fun x => norm_nonneg _
  have hb (r : ℝ) : ‖paperFourier f r‖ ≤ M := by
    simpa only [paperFourier_eq_logUncertainty] using LogUncertainty.paperFourier_norm_le f r
  have hds (n : ℕ) : 0 < s n := by linarith [hs n]
  have hd (n : ℕ) (r : ℝ) : ‖paperFourier (inwardDilation (s n) f) r‖ ≤ M := by
    rw [paperFourier_inwardDilation (hds n), norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hds n)]
    have hbr := hb (s n * r)
    push_cast at hbr
    exact (mul_le_mul_of_nonneg_left hbr (hds n).le).trans (mul_le_of_le_one_left hM (hs1 n))
  have hc := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioo (-R) R))
    (F := fun n r => fourierLogDistance (inwardDilation (s n) f) f r)
    (f := fun _ => (0 : ℝ)) (fun _ : ℝ => Real.log (2 + |R|) * (2 * M) ^ 2)
  simp only [integral_zero] at hc
  apply hc
  · intro n
    exact (fourierLogDistance_integrable (InWindowFormDomain.inwardDilation (hs n) hf)
      hf).integrableOn.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (fourierLogDistance_nonneg _ _ _)]
    apply mul_le_mul
    · apply Real.log_le_log (by positivity)
      have hrr : |r| < R := abs_lt.mpr hr
      linarith [le_abs_self R]
    · apply pow_le_pow_left₀ (norm_nonneg _)
      exact (norm_sub_le _ _).trans (by linarith [hd n r, hb r])
    · exact sq_nonneg _
    · exact (logWindowWeight_pos R).le
  · filter_upwards [] with r
    have h := (inwardDilation_fourier_tendsto hf hds ht r).sub
      (tendsto_const_nhds (x := paperFourier f r))
    simpa [fourierLogDistance] using (h.norm.pow 2).const_mul (Real.log (2 + |r|))

/-- Inward dilations converge in the full logarithmic Fourier seminorm.
The proof uses Fourier scaling and the integrable weighted tails. -/
theorem inwardDilation_logDistance_tendsto {a : ℝ} {f : ℝ → ℂ}
    (hf : ThetaTrial.Paper.InWindowFormDomain a f) {s : ℕ → ℝ}
    (hs : ∀ n, (1 : ℝ) / 2 ≤ s n) (hs1 : ∀ n, s n ≤ 1)
    (ht : Tendsto s atTop (𝓝 1)) :
    Tendsto (fun n => ∫ r : ℝ,
      fourierLogDistance (inwardDilation (s n) f) f r) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Eventually.of_forall fun n => hb.trans_le
      (integral_nonneg (fourierLogDistance_nonneg _ _))
  · intro ε hε
    obtain ⟨N, hN⟩ := ((tendsto_order.mp (logDensity_tail_tendsto_zero hf)).2
      (ε / 12) (by linarith)).exists
    let R : ℝ := 2 * (N : ℝ)
    have hR : 0 ≤ R := by dsimp [R]; positivity
    have hl := inwardDilation_local_logDistance_tendsto hf hs hs1 ht R
    filter_upwards [(tendsto_order.mp hl).2 (ε / 2) (by linarith)] with n hn
    have htail := inwardDilation_logDistance_tail (hs n) (hs1 n) hR hf
    have hRdiv : R / 2 = (N : ℝ) := by dsimp [R]; ring
    rw [hRdiv] at htail
    have hc : (Ioo (-R) R)ᶜ = {r : ℝ | R ≤ |r|} := by
      ext r
      simp only [mem_compl_iff, mem_Ioo, mem_ofPred_eq, ← abs_lt, not_lt]
    rw [← integral_add_compl measurableSet_Ioo
      (fourierLogDistance_integrable (InWindowFormDomain.inwardDilation (hs n) hf) hf), hc]
    linarith

def coreBump : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

def coreKernel (x : ℝ) : ℂ := (coreBump.normed volume x : ℂ)

lemma coreKernel_integrable : Integrable coreKernel :=
  Complex.ofRealCLM.integrable_comp coreBump.integrable_normed

lemma coreKernel_contDiff : ContDiff ℝ ∞ coreKernel :=
  Complex.ofRealCLM.contDiff.comp coreBump.contDiff_normed

lemma coreKernel_support : Function.support coreKernel ⊆ Icc (-1 : ℝ) 1 := by
  intro x hx
  have hn : coreBump.normed volume x ≠ 0 := by
    intro he
    exact hx (by simp [coreKernel, he])
  have hm : x ∈ Metric.ball (0 : ℝ) coreBump.rOut := by
    rw [← coreBump.support_normed_eq (μ := volume)]
    exact hn
  have h : |x| < 1 := by simpa [coreBump, Real.dist_eq] using hm
  exact ⟨(abs_lt.mp h).1.le, (abs_lt.mp h).2.le⟩

lemma coreKernel_compact : HasCompactSupport coreKernel :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal coreKernel_support isClosed_Icc)

lemma coreKernel_norm_integral : (∫ x : ℝ, ‖coreKernel x‖) = 1 := by
  simp only [coreKernel, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (coreBump.nonneg_normed _), coreBump.integral_normed]

lemma coreKernel_integral : (∫ x : ℝ, coreKernel x) = 1 := by
  have h := Complex.ofRealCLM.integral_comp_comm (coreBump.integrable_normed (μ := volume))
  simpa [coreKernel, coreBump.integral_normed] using h

def mollifier (δ : ℝ) (x : ℝ) : ℂ := (δ⁻¹ : ℂ) * coreKernel (x / δ)

def smoothApprox (δ : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  mollifier δ ⋆[ContinuousLinearMap.mul ℝ ℂ] f

lemma mollifier_integrable {δ : ℝ} (hδ : 0 < δ) : Integrable (mollifier δ) :=
  (coreKernel_integrable.comp_div hδ.ne').const_mul _

lemma mollifier_contDiff (δ : ℝ) : ContDiff ℝ ∞ (mollifier δ) := by
  exact contDiff_const.mul (coreKernel_contDiff.comp (contDiff_id.div_const δ))

lemma mollifier_support {δ : ℝ} (hδ : 0 < δ) :
    Function.support (mollifier δ) ⊆ Icc (-δ) δ := by
  intro x hx
  have hs : x ∈ Function.support (inwardDilation δ coreKernel) := by
    intro hz
    exact hx (by simp [mollifier, inwardDilation] at hz ⊢; simp [hz])
  simpa only [mul_one] using inwardDilation_support hδ coreKernel_support hs

lemma mollifier_compact {δ : ℝ} (hδ : 0 < δ) : HasCompactSupport (mollifier δ) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal (mollifier_support hδ) isClosed_Icc)

lemma mollifier_norm_integral {δ : ℝ} (hδ : 0 < δ) :
    (∫ x : ℝ, ‖mollifier δ x‖) = 1 := by
  simp only [mollifier, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  rw [integral_const_mul]
  change δ⁻¹ * (∫ x : ℝ, (fun y => ‖coreKernel y‖) (x / δ)) = 1
  rw [Measure.integral_comp_div (fun y : ℝ => ‖coreKernel y‖) δ, coreKernel_norm_integral,
    abs_of_pos hδ, smul_eq_mul, mul_one, inv_mul_cancel₀ hδ.ne']

lemma paperFourier_const_mul (c : ℂ) (f : ℝ → ℂ) (z : ℂ) :
    paperFourier (fun x => c * f x) z = c * paperFourier f z := by
  simp only [paperFourier, mul_assoc, integral_const_mul]

lemma paperFourier_mollifier {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    paperFourier (mollifier δ) r = paperFourier coreKernel (δ * r : ℝ) := by
  change paperFourier (fun x => (δ⁻¹ : ℂ) * inwardDilation δ coreKernel x) r = _
  rw [paperFourier_const_mul, paperFourier_inwardDilation hδ, ← mul_assoc]
  simp only [inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hδ.ne'),
    one_mul, Complex.ofReal_mul]

lemma paperFourier_mollifier_norm_le {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    ‖paperFourier (mollifier δ) r‖ ≤ 1 := by
  have h := LogUncertainty.paperFourier_norm_le (mollifier δ) r
  simpa only [← paperFourier_eq_logUncertainty, mollifier_norm_integral hδ] using h

lemma paperFourier_mollifier_tendsto {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n)
    (ht : Tendsto δ atTop (𝓝 0)) (r : ℝ) :
    Tendsto (fun n => paperFourier (mollifier (δ n)) r) atTop (𝓝 1) := by
  have hc := (continuous_paperFourier coreKernel_integrable).continuousAt.tendsto.comp (ht.mul_const r)
  have hz : paperFourier coreKernel (0 : ℝ) = 1 := by
    simpa [paperFourier] using coreKernel_integral
  simpa only [paperFourier_mollifier (hδ _), zero_mul, hz, Function.comp_def] using hc

lemma paperFourier_smoothApprox {δ : ℝ} (hδ : 0 < δ) {f : ℝ → ℂ}
    (hf : Integrable f) (r : ℝ) :
    paperFourier (smoothApprox δ f) r = paperFourier (mollifier δ) r * paperFourier f r := by
  simp only [paperFourier_eq_logUncertainty, LogUncertainty.paperFourier]
  exact Real.fourier_mul_convolution_eq (mollifier_integrable hδ) hf _

lemma smoothApprox_contDiff {δ : ℝ} (hδ : 0 < δ) {f : ℝ → ℂ} (hf : Integrable f) :
    ContDiff ℝ ∞ (smoothApprox δ f) :=
  (mollifier_compact hδ).contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ)
    (mollifier_contDiff δ) hf.locallyIntegrable

lemma smoothApprox_support {δ a : ℝ} (hδ : 0 < δ) {f : ℝ → ℂ}
    (hf : Function.support f ⊆ Icc (-a) a) :
    Function.support (smoothApprox δ f) ⊆ Icc (-(a + δ)) (a + δ) := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := support_convolution_subset (ContinuousLinearMap.mul ℝ ℂ) hx
  have hy' := mollifier_support hδ hy
  have hz' := hf hz
  exact ⟨by linarith [hy'.1, hz'.1], by linarith [hy'.2, hz'.2]⟩

lemma smoothApprox_inDomain {δ a : ℝ} (hδ : 0 < δ) {f : ℝ → ℂ}
    (hf : ThetaTrial.Paper.InWindowFormDomain a f) :
    ThetaTrial.Paper.InWindowFormDomain (a + δ) (smoothApprox δ f) := by
  have hs := smoothApprox_support hδ hf.1
  have hc : HasCompactSupport (smoothApprox δ f) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hs isClosed_Icc)
  exact compact_smooth_inDomain hc (smoothApprox_contDiff hδ hf.integrable) hs

/-- Smooth convolution converges in the logarithmic Fourier seminorm;
the multiplier is uniformly bounded by one. -/
theorem smoothApprox_logDistance_tendsto {a : ℝ} {f : ℝ → ℂ}
    (hf : ThetaTrial.Paper.InWindowFormDomain a f) {δ : ℕ → ℝ}
    (hδ : ∀ n, 0 < δ n) (ht : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => ∫ r : ℝ, fourierLogDistance (smoothApprox (δ n) f) f r)
      atTop (𝓝 0) := by
  have hd := tendsto_integral_of_dominated_convergence
    (μ := volume) (F := fun n r => fourierLogDistance (smoothApprox (δ n) f) f r)
    (f := fun _ => (0 : ℝ)) (fun r => 4 * logDensity f r)
  simp only [integral_zero] at hd
  apply hd
  · intro n
    exact (fourierLogDistance_integrable (smoothApprox_inDomain (hδ n) hf) hf).aestronglyMeasurable
  · exact hf.2.2.const_mul 4
  · intro n
    filter_upwards [] with r
    rw [Real.norm_eq_abs, abs_of_nonneg (fourierLogDistance_nonneg _ _ _)]
    have hb : ‖paperFourier (smoothApprox (δ n) f) r - paperFourier f r‖ ≤
        2 * ‖paperFourier f r‖ := by
      rw [paperFourier_smoothApprox (hδ n) hf.integrable, ← sub_one_mul, norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (norm_sub_le _ _).trans (by
        rw [norm_one]
        linarith [paperFourier_mollifier_norm_le (hδ n) r])
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2)
      (logWindowWeight_pos r).le
    dsimp [fourierLogDistance, logDensity]
    nlinarith
  · filter_upwards [] with r
    have hm := (paperFourier_mollifier_tendsto hδ ht r).mul_const (paperFourier f r)
    have hs := hm.sub (tendsto_const_nhds (x := paperFourier f r))
    simpa only [paperFourier_smoothApprox (hδ _) hf.integrable, one_mul, sub_self,
      norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, fourierLogDistance]
      using (hs.norm.pow 2).const_mul (Real.log (2 + |r|))

lemma fourierLogDistance_triangle (f g h : ℝ → ℂ) (r : ℝ) :
    fourierLogDistance f h r ≤ 2 * fourierLogDistance f g r + 2 * fourierLogDistance g h r := by
  have ht := norm_sub_le_norm_sub_add_norm_sub (paperFourier f r) (paperFourier g r)
    (paperFourier h r)
  have hq : ‖paperFourier f r - paperFourier h r‖ ^ 2 ≤
      2 * ‖paperFourier f r - paperFourier g r‖ ^ 2 +
      2 * ‖paperFourier g r - paperFourier h r‖ ^ 2 := by
    nlinarith [sq_nonneg (‖paperFourier f r - paperFourier g r‖ -
      ‖paperFourier g r - paperFourier h r‖), norm_nonneg (paperFourier f r - paperFourier h r)]
  have hw := mul_le_mul_of_nonneg_left hq (logWindowWeight_pos r).le
  dsimp [fourierLogDistance]
  nlinarith

lemma fourierLogDistance_integral_triangle {a b c : ℝ} {f g h : ℝ → ℂ}
    (hf : ThetaTrial.Paper.InWindowFormDomain a f)
    (hg : ThetaTrial.Paper.InWindowFormDomain b g)
    (hh : ThetaTrial.Paper.InWindowFormDomain c h) :
    (∫ r : ℝ, fourierLogDistance f h r) ≤
      2 * (∫ r : ℝ, fourierLogDistance f g r) + 2 * (∫ r : ℝ, fourierLogDistance g h r) := by
  have hi := integral_mono_ae (fourierLogDistance_integrable hf hh)
    (((fourierLogDistance_integrable hf hg).const_mul 2).add
      ((fourierLogDistance_integrable hg hh).const_mul 2))
    (Eventually.of_forall (fourierLogDistance_triangle f g h))
  dsimp only [Pi.add_apply] at hi
  rw [integral_add ((fourierLogDistance_integrable hf hg).const_mul 2)
    ((fourierLogDistance_integrable hg hh).const_mul 2), integral_const_mul, integral_const_mul] at hi
  exact hi

def coreRadius (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

lemma coreRadius_pos (n : ℕ) : 0 < coreRadius n := by dsimp [coreRadius]; positivity

lemma coreRadius_le_one (n : ℕ) : coreRadius n ≤ 1 := by
  dsimp [coreRadius]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
  simp

lemma coreRadius_tendsto : Tendsto coreRadius atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Every form-domain function admits smooth approximations whose
support is a positive distance from both walls. -/
theorem exists_smooth_log_approximation {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : ThetaTrial.Paper.InWindowFormDomain a f) {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : ℝ → ℂ) (b : ℝ), b < a ∧ ContDiff ℝ ∞ g ∧
      Function.support g ⊆ Icc (-b) b ∧
      (∫ r : ℝ, fourierLogDistance g f r) < ε := by
  let s : ℕ → ℝ := fun n => 1 - coreRadius n / 2
  have hs (n : ℕ) : (1 : ℝ) / 2 ≤ s n := by
    dsimp [s]
    linarith [coreRadius_le_one n]
  have hs1 (n : ℕ) : s n ≤ 1 := by dsimp [s]; linarith [coreRadius_pos n]
  have hslt (n : ℕ) : s n < 1 := by dsimp [s]; linarith [coreRadius_pos n]
  have hst : Tendsto s atTop (𝓝 1) := by
    simpa only [s, zero_div, sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (coreRadius_tendsto.div_const 2)
  obtain ⟨n, hn⟩ := ((tendsto_order.mp (inwardDilation_logDistance_tendsto hf hs hs1 hst)).2
    (ε / 4) (by linarith)).exists
  let F : ℝ → ℂ := inwardDilation (s n) f
  have hF : ThetaTrial.Paper.InWindowFormDomain (s n * a) F :=
    InWindowFormDomain.inwardDilation (hs n) hf
  have hmargin : 0 < a - s n * a := by nlinarith [hslt n]
  have hsmall := (tendsto_order.mp coreRadius_tendsto).2 (a - s n * a) hmargin
  have happrox := (tendsto_order.mp
    (smoothApprox_logDistance_tendsto hF coreRadius_pos coreRadius_tendsto)).2
    (ε / 4) (by linarith)
  obtain ⟨m, hm, hm'⟩ := (hsmall.and happrox).exists
  refine ⟨smoothApprox (coreRadius m) F, s n * a + coreRadius m, by linarith,
    smoothApprox_contDiff (coreRadius_pos m) hF.integrable,
    smoothApprox_support (coreRadius_pos m) hF.1, ?_⟩
  have ht := fourierLogDistance_integral_triangle
    (smoothApprox_inDomain (coreRadius_pos m) hF) hF hf
  change (∫ r : ℝ, fourierLogDistance F f r) < ε / 4 at hn
  linarith

/-- The chosen graph vector of a domain function. Its physical
coordinate is the original `L2` equivalence class. -/
def graphOfFunction {a : ℝ} {f : ℝ → ℂ}
    (hf : ThetaTrial.Paper.InWindowFormDomain a f) : windowFormGraph a :=
  ⟨WithLp.toLp 2 (hf.2.1.toLp f, (InWindowFormDomain.exists_graph hf).choose),
    (InWindowFormDomain.exists_graph hf).choose_spec⟩

lemma graphOfFunction_ae {a : ℝ} {f : ℝ → ℂ}
    (hf : ThetaTrial.Paper.InWindowFormDomain a f) :
    ((graphOfFunction hf).val.fst : ℝ → ℂ) =ᵐ[volume] f :=
  hf.2.1.coeFn_toLp

lemma paperFourier_of_ae_eq {f g : ℝ → ℂ} (h : f =ᵐ[volume] g) (z : ℂ) :
    paperFourier f z = paperFourier g z := by
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

lemma graphOfFunction_fourier {a : ℝ} {f : ℝ → ℂ}
    (hf : ThetaTrial.Paper.InWindowFormDomain a f) (r : ℝ) :
    paperFourier (windowRepresentative a (graphOfFunction hf).val.fst) r = paperFourier f r :=
  paperFourier_of_ae_eq ((windowRepresentative_ae_eq
    (show (graphOfFunction hf).val.fst ∈ windowL2 a from (graphOfFunction hf).property.2)).trans
      (graphOfFunction_ae hf)) r

def logGraphConstant : ℝ := (1 / Real.log 2 + 1) / (2 * Real.pi)

lemma logGraphConstant_pos : 0 < logGraphConstant := by
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  dsimp [logGraphConstant]
  positivity

/-- The logarithmic energy alone controls the complete graph norm,
because its multiplier is bounded below by `log 2 > 0`. -/
lemma graph_norm_sq_le_logEnergy {a : ℝ} (p : windowFormGraph a) :
    ‖p‖ ^ 2 ≤ logGraphConstant *
      (∫ r : ℝ, logDensity (windowRepresentative a p.val.fst) r) := by
  have hp := windowRepresentative_inDomain
    (show WithLp.toLp 2 (p.val.fst, p.val.snd) ∈ windowFormGraph a from p.property)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hi := integral_mono_ae (hp.fourier_sq_integrable.const_mul (Real.log 2)) hp.2.2
    (Eventually.of_forall fun r => mul_le_mul_of_nonneg_right
      (Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith [abs_nonneg r])) (sq_nonneg _))
  rw [integral_const_mul, graph_fourier_mass] at hi
  have hpineq : ‖physicalInclusion a p‖ ^ 2 ≤
      (∫ r : ℝ, logDensity (windowRepresentative a p.val.fst) r) /
        (2 * Real.pi * Real.log 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi * Real.log 2)).mpr
    dsimp only [logDensity]
    nlinarith [hi]
  rw [windowFormGraph_norm_sq, windowRepresentative_squaredNorm
    (show p.val.fst ∈ windowL2 a from p.property.2)]
  change ‖physicalInclusion a p‖ ^ 2 +
    (∫ r : ℝ, logDensity (windowRepresentative a p.val.fst) r) / (2 * Real.pi) ≤ _
  calc
    _ ≤ (∫ r : ℝ, logDensity (windowRepresentative a p.val.fst) r) /
        (2 * Real.pi * Real.log 2) +
        (∫ r : ℝ, logDensity (windowRepresentative a p.val.fst) r) / (2 * Real.pi) :=
      by linarith [hpineq]
    _ = _ := by
      dsimp [logGraphConstant]
      field_simp

lemma graph_dist_sq_le_logDistance {a : ℝ} (p q : windowFormGraph a) :
    dist p q ^ 2 ≤ logGraphConstant *
      (∫ r : ℝ, fourierLogDistance (windowRepresentative a p.val.fst)
        (windowRepresentative a q.val.fst) r) := by
  have h := graph_norm_sq_le_logEnergy (p - q)
  simpa only [dist_eq_norm, logDensity, graph_fourier_sub, fourierLogDistance] using h

/-- Smooth functions supported strictly inside the physical window,
viewed as vectors of the form graph. -/
def smoothCoreVectors (a : ℝ) : Set (windowFormGraph a) :=
  {p | ∃ (f : ℝ → ℂ) (b : ℝ), b < a ∧ ContDiff ℝ ∞ f ∧
    Function.support f ⊆ Icc (-b) b ∧ (p.val.fst : ℝ → ℂ) =ᵐ[volume] f}

/-- `C_c^∞(-a,a)` is dense in the logarithmically weighted graph
norm. This is stronger than ambient `L2` density. -/
theorem smoothCoreVectors_dense {a : ℝ} (ha : 0 < a) : Dense (smoothCoreVectors a) := by
  rw [Metric.dense_iff]
  intro p ε hε
  let f : ℝ → ℂ := windowRepresentative a p.val.fst
  have hf : ThetaTrial.Paper.InWindowFormDomain a f := windowRepresentative_inDomain
    (show WithLp.toLp 2 (p.val.fst, p.val.snd) ∈ windowFormGraph a from p.property)
  have he : 0 < ε ^ 2 / logGraphConstant := by
    exact div_pos (sq_pos_of_pos hε) logGraphConstant_pos
  obtain ⟨g, b, hba, hgc, hgs, hgapprox⟩ := exists_smooth_log_approximation ha hf he
  have hcompact : HasCompactSupport g :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hgs isClosed_Icc)
  have hg : ThetaTrial.Paper.InWindowFormDomain a g := compact_smooth_inDomain hcompact hgc
    (hgs.trans (Icc_subset_Icc (by linarith) hba.le))
  let q := graphOfFunction hg
  refine ⟨q, ?_, ⟨g, b, hba, hgc, hgs, graphOfFunction_ae hg⟩⟩
  rw [Metric.mem_ball]
  have hbound := graph_dist_sq_le_logDistance q p
  have hsame : (∫ r : ℝ, fourierLogDistance (windowRepresentative a q.val.fst)
      (windowRepresentative a p.val.fst) r) = ∫ r : ℝ, fourierLogDistance g f r := by
    apply integral_congr_ae
    filter_upwards [] with r
    simp only [fourierLogDistance, q, graphOfFunction_fourier]
    rfl
  rw [hsame] at hbound
  have hstrict := mul_lt_mul_of_pos_left hgapprox logGraphConstant_pos
  rw [mul_div_cancel₀ _ logGraphConstant_pos.ne'] at hstrict
  have hsq : dist q p ^ 2 < ε ^ 2 := hbound.trans_lt hstrict
  nlinarith [dist_nonneg (x := q) (y := p)]

/-- Unbundled interpretation of a smooth core vector, including compact
support strictly inside the open window. -/
theorem smoothCoreVectors_representative {a : ℝ} {p : windowFormGraph a}
    (hp : p ∈ smoothCoreVectors a) :
    ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Ioo (-a) a ∧ (p.val.fst : ℝ → ℂ) =ᵐ[volume] f := by
  obtain ⟨f, b, hba, hfc, hfs, hfe⟩ := hp
  have ht : tsupport f ⊆ Icc (-b) b := closure_minimal hfs isClosed_Icc
  refine ⟨f, hfc, isCompact_Icc.of_isClosed_subset isClosed_closure ht, ?_, hfe⟩
  intro x hx
  have hx' := ht hx
  exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩

/-- Sequential smooth approximation in the form graph. -/
theorem exists_smoothCore_sequence {a : ℝ} (ha : 0 < a) (p : windowFormGraph a) :
    ∃ u : ℕ → windowFormGraph a, (∀ n, u n ∈ smoothCoreVectors a) ∧
      Tendsto u atTop (𝓝 p) :=
  mem_closure_iff_seq_limit.mp (smoothCoreVectors_dense ha p)

#print axioms inwardDilation_logDistance_tendsto
#print axioms smoothApprox_logDistance_tendsto
#print axioms exists_smooth_log_approximation
#print axioms smoothCoreVectors_dense
#print axioms exists_smoothCore_sequence

end ThetaTrial.Paper.FormDomain

