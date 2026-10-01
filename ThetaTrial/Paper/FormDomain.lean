import ThetaTrial.Paper.FullForm
import ThetaTrial.Paper.LogUncertainty
import ThetaTrial.Paper.Archimedean
import ThetaTrial.ArchimedeanMultiplier
import ThetaTrial.Imported.Zeta23.WeilEF.VerticalLine
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.Sequences
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
The logarithmic Fourier form domain of Proposition `pre:form`.

The domain is realized as a closed weighted Fourier graph inside `L2`. This
file identifies its Hilbert norm with the integral norm of the paper and
proves the estimates used for compactness.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set

namespace ThetaTrial.Paper

lemma logWindowWeight_pos (r : ℝ) : 0 < Real.log (2 + |r|) :=
  Real.log_pos (by linarith [abs_nonneg r])

/-- Finite support and `L2` imply `L1`, so the ordinary Fourier integral
represents the `L2` Fourier transform. -/
theorem InWindowFormDomain.integrable {a : ℝ} {f : ℝ → ℂ}
    (hf : InWindowFormDomain a f) : Integrable f := by
  apply (integrableOn_iff_integrable_of_support_subset hf.1).mp
  exact MemLp.integrable (by norm_num) (hf.2.1.restrict (Icc (-a) a))

lemma paperFourier_eq_logUncertainty (f : ℝ → ℂ) (r : ℝ) :
    paperFourier f r = LogUncertainty.paperFourier f r := by
  exact (LogUncertainty.paperFourier_eq_integral f r).symm

/-- Plancherel with the paper's `2*pi` normalization on its domain. -/
theorem InWindowFormDomain.paperFourier_mass {a : ℝ} {f : ℝ → ℂ}
    (hf : InWindowFormDomain a f) :
    (∫ r : ℝ, ‖paperFourier f r‖ ^ 2) = 2 * Real.pi * squaredNorm f := by
  simp_rw [paperFourier_eq_logUncertainty]
  exact LogUncertainty.paperFourier_mass hf.integrable hf.2.1

/-- Logarithmic Fourier integrability includes ordinary square integrability.
This uses the ordinary Fourier integral in `Definitions.lean`. -/
theorem InWindowFormDomain.fourier_sq_integrable {a : ℝ} {f : ℝ → ℂ}
    (hf : InWindowFormDomain a f) :
    Integrable (fun r : ℝ => ‖paperFourier f r‖ ^ 2) := by
  have hm : AEStronglyMeasurable (fun r : ℝ => (Real.log (2 + |r|))⁻¹) := by
    have hc : Continuous (fun r : ℝ => Real.log (2 + |r|)) :=
      (continuous_const.add continuous_abs).log
        (fun r => ne_of_gt (by change 0 < 2 + |r|; linarith [abs_nonneg r]))
    exact (hc.inv₀ (fun r => (logWindowWeight_pos r).ne')).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun r : ℝ => ‖paperFourier f r‖ ^ 2) := by
    apply (hf.2.2.aestronglyMeasurable.mul hm).congr
    filter_upwards [] with r
    dsimp
    field_simp [(logWindowWeight_pos r).ne']
  apply (hf.2.2.div_const (Real.log 2)).mono' hmeas
  filter_upwards [] with r
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hl : Real.log 2 ≤ Real.log (2 + |r|) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg r])
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right hl (sq_nonneg ‖paperFourier f r‖)

/-- Quantitative Fourier tightness of the form domain. Every frequency
outside `[-R,R]` costs at least `log (2+R)` in the logarithmic form norm. -/
theorem InWindowFormDomain.fourier_tail_bound {a R : ℝ} {f : ℝ → ℂ}
    (hf : InWindowFormDomain a f) (hR : 0 ≤ R) :
    (∫ r : ℝ in {r | R ≤ |r|}, ‖paperFourier f r‖ ^ 2) ≤
      (∫ r : ℝ, Real.log (2 + |r|) * ‖paperFourier f r‖ ^ 2) /
        Real.log (2 + R) := by
  have hlog : 0 < Real.log (2 + R) := Real.log_pos (by linarith)
  have hs : MeasurableSet {r : ℝ | R ≤ |r|} := by measurability
  have hi := hf.fourier_sq_integrable
  have hc := setIntegral_mono_on
    ((hi.const_mul (Real.log (2 + R))).integrableOn)
    hf.2.2.integrableOn hs (fun r hr =>
      mul_le_mul_of_nonneg_right
        (Real.log_le_log (by linarith : 0 < 2 + R)
          (by linarith [show R ≤ |r| from hr] : 2 + R ≤ 2 + |r|))
        (sq_nonneg ‖paperFourier f r‖))
  have hn : ∀ᵐ r : ℝ, 0 ≤ Real.log (2 + |r|) * ‖paperFourier f r‖ ^ 2 := by
    filter_upwards [] with r
    exact mul_nonneg (logWindowWeight_pos r).le (sq_nonneg _)
  have ht := hc.trans (setIntegral_le_integral hf.2.2 hn)
  rw [integral_const_mul] at ht
  exact (le_div_iff₀ hlog).mpr (by simpa only [mul_comm] using ht)

/-- A bound on the logarithmic Fourier energy gives a tail cutoff that is
independent of the function. -/
theorem InWindowFormDomain.fourier_tail_le_of_log_energy_le
    {a A ε : ℝ} {f : ℝ → ℂ} (hf : InWindowFormDomain a f) (hε : 0 < ε)
    (hA : (∫ r : ℝ, Real.log (2 + |r|) * ‖paperFourier f r‖ ^ 2) ≤ A) :
    (∫ r : ℝ in {r | Real.exp (A / ε) ≤ |r|}, ‖paperFourier f r‖ ^ 2) ≤ ε := by
  have hR : 0 ≤ Real.exp (A / ε) := (Real.exp_pos _).le
  have hlog : 0 < Real.log (2 + Real.exp (A / ε)) := Real.log_pos (by linarith)
  have hl : A / ε ≤ Real.log (2 + Real.exp (A / ε)) := by
    simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos (A / ε))
        (show Real.exp (A / ε) ≤ 2 + Real.exp (A / ε) by linarith)
  calc
    _ ≤ (∫ r : ℝ, Real.log (2 + |r|) * ‖paperFourier f r‖ ^ 2) /
        Real.log (2 + Real.exp (A / ε)) := hf.fourier_tail_bound hR
    _ ≤ A / Real.log (2 + Real.exp (A / ε)) :=
      div_le_div_of_nonneg_right hA hlog.le
    _ ≤ ε := by
      apply (div_le_iff₀ hlog).mpr
      have hh := (div_le_iff₀ hε).mp hl
      simpa only [mul_comm] using hh

/-- The quarter-line digamma multiplier has logarithmic growth.
The source is the proved digamma strip estimate, with its argument checked
at `1/4 + i*r/2`. -/
theorem gammaWeight_log_bound : ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ,
    |gammaWeight r| ≤ C * Real.log (2 + |r|) + |Real.log Real.pi| := by
  obtain ⟨C, hC, hbound⟩ := Zeta23.WeilEF.digamma_growth_strip
  refine ⟨C, hC, fun r => ?_⟩
  have hd := hbound (1 / 4 + Complex.I * (r : ℂ) / 2) (by norm_num) (by norm_num)
  have him : (1 / 4 + Complex.I * (r : ℂ) / 2 : ℂ).im = r / 2 := by simp
  rw [him] at hd
  have hl : Real.log (2 + |r / 2|) ≤ Real.log (2 + |r|) := by
    apply Real.log_le_log (by linarith [abs_nonneg (r / 2)])
    rw [abs_div]
    norm_num
  calc
    |gammaWeight r| ≤
        |(Complex.digamma (1 / 4 + Complex.I * (r : ℂ) / 2)).re| +
          |Real.log Real.pi| := abs_sub _ _
    _ ≤ ‖Complex.digamma (1 / 4 + Complex.I * (r : ℂ) / 2)‖ +
          |Real.log Real.pi| := add_le_add (Complex.abs_re_le_norm _) (le_refl _)
    _ ≤ C * Real.log (2 + |r|) + |Real.log Real.pi| :=
      add_le_add (hd.trans (mul_le_mul_of_nonneg_left hl hC.le)) (le_refl _)

/-- For functions in the form domain, the gamma integral converges. -/
theorem InWindowFormDomain.gamma_integrable {a : ℝ} {f : ℝ → ℂ}
    (hf : InWindowFormDomain a f) :
    Integrable (fun r : ℝ => gammaWeight r * ‖paperFourier f r‖ ^ 2) := by
  obtain ⟨C, _, hC⟩ := gammaWeight_log_bound
  have hg : AEStronglyMeasurable gammaWeight := by
    have he : gammaWeight = ThetaTrial.GammaEnergy.gammaMultiplier := funext gammaWeight_eq_weilFormula
    rw [he]
    exact ThetaTrial.RationalFourier.gammaMultiplier_aestronglyMeasurable
  apply ((hf.2.2.const_mul C).add
    (hf.fourier_sq_integrable.const_mul |Real.log Real.pi|)).mono'
    (hg.mul hf.fourier_sq_integrable.aestronglyMeasurable)
  filter_upwards [] with r
  dsimp only [Pi.mul_apply, Pi.add_apply]
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (sq_nonneg ‖paperFourier f r‖)]
  calc
    |gammaWeight r| * ‖paperFourier f r‖ ^ 2 ≤
        (C * Real.log (2 + |r|) + |Real.log Real.pi|) * ‖paperFourier f r‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hC r) (sq_nonneg _)
    _ = _ := by ring

/-- A lower bound for the archimedean integral on the whole form domain. Full Weil semiboundedness also needs the bounded polar and prime
terms and is not inferred from this result alone. -/
theorem InWindowFormDomain.gamma_lower_bound {a : ℝ} {f : ℝ → ℂ}
    (hf : InWindowFormDomain a f) :
    ThetaTrial.GammaEnergy.gammaBase * (∫ r : ℝ, ‖paperFourier f r‖ ^ 2) ≤
      ∫ r : ℝ, gammaWeight r * ‖paperFourier f r‖ ^ 2 := by
  rw [← integral_const_mul]
  apply integral_mono (hf.fourier_sq_integrable.const_mul _) hf.gamma_integrable
  intro r
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  rw [gammaWeight_eq_weilFormula]
  exact sub_nonneg.mp (ThetaTrial.GammaEnergy.gammaMultiplier_sub_base_nonneg r)

/-- Semiboundedness of the archimedean term in the physical `L2`
norm, with all Fourier normalization factors included. -/
theorem InWindowFormDomain.archimedean_lower_bound {a : ℝ} {f : ℝ → ℂ}
    (hf : InWindowFormDomain a f) :
    ThetaTrial.GammaEnergy.gammaBase * squaredNorm f ≤
      (1 / (2 * Real.pi)) *
        (∫ r : ℝ, gammaWeight r * Complex.normSq (paperFourier f r)) := by
  have h := hf.gamma_lower_bound
  rw [hf.paperFourier_mass] at h
  have hh : ThetaTrial.GammaEnergy.gammaBase * squaredNorm f ≤
      (∫ r : ℝ, gammaWeight r * ‖paperFourier f r‖ ^ 2) / (2 * Real.pi) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    nlinarith only [h]
  simpa only [← Complex.sq_norm, div_eq_mul_inv, one_mul, mul_comm] using hh

end ThetaTrial.Paper

#print axioms ThetaTrial.Paper.InWindowFormDomain.fourier_tail_bound
#print axioms ThetaTrial.Paper.InWindowFormDomain.fourier_tail_le_of_log_energy_le
#print axioms ThetaTrial.Paper.InWindowFormDomain.gamma_integrable
#print axioms ThetaTrial.Paper.InWindowFormDomain.gamma_lower_bound
#print axioms ThetaTrial.Paper.InWindowFormDomain.archimedean_lower_bound

namespace ThetaTrial.Paper.FormDomain

open Filter
open scoped Topology FourierTransform ComplexConjugate SchwartzMap ContDiff ENNReal NNReal

/-- Ambient physical or frequency Hilbert space, modulo equality almost everywhere. -/
abbrev L2 := MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)

/-- The graph of multiplication by a fixed, possibly unbounded, weight. -/
def multiplicationGraph (w : ℝ → ℂ) : Submodule ℂ (L2 × L2) where
  carrier := {p | ∀ᵐ x : ℝ, p.2 x = w x * p.1 x}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))] with x hx
    change (0 : L2) x = w x * (0 : L2) x
    simp
  add_mem' := by
    intro p q hp hq
    filter_upwards [hp, hq, Lp.coeFn_add p.1 q.1, Lp.coeFn_add p.2 q.2]
      with x hpx hqx hfst hsnd
    change (p.2 + q.2) x = w x * (p.1 + q.1) x
    rw [hfst, hsnd]
    change p.2 x + q.2 x = w x * (p.1 x + q.1 x)
    rw [hpx, hqx]
    ring
  smul_mem' := by
    intro c p hp
    filter_upwards [hp, Lp.coeFn_smul c p.1, Lp.coeFn_smul c p.2]
      with x hpx hfst hsnd
    change (c • p.2) x = w x * (c • p.1) x
    rw [hfst, hsnd]
    change c * p.2 x = w x * (c * p.1 x)
    rw [hpx]
    ring

/-- Closedness of an unbounded multiplication graph, proved by extracting
almost-everywhere convergent subsequences from the two `L2` limits. -/
theorem multiplicationGraph_isClosed (w : ℝ → ℂ) :
    IsClosed (multiplicationGraph w : Set (L2 × L2)) := by
  apply IsSeqClosed.isClosed
  intro u p hu hup
  obtain ⟨ns, hns, hf⟩ := (tendstoInMeasure_of_tendsto_Lp
    ((continuous_fst.tendsto p).comp hup)).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hg⟩ := (tendstoInMeasure_of_tendsto_Lp
    (((continuous_snd.tendsto p).comp hup).comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have he : ∀ᵐ x : ℝ, ∀ n : ℕ,
      (u (ns (ms n))).2 x = w x * (u (ns (ms n))).1 x :=
    ae_all_iff.mpr (fun n => hu (ns (ms n)))
  filter_upwards [hf, hg, he] with x hfx hgx hex
  have ht := (tendsto_const_nhds (x := w x)).mul (hfx.comp hms.tendsto_atTop)
  exact tendsto_nhds_unique hgx (ht.congr' (Eventually.of_forall fun n => (hex n).symm))

/-- The support condition on the `L2` equivalence class. -/
def windowL2 (a : ℝ) : Submodule ℂ L2 where
  carrier := {f | ∀ᵐ x : ℝ, x ∉ Icc (-a) a → f x = 0}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))] with x hx
    exact fun _ => hx
  add_mem' := by
    intro f g hf hg
    filter_upwards [hf, hg, Lp.coeFn_add f g] with x hx hy hxy
    intro hout
    change (f + g) x = 0
    rw [hxy]
    change f x + g x = 0
    rw [hx hout, hy hout, add_zero]
  smul_mem' := by
    intro c f hf
    filter_upwards [hf, Lp.coeFn_smul c f] with x hx hcx
    intro hout
    simp [hcx, hx hout]

theorem windowL2_isClosed (a : ℝ) : IsClosed (windowL2 a : Set L2) := by
  apply IsSeqClosed.isClosed
  intro u f hu huf
  obtain ⟨ns, _, ht⟩ :=
    (tendstoInMeasure_of_tendsto_Lp huf).exists_seq_tendsto_ae
  have he : ∀ᵐ x : ℝ, ∀ n : ℕ, x ∉ Icc (-a) a → u (ns n) x = 0 :=
    ae_all_iff.mpr (fun n => hu (ns n))
  filter_upwards [ht, he] with x hx hex
  intro hout
  exact tendsto_nhds_unique hx
    (tendsto_const_nhds.congr' (Eventually.of_forall fun n => (hex n hout).symm))

/-- Mathlib uses frequency `r/(2*pi)`, hence this precise rescaling of
the paper's logarithmic weight. -/
def frequencyWeight (x : ℝ) : ℂ :=
  (Real.sqrt (Real.log (2 + |2 * Real.pi * x|)) : ℂ)

/-- Physical input paired with its weighted Fourier transform. -/
def fourierGraph : Submodule ℂ (L2 × L2) :=
  (multiplicationGraph frequencyWeight).comap
    ((Lp.fourierTransformₗᵢ ℝ ℂ).toLinearMap.prodMap (LinearMap.id : L2 →ₗ[ℂ] L2))

theorem fourierGraph_isClosed : IsClosed (fourierGraph : Set (L2 × L2)) := by
  exact (multiplicationGraph_isClosed frequencyWeight).preimage
    (((Lp.fourierTransformₗᵢ ℝ ℂ).continuous.comp continuous_fst).prodMk continuous_snd)

/-- The logarithmic form graph with both the Fourier and support conditions,
equipped with the Hilbert norm on the product. -/
def windowFormGraph (a : ℝ) : Submodule ℂ (WithLp 2 (L2 × L2)) :=
  (fourierGraph ⊓ (windowL2 a).comap (LinearMap.fst ℂ L2 L2)).comap
    (WithLp.linearEquiv 2 ℂ (L2 × L2)).toLinearMap

theorem windowFormGraph_isClosed (a : ℝ) :
    IsClosed (windowFormGraph a : Set (WithLp 2 (L2 × L2))) := by
  have hs : IsClosed
      (fourierGraph ⊓ (windowL2 a).comap (LinearMap.fst ℂ L2 L2) : Set (L2 × L2)) :=
    fourierGraph_isClosed.inter ((windowL2_isClosed a).preimage continuous_fst)
  exact hs.preimage (WithLp.prod_continuous_ofLp 2 L2 L2)

/-- The graph space is complete, proved through closedness. -/
instance windowFormGraph_completeSpace (a : ℝ) : CompleteSpace (windowFormGraph a) :=
  (windowFormGraph_isClosed a).completeSpace_coe

lemma frequencyWeight_continuous : Continuous frequencyWeight := by
  unfold frequencyWeight
  apply Complex.continuous_ofReal.comp
  apply Real.continuous_sqrt.comp
  exact (continuous_const.add ((continuous_const.mul continuous_id).abs)).log
    (fun x => ne_of_gt (by positivity : 0 < 2 + |2 * Real.pi * x|))

lemma frequencyWeight_norm_sq (x : ℝ) :
    ‖frequencyWeight x‖ ^ 2 = Real.log (2 + |2 * Real.pi * x|) := by
  simp only [frequencyWeight, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact Real.sq_sqrt (logWindowWeight_pos (2 * Real.pi * x)).le

lemma paperFourier_rescale (f : ℝ → ℂ) (x : ℝ) :
    paperFourier f ((2 * Real.pi * x : ℝ) : ℂ) = 𝓕 f x := by
  rw [paperFourier_eq_logUncertainty, LogUncertainty.paperFourier]
  field_simp

/-- The graph's weight is the paper's weight, after accounting for the Fourier
normalization. -/
theorem weighted_fourier_memLp_iff {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2) :
    MemLp (fun x => frequencyWeight x * (𝓕 (hf2.toLp f) : L2) x) 2 ↔
      Integrable (fun r : ℝ => Real.log (2 + |r|) * ‖paperFourier f r‖ ^ 2) := by
  have hae : (fun x => frequencyWeight x * (𝓕 (hf2.toLp f) : L2) x) =ᵐ[volume]
      (fun x => frequencyWeight x * 𝓕 f x) := by
    filter_upwards [LogUncertainty.ordinary_fourier_ae_L2 hf hf2] with x hx
    rw [hx]
  rw [memLp_congr_ae hae]
  have hm : AEStronglyMeasurable (fun x => frequencyWeight x * 𝓕 f x) volume :=
    frequencyWeight_continuous.aestronglyMeasurable.mul
      (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        continuous_inner hf).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hm]
  simp only [norm_mul, mul_pow, frequencyWeight_norm_sq]
  have h := integrable_comp_mul_left_iff
    (fun r : ℝ => Real.log (2 + |r|) * ‖paperFourier f r‖ ^ 2)
    (R := 2 * Real.pi) (by positivity)
  simpa only [paperFourier_rescale] using h

/-- Membership in the weighted Fourier graph is precisely square
integrability of the weighted transform. -/
theorem exists_fourierGraph_iff (f : L2) :
    (∃ g : L2, (f, g) ∈ fourierGraph) ↔
      MemLp (fun x => frequencyWeight x * (𝓕 f : L2) x) 2 := by
  constructor
  · rintro ⟨g, hg⟩
    exact (Lp.memLp g).ae_eq hg
  · intro h
    exact ⟨h.toLp _, h.coeFn_toLp⟩

theorem mem_windowL2_of_support_subset {a : ℝ} {f : ℝ → ℂ}
    (hs : Function.support f ⊆ Icc (-a) a) (hf : MemLp f 2 volume) :
    hf.toLp f ∈ windowL2 a := by
  filter_upwards [hf.coeFn_toLp] with x hx
  intro hout
  rw [hx]
  exact Function.notMem_support.mp (fun h => hout (hs h))

/-- Every member of the paper's form domain determines a vector
in the complete Hilbert graph above. -/
theorem InWindowFormDomain.exists_graph {a : ℝ} {f : ℝ → ℂ}
    (hf : ThetaTrial.Paper.InWindowFormDomain a f) :
    ∃ g : L2, WithLp.toLp 2 (hf.2.1.toLp f, g) ∈ windowFormGraph a := by
  obtain ⟨g, hg⟩ := (exists_fourierGraph_iff _).mpr
    ((weighted_fourier_memLp_iff hf.integrable hf.2.1).mpr hf.2.2)
  exact ⟨g, hg, mem_windowL2_of_support_subset hf.1 hf.2.1⟩

/-- A representative which satisfies the paper's pointwise support
condition even when the original `Lp` representative only does so a.e. -/
def windowRepresentative (a : ℝ) (f : L2) : ℝ → ℂ :=
  (Icc (-a) a).indicator (f : ℝ → ℂ)

lemma windowRepresentative_support (a : ℝ) (f : L2) :
    Function.support (windowRepresentative a f) ⊆ Icc (-a) a := by
  intro x hx
  by_contra hout
  exact hx (by simp [windowRepresentative, hout])

lemma windowRepresentative_memLp (a : ℝ) (f : L2) :
    MemLp (windowRepresentative a f) 2 volume :=
  (Lp.memLp f).indicator measurableSet_Icc

lemma windowRepresentative_integrable (a : ℝ) (f : L2) :
    Integrable (windowRepresentative a f) := by
  apply (integrableOn_iff_integrable_of_support_subset
    (windowRepresentative_support a f)).mp
  exact MemLp.integrable (by norm_num)
    ((windowRepresentative_memLp a f).restrict (Icc (-a) a))

lemma windowRepresentative_ae_eq {a : ℝ} {f : L2} (hf : f ∈ windowL2 a) :
    windowRepresentative a f =ᵐ[volume] (f : ℝ → ℂ) := by
  filter_upwards [hf] with x hx
  by_cases hin : x ∈ Icc (-a) a
  · simp [windowRepresentative, hin]
  · simp [windowRepresentative, hin, hx hin]

lemma windowRepresentative_toLp {a : ℝ} {f : L2} (hf : f ∈ windowL2 a) :
    (windowRepresentative_memLp a f).toLp (windowRepresentative a f) = f := by
  apply Lp.ext
  exact (windowRepresentative_memLp a f).coeFn_toLp.trans (windowRepresentative_ae_eq hf)

/-- Conversely, every vector of the Hilbert graph has a representative in
the exact domain of the paper. -/
theorem windowRepresentative_inDomain {a : ℝ} {f g : L2}
    (h : WithLp.toLp 2 (f, g) ∈ windowFormGraph a) :
    ThetaTrial.Paper.InWindowFormDomain a (windowRepresentative a f) := by
  refine ⟨windowRepresentative_support a f, windowRepresentative_memLp a f, ?_⟩
  apply (weighted_fourier_memLp_iff (windowRepresentative_integrable a f)
    (windowRepresentative_memLp a f)).mp
  have hs : f ∈ windowL2 a := h.2
  rw [windowRepresentative_toLp hs]
  exact (exists_fourierGraph_iff f).mp ⟨g, h.1⟩

/-- The physical inclusion of the complete graph into the ambient `L2`. -/
def physicalInclusion (a : ℝ) : windowFormGraph a →L[ℂ] L2 :=
  (WithLp.fstL 2 ℂ L2 L2).comp (windowFormGraph a).subtypeL

theorem physicalInclusion_injective (a : ℝ) : Function.Injective (physicalInclusion a) := by
  intro p q hpq
  apply Subtype.ext
  apply (WithLp.linearEquiv 2 ℂ (L2 × L2)).injective
  apply Prod.ext hpq
  apply Lp.ext
  have hp : ∀ᵐ x : ℝ, p.val.snd x = frequencyWeight x * (𝓕 p.val.fst : L2) x := p.property.1
  have hq : ∀ᵐ x : ℝ, q.val.snd x = frequencyWeight x * (𝓕 q.val.fst : L2) x := q.property.1
  change p.val.fst = q.val.fst at hpq
  filter_upwards [hp, hq] with x hx hy
  change p.val.snd x = q.val.snd x
  rw [hx, hy, hpq]

theorem physicalInclusion_norm_le (a : ℝ) (p : windowFormGraph a) :
    ‖physicalInclusion a p‖ ≤ ‖p‖ := WithLp.norm_fst_le (p := 2) L2 p.val

lemma integral_norm_sq_L2 (f : L2) : (∫ x : ℝ, ‖f x‖ ^ 2) = ‖f‖ ^ 2 := by
  apply Complex.ofRealLI.injective
  have h := (L2.inner_def (𝕜 := ℂ) f f).symm
  simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using h

lemma paperLogEnergy_rescale (f : ℝ → ℂ) :
    (∫ r : ℝ, Real.log (2 + |r|) * ‖paperFourier f r‖ ^ 2) =
      (2 * Real.pi) * ∫ x : ℝ, Real.log (2 + |2 * Real.pi * x|) * ‖𝓕 f x‖ ^ 2 := by
  have h := Measure.integral_comp_div
    (fun x : ℝ => Real.log (2 + |2 * Real.pi * x|) * ‖𝓕 f x‖ ^ 2) (2 * Real.pi)
  simp only [abs_of_pos (by positivity : 0 < 2 * Real.pi), smul_eq_mul] at h
  convert h using 1
  congr 1
  funext r
  rw [paperFourier_eq_logUncertainty, LogUncertainty.paperFourier]
  congr 3
  field_simp

theorem graph_logEnergy {a : ℝ} {f g : L2}
    (h : WithLp.toLp 2 (f, g) ∈ windowFormGraph a) :
    (∫ r : ℝ, Real.log (2 + |r|) * ‖paperFourier (windowRepresentative a f) r‖ ^ 2) =
      (2 * Real.pi) * ‖g‖ ^ 2 := by
  rw [paperLogEnergy_rescale, ← integral_norm_sq_L2 g]
  congr 1
  apply integral_congr_ae
  have hs : f ∈ windowL2 a := h.2
  have hg : ∀ᵐ x : ℝ, g x = frequencyWeight x * (𝓕 f : L2) x := h.1
  have he := LogUncertainty.ordinary_fourier_ae_L2
    (windowRepresentative_integrable a f) (windowRepresentative_memLp a f)
  rw [windowRepresentative_toLp hs] at he
  filter_upwards [hg, he] with x hx hxe
  rw [hx, norm_mul, mul_pow, frequencyWeight_norm_sq, hxe]

/-- The complete graph norm is the logarithmic form norm, with
the exact `1/(2*pi)` Plancherel factor. -/
theorem windowFormGraph_norm_sq (a : ℝ) (p : windowFormGraph a) :
    ‖p‖ ^ 2 = squaredNorm (windowRepresentative a p.val.fst) +
      (∫ r : ℝ, Real.log (2 + |r|) *
        ‖paperFourier (windowRepresentative a p.val.fst) r‖ ^ 2) / (2 * Real.pi) := by
  have hp : WithLp.toLp 2 (p.val.fst, p.val.snd) ∈ windowFormGraph a := p.property
  rw [graph_logEnergy hp, mul_div_cancel_left₀ _ (by positivity : 2 * Real.pi ≠ 0)]
  change ‖p.val‖ ^ 2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2]
  congr 1
  rw [← integral_norm_sq_L2 p.val.fst]
  unfold squaredNorm
  apply integral_congr_ae
  filter_upwards [windowRepresentative_ae_eq (show p.val.fst ∈ windowL2 a from p.property.2)]
    with x hx
  rw [hx]

instance windowL2_completeSpace (a : ℝ) : CompleteSpace (windowL2 a) :=
  (windowL2_isClosed a).completeSpace_coe

/-- The ambient Hilbert space consists of the supported `L2` vectors;
density is asserted in this space. -/
def windowInclusion (a : ℝ) : windowFormGraph a →L[ℂ] windowL2 a :=
  (physicalInclusion a).codRestrict (windowL2 a) (fun p => p.property.2)

@[simp] lemma windowInclusion_coe (a : ℝ) (p : windowFormGraph a) :
    (windowInclusion a p).val = p.val.fst := rfl

theorem windowInclusion_injective (a : ℝ) : Function.Injective (windowInclusion a) := by
  intro p q h
  exact physicalInclusion_injective a (congrArg Subtype.val h)

lemma schwartz_weighted_memLp (F : 𝓢(ℝ, ℂ)) :
    MemLp (fun x => frequencyWeight x * F x) 2 volume := by
  let M : ℝ := SchwartzMap.seminorm ℝ 0 0 F
  have hM : 0 ≤ M := (norm_nonneg (F 0)).trans (F.norm_le_seminorm ℝ 0)
  have h0 : Integrable (fun x : ℝ => ‖F x‖) := F.integrable.norm
  have h1 : Integrable (fun x : ℝ => |x| * ‖F x‖) := by
    simpa only [pow_one, Real.norm_eq_abs] using F.integrable_pow_mul volume 1
  have hi : Integrable (fun x : ℝ => (2 + |2 * Real.pi * x|) * M * ‖F x‖) := by
    apply (((h0.const_mul 2).add (h1.const_mul (2 * Real.pi))).mul_const M).congr
    filter_upwards [] with x
    change (2 * ‖F x‖ + (2 * Real.pi) * (|x| * ‖F x‖)) * M = _
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    ring
  apply (memLp_two_iff_integrable_sq_norm
    (frequencyWeight_continuous.mul F.continuous).aestronglyMeasurable).mpr
  apply hi.mono' ((frequencyWeight_continuous.mul F.continuous).norm.pow 2).aestronglyMeasurable
  filter_upwards [] with x
  change ‖(‖frequencyWeight x * F x‖ ^ 2 : ℝ)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow,
    frequencyWeight_norm_sq]
  have hl : Real.log (2 + |2 * Real.pi * x|) ≤ 2 + |2 * Real.pi * x| :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  calc
    Real.log (2 + |2 * Real.pi * x|) * ‖F x‖ ^ 2 ≤
        Real.log (2 + |2 * Real.pi * x|) * (M * ‖F x‖) := by
      apply mul_le_mul_of_nonneg_left _ (logWindowWeight_pos _).le
      simpa only [pow_two] using mul_le_mul_of_nonneg_right
        (F.norm_le_seminorm ℝ x) (norm_nonneg (F x))
    _ ≤ (2 + |2 * Real.pi * x|) * (M * ‖F x‖) :=
      mul_le_mul_of_nonneg_right hl (mul_nonneg hM (norm_nonneg _))
    _ = _ := by ring

theorem schwartz_inDomain {a : ℝ} (f : 𝓢(ℝ, ℂ))
    (hs : Function.support f ⊆ Icc (-a) a) :
    ThetaTrial.Paper.InWindowFormDomain a f := by
  refine ⟨hs, f.memLp 2 volume, ?_⟩
  apply (weighted_fourier_memLp_iff f.integrable (f.memLp 2 volume)).mp
  apply (schwartz_weighted_memLp (𝓕 f)).ae_eq
  filter_upwards [LogUncertainty.ordinary_fourier_ae_L2 f.integrable (f.memLp 2 volume)]
    with x hx
  change frequencyWeight x * 𝓕 (f : ℝ → ℂ) x = _
  rw [hx]

theorem compact_smooth_inDomain {a : ℝ} {f : ℝ → ℂ}
    (hc : HasCompactSupport f) (hd : ContDiff ℝ ∞ f)
    (hs : Function.support f ⊆ Icc (-a) a) :
    ThetaTrial.Paper.InWindowFormDomain a f :=
  schwartz_inDomain (hc.toSchwartzMap hd) hs

set_option maxHeartbeats 800000 in
/-- The form domain is dense in the supported ambient Hilbert
space. The proof uses the vanishing of the orthogonal annihilator, tested
against smooth functions compactly supported in the open interval. -/
theorem windowInclusion_denseRange (a : ℝ) : DenseRange (windowInclusion a) := by
  let K : Submodule ℂ (windowL2 a) := LinearMap.range (windowInclusion a).toLinearMap
  have hK : Kᗮ = ⊥ := by
    apply le_antisymm _ bot_le
    intro F hF
    have hlocal : LocallyIntegrable (F.val : ℝ → ℂ) volume :=
      (Lp.memLp F.val).locallyIntegrable (show 1 ≤ (2 : ℝ≥0∞) by norm_num)
    have hinside : ∀ᵐ x : ℝ, x ∈ Ioo (-a) a → F.val x = 0 := by
      apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (hlocal.locallyIntegrableOn (Ioo (-a) a))
      intro g hgd hgc hgs
      let G : ℝ → ℂ := fun x => (g x : ℂ)
      have hGc : HasCompactSupport G := by
        exact hgc.comp_left (g := Complex.ofReal) rfl
      have hGd : ContDiff ℝ ∞ G := by
        exact Complex.ofRealCLM.contDiff.comp hgd
      have hGs : Function.support G ⊆ Icc (-a) a := by
        intro x hx
        have hxg : x ∈ Function.support g := by
          intro he
          exact hx (by simp [G, he])
        exact Ioo_subset_Icc_self (hgs (subset_tsupport g hxg))
      have hG := compact_smooth_inDomain hGc hGd hGs
      obtain ⟨v, hv⟩ := InWindowFormDomain.exists_graph hG
      let p : windowFormGraph a := ⟨WithLp.toLp 2 (hG.2.1.toLp G, v), hv⟩
      have hz : inner ℂ (hG.2.1.toLp G) F.val = 0 :=
        hF (windowInclusion a p) ⟨p, rfl⟩
      calc
        (∫ x : ℝ, g x • F.val x) =
            ∫ x : ℝ, inner ℂ ((hG.2.1.toLp G) x) (F.val x) := by
          apply integral_congr_ae
          filter_upwards [hG.2.1.coeFn_toLp] with x hx
          rw [hx]
          simp [G, RCLike.inner_apply, Complex.real_smul, mul_comm]
        _ = inner ℂ (hG.2.1.toLp G) F.val := (L2.inner_def _ _).symm
        _ = 0 := hz
    have hz : (F.val : ℝ → ℂ) =ᵐ[volume] 0 := by
      filter_upwards [hinside, F.property, volume.ae_ne (-a), volume.ae_ne a]
        with x hin hout hxa hxb
      by_cases h : x ∈ Icc (-a) a
      · exact hin ⟨lt_of_le_of_ne h.1 hxa.symm, lt_of_le_of_ne h.2 hxb⟩
      · exact hout h
    have hzero : F.val = 0 := by
      apply Lp.ext
      exact hz.trans (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume)).symm
    exact (Submodule.mem_bot ℂ).mpr (Subtype.ext hzero)
  have hclosure := (K.topologicalClosure_eq_top_iff).mpr hK
  rw [← SetLike.coe_set_eq] at hclosure
  exact denseRange_iff_closure_range.mpr hclosure

/-- Sequential weak compactness of the unit ball of the complete
logarithmic graph. This is a concrete application of sequential
Banach--Alaoglu and Riesz representation. -/
theorem graph_unit_ball_weak_subsequence (a : ℝ) (u : ℕ → windowFormGraph a)
    (hu : ∀ n, ‖u n‖ ≤ 1) :
    ∃ p : windowFormGraph a, ‖p‖ ≤ 1 ∧ ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ v : windowFormGraph a,
        Tendsto (fun n => inner ℂ (u (ns n)) v) atTop (𝓝 (inner ℂ p v)) := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let d : ℕ → WeakDual ℂ (windowFormGraph a) := fun n =>
    (InnerProductSpace.toDual ℂ (windowFormGraph a) (u n)).toWeakDual
  have hd : ∀ n, d n ∈ WeakDual.toStrongDual ⁻¹'
      Metric.closedBall (0 : StrongDual ℂ (windowFormGraph a)) 1 := by
    intro n
    change dist (InnerProductSpace.toDual ℂ (windowFormGraph a) (u n)) 0 ≤ 1
    erw [dist_eq_norm, sub_zero]
    simpa only [LinearIsometryEquiv.norm_map] using hu n
  obtain ⟨b, hb, ns, hns, ht⟩ :=
    (WeakDual.isSeqCompact_closedBall ℂ (windowFormGraph a)
      (0 : StrongDual ℂ (windowFormGraph a)) 1) hd
  let p : windowFormGraph a :=
    (InnerProductSpace.toDual ℂ (windowFormGraph a)).symm b.toStrongDual
  refine ⟨p, ?_, ns, hns, ?_⟩
  · change dist b.toStrongDual 0 ≤ 1 at hb
    erw [dist_eq_norm, sub_zero] at hb
    simpa only [p, LinearIsometryEquiv.norm_map] using hb
  · intro v
    have hv := ((WeakDual.eval_continuous v).tendsto b).comp ht
    simpa [d, p, Function.comp_def, InnerProductSpace.toDual_symm_apply] using hv

/-- The compactly supported exponential representing a Fourier evaluation
as an `L2` inner product. -/
def windowExponential (a r : ℝ) : ℝ → ℂ :=
  (Icc (-a) a).indicator (fun x => Complex.exp (Complex.I * ((r * x : ℝ) : ℂ)))

lemma windowExponential_memLp (a r : ℝ) : MemLp (windowExponential a r) 2 volume := by
  apply (memLp_indicator_iff_restrict measurableSet_Icc).mpr
  apply MemLp.of_bound (by fun_prop) 1
  filter_upwards [] with x
  simp only [Complex.norm_exp_I_mul_ofReal, le_refl]

def fourierEvaluation (a r : ℝ) : windowL2 a →L[ℂ] ℂ :=
  (innerSL ℂ ((windowExponential_memLp a r).toLp (windowExponential a r))).comp
    (windowL2 a).subtypeL

theorem fourierEvaluation_eq (a r : ℝ) (f : windowL2 a) :
    fourierEvaluation a r f = paperFourier (windowRepresentative a f.val) r := by
  change inner ℂ ((windowExponential_memLp a r).toLp (windowExponential a r)) f.val = _
  rw [L2.inner_def]
  unfold paperFourier
  apply integral_congr_ae
  filter_upwards [(windowExponential_memLp a r).coeFn_toLp, f.property] with x hx hfx
  rw [hx]
  by_cases hin : x ∈ Icc (-a) a
  · simp only [windowExponential, windowRepresentative, Set.indicator_of_mem hin,
      RCLike.inner_apply, ← Complex.exp_conj, map_mul, Complex.conj_I,
      Complex.conj_ofReal, Complex.ofReal_mul]
    congr 1
    congr 1
    ring
  · simp [windowExponential, windowRepresentative, hin, hfx hin]

/-- Weak convergence of graph vectors gives pointwise convergence of the
Fourier integrals, because support turns evaluation into a bounded
functional. -/
theorem weak_graph_fourier_tendsto {a : ℝ} {u : ℕ → windowFormGraph a}
    {p : windowFormGraph a}
    (h : ∀ v : windowFormGraph a,
      Tendsto (fun n => inner ℂ (u n) v) atTop (𝓝 (inner ℂ p v))) (r : ℝ) :
    Tendsto (fun n => paperFourier (windowRepresentative a (u n).val.fst) r)
      atTop (𝓝 (paperFourier (windowRepresentative a p.val.fst) r)) := by
  let L : windowFormGraph a →L[ℂ] ℂ := (fourierEvaluation a r).comp (windowInclusion a)
  let v : windowFormGraph a := (InnerProductSpace.toDual ℂ (windowFormGraph a)).symm L
  have hv := Complex.continuous_conj.continuousAt.tendsto.comp (h v)
  have he (q : windowFormGraph a) : conj (inner ℂ q v) = L q := by
    rw [inner_conj_symm]
    exact InnerProductSpace.toDual_symm_apply
  change Tendsto (fun n => conj (inner ℂ (u n) v)) atTop (𝓝 (conj (inner ℂ p v))) at hv
  simp_rw [he] at hv
  simpa only [L, ContinuousLinearMap.comp_apply, fourierEvaluation_eq, windowInclusion_coe] using hv

lemma windowExponential_norm_sq (a r : ℝ) :
    ‖(windowExponential_memLp a r).toLp (windowExponential a r)‖ ^ 2 =
      (volume (Icc (-a) a)).toReal := by
  rw [← integral_norm_sq_L2]
  calc
    (∫ x : ℝ, ‖((windowExponential_memLp a r).toLp (windowExponential a r)) x‖ ^ 2) =
        ∫ x : ℝ, (Icc (-a) a).indicator (fun _ : ℝ => (1 : ℝ)) x := by
      apply integral_congr_ae
      filter_upwards [(windowExponential_memLp a r).coeFn_toLp] with x hx
      rw [hx]
      by_cases hin : x ∈ Icc (-a) a
      · simp only [windowExponential, Set.indicator_of_mem hin,
          Complex.norm_exp_I_mul_ofReal, one_pow]
      · simp [windowExponential, hin]
    _ = _ := by simp [integral_indicator measurableSet_Icc, measureReal_def]

/-- A frequency-independent Fourier bound on every graph ball. A coarse
constant suffices for dominated convergence on bounded frequency windows. -/
theorem graph_fourier_bound (a r : ℝ) (p : windowFormGraph a) :
    ‖paperFourier (windowRepresentative a p.val.fst) r‖ ≤
      ((volume (Icc (-a) a)).toReal + 1) * ‖p‖ := by
  let k : L2 := (windowExponential_memLp a r).toLp (windowExponential a r)
  have hk : ‖k‖ ≤ (volume (Icc (-a) a)).toReal + 1 := by
    have he := windowExponential_norm_sq a r
    change ‖k‖ ^ 2 = _ at he
    nlinarith [norm_nonneg k, ENNReal.toReal_nonneg (a := volume (Icc (-a) a))]
  have hp := physicalInclusion_norm_le a p
  change ‖p.val.fst‖ ≤ ‖p‖ at hp
  calc
    ‖paperFourier (windowRepresentative a p.val.fst) r‖ = ‖inner ℂ k p.val.fst‖ := by
      exact congrArg norm (fourierEvaluation_eq a r (windowInclusion a p)).symm
    _ ≤ ‖k‖ * ‖p.val.fst‖ := norm_inner_le_norm _ _
    _ ≤ ((volume (Icc (-a) a)).toReal + 1) * ‖p‖ :=
      mul_le_mul hk hp (norm_nonneg _) (by positivity)

theorem graph_logEnergy_le (a : ℝ) (p : windowFormGraph a) :
    (∫ r : ℝ, Real.log (2 + |r|) *
      ‖paperFourier (windowRepresentative a p.val.fst) r‖ ^ 2) ≤
      (2 * Real.pi) * ‖p‖ ^ 2 := by
  rw [graph_logEnergy (show WithLp.toLp 2 (p.val.fst, p.val.snd) ∈
    windowFormGraph a from p.property)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (norm_nonneg _) (WithLp.norm_snd_le (p := 2) L2 p.val) 2

theorem graph_fourier_sub (a r : ℝ) (p q : windowFormGraph a) :
    paperFourier (windowRepresentative a (p - q).val.fst) r =
      paperFourier (windowRepresentative a p.val.fst) r -
        paperFourier (windowRepresentative a q.val.fst) r := by
  have he (v : windowFormGraph a) := fourierEvaluation_eq a r (windowInclusion a v)
  simp only [windowInclusion_coe] at he
  rw [← he (p - q), map_sub, map_sub, he p, he q]

theorem graph_fourier_tail (a : ℝ) (p : windowFormGraph a) {R : ℝ} (hR : 0 ≤ R) :
    (∫ r : ℝ in {r | R ≤ |r|},
      ‖paperFourier (windowRepresentative a p.val.fst) r‖ ^ 2) ≤
        (2 * Real.pi) * ‖p‖ ^ 2 / Real.log (2 + R) := by
  have hp := windowRepresentative_inDomain
    (show WithLp.toLp 2 (p.val.fst, p.val.snd) ∈ windowFormGraph a from p.property)
  exact (hp.fourier_tail_bound hR).trans
    (div_le_div_of_nonneg_right (graph_logEnergy_le a p)
      (Real.log_nonneg (by linarith)))

theorem windowRepresentative_squaredNorm {a : ℝ} {f : L2} (hf : f ∈ windowL2 a) :
    squaredNorm (windowRepresentative a f) = ‖f‖ ^ 2 := by
  rw [← integral_norm_sq_L2 f]
  apply integral_congr_ae
  filter_upwards [windowRepresentative_ae_eq hf] with x hx
  rw [hx]

theorem graph_fourier_mass (a : ℝ) (p : windowFormGraph a) :
    (∫ r : ℝ, ‖paperFourier (windowRepresentative a p.val.fst) r‖ ^ 2) =
      (2 * Real.pi) * ‖physicalInclusion a p‖ ^ 2 := by
  have hp := windowRepresentative_inDomain
    (show WithLp.toLp 2 (p.val.fst, p.val.snd) ∈ windowFormGraph a from p.property)
  rw [hp.paperFourier_mass, windowRepresentative_squaredNorm
    (show p.val.fst ∈ windowL2 a from p.property.2)]
  rfl

/-- On a bounded frequency interval, pointwise convergence to zero of
Fourier transforms of a graph-bounded sequence gives convergence in `L2`. -/
theorem graph_local_mass_tendsto_zero {a B : ℝ} (u : ℕ → windowFormGraph a)
    (hu : ∀ n, ‖u n‖ ≤ B)
    (h : ∀ r : ℝ, Tendsto
      (fun n => paperFourier (windowRepresentative a (u n).val.fst) r) atTop (𝓝 0))
    (R : ℝ) :
    Tendsto (fun n => ∫ r : ℝ in Ioo (-R) R,
      ‖paperFourier (windowRepresentative a (u n).val.fst) r‖ ^ 2) atTop (𝓝 0) := by
  let C : ℝ := (volume (Icc (-a) a)).toReal + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hB : 0 ≤ B := (norm_nonneg (u 0)).trans (hu 0)
  have ht : Tendsto (fun n => ∫ r : ℝ in Ioo (-R) R,
      ‖paperFourier (windowRepresentative a (u n).val.fst) r‖ ^ 2) atTop
      (𝓝 (∫ _ : ℝ in Ioo (-R) R, (0 : ℝ))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => (C * B) ^ 2)
    · intro n
      have hp := windowRepresentative_inDomain
        (show WithLp.toLp 2 ((u n).val.fst, (u n).val.snd) ∈ windowFormGraph a from (u n).property)
      exact hp.fourier_sq_integrable.integrableOn.aestronglyMeasurable
    · exact integrable_const _
    · intro n
      filter_upwards [] with r
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact (graph_fourier_bound a r (u n)).trans (mul_le_mul_of_nonneg_left (hu n) hC)
    · filter_upwards [] with r
      simpa using (h r).norm.pow 2
  simpa only [integral_zero] using ht

/-- Uniform logarithmic tails upgrade the preceding local convergence to
convergence on the whole frequency line. -/
theorem graph_mass_tendsto_zero {a B : ℝ} (u : ℕ → windowFormGraph a)
    (hu : ∀ n, ‖u n‖ ≤ B)
    (h : ∀ r : ℝ, Tendsto
      (fun n => paperFourier (windowRepresentative a (u n).val.fst) r) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ r : ℝ,
      ‖paperFourier (windowRepresentative a (u n).val.fst) r‖ ^ 2) atTop (𝓝 0) := by
  have hdom (n : ℕ) := windowRepresentative_inDomain
    (show WithLp.toLp 2 ((u n).val.fst, (u n).val.snd) ∈ windowFormGraph a from (u n).property)
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Eventually.of_forall fun n => hb.trans_le (integral_nonneg fun _ => sq_nonneg _)
  · intro ε hε
    let A : ℝ := (2 * Real.pi) * B ^ 2
    let R : ℝ := Real.exp (A / (ε / 2))
    have hlocal := graph_local_mass_tendsto_zero u hu h R
    have hsmall := (tendsto_order.mp hlocal).2 (ε / 2) (by linarith)
    filter_upwards [hsmall] with n hn
    have henergy : (∫ r : ℝ, Real.log (2 + |r|) *
        ‖paperFourier (windowRepresentative a (u n).val.fst) r‖ ^ 2) ≤ A :=
      (graph_logEnergy_le a (u n)).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hu n) 2) (by positivity))
    have htail := (hdom n).fourier_tail_le_of_log_energy_le
      (show 0 < ε / 2 by linarith) henergy
    have hs : (Ioo (-R) R)ᶜ = {r : ℝ | R ≤ |r|} := by
      ext r
      simp only [mem_compl_iff, mem_Ioo, mem_ofPred_eq, ← abs_lt, not_lt]
    rw [← integral_add_compl measurableSet_Ioo (hdom n).fourier_sq_integrable, hs]
    change (∫ r : ℝ in Ioo (-R) R,
        ‖paperFourier (windowRepresentative a (u n).val.fst) r‖ ^ 2) +
      (∫ r : ℝ in {r | R ≤ |r|},
        ‖paperFourier (windowRepresentative a (u n).val.fst) r‖ ^ 2) < ε
    change (∫ r : ℝ in {r | R ≤ |r|},
      ‖paperFourier (windowRepresentative a (u n).val.fst) r‖ ^ 2) ≤ ε / 2 at htail
    linarith

/-- A weakly convergent sequence in the graph unit ball converges strongly
after physical inclusion. Both compactness inputs, support and logarithmic
frequency control, are used in the proof. -/
theorem weak_graph_physical_tendsto {a : ℝ} {u : ℕ → windowFormGraph a}
    {p : windowFormGraph a} (hu : ∀ n, ‖u n‖ ≤ 1) (hp : ‖p‖ ≤ 1)
    (h : ∀ v : windowFormGraph a,
      Tendsto (fun n => inner ℂ (u n) v) atTop (𝓝 (inner ℂ p v))) :
    Tendsto (fun n => physicalInclusion a (u n)) atTop (𝓝 (physicalInclusion a p)) := by
  let v : ℕ → windowFormGraph a := fun n => u n - p
  have hv : ∀ n, ‖v n‖ ≤ 2 := by
    intro n
    exact (norm_sub_le (u n) p).trans (by linarith [hu n])
  have ht (r : ℝ) : Tendsto
      (fun n => paperFourier (windowRepresentative a (v n).val.fst) r) atTop (𝓝 0) := by
    simpa only [v, graph_fourier_sub, sub_self] using
      (weak_graph_fourier_tendsto h r).sub (tendsto_const_nhds
        (x := paperFourier (windowRepresentative a p.val.fst) r))
  have hm := graph_mass_tendsto_zero v hv ht
  have hn2 : Tendsto (fun n => ‖physicalInclusion a (v n)‖ ^ 2) atTop (𝓝 0) := by
    have hd := hm.div_const (2 * Real.pi)
    simpa only [graph_fourier_mass, mul_div_cancel_left₀ _
      (show 2 * Real.pi ≠ 0 by positivity), zero_div] using hd
  have hn : Tendsto (fun n => ‖physicalInclusion a (v n)‖) atTop (𝓝 0) := by
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hn2
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [v, map_sub, dist_eq_norm] using hn

/-- The logarithmic form domain embeds compactly into the supported `L2`
space. This is derived from weak graph compactness, ordinary Fourier
evaluation, bounded-window dominated convergence, and the uniform tails. -/
theorem windowInclusion_isCompactOperator (a : ℝ) : IsCompactOperator (windowInclusion a) := by
  have hc : IsSeqCompact ((windowInclusion a) '' Metric.closedBall 0 1) := by
    intro f hf
    choose u hu huf using hf
    have hu' : ∀ n, ‖u n‖ ≤ 1 := by
      intro n
      simpa only [Metric.mem_closedBall, dist_zero_right] using hu n
    obtain ⟨p, hp, ns, hns, ht⟩ := graph_unit_ball_weak_subsequence a u hu'
    refine ⟨windowInclusion a p, ⟨p, ?_, rfl⟩, ns, hns, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hp
    · apply tendsto_subtype_rng.mpr
      have he : (fun n => (f (ns n)).val) =
          (fun n => physicalInclusion a (u (ns n))) := by
        funext n
        rw [← huf (ns n)]
        rfl
      change Tendsto (fun n => (f (ns n)).val) atTop (𝓝 (physicalInclusion a p))
      rw [he]
      exact weak_graph_physical_tendsto (fun n => hu' (ns n)) hp ht
  exact (isCompactOperator_iff_image_closedBall_subset_compact
    (windowInclusion a).toLinearMap (show (0 : ℝ) < 1 by norm_num)).mpr
      ⟨_, hc.isCompact, Subset.rfl⟩

end ThetaTrial.Paper.FormDomain

namespace ThetaTrial.Paper

/-- The gamma multiplier differs from the logarithmic reference
multiplier by a bounded function on the whole real line. The large rays
use the proved Stirling estimate and the compact part uses continuity. -/
theorem gammaWeight_sub_log_bounded : ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ,
    |gammaWeight r - Real.log (2 + |r|)| ≤ C := by
  obtain ⟨x, _, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (-2 : ℝ) 2).Nonempty from ⟨0, by norm_num⟩)
    ThetaTrial.ArchimedeanMultiplier.multiplier_continuous.abs.continuousOn
  let C : ℝ := |ThetaTrial.ArchimedeanMultiplier.multiplier x| +
    |Real.log Real.pi| + 21 + archimedeanConstant +
    |Real.log 3| + |ThetaTrial.GammaEnergy.gammaBase|
  have hC : 0 < C := by
    dsimp [C]
    linarith [abs_nonneg (ThetaTrial.ArchimedeanMultiplier.multiplier x),
      abs_nonneg (Real.log Real.pi), archimedeanConstant_nonneg,
      abs_nonneg (Real.log 3), abs_nonneg ThetaTrial.GammaEnergy.gammaBase]
  refine ⟨C, hC, fun r => abs_le.mpr ⟨?_, ?_⟩⟩
  · have hlower : Real.log (2 + |r|) - gammaWeight r ≤
        archimedeanConstant + |Real.log 3| + |ThetaTrial.GammaEnergy.gammaBase| := by
      by_cases hr : 1 ≤ |r|
      · have hr0 : 0 < |r| := lt_of_lt_of_le zero_lt_one hr
        have hl : Real.log (2 + |r|) ≤ Real.log 3 + Real.log |r| := by
          rw [← Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hr0.ne']
          exact Real.log_le_log (by positivity) (by linarith)
        linarith [gammaWeight_ge_log r, le_abs_self (Real.log 3),
          abs_nonneg ThetaTrial.GammaEnergy.gammaBase]
      · have hl : Real.log (2 + |r|) ≤ Real.log 3 :=
          Real.log_le_log (by positivity) (by linarith [le_of_not_ge hr])
        linarith [gammaWeight_ge_base r, archimedeanConstant_nonneg,
          le_abs_self (Real.log 3), neg_le_abs ThetaTrial.GammaEnergy.gammaBase]
    dsimp [C]
    linarith [abs_nonneg (ThetaTrial.ArchimedeanMultiplier.multiplier x),
      abs_nonneg (Real.log Real.pi)]
  · have hupper : gammaWeight r - Real.log (2 + |r|) ≤
        |ThetaTrial.ArchimedeanMultiplier.multiplier x| + |Real.log Real.pi| + 20 := by
      by_cases hr : 2 ≤ |r|
      · have h := ThetaTrial.ArchimedeanMultiplier.multiplier_large_bound r hr
        change |gammaWeight r| ≤ _ at h
        linarith [le_abs_self (gammaWeight r), abs_nonneg (ThetaTrial.ArchimedeanMultiplier.multiplier x)]
      · have hrmem : r ∈ Icc (-2 : ℝ) 2 := by
          obtain ⟨hl, hh⟩ := abs_lt.mp (lt_of_not_ge hr)
          exact ⟨hl.le, hh.le⟩
        have h := hmax hrmem
        change |gammaWeight r| ≤ |ThetaTrial.ArchimedeanMultiplier.multiplier x| at h
        linarith [le_abs_self (gammaWeight r), (logWindowWeight_pos r).le,
          abs_nonneg (Real.log Real.pi)]
    dsimp [C]
    linarith [archimedeanConstant_nonneg, abs_nonneg (Real.log 3),
      abs_nonneg ThetaTrial.GammaEnergy.gammaBase]

/-- The archimedean form is a bounded `L2` perturbation of the
logarithmic form, uniformly over all supported form-domain vectors. -/
theorem archimedean_log_bounded_perturbation : ∃ C : ℝ, 0 < C ∧
    ∀ (a : ℝ) (f : ℝ → ℂ), InWindowFormDomain a f →
      |archimedeanEnergy f - (1 / (2 * Real.pi)) *
        (∫ r : ℝ, Real.log (2 + |r|) * ‖paperFourier f r‖ ^ 2)| ≤ C * squaredNorm f := by
  obtain ⟨C, hC, hweight⟩ := gammaWeight_sub_log_bounded
  refine ⟨C, hC, fun a f hf => ?_⟩
  have hupper := integral_mono hf.gamma_integrable
    (hf.2.2.add (hf.fourier_sq_integrable.const_mul C)) (fun r => by
      dsimp only [Pi.add_apply]
      have h := (abs_le.mp (hweight r)).2
      nlinarith [sq_nonneg ‖paperFourier f r‖])
  have hlower := integral_mono
    (hf.2.2.sub (hf.fourier_sq_integrable.const_mul C)) hf.gamma_integrable (fun r => by
      dsimp only [Pi.sub_apply]
      have h := (abs_le.mp (hweight r)).1
      nlinarith [sq_nonneg ‖paperFourier f r‖])
  dsimp only [Pi.add_apply, Pi.sub_apply] at hupper hlower
  rw [integral_add hf.2.2 (hf.fourier_sq_integrable.const_mul C),
    integral_const_mul, hf.paperFourier_mass] at hupper
  rw [integral_sub hf.2.2 (hf.fourier_sq_integrable.const_mul C),
    integral_const_mul, hf.paperFourier_mass] at hlower
  have hi : |(∫ r : ℝ, gammaWeight r * ‖paperFourier f r‖ ^ 2) -
      (∫ r : ℝ, Real.log (2 + |r|) * ‖paperFourier f r‖ ^ 2)| ≤
        C * ((2 * Real.pi) * squaredNorm f) := by
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  simp only [archimedeanEnergy, ← Complex.sq_norm]
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  calc
    _ ≤ (1 / (2 * Real.pi)) * (C * ((2 * Real.pi) * squaredNorm f)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by field_simp

end ThetaTrial.Paper

#print axioms ThetaTrial.Paper.FormDomain.multiplicationGraph_isClosed
#print axioms ThetaTrial.Paper.FormDomain.windowFormGraph_isClosed
#print axioms ThetaTrial.Paper.FormDomain.windowFormGraph_norm_sq
#print axioms ThetaTrial.Paper.FormDomain.windowInclusion_denseRange
#print axioms ThetaTrial.Paper.FormDomain.graph_unit_ball_weak_subsequence
#print axioms ThetaTrial.Paper.FormDomain.weak_graph_fourier_tendsto
#print axioms ThetaTrial.Paper.FormDomain.windowInclusion_isCompactOperator
#print axioms ThetaTrial.Paper.gammaWeight_sub_log_bounded
#print axioms ThetaTrial.Paper.archimedean_log_bounded_perturbation
