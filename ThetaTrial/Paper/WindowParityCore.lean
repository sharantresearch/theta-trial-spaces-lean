import ThetaTrial.Paper.WindowParity
import ThetaTrial.Paper.WindowFormCore

/-!
# Smooth form cores in the even and odd sectors

Averaging a smooth interior approximant with its reflection preserves its
interior support margin. Continuity of this graph projection then
gives approximation in each sector, in the physical norm and in the full
shifted Weil form.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set Filter
open scoped Topology ContDiff

namespace ThetaTrial.Paper.WindowParity
open FormDomain WindowFormAssembly ParityFormEmbedding

/-- The smooth representative of the parity projection. -/
def smoothParityAverage (ε : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (2 : ℂ)⁻¹ • (f x + ε • f (-x))

theorem smoothParityAverage_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (ε : ℂ) :
    ContDiff ℝ ∞ (smoothParityAverage ε f) :=
  (hf.add ((hf.comp contDiff_neg).const_smul ε)).const_smul (2 : ℂ)⁻¹

/-- Averaging keeps the same closed support interval. -/
theorem smoothParityAverage_support {f : ℝ → ℂ} {b : ℝ}
    (hf : Function.support f ⊆ Icc (-b) b) (ε : ℂ) :
    Function.support (smoothParityAverage ε f) ⊆ Icc (-b) b := by
  intro x hx
  by_contra hn
  have hz : f x = 0 := Function.notMem_support.mp (fun h => hn (hf h))
  have hn' : -x ∉ Icc (-b) b := by
    rintro ⟨hl, hr⟩
    exact hn ⟨by linarith, by linarith⟩
  have hz' : f (-x) = 0 := Function.notMem_support.mp (fun h => hn' (hf h))
  exact hx (by simp [smoothParityAverage, hz, hz'])

theorem smoothParityAverage_parity (ε : ℂ) (hε : ε ^ 2 = 1)
    (f : ℝ → ℂ) (x : ℝ) :
    smoothParityAverage ε f (-x) = ε • smoothParityAverage ε f x := by
  have he : ε * ε = 1 := by simpa only [pow_two] using hε
  simp only [smoothParityAverage, neg_neg, smul_add, smul_smul]
  rw [mul_left_comm ε (2 : ℂ)⁻¹ ε, he, mul_one]
  module

/-- The abstract graph projection has the explicit reflected average as
its physical representative, almost everywhere. -/
theorem projection_fst_ae (a : ℝ) (ε : ℂ) (p : windowFormGraph a) :
    ((projection (graphReflectionCLM a) ε p).val.fst : ℝ → ℂ) =ᵐ[volume]
      smoothParityAverage ε (p.val.fst : ℝ → ℂ) := by
  change (fun x => ((2 : ℂ)⁻¹ •
    (p.val.fst + ε • l2Reflection p.val.fst) : L2) x) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_smul (2 : ℂ)⁻¹ (p.val.fst + ε • l2Reflection p.val.fst),
    Lp.coeFn_add p.val.fst (ε • l2Reflection p.val.fst),
    Lp.coeFn_smul ε (l2Reflection p.val.fst), l2Reflection_coeFn p.val.fst]
      with x ho ha hs hr
  rw [ho]
  change (2 : ℂ)⁻¹ • ((p.val.fst + ε • l2Reflection p.val.fst) x) = _
  rw [ha]
  change (2 : ℂ)⁻¹ • (p.val.fst x + (ε • l2Reflection p.val.fst : L2) x) = _
  rw [hs]
  change (2 : ℂ)⁻¹ • (p.val.fst x + ε • l2Reflection p.val.fst x) = _
  rw [hr]
  rfl

theorem smoothParityAverage_congr_ae (ε : ℂ) {f g : ℝ → ℂ}
    (hfg : f =ᵐ[volume] g) :
    smoothParityAverage ε f =ᵐ[volume] smoothParityAverage ε g := by
  have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hfg
  filter_upwards [hfg, hn] with x hx hn
  simp only [smoothParityAverage, hx, hn]

/-- The parity projection preserves the smooth graph core, with
the original witness `b < a`; no endpoint trace condition is introduced. -/
theorem smoothCoreVectors_projection {a : ℝ} {p : windowFormGraph a}
    (hp : p ∈ smoothCoreVectors a) (ε : ℂ) :
    projection (graphReflectionCLM a) ε p ∈ smoothCoreVectors a := by
  obtain ⟨f, b, hba, hfc, hfs, hfe⟩ := hp
  exact ⟨smoothParityAverage ε f, b, hba, smoothParityAverage_contDiff hfc ε,
    smoothParityAverage_support hfs ε,
    (projection_fst_ae a ε p).trans (smoothParityAverage_congr_ae ε hfe)⟩

/-- Smooth core vectors in the parity subspace of the form graph. -/
def paritySmoothCoreVectors (a : ℝ) (ε : ℂ) : Set (graphSector a ε) :=
  {p | p.val ∈ smoothCoreVectors a}

/-- A sector core vector has a pointwise even or odd smooth
representative, supported in the same strictly smaller interval. -/
theorem paritySmoothCoreVectors_representative {a : ℝ} (ε : ℂ) (hε : ε ^ 2 = 1)
    {p : graphSector a ε} (hp : p ∈ paritySmoothCoreVectors a ε) :
    ∃ (f : ℝ → ℂ) (b : ℝ), b < a ∧ ContDiff ℝ ∞ f ∧
      Function.support f ⊆ Icc (-b) b ∧ (∀ x : ℝ, f (-x) = ε • f x) ∧
      (p.val.val.fst : ℝ → ℂ) =ᵐ[volume] f := by
  obtain ⟨f, b, hba, hfc, hfs, hfe⟩ := hp
  have he := (projection_fst_ae a ε p.val).trans (smoothParityAverage_congr_ae ε hfe)
  rw [projection_eq_self (graphReflectionCLM a) ε hε p.property] at he
  exact ⟨smoothParityAverage ε f, b, hba, smoothParityAverage_contDiff hfc ε,
    smoothParityAverage_support hfs ε, smoothParityAverage_parity ε hε f, he⟩

theorem exists_smooth_parity_core_sequence {a : ℝ} (ha : 0 < a)
    (ε : ℂ) (hε : ε ^ 2 = 1) (p : graphSector a ε) :
    ∃ u : ℕ → graphSector a ε,
      (∀ n, (u n).val ∈ smoothCoreVectors a) ∧ Tendsto u atTop (𝓝 p) := by
  obtain ⟨u, hu, ht⟩ := exists_smoothCore_sequence ha p.val
  let P := projectionToSector (graphReflectionCLM a) (graphReflection_involutive a) ε hε
  have hPp : P p.val = p :=
    Subtype.ext (projection_eq_self (graphReflectionCLM a) ε hε p.property)
  refine ⟨fun n => P (u n), fun n => smoothCoreVectors_projection (hu n) ε, ?_⟩
  simpa only [hPp, Function.comp_def] using P.continuous.continuousAt.tendsto.comp ht

theorem paritySmoothCoreVectors_dense {a : ℝ} (ha : 0 < a)
    (ε : ℂ) (hε : ε ^ 2 = 1) : Dense (paritySmoothCoreVectors a ε) := by
  intro p
  obtain ⟨u, hu, ht⟩ := exists_smooth_parity_core_sequence ha ε hε p
  exact mem_closure_iff_seq_limit.mpr ⟨u, hu, ht⟩

/-- Each parity sector has a compact smooth interior core for the full shifted form, with both physical and form-energy convergence. -/
theorem exists_smooth_parity_full_form_core_sequence {a : ℝ} (ha : 0 < a)
    (ε : ℂ) (hε : ε ^ 2 = 1) (p : graphSector a ε) :
    ∃ u : ℕ → graphSector a ε,
      (∀ n, (u n).val ∈ smoothCoreVectors a) ∧
      Tendsto u atTop (𝓝 p) ∧
      Tendsto (fun n => ‖parityInclusion a ε (u n - p)‖) atTop (𝓝 0) ∧
      Tendsto (fun n => (parityShiftedForm a ε (u n - p) (u n - p)).re)
        atTop (𝓝 0) := by
  obtain ⟨u, hu, ht⟩ := exists_smooth_parity_core_sequence ha ε hε p
  have hz : Tendsto (fun n => u n - p) atTop (𝓝 0) := by
    simpa only [sub_self] using ht.sub_const p
  refine ⟨u, hu, ht, ?_, ?_⟩
  · simpa only [map_zero, norm_zero, Function.comp_def] using
      ((parityInclusion a ε).continuous.continuousAt.tendsto.comp hz).norm
  · have hcont : Continuous (fun v : graphSector a ε => (parityShiftedForm a ε v v).re) := by
      fun_prop
    simpa only [map_zero, zero_apply, Complex.zero_re, Function.comp_def] using
      hcont.continuousAt.tendsto.comp hz

end ThetaTrial.Paper.WindowParity
