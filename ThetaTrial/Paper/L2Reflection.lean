import ThetaTrial.Paper.FormDomain

/-! Reflection on `L²`. Even and odd functions form complex subspaces, and
real-valued functions form a real subspace. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set Filter
open scoped Topology ComplexConjugate FourierTransform SchwartzMap

namespace ThetaTrial.Paper.FormDomain

def l2Reflection : L2 →ₗᵢ[ℂ] L2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => -x) (Measure.measurePreserving_neg volume)

theorem l2Reflection_coeFn (f : L2) : l2Reflection f =ᵐ[volume] fun x : ℝ => f (-x) :=
  Lp.coeFn_compMeasurePreserving f (Measure.measurePreserving_neg volume)

@[simp] theorem l2Reflection_involutive (f : L2) : l2Reflection (l2Reflection f) = f := by
  change Lp.compMeasurePreserving (fun x : ℝ => -x) (Measure.measurePreserving_neg volume)
    (Lp.compMeasurePreserving (fun x : ℝ => -x) (Measure.measurePreserving_neg volume) f) = f
  rw [← Lp.compMeasurePreserving_comp_apply]
  simpa only [Function.comp_def, neg_neg, id_eq] using! Lp.compMeasurePreserving_id_apply f

@[simp] theorem l2Reflection_norm (f : L2) : ‖l2Reflection f‖ = ‖f‖ :=
  l2Reflection.norm_map f

def l2ReflectionEquiv : L2 ≃ₗᵢ[ℂ] L2 :=
  LinearIsometryEquiv.ofSurjective l2Reflection
    (fun f => ⟨l2Reflection f, l2Reflection_involutive f⟩)

@[simp] theorem l2ReflectionEquiv_apply (f : L2) : l2ReflectionEquiv f = l2Reflection f := rfl

def evenL2 : Submodule ℂ L2 :=
  LinearMap.ker (l2Reflection.toLinearMap - LinearMap.id)

def oddL2 : Submodule ℂ L2 :=
  LinearMap.ker (l2Reflection.toLinearMap + LinearMap.id)

theorem mem_evenL2_iff (f : L2) : f ∈ evenL2 ↔ l2Reflection f = f := by
  simp [evenL2, LinearMap.mem_ker, sub_eq_zero]

theorem mem_oddL2_iff (f : L2) : f ∈ oddL2 ↔ l2Reflection f = -f := by
  simp [oddL2, LinearMap.mem_ker, add_eq_zero_iff_eq_neg]

theorem mem_evenL2_iff_ae (f : L2) :
    f ∈ evenL2 ↔ ∀ᵐ x : ℝ, f (-x) = f x := by
  rw [mem_evenL2_iff]
  constructor
  · intro h
    have he := (l2Reflection_coeFn f).symm
    rwa [h] at he
  · intro h
    exact Lp.ext ((l2Reflection_coeFn f).trans h)

theorem mem_oddL2_iff_ae (f : L2) :
    f ∈ oddL2 ↔ ∀ᵐ x : ℝ, f (-x) = -f x := by
  rw [mem_oddL2_iff]
  constructor
  · intro h
    have he := (l2Reflection_coeFn f).symm
    rw [h] at he
    exact he.trans (Lp.coeFn_neg f)
  · intro h
    apply Lp.ext
    filter_upwards [l2Reflection_coeFn f, h, Lp.coeFn_neg f] with x hx hodd hn
    rw [hx, hn]
    exact hodd

theorem evenL2_isClosed : IsClosed (evenL2 : Set L2) := by
  have he : (evenL2 : Set L2) = {f | l2Reflection f = f} := Set.ext mem_evenL2_iff
  rw [he]
  exact isClosed_eq l2Reflection.continuous continuous_id

theorem oddL2_isClosed : IsClosed (oddL2 : Set L2) := by
  have he : (oddL2 : Set L2) = {f | l2Reflection f = -f} := Set.ext mem_oddL2_iff
  rw [he]
  exact isClosed_eq l2Reflection.continuous continuous_id.neg

theorem even_odd_inner_eq_zero {f g : L2} (hf : f ∈ evenL2) (hg : g ∈ oddL2) :
    inner ℂ f g = 0 := by
  have h := l2Reflection.inner_map_map f g
  rw [(mem_evenL2_iff f).mp hf, (mem_oddL2_iff g).mp hg, inner_neg_right] at h
  linear_combination -h / 2

def realL2 : Submodule ℝ L2 where
  carrier := {f | ∀ᵐ x : ℝ, (f x).im = 0}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx
    change ((0 : L2) x).im = 0
    rw [hx]
    rfl
  add_mem' := by
    intro f g hf hg
    filter_upwards [hf, hg, Lp.coeFn_add f g] with x hx hy hxy
    change ((f + g : L2) x).im = 0
    rw [hxy]
    change (f x + g x).im = 0
    simp [hx, hy]
  smul_mem' := by
    intro c f hf
    filter_upwards [hf, Lp.coeFn_smul c f] with x hx hcx
    rw [hcx]
    change (((c : ℂ) * f x)).im = 0
    simp [Complex.mul_im, hx]

theorem mem_realL2_iff (f : L2) : f ∈ realL2 ↔ ∀ᵐ x : ℝ, (f x).im = 0 := Iff.rfl

theorem realL2_isClosed : IsClosed (realL2 : Set L2) := by
  apply IsSeqClosed.isClosed
  intro u f hu huf
  obtain ⟨ns, _, ht⟩ := (tendstoInMeasure_of_tendsto_Lp huf).exists_seq_tendsto_ae
  have he : ∀ᵐ x : ℝ, ∀ n : ℕ, (u (ns n) x).im = 0 :=
    ae_all_iff.mpr (fun n => hu (ns n))
  filter_upwards [ht, he] with x hx hex
  exact tendsto_nhds_unique (Complex.continuous_im.continuousAt.tendsto.comp hx)
    (tendsto_const_nhds.congr' (Eventually.of_forall fun n => (hex n).symm))

theorem l2Reflection_mem_realL2 {f : L2} (hf : f ∈ realL2) : l2Reflection f ∈ realL2 := by
  have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hf
  filter_upwards [l2Reflection_coeFn f, hn] with x hx hn
  simpa only [hx] using hn

theorem l2Reflection_mem_windowL2 {a : ℝ} {f : L2} (hf : f ∈ windowL2 a) :
    l2Reflection f ∈ windowL2 a := by
  have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hf
  filter_upwards [l2Reflection_coeFn f, hn] with x hx hn
  intro hout
  rw [hx]
  apply hn
  intro hneg
  apply hout
  exact ⟨by linarith [hneg.2], by linarith [hneg.1]⟩

theorem l2Reflection_mem_windowL2_iff (a : ℝ) (f : L2) :
    l2Reflection f ∈ windowL2 a ↔ f ∈ windowL2 a := by
  constructor
  · intro h
    simpa only [l2Reflection_involutive] using l2Reflection_mem_windowL2 h
  · exact l2Reflection_mem_windowL2

def evenWindowL2 (a : ℝ) : Submodule ℂ L2 := windowL2 a ⊓ evenL2
def oddWindowL2 (a : ℝ) : Submodule ℂ L2 := windowL2 a ⊓ oddL2
def realWindowL2 (a : ℝ) : Submodule ℝ L2 := (windowL2 a).restrictScalars ℝ ⊓ realL2

theorem evenWindowL2_isClosed (a : ℝ) : IsClosed (evenWindowL2 a : Set L2) :=
  (windowL2_isClosed a).inter evenL2_isClosed

theorem oddWindowL2_isClosed (a : ℝ) : IsClosed (oddWindowL2 a : Set L2) :=
  (windowL2_isClosed a).inter oddL2_isClosed

theorem realWindowL2_isClosed (a : ℝ) : IsClosed (realWindowL2 a : Set L2) :=
  (windowL2_isClosed a).inter realL2_isClosed

/-- Reflection respects the multiplication graph of every even weight. -/
theorem l2Reflection_multiplicationGraph {w : ℝ → ℂ} (hw : ∀ x, w (-x) = w x)
    {f g : L2} (h : (f, g) ∈ multiplicationGraph w) :
    (l2Reflection f, l2Reflection g) ∈ multiplicationGraph w := by
  have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae h
  filter_upwards [l2Reflection_coeFn f, l2Reflection_coeFn g, hn] with x hfx hgx hn
  rw [hfx, hgx]
  simpa only [hw] using hn

theorem l2Reflection_toLp {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    l2Reflection (hf.toLp f) =
      (hf.comp_measurePreserving (Measure.measurePreserving_neg volume)).toLp (fun x => f (-x)) :=
  rfl

theorem l2Reflection_fourier_toLp {f : ℝ → ℂ} (hi : Integrable f) (hf : MemLp f 2 volume) :
    𝓕 (l2Reflection (hf.toLp f)) = l2Reflection (𝓕 (hf.toLp f)) := by
  have hfn := hf.comp_measurePreserving (Measure.measurePreserving_neg volume)
  have hl := LogUncertainty.ordinary_fourier_ae_L2 hi.comp_neg hfn
  rw [← l2Reflection_toLp hf] at hl
  have hr := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
    (LogUncertainty.ordinary_fourier_ae_L2 hi hf)
  apply Lp.ext
  filter_upwards [hl, hr, l2Reflection_coeFn (𝓕 (hf.toLp f))] with x hlx hrx hx
  calc
    (𝓕 (l2Reflection (hf.toLp f)) : L2) x = 𝓕 (fun y => f (-y)) x := hlx.symm
    _ = 𝓕 f (-x) := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) f x
    _ = (𝓕 (hf.toLp f) : L2) (-x) := hrx
    _ = l2Reflection (𝓕 (hf.toLp f)) x := hx.symm

/-- Reflection commutes with the `L²` Fourier transform (from the case of ordinary
Fourier integrals, by density). -/
theorem l2Reflection_fourier (f : L2) :
    𝓕 (l2Reflection f) = l2Reflection (𝓕 f) := by
  let q : L2 → Prop := fun g => 𝓕 (l2Reflection g) = l2Reflection (𝓕 g)
  change q f
  apply DenseRange.induction_on (p := q)
    (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2)
      ENNReal.ofNat_ne_top) f
  · exact isClosed_eq ((Lp.fourierTransformₗᵢ ℝ ℂ).continuous.comp l2Reflection.continuous)
      (l2Reflection.continuous.comp (Lp.fourierTransformₗᵢ ℝ ℂ).continuous)
  · intro g
    dsimp [q]
    simpa only [SchwartzMap.toLpCLM_apply] using!
      l2Reflection_fourier_toLp g.integrable (g.memLp 2 volume)

@[simp] theorem frequencyWeight_neg (x : ℝ) : frequencyWeight (-x) = frequencyWeight x := by
  simp [frequencyWeight, mul_neg]

theorem l2Reflection_fourierGraph {f g : L2} (h : (f, g) ∈ fourierGraph) :
    (l2Reflection f, l2Reflection g) ∈ fourierGraph := by
  change (𝓕 (l2Reflection f), l2Reflection g) ∈ multiplicationGraph frequencyWeight
  rw [l2Reflection_fourier]
  exact l2Reflection_multiplicationGraph frequencyWeight_neg h

def reflectionPair : WithLp 2 (L2 × L2) →ₗᵢ[ℂ] WithLp 2 (L2 × L2) :=
  l2Reflection.withLpProdMap 2 l2Reflection

@[simp] theorem reflectionPair_apply (p : WithLp 2 (L2 × L2)) :
    reflectionPair p = WithLp.toLp 2 (l2Reflection p.fst, l2Reflection p.snd) := rfl

@[simp] theorem reflectionPair_involutive (p : WithLp 2 (L2 × L2)) :
    reflectionPair (reflectionPair p) = p := by
  simp [reflectionPair_apply]
  rfl

theorem reflectionPair_mem_windowFormGraph {a : ℝ} {p : WithLp 2 (L2 × L2)}
    (hp : p ∈ windowFormGraph a) : reflectionPair p ∈ windowFormGraph a := by
  exact ⟨l2Reflection_fourierGraph hp.1, l2Reflection_mem_windowL2 hp.2⟩

def windowReflectionIsometry (a : ℝ) : windowL2 a →ₗᵢ[ℂ] windowL2 a where
  toLinearMap := (l2Reflection.toLinearMap.comp (windowL2 a).subtype).codRestrict
    (windowL2 a) (fun f => l2Reflection_mem_windowL2 f.property)
  norm_map' f := l2Reflection.norm_map f

@[simp] theorem windowReflectionIsometry_coe (a : ℝ) (f : windowL2 a) :
    (windowReflectionIsometry a f : L2) = l2Reflection f := rfl

@[simp] theorem windowReflectionIsometry_involutive (a : ℝ) (f : windowL2 a) :
    windowReflectionIsometry a (windowReflectionIsometry a f) = f := by
  apply Subtype.ext
  exact l2Reflection_involutive f

def windowReflection (a : ℝ) : windowL2 a ≃ₗᵢ[ℂ] windowL2 a :=
  LinearIsometryEquiv.ofSurjective (windowReflectionIsometry a)
    (fun f => ⟨windowReflectionIsometry a f, windowReflectionIsometry_involutive a f⟩)

@[simp] theorem windowReflection_coe (a : ℝ) (f : windowL2 a) :
    (windowReflection a f : L2) = l2Reflection f := rfl

@[simp] theorem windowReflection_involutive (a : ℝ) (f : windowL2 a) :
    windowReflection a (windowReflection a f) = f := windowReflectionIsometry_involutive a f

def graphReflectionIsometry (a : ℝ) : windowFormGraph a →ₗᵢ[ℂ] windowFormGraph a where
  toLinearMap := (reflectionPair.toLinearMap.comp (windowFormGraph a).subtype).codRestrict
    (windowFormGraph a) (fun p => reflectionPair_mem_windowFormGraph p.property)
  norm_map' p := reflectionPair.norm_map p

@[simp] theorem graphReflectionIsometry_coe (a : ℝ) (p : windowFormGraph a) :
    (graphReflectionIsometry a p : WithLp 2 (L2 × L2)) = reflectionPair p := rfl

@[simp] theorem graphReflectionIsometry_involutive (a : ℝ) (p : windowFormGraph a) :
    graphReflectionIsometry a (graphReflectionIsometry a p) = p := by
  apply Subtype.ext
  exact reflectionPair_involutive p

def graphReflection (a : ℝ) : windowFormGraph a ≃ₗᵢ[ℂ] windowFormGraph a :=
  LinearIsometryEquiv.ofSurjective (graphReflectionIsometry a)
    (fun p => ⟨graphReflectionIsometry a p, graphReflectionIsometry_involutive a p⟩)

@[simp] theorem graphReflection_coe (a : ℝ) (p : windowFormGraph a) :
    (graphReflection a p : WithLp 2 (L2 × L2)) = reflectionPair p := rfl

@[simp] theorem graphReflection_involutive (a : ℝ) (p : windowFormGraph a) :
    graphReflection a (graphReflection a p) = p := graphReflectionIsometry_involutive a p

/-- The compact graph inclusion intertwines the two constructed reflections. -/
theorem windowInclusion_graphReflection (a : ℝ) (p : windowFormGraph a) :
    windowInclusion a (graphReflection a p) = windowReflection a (windowInclusion a p) := by
  apply Subtype.ext
  rfl

/-- The supported representative of the reflected class is the reflected
supported representative, almost everywhere. -/
theorem windowRepresentative_l2Reflection (a : ℝ) (f : L2) :
    windowRepresentative a (l2Reflection f) =ᵐ[volume]
      fun x => windowRepresentative a f (-x) := by
  filter_upwards [l2Reflection_coeFn f] with x hx
  have hi : -x ∈ Icc (-a) a ↔ x ∈ Icc (-a) a := by
    simp only [mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  by_cases h : x ∈ Icc (-a) a
  · simp only [windowRepresentative, indicator_of_mem h, indicator_of_mem (hi.mpr h)]
    exact hx
  · simp [windowRepresentative, h, hi]

end ThetaTrial.Paper.FormDomain
