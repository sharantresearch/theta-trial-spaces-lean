import ThetaTrial.Paper.WindowParitySpectrum
import ThetaTrial.Paper.WindowOperatorParity

/-!
# The parity operators are restrictions of the same full Weil operator

The full coercive solution of a parity source remains in the corresponding
graph sector. Uniqueness of the restricted Riesz solution therefore
identifies the two resolvents. Both inverse identities then give
the exact domain and value identities for the named unbounded operators.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 600000
open Complex
open scoped InnerProductSpace

namespace ThetaTrial.Paper
open FormDomain WindowFormAssembly WindowParity CoerciveFormRepresentation
open InvariantFormReflection ParityFormEmbedding

attribute [local irreducible] ParityFormEmbedding.sector
  graphReflectionCLM windowReflectionCLM parityInclusion

@[simp] theorem parityInclusion_coe (a : ℝ) (ε : ℂ) (v : graphSector a ε) :
    (parityInclusion a ε v : windowL2 a) = windowInclusion a v.val := by
  unfold parityInclusion
  rfl

theorem windowAdjoint_preserves_sector (a : ℝ) (ε : ℂ) {f : windowL2 a}
    (hf : f ∈ physicalSector a ε) :
    (windowInclusion a).adjoint f ∈ graphSector a ε := by
  rw [mem_sector] at hf ⊢
  unfold windowReflectionCLM at hf
  unfold graphReflectionCLM
  change windowReflection a f = ε • f at hf
  change graphReflection a ((windowInclusion a).adjoint f) =
    ε • (windowInclusion a).adjoint f
  calc
    _ = (windowInclusion a).adjoint (windowReflection a f) :=
      (adjoint_intertwines (graphReflection a) (windowReflection a) (windowInclusion a)
        (windowInclusion_graphReflection a) f).symm
    _ = (windowInclusion a).adjoint (ε • f) := congrArg (windowInclusion a).adjoint hf
    _ = _ := map_smul _ _ _

theorem windowFormInverse_preserves_sector (a : ℝ) (ε : ℂ) {v : windowFormGraph a}
    (hv : v ∈ graphSector a ε) :
    coerciveInverse (windowFormOperator a) (windowFormOperator_coercive a) v ∈
      graphSector a ε := by
  have hcomm (w : windowFormGraph a) :
      coerciveInverse (windowFormOperator a) (windowFormOperator_coercive a)
          (graphReflection a w) =
        graphReflection a
          (coerciveInverse (windowFormOperator a) (windowFormOperator_coercive a) w) :=
    formInverse_commutes (graphReflection a) (shiftedForm a) (windowFormOperator_coercive a)
      (shiftedForm_reflection a) w
  rw [mem_sector] at hv ⊢
  unfold graphReflectionCLM at hv ⊢
  change graphReflection a v = ε • v at hv
  change graphReflection a
      (coerciveInverse (windowFormOperator a) (windowFormOperator_coercive a) v) = _
  calc
    _ = coerciveInverse (windowFormOperator a) (windowFormOperator_coercive a)
        (graphReflection a v) := (hcomm v).symm
    _ = coerciveInverse (windowFormOperator a) (windowFormOperator_coercive a) (ε • v) :=
      congrArg (coerciveInverse (windowFormOperator a) (windowFormOperator_coercive a)) hv
    _ = _ := map_smul _ _ _

/-- The full coercive solution in the complete graph space. -/
def windowFormSolution (a : ℝ) : windowL2 a →L[ℂ] windowFormGraph a :=
  (coerciveInverse (windowFormOperator a) (windowFormOperator_coercive a)).comp
    (windowInclusion a).adjoint

@[simp] theorem windowFormSolution_apply (a : ℝ) (f : windowL2 a) :
    windowFormSolution a f =
      coerciveInverse (windowFormOperator a) (windowFormOperator_coercive a)
        ((windowInclusion a).adjoint f) := rfl

theorem windowFormSolution_mem_sector (a : ℝ) (ε : ℂ) (f : physicalSector a ε) :
    windowFormSolution a f.val ∈ graphSector a ε :=
  windowFormInverse_preserves_sector a ε (windowAdjoint_preserves_sector a ε f.property)

theorem windowFormSolution_apply_operator (a : ℝ) (f : windowL2 a) :
    windowFormOperator a (windowFormSolution a f) = (windowInclusion a).adjoint f :=
  coercive_apply_inverse (windowFormOperator a) (windowFormOperator_coercive a)
    ((windowInclusion a).adjoint f)

theorem parityFormOperator_inner_full (a : ℝ) (ε : ℂ) (v w : graphSector a ε) :
    inner ℂ (parityFormOperator a ε v) w =
      inner ℂ (windowFormOperator a v.val) w.val := by
  calc
    _ = parityShiftedForm a ε v w :=
      @formOperator_inner (graphSector a ε) inferInstance inferInstance inferInstance
        (parityShiftedForm a ε) v w
    _ = shiftedForm a v.val w.val := parityShiftedForm_apply a ε v w
    _ = _ := (formOperator_inner (shiftedForm a) v.val w.val).symm

/-- The restricted Riesz solution is the full solution, with its proved
sector membership. This identifies solutions before applying the embedding. -/
theorem parityFormSolution_coe (a : ℝ) (ε : ℂ) (f : physicalSector a ε) :
    (@coerciveInverse (graphSector a ε) inferInstance inferInstance inferInstance
        (parityFormOperator a ε) (parityFormOperator_coercive a ε)
        (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := graphSector a ε) (F := physicalSector a ε)
          (parityInclusion a ε) f) : windowFormGraph a) =
      windowFormSolution a f.val := by
  let v : graphSector a ε :=
    ⟨windowFormSolution a f.val, windowFormSolution_mem_sector a ε f⟩
  have hv : parityFormOperator a ε v =
      ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := graphSector a ε) (F := physicalSector a ε)
        (parityInclusion a ε) f := by
    apply ext_inner_right ℂ (E := graphSector a ε)
    intro w
    calc
      inner ℂ (parityFormOperator a ε v) w =
          inner ℂ (windowFormOperator a v.val) w.val := parityFormOperator_inner_full a ε v w
      _ = inner ℂ ((windowInclusion a).adjoint f.val) w.val :=
        congrArg (fun z : windowFormGraph a => inner ℂ z w.val)
          (windowFormSolution_apply_operator a f.val)
      _ = inner ℂ f.val (windowInclusion a w.val) :=
        (windowInclusion a).adjoint_inner_left w.val f.val
      _ = inner ℂ f (parityInclusion a ε w) := by
        change inner ℂ f.val (windowInclusion a w.val) =
          inner ℂ f.val (parityInclusion a ε w : windowL2 a)
        rw [parityInclusion_coe]
      _ = inner ℂ (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := graphSector a ε)
          (F := physicalSector a ε) (parityInclusion a ε) f) w :=
        (ContinuousLinearMap.adjoint_inner_left (𝕜 := ℂ) (E := graphSector a ε)
          (F := physicalSector a ε) (parityInclusion a ε) w f).symm
  have he : @coerciveInverse (graphSector a ε) inferInstance inferInstance inferInstance
      (parityFormOperator a ε) (parityFormOperator_coercive a ε)
      (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := graphSector a ε)
        (F := physicalSector a ε) (parityInclusion a ε) f) = v := by
    exact (congrArg (@coerciveInverse (graphSector a ε) inferInstance inferInstance inferInstance
      (parityFormOperator a ε) (parityFormOperator_coercive a ε)) hv).symm.trans
        (@coercive_inverse_apply (graphSector a ε) inferInstance inferInstance inferInstance
          (parityFormOperator a ε) (parityFormOperator_coercive a ε) v)
  exact congrArg (fun z : graphSector a ε => z.val) he

/-- The named resolvent of the parity form. -/
def parityResolvent (a : ℝ) (ε : ℂ) : physicalSector a ε →L[ℂ] physicalSector a ε :=
  @coerciveResolvent (graphSector a ε) (physicalSector a ε)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (parityInclusion a ε) (parityFormOperator a ε)
    (parityFormOperator_coercive a ε)

@[simp] theorem parityResolvent_coe (a : ℝ) (ε : ℂ) (f : physicalSector a ε) :
    (parityResolvent a ε f : windowL2 a) = windowResolvent a f.val := by
  have h := @coerciveResolvent_apply (graphSector a ε) (physicalSector a ε)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (parityInclusion a ε) (parityFormOperator a ε) (parityFormOperator_coercive a ε) f
  have hc := congrArg (fun z : physicalSector a ε => z.val) h
  rw [parityInclusion_coe, parityFormSolution_coe] at hc
  exact hc

theorem parityWeilOperator_domain (a : ℝ) (ε : ℂ) (hε : ε ^ 2 = 1) :
    (parityWeilOperator a ε hε).domain = (parityResolvent a ε).range := rfl

theorem parityWeilOperator_left_resolvent (a : ℝ) (ε : ℂ) (hε : ε ^ 2 = 1)
    (x : (parityWeilOperator a ε hε).domain) :
    parityResolvent a ε
      (parityWeilOperator a ε hε x + (shiftConstant a : ℂ) • (x : physicalSector a ε)) = x :=
  @coerciveAssociatedOperator_left_resolvent (graphSector a ε) (physicalSector a ε)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (parityInclusion a ε)
    (parityInclusion_injective a ε) (parityInclusion_denseRange a ε hε)
    (parityFormOperator a ε) (parityFormOperator_coercive a ε) (shiftConstant a) x

/-- Equality of operator domains under the sector inclusion. -/
theorem parityWeilOperator_domain_iff (a : ℝ) (ε : ℂ) (hε : ε ^ 2 = 1)
    (x : physicalSector a ε) :
    x ∈ (parityWeilOperator a ε hε).domain ↔
      x.val ∈ (windowWeilOperator a).domain := by
  change x ∈ (parityResolvent a ε).range ↔ x.val ∈ (windowResolvent a).range
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f.val, ?_⟩
    exact (parityResolvent_coe a ε f).symm.trans
      (congrArg (fun z : physicalSector a ε => z.val) hf)
  · intro hx
    let y : (windowWeilOperator a).domain := ⟨x.val, hx⟩
    let g : physicalSector a ε :=
      ⟨windowWeilOperator a y + (shiftConstant a : ℂ) • x.val,
        (physicalSector a ε).add_mem (windowWeilOperator_preserves_sector a ε y x.property)
          ((physicalSector a ε).smul_mem (shiftConstant a : ℂ) x.property)⟩
    refine ⟨g, Subtype.ext ?_⟩
    exact (parityResolvent_coe a ε g).trans (windowWeilOperator_left_resolvent a y)

/-- Equality of operator values after coercing the parity space. -/
theorem parityWeilOperator_coe (a : ℝ) (ε : ℂ) (hε : ε ^ 2 = 1)
    (x : (parityWeilOperator a ε hε).domain) :
    (parityWeilOperator a ε hε x : windowL2 a) =
      windowWeilOperator a
        ⟨x.val.val, (parityWeilOperator_domain_iff a ε hε x.val).mp x.property⟩ := by
  let y : (windowWeilOperator a).domain :=
    ⟨x.val.val, (parityWeilOperator_domain_iff a ε hε x.val).mp x.property⟩
  have hp := congrArg Subtype.val (parityWeilOperator_left_resolvent a ε hε x)
  rw [parityResolvent_coe] at hp
  change windowResolvent a
    ((parityWeilOperator a ε hε x : windowL2 a) + (shiftConstant a : ℂ) • x.val.val) =
      x.val.val at hp
  have hf := windowWeilOperator_left_resolvent a y
  have he := (windowResolvent_injective a) (hp.trans hf.symm)
  exact add_right_cancel he

/-- Exact equality of the operator graphs under the sector inclusion.
This identifies the named parity operator with the full operator's restriction. -/
theorem parityWeilOperator_graph_iff (a : ℝ) (ε : ℂ) (hε : ε ^ 2 = 1)
    (x y : physicalSector a ε) :
    (∃ hx : x ∈ (parityWeilOperator a ε hε).domain,
      parityWeilOperator a ε hε ⟨x, hx⟩ = y) ↔
    (∃ hx : x.val ∈ (windowWeilOperator a).domain,
      windowWeilOperator a ⟨x.val, hx⟩ = y.val) := by
  constructor
  · rintro ⟨hx, hxy⟩
    refine ⟨(parityWeilOperator_domain_iff a ε hε x).mp hx, ?_⟩
    rw [← parityWeilOperator_coe a ε hε ⟨x, hx⟩, hxy]
  · rintro ⟨hx, hxy⟩
    refine ⟨(parityWeilOperator_domain_iff a ε hε x).mpr hx, ?_⟩
    apply Subtype.ext
    rw [parityWeilOperator_coe]
    exact hxy

/-- Equality of domain submodules, rather than only one inclusion. -/
theorem parityWeilOperator_domain_eq_comap (a : ℝ) (ε : ℂ) (hε : ε ^ 2 = 1) :
    (parityWeilOperator a ε hε).domain =
      (windowWeilOperator a).domain.comap (physicalSector a ε).subtype := by
  ext x
  exact parityWeilOperator_domain_iff a ε hε x

/-- The named parity operator's graph is exactly the full graph pulled
back along the two sector inclusions. -/
theorem parityWeilOperator_graph_eq_comap (a : ℝ) (ε : ℂ) (hε : ε ^ 2 = 1) :
    (parityWeilOperator a ε hε).graph =
      (windowWeilOperator a).graph.comap
        ((physicalSector a ε).subtype.prodMap (physicalSector a ε).subtype) := by
  ext ⟨x, y⟩
  change (x, y) ∈ (parityWeilOperator a ε hε).graph ↔
    (x.val, y.val) ∈ (windowWeilOperator a).graph
  simpa only [LinearPMap.mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left] using
    parityWeilOperator_graph_iff a ε hε x y

theorem parityResolvent_compact (a : ℝ) (ε : ℂ) : IsCompactOperator (parityResolvent a ε) :=
  @coerciveResolvent_compact (graphSector a ε) (physicalSector a ε)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (parityInclusion a ε) (parityInclusion_isCompactOperator a ε)
    (parityFormOperator a ε) (parityFormOperator_coercive a ε)

theorem parityWeilOperator_closed (a : ℝ) (ε : ℂ) (hε : ε ^ 2 = 1) :
    (parityWeilOperator a ε hε).IsClosed :=
  IsSelfAdjoint.isClosed (𝕜 := ℂ) (E := physicalSector a ε)
    (parityWeilOperator_selfAdjoint a ε hε)

theorem parityWeilOperator_semibounded (a : ℝ) (ε : ℂ) (hε : ε ^ 2 = 1)
    (x : (parityWeilOperator a ε hε).domain) :
    -shiftConstant a * ‖(x : physicalSector a ε)‖ ^ 2 ≤
      (inner ℂ (parityWeilOperator a ε hε x) (x : physicalSector a ε)).re :=
  @coerciveAssociatedOperator_semibounded (graphSector a ε) (physicalSector a ε)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (parityInclusion a ε) (parityInclusion_injective a ε) (parityInclusion_denseRange a ε hε)
    (parityFormOperator a ε) (parityFormOperator_coercive a ε) (shiftConstant a) x

end ThetaTrial.Paper
