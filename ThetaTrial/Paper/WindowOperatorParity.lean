import ThetaTrial.Paper.WindowOperator
import ThetaTrial.Paper.WindowParity
import ThetaTrial.Paper.InvariantFormReflection

/-! Reflection commutes with the full Weil operator, including its
unbounded domain. Thus parity is a reducing symmetry of this same operator. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex
open scoped ComplexConjugate

namespace ThetaTrial.Paper
open FormDomain WindowFormAssembly WindowParity InvariantFormReflection

theorem windowFormOperator_reflection (a : ℝ) (v : windowFormGraph a) :
    windowFormOperator a (graphReflection a v) = graphReflection a (windowFormOperator a v) :=
  formOperator_commutes (graphReflection a) (shiftedForm a) (shiftedForm_reflection a) v

theorem windowResolvent_reflection (a : ℝ) (f : windowL2 a) :
    windowResolvent a (windowReflection a f) = windowReflection a (windowResolvent a f) :=
  formResolvent_commutes (graphReflection a) (windowReflection a) (windowInclusion a)
    (windowInclusion_graphReflection a) (shiftedForm a) (windowFormOperator_coercive a)
    (shiftedForm_reflection a) f

theorem windowWeilOperator_reflection_domain (a : ℝ) {x : windowL2 a}
    (hx : x ∈ (windowWeilOperator a).domain) :
    windowReflection a x ∈ (windowWeilOperator a).domain :=
  formAssociatedOperator_domain_invariant (graphReflection a) (windowReflection a)
    (windowInclusion a) (windowInclusion_injective a) (windowInclusion_denseRange a)
    (windowInclusion_graphReflection a) (shiftedForm a) (windowFormOperator_coercive a)
    (shiftedForm_reflection a) (shiftConstant a) hx

theorem windowWeilOperator_reflection (a : ℝ) (x : (windowWeilOperator a).domain) :
    windowWeilOperator a
        ⟨windowReflection a x, windowWeilOperator_reflection_domain a x.property⟩ =
      windowReflection a (windowWeilOperator a x) :=
  formAssociatedOperator_commutes (graphReflection a) (windowReflection a)
    (windowInclusion a) (windowInclusion_injective a) (windowInclusion_denseRange a)
    (windowInclusion_graphReflection a) (shiftedForm a) (windowFormOperator_coercive a)
    (shiftedForm_reflection a) (shiftConstant a) x

theorem windowResolvent_preserves_sector (a : ℝ) (ε : ℂ) {f : windowL2 a}
    (hf : f ∈ physicalSector a ε) : windowResolvent a f ∈ physicalSector a ε := by
  rw [ParityFormEmbedding.mem_sector] at hf ⊢
  change windowReflection a f = ε • f at hf
  change windowReflection a (windowResolvent a f) = ε • windowResolvent a f
  rw [← windowResolvent_reflection, hf, map_smul]

theorem windowWeilOperator_preserves_sector (a : ℝ) (ε : ℂ)
    (x : (windowWeilOperator a).domain) (hx : (x : windowL2 a) ∈ physicalSector a ε) :
    windowWeilOperator a x ∈ physicalSector a ε := by
  rw [ParityFormEmbedding.mem_sector] at hx ⊢
  change windowReflection a (x : windowL2 a) = ε • (x : windowL2 a) at hx
  change windowReflection a (windowWeilOperator a x) = ε • windowWeilOperator a x
  rw [← windowWeilOperator_reflection]
  have he : (⟨windowReflection a (x : windowL2 a),
      windowWeilOperator_reflection_domain a x.property⟩ : (windowWeilOperator a).domain) =
      ε • x := Subtype.ext hx
  rw [he]
  exact (windowWeilOperator a).toFun.map_smul ε x

#print axioms windowResolvent_reflection
#print axioms windowWeilOperator_reflection_domain
#print axioms windowWeilOperator_reflection
#print axioms windowWeilOperator_preserves_sector

end ThetaTrial.Paper
