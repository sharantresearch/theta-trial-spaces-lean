import ThetaTrial.Paper.WindowFormAssembly
import ThetaTrial.Paper.L2Reflection
import ThetaTrial.Paper.ReflectionPairing
import ThetaTrial.Paper.ParityFormEmbedding

/-! Even and odd restrictions of the Weil form.
Sector density is derived by averaging the constructed reflection. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Complex MeasureTheory Set Filter
open scoped ComplexConjugate

namespace ThetaTrial.Paper.WindowParity
open FormDomain WindowFormAssembly ParityFormEmbedding Radical

def graphReflectionCLM (a : ℝ) : windowFormGraph a →L[ℂ] windowFormGraph a :=
  (graphReflection a).toContinuousLinearEquiv.toContinuousLinearMap

def windowReflectionCLM (a : ℝ) : windowL2 a →L[ℂ] windowL2 a :=
  (windowReflection a).toContinuousLinearEquiv.toContinuousLinearMap

abbrev graphSector (a : ℝ) (ε : ℂ) := sector (graphReflectionCLM a) ε
abbrev physicalSector (a : ℝ) (ε : ℂ) := sector (windowReflectionCLM a) ε

instance graphSector_completeSpace (a : ℝ) (ε : ℂ) : CompleteSpace (graphSector a ε) :=
  ParityFormEmbedding.sector_completeSpace _ _

instance physicalSector_completeSpace (a : ℝ) (ε : ℂ) : CompleteSpace (physicalSector a ε) :=
  ParityFormEmbedding.sector_completeSpace _ _

instance physicalSector_pmapStar (a : ℝ) (ε : ℂ) :
    Star (physicalSector a ε →ₗ.[ℂ] physicalSector a ε) :=
  @LinearPMap.instStar ℂ (physicalSector a ε) _ _ _ _

theorem physicalSector_one_mem_even {a : ℝ} (f : physicalSector a 1) :
    f.val.val ∈ evenL2 := by
  apply (mem_evenL2_iff _).mpr
  have h := (mem_sector (windowReflectionCLM a) 1 f.val).mp f.property
  have he := congrArg Subtype.val h
  change l2Reflection f.val.val = (1 : ℂ) • f.val.val at he
  simpa only [one_smul] using he

theorem physicalSector_neg_one_mem_odd {a : ℝ} (f : physicalSector a (-1)) :
    f.val.val ∈ oddL2 := by
  apply (mem_oddL2_iff _).mpr
  have h := (mem_sector (windowReflectionCLM a) (-1) f.val).mp f.property
  have he := congrArg Subtype.val h
  change l2Reflection f.val.val = (-1 : ℂ) • f.val.val at he
  simpa only [neg_one_smul] using he

def evenSectorEquiv (a : ℝ) : evenWindowL2 a ≃ₗᵢ[ℂ] physicalSector a 1 where
  toLinearEquiv :=
    { toFun := fun f => ⟨⟨f.val, f.property.1⟩, by
        apply (mem_sector _ _ _).mpr
        apply Subtype.ext
        change l2Reflection f.val = (1 : ℂ) • f.val
        simpa only [one_smul] using (mem_evenL2_iff f.val).mp f.property.2⟩
      invFun := fun f => ⟨f.val.val, f.val.property, physicalSector_one_mem_even f⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  norm_map' := fun _ => rfl

def oddSectorEquiv (a : ℝ) : oddWindowL2 a ≃ₗᵢ[ℂ] physicalSector a (-1) where
  toLinearEquiv :=
    { toFun := fun f => ⟨⟨f.val, f.property.1⟩, by
        apply (mem_sector _ _ _).mpr
        apply Subtype.ext
        change l2Reflection f.val = (-1 : ℂ) • f.val
        simpa only [neg_one_smul] using (mem_oddL2_iff f.val).mp f.property.2⟩
      invFun := fun f => ⟨f.val.val, f.val.property, physicalSector_neg_one_mem_odd f⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  norm_map' := fun _ => rfl

theorem reflection_intertwining (a : ℝ) (p : windowFormGraph a) :
    windowInclusion a (graphReflectionCLM a p) = windowReflectionCLM a (windowInclusion a p) :=
  windowInclusion_graphReflection a p

def parityInclusion (a : ℝ) (ε : ℂ) : graphSector a ε →L[ℂ] physicalSector a ε :=
  inclusion (graphReflectionCLM a) (windowReflectionCLM a) (windowInclusion a)
    (reflection_intertwining a) ε

theorem parityInclusion_injective (a : ℝ) (ε : ℂ) : Function.Injective (parityInclusion a ε) :=
  inclusion_injective _ _ _ (reflection_intertwining a) (windowInclusion_injective a) ε

theorem parityInclusion_denseRange (a : ℝ) (ε : ℂ) (hε : ε ^ 2 = 1) :
    DenseRange (parityInclusion a ε) :=
  inclusion_denseRange _ _ _ (reflection_intertwining a) (graphReflection_involutive a)
    (windowReflection_involutive a) (windowInclusion_denseRange a) ε hε

theorem parityInclusion_isCompactOperator (a : ℝ) (ε : ℂ) :
    IsCompactOperator (parityInclusion a ε) :=
  inclusion_isCompactOperator _ _ _ (reflection_intertwining a)
    (windowInclusion_isCompactOperator a) ε

theorem representative_reflection (a : ℝ) (p : windowFormGraph a) :
    representative a (graphReflection a p) =ᵐ[volume] reflect (representative a p) := by
  filter_upwards [l2Reflection_coeFn p.val.fst] with u hu
  change (Icc (-a) a).indicator (fun u => l2Reflection p.val.fst u) u =
    (Icc (-a) a).indicator (fun u => p.val.fst u) (-u)
  have hmem : u ∈ Icc (-a) a ↔ -u ∈ Icc (-a) a := by
    constructor <;> rintro ⟨hl, hr⟩ <;> constructor <;> linarith
  by_cases hin : u ∈ Icc (-a) a
  · simpa only [Set.indicator_of_mem hin, Set.indicator_of_mem (hmem.mp hin)] using hu
  · simp [hin, (not_congr hmem).mp hin]

theorem rawForm_reflection (a : ℝ) (p q : windowFormGraph a) :
    rawForm a (graphReflection a p) (graphReflection a q) = rawForm a p q := by
  change fullPairing (representative a (graphReflection a q))
    (representative a (graphReflection a p)) = _
  rw [fullPairing_congr (representative_reflection a q) (representative_reflection a p),
    fullPairing_reflect]
  rfl

theorem shiftedForm_reflection (a : ℝ) (p q : windowFormGraph a) :
    shiftedForm a (graphReflection a p) (graphReflection a q) = shiftedForm a p q := by
  simp only [shiftedForm_apply, rawForm_reflection, windowInclusion_graphReflection,
    LinearIsometryEquiv.inner_map_map]

def parityRawForm (a : ℝ) (ε : ℂ) : graphSector a ε →ₗ⋆[ℂ] graphSector a ε →ₗ[ℂ] ℂ :=
  (rawForm a).domRestrict₁₂ (graphSector a ε) (graphSector a ε)

theorem parityRawForm_hermitian (a : ℝ) (ε : ℂ) : (parityRawForm a ε).IsSymm :=
  (rawForm_hermitian a).domRestrict _

theorem parityRawForm_diagonal_bound (a : ℝ) (ε : ℂ) (p : graphSector a ε) :
    |(parityRawForm a ε p p).re| ≤ (perturbationConstant a + 1) * ‖p‖ ^ 2 :=
  rawForm_diagonal_bound a p.val

def parityContinuousForm (a : ℝ) (ε : ℂ) :
    graphSector a ε →L⋆[ℂ] graphSector a ε →L[ℂ] ℂ :=
  (parityRawForm a ε).mkContinuous₂ (4 * (perturbationConstant a + 1))
    (sesquilinear_norm_le_of_diagonal (parityRawForm a ε) (parityRawForm_hermitian a ε)
      (by linarith [perturbationConstant_pos a]) (parityRawForm_diagonal_bound a ε))

def parityInnerForm (a : ℝ) (ε : ℂ) :
    graphSector a ε →L⋆[ℂ] graphSector a ε →L[ℂ] ℂ :=
  (ContinuousLinearMap.toSesqForm (𝕜 := ℂ) (E := graphSector a ε)
    (E' := physicalSector a ε) (parityInclusion a ε)).comp (parityInclusion a ε)

def parityShiftedForm (a : ℝ) (ε : ℂ) :
    graphSector a ε →L⋆[ℂ] graphSector a ε →L[ℂ] ℂ :=
  parityContinuousForm a ε + (shiftConstant a : ℂ) • parityInnerForm a ε

theorem parityShiftedForm_apply (a : ℝ) (ε : ℂ) (p q : graphSector a ε) :
    parityShiftedForm a ε p q = shiftedForm a p.val q.val := rfl

theorem parityShiftedForm_hermitian (a : ℝ) (ε : ℂ) (p q : graphSector a ε) :
    conj (parityShiftedForm a ε q p) = parityShiftedForm a ε p q :=
  shiftedForm_hermitian a p.val q.val

theorem parityShiftedForm_coercive (a : ℝ) (ε : ℂ) : ∃ m : ℝ, 0 < m ∧
    ∀ p : graphSector a ε, m * ‖p‖ ^ 2 ≤ (parityShiftedForm a ε p p).re := by
  obtain ⟨m, hm, h⟩ := shiftedForm_coercive a
  exact ⟨m, hm, fun p => h p.val⟩

theorem rawForm_even_odd_eq_zero (a : ℝ) (p : graphSector a 1) (q : graphSector a (-1)) :
    rawForm a p.val q.val = 0 := by
  have hp : graphReflection a p.val = p.val := by
    have h := (mem_sector (graphReflectionCLM a) 1 p.val).mp p.property
    change graphReflection a p.val = (1 : ℂ) • p.val at h
    simpa only [one_smul] using h
  have hq : graphReflection a q.val = -q.val := by
    have h := (mem_sector (graphReflectionCLM a) (-1) q.val).mp q.property
    change graphReflection a q.val = (-1 : ℂ) • q.val at h
    simpa only [neg_one_smul] using h
  have h := rawForm_reflection a p.val q.val
  rw [hp, hq, map_neg] at h
  exact neg_eq_self.mp h

#print axioms shiftedForm_reflection
#print axioms rawForm_even_odd_eq_zero


end ThetaTrial.Paper.WindowParity

