import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
# Restricting a dense compact form embedding to an involution sector

Density of the sector embedding follows from the averaging projection
`(id + ε R) / 2`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace ThetaTrial.Paper.ParityFormEmbedding

variable {V H : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℂ V]
variable [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- The eigenspace of a continuous linear involution with eigenvalue `ε`. -/
def sector (R : V →L[ℂ] V) (ε : ℂ) : Submodule ℂ V :=
  (R - ε • ContinuousLinearMap.id ℂ V).ker

@[simp] theorem mem_sector (R : V →L[ℂ] V) (ε : ℂ) (v : V) :
    v ∈ sector R ε ↔ R v = ε • v := by
  simp [sector, sub_eq_zero]

theorem sector_isClosed (R : V →L[ℂ] V) (ε : ℂ) :
    IsClosed (sector R ε : Set V) :=
  (R - ε • ContinuousLinearMap.id ℂ V).isClosed_ker

instance sector_completeSpace [CompleteSpace V] (R : V →L[ℂ] V) (ε : ℂ) :
    CompleteSpace (sector R ε) :=
  (sector_isClosed R ε).completeSpace_coe

/-- Averaging onto either involution sector. -/
def projection (R : V →L[ℂ] V) (ε : ℂ) : V →L[ℂ] V :=
  (2 : ℂ)⁻¹ • (ContinuousLinearMap.id ℂ V + ε • R)

@[simp] theorem projection_apply (R : V →L[ℂ] V) (ε : ℂ) (v : V) :
    projection R ε v = (2 : ℂ)⁻¹ • (v + ε • R v) := rfl

theorem projection_mem (R : V →L[ℂ] V) (hR : Function.Involutive R)
    (ε : ℂ) (hε : ε ^ 2 = 1) (v : V) :
    projection R ε v ∈ sector R ε := by
  rw [mem_sector, projection_apply]
  have he : ε * ε = 1 := by simpa only [pow_two] using hε
  simp only [map_smul, map_add]
  rw [hR v]
  simp only [smul_add, smul_smul]
  rw [mul_left_comm ε (2 : ℂ)⁻¹ ε, he, mul_one]
  module

theorem projection_eq_self (R : V →L[ℂ] V) (ε : ℂ) (hε : ε ^ 2 = 1)
    {v : V} (hv : v ∈ sector R ε) : projection R ε v = v := by
  rw [mem_sector] at hv
  have he : ε * ε = 1 := by simpa only [pow_two] using hε
  simp only [projection_apply, hv, smul_smul, he, one_smul]
  module

def projectionToSector (R : V →L[ℂ] V) (hR : Function.Involutive R)
    (ε : ℂ) (hε : ε ^ 2 = 1) : V →L[ℂ] sector R ε :=
  (projection R ε).codRestrict (sector R ε) (projection_mem R hR ε hε)

@[simp] theorem coe_projectionToSector (R : V →L[ℂ] V) (hR : Function.Involutive R)
    (ε : ℂ) (hε : ε ^ 2 = 1) (v : V) :
    (projectionToSector R hR ε hε v : V) = projection R ε v := rfl

theorem projectionToSector_surjective (R : V →L[ℂ] V)
    (hR : Function.Involutive R) (ε : ℂ) (hε : ε ^ 2 = 1) :
    Function.Surjective (projectionToSector R hR ε hε) := by
  intro v
  refine ⟨v.val, Subtype.ext ?_⟩
  exact projection_eq_self R ε hε v.property

variable (RV : V →L[ℂ] V) (R_H : H →L[ℂ] H) (J : V →L[ℂ] H)
variable (hcomm : ∀ v, J (RV v) = R_H (J v))
include hcomm

theorem map_mem_sector (ε : ℂ) {v : V} (hv : v ∈ sector RV ε) :
    J v ∈ sector R_H ε := by
  rw [mem_sector] at hv ⊢
  rw [← hcomm, hv, map_smul]

/-- The embedding with both its domain and codomain restricted to a sector. -/
def inclusion (ε : ℂ) : sector RV ε →L[ℂ] sector R_H ε :=
  J.restrict (fun _ hv => map_mem_sector RV R_H J hcomm ε hv)

@[simp] theorem coe_inclusion (ε : ℂ) (v : sector RV ε) :
    (inclusion RV R_H J hcomm ε v : H) = J v := rfl

theorem inclusion_injective (hJi : Function.Injective J) (ε : ℂ) :
    Function.Injective (inclusion RV R_H J hcomm ε) := by
  intro v w hvw
  exact Subtype.ext (hJi (congrArg Subtype.val hvw))

theorem map_projection (ε : ℂ) (v : V) :
    J (projection RV ε v) = projection R_H ε (J v) := by
  simp only [projection_apply, map_smul, map_add, hcomm]

/-- Density in each sector follows from density of the full embedding and the
averaging projections. -/
theorem inclusion_denseRange (hV : Function.Involutive RV)
    (hH : Function.Involutive R_H) (hJ : DenseRange J)
    (ε : ℂ) (hε : ε ^ 2 = 1) :
    DenseRange (inclusion RV R_H J hcomm ε) := by
  have hd : DenseRange ((projectionToSector R_H hH ε hε) ∘ J) :=
    (projectionToSector_surjective R_H hH ε hε).denseRange.comp hJ
      (projectionToSector R_H hH ε hε).continuous
  apply hd.mono
  rintro _ ⟨v, rfl⟩
  refine ⟨projectionToSector RV hV ε hε v, Subtype.ext ?_⟩
  exact map_projection RV R_H J hcomm ε v

theorem inclusion_isCompactOperator (hJ : IsCompactOperator J) (ε : ℂ) :
    IsCompactOperator (inclusion RV R_H J hcomm ε) := by
  exact (hJ.comp_clm (sector RV ε).subtypeL).codRestrict
    (fun v => map_mem_sector RV R_H J hcomm ε v.property) (sector_isClosed R_H ε)

end ThetaTrial.Paper.ParityFormEmbedding
