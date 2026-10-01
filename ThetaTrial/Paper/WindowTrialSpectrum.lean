import ThetaTrial.Paper.WindowSpectrum
import ThetaTrial.Paper.ThetaAvgSpaceVectors

/-!
# Physical trial spaces and the window spectrum

A supported `L2` trial space with canonical representatives in the form
domain lifts uniquely to the Fourier graph. The lift is a linear
equivalence, so its dimension and all physical energy bounds are preserved.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex Set Filter MeasureTheory
open scoped InnerProductSpace Topology

namespace ThetaTrial.Paper

open FormDomain WindowFormAssembly

def graphTrial (a : ℝ) (S : Submodule ℂ L2) : Submodule ℂ (windowFormGraph a) :=
  S.comap (physicalInclusion a).toLinearMap

def graphTrialMap (a : ℝ) (S : Submodule ℂ L2) : graphTrial a S →ₗ[ℂ] S :=
  (((physicalInclusion a).toLinearMap).domRestrict (graphTrial a S)).codRestrict S
    (fun v => v.property)

theorem graphTrialMap_injective (a : ℝ) (S : Submodule ℂ L2) :
    Function.Injective (graphTrialMap a S) := by
  intro v w h
  apply Subtype.ext
  exact physicalInclusion_injective a (congrArg Subtype.val h)

theorem graphTrialMap_surjective (a : ℝ) (S : Submodule ℂ L2)
    (hs : S ≤ windowL2 a)
    (hdom : ∀ f ∈ S, InWindowFormDomain a (windowRepresentative a f)) :
    Function.Surjective (graphTrialMap a S) := by
  intro f
  have hf := hdom f f.property
  obtain ⟨g, hg⟩ := InWindowFormDomain.exists_graph hf
  let p : windowFormGraph a := ⟨WithLp.toLp 2 (hf.2.1.toLp (windowRepresentative a f), g), hg⟩
  have hp : physicalInclusion a p = (f : L2) :=
    windowRepresentative_toLp (hs f.property)
  have hpS : p ∈ graphTrial a S := by
    change physicalInclusion a p ∈ S
    rw [hp]
    exact f.property
  refine ⟨⟨p, hpS⟩, ?_⟩
  exact Subtype.ext hp

def graphTrialEquiv (a : ℝ) (S : Submodule ℂ L2)
    (hs : S ≤ windowL2 a)
    (hdom : ∀ f ∈ S, InWindowFormDomain a (windowRepresentative a f)) :
    graphTrial a S ≃ₗ[ℂ] S :=
  LinearEquiv.ofBijective (graphTrialMap a S)
    ⟨graphTrialMap_injective a S, graphTrialMap_surjective a S hs hdom⟩

theorem graphTrial_finrank (a : ℝ) (S : Submodule ℂ L2)
    (hs : S ≤ windowL2 a)
    (hdom : ∀ f ∈ S, InWindowFormDomain a (windowRepresentative a f)) :
    Module.finrank ℂ (graphTrial a S) = Module.finrank ℂ S :=
  (graphTrialEquiv a S hs hdom).finrank_eq

theorem graphTrial_finiteDimensional (a : ℝ) (S : Submodule ℂ L2)
    [FiniteDimensional ℂ S] : FiniteDimensional ℂ (graphTrial a S) :=
  FiniteDimensional.of_injective (graphTrialMap a S) (graphTrialMap_injective a S)

/-- Min--max on a physical `L2` trial space. Domain membership is
used only to construct its unique graph lift. -/
theorem windowEigenvalue_le_of_L2_trial {a : ℝ} (ha : 0 < a)
    (S : Submodule ℂ L2) [FiniteDimensional ℂ S]
    (hs : S ≤ windowL2 a)
    (hdom : ∀ f ∈ S, InWindowFormDomain a (windowRepresentative a f))
    (n : ℕ) (hdim : n < Module.finrank ℂ S) (L : ℝ)
    (hbound : ∀ f ∈ S, fullWeilForm (windowRepresentative a f) ≤ L * ‖f‖ ^ 2) :
    windowEigenvalue a n ≤ L := by
  letI := graphTrial_finiteDimensional a S
  apply windowEigenvalue_le_of_form_trial ha (graphTrial a S) n
    (by rwa [graphTrial_finrank a S hs hdom]) L
  intro v hv
  exact hbound (physicalInclusion a v) hv

/-- Theorem `avg:spaces` bounds the corresponding window eigenvalue. The index
`k` here is `k+1` in the paper. -/
theorem thetaAvg_eigenvalue_spaces :
    ∃ C₁ > 0, ∃ C₂ > 0, ∃ a₁ : ℝ, 1 ≤ a₁ ∧
      ∀ a ≥ a₁, ∀ k : ℕ,
        (k : ℝ) * (Real.log ((k : ℝ) + 1) + 4 * a) +
          C₁ * ((k : ℝ) + a) ≤ scaleT a →
        windowEigenvalue a k ≤ Real.exp (-2 * scaleT a + 8 * (k : ℝ) * a +
          2 * (k : ℝ) * Real.log ((k : ℝ) + 1) + C₂ * ((k : ℝ) + a)) := by
  obtain ⟨C₁, hC₁, C₂, hC₂, a₁, ha₁, hall⟩ := thetaAvg_spaces_L2
  refine ⟨C₁, hC₁, C₂, hC₂, a₁, ha₁, ?_⟩
  intro a haa k hk
  obtain ⟨ha0, hZ, hspace⟩ := hall a haa
  obtain ⟨hdim, hbound⟩ := hspace k hk
  let S := thetaAvgTrialSpace a ha0 hZ k
  letI : FiniteDimensional ℂ S := FiniteDimensional.of_finrank_eq_succ hdim
  apply windowEigenvalue_le_of_L2_trial (by linarith : 0 < a) S
    (fun _ hv => thetaAvgTrialSpace_mem_windowL2 hv)
    (fun _ hv => (hbound _ hv).1) k (by
      change k < Module.finrank ℂ S
      have hd : Module.finrank ℂ S = k + 1 := hdim
      rw [hd]
      exact Nat.lt_succ_self k)
  intro v hv
  exact (le_abs_self _).trans (hbound v hv).2.2.1

/-- Corollary `avg:large-space` bounds every eigenvalue up to that index. -/
theorem thetaAvg_large_eigenvalue_space :
    ∀ᶠ a : ℝ in atTop, ∀ n ≤ TrialBounds.selectedDegree a,
      windowEigenvalue a n ≤ Real.exp (-scaleT a) := by
  filter_upwards [thetaAvg_large_space_L2, eventually_gt_atTop (0 : ℝ)] with a hspace ha
  obtain ⟨ha0, hZ, hdim, hbound⟩ := hspace
  let k := TrialBounds.selectedDegree a
  let S := thetaAvgTrialSpace a ha0 hZ k
  letI : FiniteDimensional ℂ S := FiniteDimensional.of_finrank_eq_succ hdim
  have hk : windowEigenvalue a k ≤ Real.exp (-scaleT a) := by
    apply windowEigenvalue_le_of_L2_trial ha S
      (fun _ hv => thetaAvgTrialSpace_mem_windowL2 hv)
      (fun _ hv => (hbound _ hv).1) k (by
        change k < Module.finrank ℂ S
        have hd : Module.finrank ℂ S = k + 1 := hdim
        rw [hd]
        exact Nat.lt_succ_self k)
    intro v hv
    exact (le_abs_self _).trans (hbound v hv).2.2.1
  intro n hn
  exact ((windowEigenvalue_monotone a) hn).trans hk

end ThetaTrial.Paper
