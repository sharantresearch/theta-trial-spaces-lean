import ThetaTrial.Paper.ThetaAvgPolynomialRegularity
import Mathlib.RingTheory.Polynomial.DegreeLT

/-! The theta-average polynomial trial space as a subspace of `L²`. The
dimension theorem here assumes a lower bound on the norm; that bound is proved
in `ThetaAvgPolynomialNorm`. -/

noncomputable section
open Complex MeasureTheory Set Polynomial Module

namespace ThetaTrial.Paper

theorem polynomialDerivative_add_left (P Q : ℂ[X]) (f : ℝ → ℂ) :
    polynomialDerivative (P + Q) f = polynomialDerivative P f + polynomialDerivative Q f := by
  funext u
  exact P.sum_add_index Q (fun j c => c * ((differentialOperator^[j]) f) u)
    (fun j => zero_mul _) (fun j b c => add_mul _ _ _)

theorem polynomialDerivative_smul_left (c : ℂ) (P : ℂ[X]) (f : ℝ → ℂ) :
    polynomialDerivative (c • P) f = c • polynomialDerivative P f := by
  funext u
  have h := P.sum_smul_index c (fun j b => b * ((differentialOperator^[j]) f) u)
    (fun j => zero_mul _)
  simpa only [Polynomial.sum_def, polynomialDerivative, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc] using h

/-- The same exact polynomial-window construction for any fixed source. -/
def polynomialWindowLinearMap (a : ℝ) (F : ℝ → ℂ) : ℂ[X] →ₗ[ℂ] (ℝ → ℂ) where
  toFun P := windowCut a (polynomialDerivative P F)
  map_add' P Q := by
    funext u
    by_cases hu : u ∈ Icc (-a) a <;>
      simp [windowCut, hu, polynomialDerivative_add_left]
  map_smul' c P := by
    funext u
    by_cases hu : u ∈ Icc (-a) a <;>
      simp [windowCut, hu, polynomialDerivative_smul_left]

/-- `L²` classes for a fixed source; only `L²` membership is needed to define the map. -/
def polynomialWindowL2LinearMap (a : ℝ) (F : ℝ → ℂ)
    (hmem : ∀ P : ℂ[X], MemLp (windowCut a (polynomialDerivative P F)) 2 volume) :
    ℂ[X] →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun P := (hmem P).toLp (windowCut a (polynomialDerivative P F))
  map_add' P Q := by
    calc
      _ = ((hmem P).add (hmem Q)).toLp
          (windowCut a (polynomialDerivative P F) + windowCut a (polynomialDerivative Q F)) :=
        MemLp.toLp_congr _ _ (Filter.Eventually.of_forall
          (congrFun ((polynomialWindowLinearMap a F).map_add P Q)))
      _ = _ := MemLp.toLp_add _ _
  map_smul' c P := by
    calc
      _ = ((hmem P).const_smul c).toLp (c • windowCut a (polynomialDerivative P F)) :=
        MemLp.toLp_congr _ _ (Filter.Eventually.of_forall
          (congrFun ((polynomialWindowLinearMap a F).map_smul c P)))
      _ = _ := MemLp.toLp_const_smul _ _

theorem polynomialWindowL2LinearMap_coeFn (a : ℝ) (F : ℝ → ℂ)
    (hmem : ∀ P : ℂ[X], MemLp (windowCut a (polynomialDerivative P F)) 2 volume)
    (P : ℂ[X]) :
    polynomialWindowL2LinearMap a F hmem P =ᵐ[volume] windowCut a (polynomialDerivative P F) :=
  MemLp.coeFn_toLp (hmem P)

theorem polynomialWindowL2LinearMap_eq_zero_iff_ae (a : ℝ) (F : ℝ → ℂ)
    (hmem : ∀ P : ℂ[X], MemLp (windowCut a (polynomialDerivative P F)) 2 volume)
    (P : ℂ[X]) :
    polynomialWindowL2LinearMap a F hmem P = 0 ↔
      windowCut a (polynomialDerivative P F) =ᵐ[volume] 0 := by
  constructor
  · intro hP
    have he := (polynomialWindowL2LinearMap_coeFn a F hmem P).symm
    rw [hP] at he
    exact he.trans (Lp.coeFn_zero _ _ _)
  · intro hP
    apply Lp.ext
    exact (polynomialWindowL2LinearMap_coeFn a F hmem P).trans
      (hP.trans (Lp.coeFn_zero _ _ _).symm)

theorem polynomialWindowL2LinearMap_zero_squaredNorm (a : ℝ) (F : ℝ → ℂ)
    (hmem : ∀ P : ℂ[X], MemLp (windowCut a (polynomialDerivative P F)) 2 volume)
    (P : ℂ[X]) (hP : polynomialWindowL2LinearMap a F hmem P = 0) :
    squaredNorm (windowCut a (polynomialDerivative P F)) = 0 := by
  have hz := (polynomialWindowL2LinearMap_eq_zero_iff_ae a F hmem P).mp hP
  unfold squaredNorm
  calc
    _ = ∫ _u : ℝ, (0 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [hz] with u hu
      simp only [hu, Pi.zero_apply, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    _ = 0 := integral_zero _ _

def polynomialDegreeWindowL2Map (a : ℝ) (F : ℝ → ℂ)
    (hmem : ∀ P : ℂ[X], MemLp (windowCut a (polynomialDerivative P F)) 2 volume) (k : ℕ) :
    Polynomial.degreeLT ℂ (k + 1) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (polynomialWindowL2LinearMap a F hmem).comp (Polynomial.degreeLT ℂ (k + 1)).subtype

def polynomialWindowTrialSpace (a : ℝ) (F : ℝ → ℂ)
    (hmem : ∀ P : ℂ[X], MemLp (windowCut a (polynomialDerivative P F)) 2 volume) (k : ℕ) :
    Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) :=
  LinearMap.range (polynomialDegreeWindowL2Map a F hmem k)

/-- Dimension of the image of the polynomials, for either family of trial
functions. -/
theorem polynomialWindowTrialSpace_finrank_of_separation (a : ℝ) (F : ℝ → ℂ)
    (hmem : ∀ P : ℂ[X], MemLp (windowCut a (polynomialDerivative P F)) 2 volume) (k : ℕ)
    (hsep : ∀ P : ℂ[X], P.natDegree ≤ k → P ≠ 0 →
      0 < squaredNorm (windowCut a (polynomialDerivative P F))) :
    Module.finrank ℂ (polynomialWindowTrialSpace a F hmem k) = k + 1 := by
  have hinj : Function.Injective (polynomialDegreeWindowL2Map a F hmem k) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro P hP
    apply Subtype.ext
    by_contra hne
    have hne' : (P : ℂ[X]) ≠ 0 := hne
    have hd : (P : ℂ[X]).natDegree ≤ k := by
      apply Nat.lt_succ_iff.mp
      exact (Polynomial.natDegree_lt_iff_degree_lt hne').mpr
        (Polynomial.mem_degreeLT.mp P.property)
    have hp := hsep P hd hne'
    have hz := polynomialWindowL2LinearMap_zero_squaredNorm a F hmem P hP
    linarith
  rw [polynomialWindowTrialSpace, LinearMap.finrank_range_of_inj hinj]
  simpa using Module.finrank_eq_card_basis (Polynomial.degreeLT.basis ℂ (k + 1))

def thetaAvgWindowProfile (a : ℝ) (P : ℂ[X]) : ℝ → ℂ :=
  windowCut a (polynomialDerivative P (fun u : ℝ => shiftedAverage a (u : ℂ)))

theorem thetaAvgWindowProfile_add (a : ℝ) (P Q : ℂ[X]) :
    thetaAvgWindowProfile a (P + Q) = thetaAvgWindowProfile a P + thetaAvgWindowProfile a Q := by
  funext u
  by_cases hu : u ∈ Icc (-a) a <;>
    simp [thetaAvgWindowProfile, windowCut, hu, polynomialDerivative_add_left]

theorem thetaAvgWindowProfile_smul (a : ℝ) (c : ℂ) (P : ℂ[X]) :
    thetaAvgWindowProfile a (c • P) = c • thetaAvgWindowProfile a P := by
  funext u
  by_cases hu : u ∈ Icc (-a) a <;>
    simp [thetaAvgWindowProfile, windowCut, hu, polynomialDerivative_smul_left]

theorem thetaAvgWindowProfile_memLp {a : ℝ} (ha : 0 ≤ a) (hZ : 16 ≤ scaleZ a)
    (P : ℂ[X]) : MemLp (thetaAvgWindowProfile a P) 2 volume :=
  MemLp.indicator measurableSet_Icc (polynomialDerivative_shiftedAverage_memLp_two ha hZ P)

/-- The hard-window polynomial source as an `L²` equivalence class. -/
def thetaAvgWindowL2LinearMap (a : ℝ) (ha : 0 ≤ a) (hZ : 16 ≤ scaleZ a) :
    ℂ[X] →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun P := (thetaAvgWindowProfile_memLp ha hZ P).toLp (thetaAvgWindowProfile a P)
  map_add' P Q := by
    calc
      _ = ((thetaAvgWindowProfile_memLp ha hZ P).add (thetaAvgWindowProfile_memLp ha hZ Q)).toLp
          (thetaAvgWindowProfile a P + thetaAvgWindowProfile a Q) :=
        MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (congrFun (thetaAvgWindowProfile_add a P Q)))
      _ = _ := MemLp.toLp_add _ _
  map_smul' c P := by
    calc
      _ = ((thetaAvgWindowProfile_memLp ha hZ P).const_smul c).toLp
          (c • thetaAvgWindowProfile a P) :=
        MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (congrFun (thetaAvgWindowProfile_smul a c P)))
      _ = _ := MemLp.toLp_const_smul _ _

theorem thetaAvgWindowL2LinearMap_coeFn {a : ℝ} (ha : 0 ≤ a) (hZ : 16 ≤ scaleZ a)
    (P : ℂ[X]) :
    thetaAvgWindowL2LinearMap a ha hZ P =ᵐ[volume] thetaAvgWindowProfile a P :=
  MemLp.coeFn_toLp (thetaAvgWindowProfile_memLp ha hZ P)

theorem thetaAvgWindowL2LinearMap_zero_squaredNorm {a : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (P : ℂ[X]) (hP : thetaAvgWindowL2LinearMap a ha hZ P = 0) :
    squaredNorm (thetaAvgWindowProfile a P) = 0 := by
  have he := (thetaAvgWindowL2LinearMap_coeFn ha hZ P).symm
  rw [hP] at he
  have hz : thetaAvgWindowProfile a P =ᵐ[volume] 0 := he.trans (Lp.coeFn_zero _ _ _)
  unfold squaredNorm
  calc
    _ = ∫ _u : ℝ, (0 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [hz] with u hu
      simp only [hu, Pi.zero_apply, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    _ = 0 := integral_zero _ _

/-- Restriction to the degree-`k` polynomial source module. -/
def thetaAvgDegreeWindowL2Map (a : ℝ) (ha : 0 ≤ a) (hZ : 16 ≤ scaleZ a) (k : ℕ) :
    Polynomial.degreeLT ℂ (k + 1) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (thetaAvgWindowL2LinearMap a ha hZ).comp (Polynomial.degreeLT ℂ (k + 1)).subtype

/-- The paper's polynomial trial space, in `L²`. -/
def thetaAvgTrialSpace (a : ℝ) (ha : 0 ≤ a) (hZ : 16 ≤ scaleZ a) (k : ℕ) :
    Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) :=
  LinearMap.range (thetaAvgDegreeWindowL2Map a ha hZ k)

theorem thetaAvgTrialSpace_eq_map (a : ℝ) (ha : 0 ≤ a) (hZ : 16 ≤ scaleZ a) (k : ℕ) :
    thetaAvgTrialSpace a ha hZ k =
      (Polynomial.degreeLT ℂ (k + 1)).map (thetaAvgWindowL2LinearMap a ha hZ) := by
  simp [thetaAvgTrialSpace, thetaAvgDegreeWindowL2Map, LinearMap.range_comp]

/-- Conditional algebraic helper: analytic squared-norm separation implies injectivity. -/
theorem thetaAvgDegreeWindowL2Map_injective_of_separation {a : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (k : ℕ)
    (hsep : ∀ P : ℂ[X], P.natDegree ≤ k → P ≠ 0 →
      0 < squaredNorm (windowCut a
        (polynomialDerivative P (fun u : ℝ => shiftedAverage a (u : ℂ))))) :
    Function.Injective (thetaAvgDegreeWindowL2Map a ha hZ k) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro P hP
  apply Subtype.ext
  by_contra hne
  have hne' : (P : ℂ[X]) ≠ 0 := hne
  have hd : (P : ℂ[X]).natDegree ≤ k := by
    apply Nat.lt_succ_iff.mp
    exact (Polynomial.natDegree_lt_iff_degree_lt hne').mpr
      (Polynomial.mem_degreeLT.mp P.property)
  have hp := hsep P hd hne'
  have hz := thetaAvgWindowL2LinearMap_zero_squaredNorm ha hZ P hP
  change squaredNorm (windowCut a
    (polynomialDerivative (P : ℂ[X]) (fun u : ℝ => shiftedAverage a (u : ℂ)))) = 0 at hz
  linarith

/-- Dimension theorem, assuming a lower bound on the norm. -/
theorem thetaAvgTrialSpace_finrank_of_separation {a : ℝ} (ha : 0 ≤ a)
    (hZ : 16 ≤ scaleZ a) (k : ℕ)
    (hsep : ∀ P : ℂ[X], P.natDegree ≤ k → P ≠ 0 →
      0 < squaredNorm (windowCut a
        (polynomialDerivative P (fun u : ℝ => shiftedAverage a (u : ℂ))))) :
    Module.finrank ℂ (thetaAvgTrialSpace a ha hZ k) = k + 1 := by
  rw [thetaAvgTrialSpace, LinearMap.finrank_range_of_inj
    (thetaAvgDegreeWindowL2Map_injective_of_separation ha hZ k hsep)]
  simpa using Module.finrank_eq_card_basis (Polynomial.degreeLT.basis ℂ (k + 1))

end ThetaTrial.Paper
