import ThetaTrial.Paper.L2Reflection
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.MeasureTheory.Measure.OpenPos

/-! The supported physical Hilbert space and both parity sectors are
infinite dimensional for every positive window. The witnesses are ordinary
polynomial windows `x^e P(x²)`, with `e = 0, 1`. -/

noncomputable section
open Complex MeasureTheory Set Polynomial Filter

namespace ThetaTrial.Paper.FormDomain

def parityPolynomialProfile (e : ℕ) (P : ℂ[X]) (x : ℝ) : ℂ :=
  (x : ℂ)^e * P.eval ((x : ℂ)^2)

theorem parityPolynomialProfile_continuous (e : ℕ) (P : ℂ[X]) :
    Continuous (parityPolynomialProfile e P) := by
  exact (Complex.continuous_ofReal.pow e).mul
    (P.continuous.comp (Complex.continuous_ofReal.pow 2))

def windowPolynomialProfile (a : ℝ) (e : ℕ) (P : ℂ[X]) : ℝ → ℂ :=
  (Icc (-a) a).indicator (parityPolynomialProfile e P)

theorem windowPolynomialProfile_memLp (a : ℝ) (e : ℕ) (P : ℂ[X]) :
    MemLp (windowPolynomialProfile a e P) 2 volume := by
  apply (memLp_indicator_iff_restrict measurableSet_Icc).mpr
  apply (memLp_two_iff_integrable_sq_norm
    (parityPolynomialProfile_continuous e P).aestronglyMeasurable).mpr
  exact ((parityPolynomialProfile_continuous e P).norm.pow 2).integrableOn_Icc

def windowPolynomialLinearMap (a : ℝ) (e : ℕ) : ℂ[X] →ₗ[ℂ] (ℝ → ℂ) where
  toFun P := windowPolynomialProfile a e P
  map_add' P Q := by
    funext x
    by_cases hx : x ∈ Icc (-a) a <;>
      simp [windowPolynomialProfile, parityPolynomialProfile, hx, mul_add]
  map_smul' c P := by
    funext x
    by_cases hx : x ∈ Icc (-a) a <;>
      simp [windowPolynomialProfile, parityPolynomialProfile, hx, mul_left_comm]

def windowPolynomialL2Map (a : ℝ) (e : ℕ) : ℂ[X] →ₗ[ℂ] L2 where
  toFun P := (windowPolynomialProfile_memLp a e P).toLp (windowPolynomialProfile a e P)
  map_add' P Q := by
    calc
      _ = ((windowPolynomialProfile_memLp a e P).add
          (windowPolynomialProfile_memLp a e Q)).toLp
          (windowPolynomialProfile a e P + windowPolynomialProfile a e Q) :=
        MemLp.toLp_congr _ _ (Eventually.of_forall
          (congrFun ((windowPolynomialLinearMap a e).map_add P Q)))
      _ = _ := MemLp.toLp_add _ _
  map_smul' c P := by
    calc
      _ = ((windowPolynomialProfile_memLp a e P).const_smul c).toLp
          (c • windowPolynomialProfile a e P) :=
        MemLp.toLp_congr _ _ (Eventually.of_forall
          (congrFun ((windowPolynomialLinearMap a e).map_smul c P)))
      _ = _ := MemLp.toLp_const_smul _ _

theorem windowPolynomialL2Map_coeFn (a : ℝ) (e : ℕ) (P : ℂ[X]) :
    windowPolynomialL2Map a e P =ᵐ[volume] windowPolynomialProfile a e P :=
  MemLp.coeFn_toLp (windowPolynomialProfile_memLp a e P)

theorem windowPolynomialL2Map_mem_window (a : ℝ) (e : ℕ) (P : ℂ[X]) :
    windowPolynomialL2Map a e P ∈ windowL2 a := by
  filter_upwards [windowPolynomialL2Map_coeFn a e P] with x hx
  intro hout
  simp [hx, windowPolynomialProfile, hout]

theorem windowPolynomialL2Map_injective {a : ℝ} (ha : 0 < a) (e : ℕ) :
    Function.Injective (windowPolynomialL2Map a e) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro P hP
  have hz : windowPolynomialProfile a e P =ᵐ[volume] 0 := by
    have he := (windowPolynomialL2Map_coeFn a e P).symm
    rw [hP] at he
    exact he.trans (Lp.coeFn_zero _ _ _)
  have hi : parityPolynomialProfile e P =ᵐ[volume.restrict (Ioo 0 a)] 0 := by
    filter_upwards [ae_restrict_of_ae hz, ae_restrict_mem measurableSet_Ioo] with x hx hxa
    have hxc : x ∈ Icc (-a) a := ⟨by linarith [hxa.1], le_of_lt hxa.2⟩
    simpa [windowPolynomialProfile, hxc] using hx
  have hpoint := MeasureTheory.Measure.eqOn_Ioo_of_ae_eq volume hi
    (parityPolynomialProfile_continuous e P).continuousOn continuous_const.continuousOn
  have hroot : ∀ x ∈ Ioo (0 : ℝ) a, P.IsRoot ((x : ℂ)^2) := by
    intro x hx
    have he := hpoint hx
    have hne : (x : ℂ)^e ≠ 0 := pow_ne_zero _ (by exact_mod_cast ne_of_gt hx.1)
    exact (mul_eq_zero.mp he).resolve_left hne
  have hinj : Set.InjOn (fun x : ℝ => (x : ℂ)^2) (Ioo 0 a) := by
    intro x hx y hy hxy
    have he : x^2 = y^2 := by
      have hr := congrArg Complex.re hxy
      simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using hr
    nlinarith [hx.1, hy.1]
  apply P.eq_zero_of_infinite_isRoot
  exact ((Set.Ioo_infinite ha).image hinj).mono (by
    rintro z ⟨x, hx, rfl⟩
    exact hroot x hx)

def windowPolynomialMap (a : ℝ) (e : ℕ) : ℂ[X] →ₗ[ℂ] windowL2 a :=
  (windowPolynomialL2Map a e).codRestrict (windowL2 a)
    (windowPolynomialL2Map_mem_window a e)

theorem windowL2_not_finiteDimensional {a : ℝ} (ha : 0 < a) :
    ¬ FiniteDimensional ℂ (windowL2 a) := by
  intro hfin
  let := hfin
  have hinj : Function.Injective (windowPolynomialMap a 0) := by
    intro P Q hPQ
    apply windowPolynomialL2Map_injective ha 0
    exact congrArg Subtype.val hPQ
  exact Polynomial.not_finite
    (FiniteDimensional.of_injective (windowPolynomialMap a 0) hinj)

theorem windowPolynomialProfile_even (a : ℝ) (P : ℂ[X]) (x : ℝ) :
    windowPolynomialProfile a 0 P (-x) = windowPolynomialProfile a 0 P x := by
  have hm : -x ∈ Icc (-a) a ↔ x ∈ Icc (-a) a := by
    constructor <;> intro h <;> exact ⟨by linarith [h.2], by linarith [h.1]⟩
  by_cases hx : x ∈ Icc (-a) a <;>
    simp [windowPolynomialProfile, parityPolynomialProfile, hx, hm]

theorem windowPolynomialProfile_odd (a : ℝ) (P : ℂ[X]) (x : ℝ) :
    windowPolynomialProfile a 1 P (-x) = -windowPolynomialProfile a 1 P x := by
  have hm : -x ∈ Icc (-a) a ↔ x ∈ Icc (-a) a := by
    constructor <;> intro h <;> exact ⟨by linarith [h.2], by linarith [h.1]⟩
  by_cases hx : x ∈ Icc (-a) a <;>
    simp [windowPolynomialProfile, parityPolynomialProfile, hx, hm]

theorem windowPolynomialL2Map_mem_even (a : ℝ) (P : ℂ[X]) :
    windowPolynomialL2Map a 0 P ∈ evenL2 := by
  rw [mem_evenL2_iff_ae]
  have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
    (windowPolynomialL2Map_coeFn a 0 P)
  filter_upwards [windowPolynomialL2Map_coeFn a 0 P, hn] with x hx hn
  rw [hx, hn]
  exact windowPolynomialProfile_even a P x

theorem windowPolynomialL2Map_mem_odd (a : ℝ) (P : ℂ[X]) :
    windowPolynomialL2Map a 1 P ∈ oddL2 := by
  rw [mem_oddL2_iff_ae]
  have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
    (windowPolynomialL2Map_coeFn a 1 P)
  filter_upwards [windowPolynomialL2Map_coeFn a 1 P, hn] with x hx hn
  rw [hx, hn]
  exact windowPolynomialProfile_odd a P x

def evenWindowPolynomialMap (a : ℝ) : ℂ[X] →ₗ[ℂ] evenWindowL2 a :=
  (windowPolynomialL2Map a 0).codRestrict (evenWindowL2 a) (fun P =>
    ⟨windowPolynomialL2Map_mem_window a 0 P, windowPolynomialL2Map_mem_even a P⟩)

def oddWindowPolynomialMap (a : ℝ) : ℂ[X] →ₗ[ℂ] oddWindowL2 a :=
  (windowPolynomialL2Map a 1).codRestrict (oddWindowL2 a) (fun P =>
    ⟨windowPolynomialL2Map_mem_window a 1 P, windowPolynomialL2Map_mem_odd a P⟩)

theorem evenWindowL2_not_finiteDimensional {a : ℝ} (ha : 0 < a) :
    ¬ FiniteDimensional ℂ (evenWindowL2 a) := by
  intro hfin
  let := hfin
  have hinj : Function.Injective (evenWindowPolynomialMap a) := by
    intro P Q hPQ
    apply windowPolynomialL2Map_injective ha 0
    exact congrArg Subtype.val hPQ
  exact Polynomial.not_finite
    (FiniteDimensional.of_injective (evenWindowPolynomialMap a) hinj)

theorem oddWindowL2_not_finiteDimensional {a : ℝ} (ha : 0 < a) :
    ¬ FiniteDimensional ℂ (oddWindowL2 a) := by
  intro hfin
  let := hfin
  have hinj : Function.Injective (oddWindowPolynomialMap a) := by
    intro P Q hPQ
    apply windowPolynomialL2Map_injective ha 1
    exact congrArg Subtype.val hPQ
  exact Polynomial.not_finite
    (FiniteDimensional.of_injective (oddWindowPolynomialMap a) hinj)

end ThetaTrial.Paper.FormDomain
