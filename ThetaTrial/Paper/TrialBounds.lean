import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# Scalar transfer estimates for the theta trial paper

These are conditional consequences of the analytic estimates in the paper,
not formalizations of the contour deformation or the Weil explicit formula.
The first theorem records exactly which BV, energy, and interior-norm bounds
produce the constant `34`. The later theorems prove the degree bookkeeping
using the functions `exp` and `log`, including an explicit threshold.
-/

noncomputable section

open Filter
open scoped Topology

namespace ThetaTrial.Paper.TrialBounds

def Z (a : ℝ) : ℝ := Real.pi * Real.exp (2 * a)

def T (a : ℝ) : ℝ := 2 * Z a

theorem Z_pos (a : ℝ) : 0 < Z a := by
  unfold Z
  positivity

theorem T_pos (a : ℝ) : 0 < T a := by
  unfold T
  exact mul_pos (by norm_num) (Z_pos a)

/-- The constant `34` is the sum of twice the tail exponent `16` and
the `2` in `Z a = π exp (2a)`. Here `N` represents the squared interior norm. -/
theorem normalized_energy_of_bv_bounds
    (a q N M Cq CM c : ℝ)
    (hCq : 0 ≤ Cq) (_hCM : 0 ≤ CM) (hc : 0 < c) (hM : 0 ≤ M)
    (henergy : |q| ≤ Cq * M ^ 2)
    (htail : M ≤ CM * Real.exp (16 * a - T a))
    (hinterior : c / Z a ≤ N) :
    |q| / N ≤ (Cq * CM ^ 2 * Real.pi / c) *
      Real.exp (-2 * T a + 34 * a) := by
  have hs : M ^ 2 ≤ (CM * Real.exp (16 * a - T a)) ^ 2 :=
    pow_le_pow_left₀ hM htail 2
  have hnum : |q| ≤ Cq * (CM * Real.exp (16 * a - T a)) ^ 2 :=
    henergy.trans (mul_le_mul_of_nonneg_left hs hCq)
  have hdiv := div_le_div₀ (by positivity :
      0 ≤ Cq * (CM * Real.exp (16 * a - T a)) ^ 2)
    hnum (div_pos hc (Z_pos a)) hinterior
  calc
    |q| / N ≤ Cq * (CM * Real.exp (16 * a - T a)) ^ 2 / (c / Z a) := hdiv
    _ = (Cq * CM ^ 2 * Real.pi / c) * Real.exp (-2 * T a + 34 * a) := by
      rw [mul_pow, ← Real.exp_nat_mul, Z]
      norm_num only [Nat.cast_ofNat]
      rw [div_div_eq_mul_div]
      have he : Real.exp (2 * a) * Real.exp (2 * (16 * a - T a)) =
          Real.exp (-2 * T a + 34 * a) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← he]
      ring

/-- A coarse elementary lower bound for the scale. -/
theorem four_sq_le_T {a : ℝ} (ha : 0 ≤ a) : 4 * a ^ 2 ≤ T a := by
  have hea : a ≤ Real.exp a := by linarith [Real.add_one_le_exp a]
  have hsq := pow_le_pow_left₀ ha hea 2
  have hexp : (Real.exp a) ^ 2 = Real.exp (2 * a) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [hexp] at hsq
  have hp : 4 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hh := mul_le_mul_of_nonneg_right hp (Real.exp_pos (2 * a)).le
  dsimp [T, Z]
  nlinarith

/-- Every real degree in the stated range already satisfies the logarithmic
bound used by the paper, at every `a ≥ 1`. -/
theorem log_degree_le {a k : ℝ} (ha : 1 ≤ a) (hk : 0 ≤ k)
    (hdegree : k ≤ T a / (32 * a)) : Real.log (k + 1) ≤ 3 * a := by
  have hap : 0 < a := by linarith
  have hmul : k * (32 * a) ≤ T a := (le_div_iff₀ (by positivity)).mp hdegree
  have hak : k ≤ a * k := by nlinarith [mul_nonneg hk (sub_nonneg.mpr ha)]
  have hpi : 2 * Real.pi * Real.exp (2 * a) ≤ 8 * Real.exp (2 * a) :=
    mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_four])
      (Real.exp_pos (2 * a)).le
  have hkexp : k ≤ Real.exp (2 * a) / 4 := by
    dsimp [T, Z] at hmul
    nlinarith
  have hplus : k + 1 ≤ Real.exp (2 * a) := by
    nlinarith [Real.add_one_le_exp (2 * a)]
  have hlog := Real.log_le_log (by positivity : 0 < k + 1) hplus
  rw [Real.log_exp] at hlog
  linarith

/-- A linear error `C(k+a)` is at most a quarter of `T a` once `a ≥ 2C`. -/
theorem linear_error_le {a k C : ℝ} (ha : 1 ≤ a) (hk : 0 ≤ k)
    (_hC : 0 ≤ C) (haC : 2 * C ≤ a)
    (hdegree : k ≤ T a / (32 * a)) : C * (k + a) ≤ T a / 4 := by
  have hap : 0 < a := by linarith
  have hmul : k * (32 * a) ≤ T a := (le_div_iff₀ (by positivity)).mp hdegree
  have hCk : 2 * C * k ≤ a * k := by
    nlinarith [mul_nonneg hk (sub_nonneg.mpr haC)]
  have hCa : 2 * C * a ≤ a ^ 2 := by
    nlinarith [mul_nonneg hap.le (sub_nonneg.mpr haC)]
  have hT := four_sq_le_T hap.le
  have hTp := T_pos a
  nlinarith

/-- Scalar version of the paper's degree-range condition and its small-energy
consequence, with an explicit threshold instead of unspecified eventuality. -/
theorem degree_range_and_exponent
    {a k C₁ C₂ : ℝ} (ha : 1 ≤ a) (hk : 0 ≤ k)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (haC₁ : 2 * C₁ ≤ a) (haC₂ : 2 * C₂ ≤ a)
    (hdegree : k ≤ T a / (32 * a)) :
    k * (Real.log (k + 1) + 4 * a) + C₁ * (k + a) ≤ T a ∧
      -2 * T a + 8 * k * a + 2 * k * Real.log (k + 1) +
        C₂ * (k + a) ≤ -T a := by
  have hlog := log_degree_le ha hk hdegree
  have hkl := mul_le_mul_of_nonneg_left hlog hk
  have hlin₁ := linear_error_le ha hk hC₁ haC₁ hdegree
  have hlin₂ := linear_error_le ha hk hC₂ haC₂ hdegree
  have hmul : k * (32 * a) ≤ T a :=
    (le_div_iff₀ (by positivity : 0 < 32 * a)).mp hdegree
  have hTp := T_pos a
  constructor <;> nlinarith

/-- The eventual degree corollary. Only its transfer to a particular
analytic trial space still needs that space's preceding energy theorem. -/
theorem eventually_small_degree (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∀ᶠ a : ℝ in atTop, ∀ k : ℕ, (k : ℝ) ≤ T a / (32 * a) →
      (k : ℝ) * (Real.log ((k : ℝ) + 1) + 4 * a) +
          C₁ * ((k : ℝ) + a) ≤ T a ∧
      Real.exp (-2 * T a + 8 * (k : ℝ) * a +
          2 * (k : ℝ) * Real.log ((k : ℝ) + 1) + C₂ * ((k : ℝ) + a)) ≤
        Real.exp (-T a) := by
  filter_upwards [eventually_ge_atTop (max 1 (max (2 * C₁) (2 * C₂)))] with a ha
  intro k hk
  have ha1 : 1 ≤ a := (le_max_left _ _).trans ha
  have haC₁ : 2 * C₁ ≤ a := (le_max_left _ _).trans ((le_max_right _ _).trans ha)
  have haC₂ : 2 * C₂ ≤ a := (le_max_right _ _).trans ((le_max_right _ _).trans ha)
  obtain ⟨hrange, hexponent⟩ := degree_range_and_exponent ha1
    (Nat.cast_nonneg k) hC₁ hC₂ haC₁ haC₂ hk
  exact ⟨hrange, Real.exp_le_exp.mpr hexponent⟩

/-- Transfer of the preceding estimate to a scalar energy bound, assuming the
polynomial-space estimate. -/
theorem energy_le_exp_neg_T
    {a k C₁ C₂ E : ℝ} (ha : 1 ≤ a) (hk : 0 ≤ k)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (haC₁ : 2 * C₁ ≤ a) (haC₂ : 2 * C₂ ≤ a)
    (hdegree : k ≤ T a / (32 * a))
    (henergy : E ≤ Real.exp (-2 * T a + 8 * k * a +
        2 * k * Real.log (k + 1) + C₂ * (k + a))) :
    E ≤ Real.exp (-T a) := by
  exact henergy.trans (Real.exp_le_exp.mpr
    (degree_range_and_exponent ha hk hC₁ hC₂ haC₁ haC₂ hdegree).2)

/-- The degree selected for the paper's explicit large trial space. -/
def selectedDegree (a : ℝ) : ℕ := ⌊T a / (32 * a)⌋₊

/-- Its dimension count is within one of the explicit exponential scale.
This is only a count; linear independence of the analytic trial vectors
must be supplied by the polynomial-space theorem. -/
theorem selected_dimension_bounds {a : ℝ} (ha : 0 < a) :
    T a / (32 * a) < (selectedDegree a + 1 : ℕ) ∧
      ((selectedDegree a + 1 : ℕ) : ℝ) ≤ T a / (32 * a) + 1 := by
  have hnonneg : 0 ≤ T a / (32 * a) :=
    (div_pos (T_pos a) (by positivity)).le
  constructor
  · simpa [selectedDegree] using Nat.lt_floor_add_one (T a / (32 * a))
  · simpa [selectedDegree] using add_le_add_right (Nat.floor_le hnonneg) 1

theorem selected_degree_le {a : ℝ} (ha : 0 < a) :
    (selectedDegree a : ℝ) ≤ T a / (32 * a) := by
  exact Nat.floor_le ((div_pos (T_pos a) (by positivity)).le)

/-- Choosing the natural-number floor gives the admissible degree and
the exponential estimate eventually, with the dimension bounds above. -/
theorem eventually_selected_degree (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∀ᶠ a : ℝ in atTop,
      (selectedDegree a : ℝ) * (Real.log ((selectedDegree a : ℝ) + 1) + 4 * a) +
          C₁ * ((selectedDegree a : ℝ) + a) ≤ T a ∧
      Real.exp (-2 * T a + 8 * (selectedDegree a : ℝ) * a +
          2 * (selectedDegree a : ℝ) * Real.log ((selectedDegree a : ℝ) + 1) +
          C₂ * ((selectedDegree a : ℝ) + a)) ≤ Real.exp (-T a) := by
  filter_upwards [eventually_small_degree C₁ C₂ hC₁ hC₂,
    eventually_ge_atTop (1 : ℝ)] with a hdegree ha
  exact hdegree (selectedDegree a) (selected_degree_le (by linarith))

/-- A quantitative relative error for the rounded dimension count. -/
theorem selected_dimension_relative_error {a : ℝ} (ha : 1 ≤ a) :
    0 ≤ ((selectedDegree a + 1 : ℕ) : ℝ) / (T a / (32 * a)) - 1 ∧
      ((selectedDegree a + 1 : ℕ) : ℝ) / (T a / (32 * a)) - 1 ≤ 8 / a := by
  have hap : 0 < a := by linarith
  have hR : 0 < T a / (32 * a) := div_pos (T_pos a) (by positivity)
  obtain ⟨hlo, hhi⟩ := selected_dimension_bounds hap
  have heq : ((selectedDegree a + 1 : ℕ) : ℝ) / (T a / (32 * a)) - 1 =
      (((selectedDegree a + 1 : ℕ) : ℝ) - T a / (32 * a)) /
        (T a / (32 * a)) := by
    rw [sub_div, div_self hR.ne']
  rw [heq]
  constructor
  · exact div_nonneg (by linarith) hR.le
  · calc
      _ ≤ 1 / (T a / (32 * a)) :=
        div_le_div_of_nonneg_right (by linarith) hR.le
      _ = (32 * a) / T a := by rw [one_div_div]
      _ ≤ 8 / a := by
        apply (div_le_div_iff₀ (T_pos a) hap).mpr
        nlinarith [four_sq_le_T hap.le]

/-- The rounded dimension count really is asymptotic to `T a / (32a)`.
This proves scalar counting only, not independence of analytic trial vectors. -/
theorem selected_dimension_ratio_tendsto_one :
    Tendsto (fun a : ℝ => ((selectedDegree a + 1 : ℕ) : ℝ) /
      (T a / (32 * a))) atTop (𝓝 1) := by
  have hevent := (eventually_ge_atTop (1 : ℝ)).mono
    (fun a ha => selected_dimension_relative_error ha)
  have hzero : Tendsto (fun a : ℝ => ((selectedDegree a + 1 : ℕ) : ℝ) /
      (T a / (32 * a)) - 1) atTop (𝓝 0) :=
    squeeze_zero' (hevent.mono fun _ h => h.1) (hevent.mono fun _ h => h.2)
      (tendsto_const_nhds.div_atTop tendsto_id)
  simpa only [sub_add_cancel, zero_add] using hzero.add_const 1

end ThetaTrial.Paper.TrialBounds
