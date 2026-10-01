import ThetaTrial.Paper.ShiftedAverageAnalytic
import ThetaTrial.Paper.ShiftWeightMass
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.PSeries

/-!
# Interior estimates for the shifted theta average

On a fixed central strip the theta density is uniformly Lipschitz. Near the
edge of the strip, a lower bound for the exponential gives a Gaussian-series
majorant.
-/

noncomputable section
open Complex MeasureTheory Set Filter Metric
open scoped Topology

namespace ThetaTrial.Paper

theorem complexThetaDensity_central_lipschitz :
    ∃ L > 0, ∀ u y : ℝ, |u| ≤ 1 → |y| ≤ Real.pi / 8 →
      ‖complexThetaDensity ((u : ℂ) + I * (y : ℂ)) -
        complexThetaDensity (u : ℂ)‖ ≤ L * |y| := by
  let K : Set ℂ := Icc (-1 : ℝ) 1 ×ℂ Icc (-(Real.pi / 8)) (Real.pi / 8)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hKstrip : K ⊆ thetaStrip := by
    intro z hz
    have him : |z.im| ≤ Real.pi / 8 := abs_le.mpr hz.2
    change |z.im| < Real.pi / 4
    linarith [Real.pi_pos]
  have hc : Convex ℝ K := by
    change Convex ℝ ((Complex.reLm ⁻¹' Icc (-1 : ℝ) 1) ∩
      (Complex.imLm ⁻¹' Icc (-(Real.pi / 8)) (Real.pi / 8)))
    exact ((convex_Icc (-1 : ℝ) 1).linear_preimage Complex.reLm).inter
      ((convex_Icc (-(Real.pi / 8)) (Real.pi / 8)).linear_preimage Complex.imLm)
  have hd := complexThetaDensity_differentiableOn_strip
  obtain ⟨C, hC⟩ := hK.bddAbove_image
    ((hd.deriv isOpen_thetaStrip).continuousOn.norm.mono hKstrip)
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro u y hu hy
  have h0 : (u : ℂ) ∈ K := by
    refine ⟨?_, ?_⟩
    · simpa using abs_le.mp hu
    · simp only [mem_Icc, mem_preimage, Complex.ofReal_im]
      constructor <;> linarith [Real.pi_pos]
  have h1 : (u : ℂ) + I * (y : ℂ) ∈ K := by
    simpa only [K, Complex.mem_reProdIm, mem_preimage, mem_Icc, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, mul_zero, sub_zero,
      add_zero, zero_add] using And.intro (abs_le.mp hu) (abs_le.mp hy)
  have hb (z : ℂ) (hz : z ∈ K) : ‖deriv complexThetaDensity z‖ ≤ |C| + 1 :=
    (hC (mem_image_of_mem _ hz)).trans (by linarith [le_abs_self C])
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => hd.differentiableAt (isOpen_thetaStrip.mem_nhds (hKstrip hz)))
    hb hc h0 h1
  simpa only [add_sub_cancel_left, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs] using hm

theorem polynomial_gaussian_mode_bound {s N : ℝ} (hs : 0 < s) (hN : 0 < N) :
    N ^ 4 * Real.exp (-s * N ^ 2) ≤ 6 / s ^ 3 / N ^ 2 := by
  have hp := Real.pow_div_factorial_le_exp (s * N ^ 2)
    (show 0 ≤ s * N ^ 2 by positivity) 3
  norm_num at hp
  have he : (s * N ^ 2) ^ 3 / 6 * Real.exp (-(s * N ^ 2)) ≤ 1 := by
    calc
      _ ≤ Real.exp (s * N ^ 2) * Real.exp (-(s * N ^ 2)) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  calc
    _ = ((s * N ^ 2) ^ 3 / 6 * Real.exp (-(s * N ^ 2))) *
        (6 / s ^ 3 / N ^ 2) := by
      field_simp
    _ ≤ 1 * (6 / s ^ 3 / N ^ 2) :=
      mul_le_mul_of_nonneg_right he (by positivity)
    _ = _ := one_mul _

def interiorPSeries (n : ℕ) : ℝ := (((n : ℝ) + 1) ^ 2)⁻¹

theorem summable_interiorPSeries : Summable interiorPSeries := by
  have hs := (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ)))
  simpa only [interiorPSeries, Nat.cast_add, Nat.cast_one] using!
    (summable_nat_add_iff 1).mpr hs

def interiorGaussianScale : ℝ := Real.pi * Real.exp (-2)

def interiorModeConstant : ℝ :=
  (4 * Real.pi ^ 2 + 6 * Real.pi) * Real.exp (9 / 2) *
    (6 / interiorGaussianScale ^ 3)

def interiorEdgeConstant : ℝ := interiorModeConstant * ∑' n : ℕ, interiorPSeries n

theorem moving_strip_exp_lower {a : ℝ} (ha : 16 ≤ scaleZ a)
    {u y : ℝ} (hu : |u| ≤ 1) (hy : |y| ≤ shiftWidth a) :
    Real.exp (-2) / scaleZ a ≤
      (Complex.exp (2 * ((u : ℂ) + I * (y : ℂ)))).re := by
  have hZ : 0 < scaleZ a := by linarith
  have hb := ContourArcIdentity.shiftWidth_arc_bounds ha
  have hfloor := (Contour.angularFloor_bounds ha).1
  have hbcos : Real.cos (2 * shiftWidth a) = Contour.angularFloor (scaleZ a) := by
    simpa only [shiftWidth, Contour.shiftBoundary, one_div] using
      Contour.cos_twice_shiftBoundary (scaleZ a)
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (show 0 ≤ 2 * |y| by positivity)
    (show 2 * shiftWidth a ≤ Real.pi by linarith [Real.pi_pos])
    (show 2 * |y| ≤ 2 * shiftWidth a by linarith)
  have habs : 2 * |y| = |2 * y| := by rw [abs_mul]; norm_num
  rw [habs, Real.cos_abs, hbcos] at hcos
  have hcos' : 1 / scaleZ a ≤ Real.cos (2 * y) :=
    ((div_le_iff₀ hZ).mpr (by linarith : 1 ≤
      Contour.angularFloor (scaleZ a) * scaleZ a)).trans hcos
  have he : Real.exp (-2) ≤ Real.exp (2 * u) :=
    Real.exp_le_exp.mpr (by linarith [(abs_le.mp hu).1])
  have heq : (Complex.exp (2 * ((u : ℂ) + I * (y : ℂ)))).re =
      Real.exp (2 * u) * Real.cos (2 * y) := by
    norm_num [Complex.exp_re, Complex.mul_re, Complex.mul_im]
  rw [heq]
  calc
    _ = Real.exp (-2) * (1 / scaleZ a) := by ring
    _ ≤ _ := mul_le_mul he hcos' (by positivity) (Real.exp_pos _).le

theorem complexThetaMode_moving_strip_bound {a : ℝ} (ha : 16 ≤ scaleZ a)
    {u y : ℝ} (hu : |u| ≤ 1) (hy : |y| ≤ shiftWidth a) (n : ℕ) :
    ‖complexThetaMode n ((u : ℂ) + I * (y : ℂ))‖ ≤
      interiorModeConstant * (scaleZ a) ^ 3 * interiorPSeries n := by
  let Z := scaleZ a
  let N : ℝ := (n : ℝ) + 1
  let E := Real.exp (9 / 2)
  have hZ : 0 < Z := by dsimp [Z]; linarith
  have hN : 0 < N := by dsimp [N]; positivity
  have hN1 : 1 ≤ N := by dsimp [N]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hβ : 0 < interiorGaussianScale := by unfold interiorGaussianScale; positivity
  have hA : ‖Complex.exp (9 * ((u : ℂ) + I * (y : ℂ)) / 2)‖ ≤ E := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    norm_num [Complex.div_re, Complex.mul_re, Complex.mul_im, E]
    linarith [(abs_le.mp hu).2]
  have hB : ‖Complex.exp (5 * ((u : ℂ) + I * (y : ℂ)) / 2)‖ ≤ E := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    norm_num [Complex.div_re, Complex.mul_re, Complex.mul_im, E]
    linarith [(abs_le.mp hu).2]
  have hm := complexThetaMode_norm_le n ((u : ℂ) + I * (y : ℂ))
    (moving_strip_exp_lower ha hu hy) hA hB
  have h24 : N ^ 2 ≤ N ^ 4 := by
    nlinarith [sq_nonneg (N ^ 2 - 1)]
  have hgauss : N ^ 4 * Real.exp (-Real.pi * N ^ 2 * (Real.exp (-2) / Z)) ≤
      (6 / interiorGaussianScale ^ 3) * Z ^ 3 * (N ^ 2)⁻¹ := by
    calc
      _ ≤ 6 / (interiorGaussianScale / Z) ^ 3 / N ^ 2 := by
        convert polynomial_gaussian_mode_bound (div_pos hβ hZ) hN using 1
        unfold interiorGaussianScale
        congr 2
        ring
      _ = _ := by field_simp
  have htailpos : 0 ≤ Real.exp (-Real.pi * N ^ 2 * (Real.exp (-2) / Z)) :=
    (Real.exp_pos _).le
  calc
    _ ≤ (4 * Real.pi ^ 2 * E) * (N ^ 4 * Real.exp (-Real.pi * N ^ 2 * (Real.exp (-2) / Z))) +
        (6 * Real.pi * E) * (N ^ 2 * Real.exp (-Real.pi * N ^ 2 * (Real.exp (-2) / Z))) := by
      simpa only [HurwitzKernelBounds.f_nat, Z, N] using hm
    _ ≤ (4 * Real.pi ^ 2 * E + 6 * Real.pi * E) *
        (N ^ 4 * Real.exp (-Real.pi * N ^ 2 * (Real.exp (-2) / Z))) := by
      have h := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right h24 htailpos)
        (show 0 ≤ 6 * Real.pi * E by dsimp [E]; positivity)
      nlinarith
    _ ≤ (4 * Real.pi ^ 2 * E + 6 * Real.pi * E) *
        ((6 / interiorGaussianScale ^ 3) * Z ^ 3 * (N ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left hgauss (by dsimp [E]; positivity)
    _ = _ := by dsimp [interiorModeConstant, interiorPSeries, Z, N, E]; ring

theorem interiorEdgeConstant_pos : 0 < interiorEdgeConstant := by
  have hS : 0 < ∑' n : ℕ, interiorPSeries n :=
    summable_interiorPSeries.tsum_pos
      (fun n => by unfold interiorPSeries; positivity) 0
      (by unfold interiorPSeries; norm_num)
  unfold interiorEdgeConstant interiorModeConstant interiorGaussianScale
  positivity

/-- Uniform polynomial control up to the moving shift boundary.
This coarser polynomial bound comes from a cubic exponential Taylor term. -/
theorem complexThetaDensity_moving_strip_bound {a : ℝ} (ha : 16 ≤ scaleZ a)
    {u y : ℝ} (hu : |u| ≤ 1) (hy : |y| ≤ shiftWidth a) :
    ‖complexThetaDensity ((u : ℂ) + I * (y : ℂ))‖ ≤
      interiorEdgeConstant * (scaleZ a) ^ 3 := by
  have hm := tsum_of_norm_bounded
    (summable_interiorPSeries.hasSum.mul_left (interiorModeConstant * (scaleZ a) ^ 3))
    (complexThetaMode_moving_strip_bound ha hu hy)
  change ‖complexThetaDensity ((u : ℂ) + I * (y : ℂ))‖ ≤ _ at hm
  simpa only [interiorEdgeConstant, mul_assoc, mul_comm, mul_left_comm] using hm

theorem cubic_exp_decay_le_inv {c Z : ℝ} (hc : 0 < c) (hZ : 0 < Z) :
    Z ^ 3 * Real.exp (-c * Z) ≤ (24 / c ^ 4) / Z := by
  have hp := Real.pow_div_factorial_le_exp (c * Z) (by positivity) 4
  norm_num at hp
  have he : (c * Z) ^ 4 / 24 * Real.exp (-(c * Z)) ≤ 1 := by
    calc
      _ ≤ Real.exp (c * Z) * Real.exp (-(c * Z)) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  calc
    _ = ((c * Z) ^ 4 / 24 * Real.exp (-(c * Z))) * ((24 / c ^ 4) / Z) := by
      field_simp
    _ ≤ 1 * ((24 / c ^ 4) / Z) := mul_le_mul_of_nonneg_right he (by positivity)
    _ = _ := one_mul _

/-- Uniform interior approximation. Its constant is independent of
the averaging scale and of the real point in [-1,1]. -/
theorem shiftedAverage_interior_approximation :
    ∃ C > 0, ∀ a u : ℝ, 16 ≤ scaleZ a → |u| ≤ 1 →
      ‖shiftedAverage a (u : ℂ) - (shiftMass a : ℂ) * complexThetaDensity (u : ℂ)‖ ≤
        C / scaleZ a := by
  obtain ⟨L, hL, hLip⟩ := complexThetaDensity_central_lipschitz
  let c : ℝ := Real.pi ^ 2 / 64
  have hc : 0 < c := by dsimp [c]; positivity
  have hE := interiorEdgeConstant_pos
  refine ⟨L * Real.sqrt (2 * Real.pi) + Real.pi * interiorEdgeConstant * (24 / c ^ 4),
    by positivity, ?_⟩
  intro a u ha hu
  let Z := scaleZ a
  let J := Icc (-shiftWidth a) (shiftWidth a)
  let D := 2 * interiorEdgeConstant * Z ^ 3 * Real.exp (-c * Z)
  let F : ℝ → ℂ := fun y => (shiftWeight a y : ℂ) *
    (complexThetaDensity ((u : ℂ) + I * (y : ℂ)) - complexThetaDensity (u : ℂ))
  have hZ : 0 < Z := by dsimp [Z]; linarith
  have hb := ContourArcIdentity.shiftWidth_arc_bounds ha
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hreal : ‖complexThetaDensity (u : ℂ)‖ ≤ interiorEdgeConstant * Z ^ 3 := by
    simpa [Z] using complexThetaDensity_moving_strip_bound ha hu
      (show |(0 : ℝ)| ≤ shiftWidth a by simpa using hb.1)
  have hpoint : ∀ y ∈ J, ‖F y‖ ≤ L * (|y| * shiftWeight a y) + D := by
    intro y hy
    have hw := shiftWeight_pos a y
    have hnorm : ‖F y‖ = shiftWeight a y *
        ‖complexThetaDensity ((u : ℂ) + I * (y : ℂ)) - complexThetaDensity (u : ℂ)‖ := by
      simp only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw]
    rw [hnorm]
    by_cases hcentral : |y| ≤ Real.pi / 8
    · have hh := mul_le_mul_of_nonneg_left (hLip u y hu hcentral) hw.le
      nlinarith
    · have hed := complexThetaDensity_moving_strip_bound ha hu (abs_le.mpr hy)
      have hdiff :
          ‖complexThetaDensity ((u : ℂ) + I * (y : ℂ)) - complexThetaDensity (u : ℂ)‖ ≤
            2 * interiorEdgeConstant * Z ^ 3 := by
        have hh := norm_sub_le (complexThetaDensity ((u : ℂ) + I * (y : ℂ)))
          (complexThetaDensity (u : ℂ))
        change ‖complexThetaDensity ((u : ℂ) + I * (y : ℂ))‖ ≤
          interiorEdgeConstant * Z ^ 3 at hed
        linarith
      have how : shiftWeight a y ≤ Real.exp (-c * Z) :=
        shiftWeight_outer ha hy (le_of_lt (lt_of_not_ge hcentral))
      calc
        _ ≤ shiftWeight a y * (2 * interiorEdgeConstant * Z ^ 3) :=
          mul_le_mul_of_nonneg_left hdiff hw.le
        _ ≤ Real.exp (-c * Z) * (2 * interiorEdgeConstant * Z ^ 3) :=
          mul_le_mul_of_nonneg_right how (by positivity)
        _ ≤ _ := by dsimp [D]; nlinarith [mul_nonneg hL.le (mul_nonneg (abs_nonneg y) hw.le)]
  have huStrip : |(u : ℂ).im| < 1 / scaleZ a := by
    simp only [Complex.ofReal_im, abs_zero]
    exact one_div_pos.mpr hZ
  have hi : IntegrableOn (fun y : ℝ => (shiftWeight a y : ℂ) *
      complexThetaDensity ((u : ℂ) + I * (y : ℂ))) J :=
    (weighted_shift_continuousOn ha huStrip
      complexThetaDensity_differentiableOn_strip.continuousOn).integrableOn_Icc
  have hi0 : IntegrableOn (fun y : ℝ => (shiftWeight a y : ℂ) *
      complexThetaDensity (u : ℂ)) J := by
    apply ContinuousOn.integrableOn_Icc
    exact ((Complex.continuous_ofReal.comp (shiftWeight_continuous a)).mul
      continuous_const).continuousOn
  have hid : (∫ y : ℝ in J, F y) = shiftedAverage a (u : ℂ) -
      (shiftMass a : ℂ) * complexThetaDensity (u : ℂ) := by
    simp only [F, mul_sub]
    rw [integral_sub hi hi0, integral_mul_const, integral_complex_ofReal]
    rfl
  have hiM : IntegrableOn (fun y : ℝ => L * (|y| * shiftWeight a y)) J := by
    apply ContinuousOn.integrableOn_Icc
    exact (continuous_const.mul (continuous_abs.mul (shiftWeight_continuous a))).continuousOn
  have hiD : IntegrableOn (fun _y : ℝ => D) J := continuous_const.continuousOn.integrableOn_Icc
  have hiBound := hiM.add hiD
  have hint : ‖∫ y : ℝ in J, F y‖ ≤
      ∫ y : ℝ in J, L * (|y| * shiftWeight a y) + D := by
    apply norm_integral_le_of_norm_le hiBound
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact hpoint y hy
  rw [← hid]
  calc
    _ ≤ ∫ y : ℝ in J, L * (|y| * shiftWeight a y) + D := hint
    _ = L * (∫ y : ℝ in J, |y| * shiftWeight a y) + (2 * shiftWidth a) * D := by
      rw [integral_add hiM hiD, integral_const_mul, setIntegral_const]
      rw [show J = Icc (-shiftWidth a) (shiftWidth a) from rfl,
        Real.volume_real_Icc_of_le (by linarith : -shiftWidth a ≤ shiftWidth a)]
      simp only [smul_eq_mul]
      ring
    _ ≤ L * (Real.sqrt (2 * Real.pi) / Z) + (Real.pi / 2) * D :=
      add_le_add (mul_le_mul_of_nonneg_left (shiftWeight_first_moment ha) hL.le)
        (mul_le_mul_of_nonneg_right hb.2.le hD)
    _ = L * (Real.sqrt (2 * Real.pi) / Z) +
        Real.pi * interiorEdgeConstant * (Z ^ 3 * Real.exp (-c * Z)) := by dsimp [D]; ring
    _ ≤ L * (Real.sqrt (2 * Real.pi) / Z) +
        Real.pi * interiorEdgeConstant * ((24 / c ^ 4) / Z) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (cubic_exp_decay_le_inv hc hZ)
        (by positivity))
    _ = _ := by dsimp [Z]; ring

/-- The real theta density has a positive minimum on the fixed interior. -/
theorem thetaDensity_interior_lower :
    ∃ m > 0, ∀ u : ℝ, |u| ≤ 1 → m ≤ thetaDensity u := by
  have hc : Continuous thetaDensity := by
    have hh : Continuous (fun u : ℝ => complexThetaDensity (u : ℂ)) := by
      apply continuous_iff_continuousAt.mpr
      intro u
      have hu : (u : ℂ) ∈ thetaStrip := by
        simp only [thetaStrip, mem_ofPred_eq, Complex.ofReal_im, abs_zero]
        positivity
      exact (complexThetaDensity_analyticOnNhd_strip (u : ℂ) hu).continuousAt.comp
        Complex.continuous_ofReal.continuousAt
    simpa only [Function.comp_def, complexThetaDensity_ofReal, Complex.ofReal_re] using!
      Complex.continuous_re.comp hh
  obtain ⟨m, hm, hl⟩ := isCompact_Icc.exists_forall_le'
    (s := Icc (-1 : ℝ) 1) hc.continuousOn (fun u _hu => thetaDensity_pos u)
  exact ⟨m, hm, fun u hu => hl u (abs_le.mp hu)⟩

theorem shiftMass_eq_multiplier_zero (a : ℝ) :
    shiftMass a = (shiftMultiplier a 0).re := by
  have h := shiftMultiplier_real a 0
  simp only [Complex.ofReal_zero, zero_mul, Real.cosh_zero, mul_one] at h
  rw [h, Complex.ofReal_re]
  rfl

theorem scaleZ_ge_self_of_nonneg {a : ℝ} (ha : 0 ≤ a) : a ≤ scaleZ a := by
  calc
    a ≤ Real.exp (2 * a) := by linarith [Real.add_one_le_exp (2 * a)]
    _ ≤ Real.pi * Real.exp (2 * a) :=
      le_mul_of_one_le_left (Real.exp_pos _).le (by linarith [Real.pi_gt_three])
    _ = scaleZ a := rfl

/-- Positivity of the average, uniformly on the fixed real interior. -/
theorem shiftedAverage_interior_positive_lower :
    ∃ c > 0, ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ a ≥ a₀,
      16 ≤ scaleZ a ∧ ∀ u : ℝ, |u| ≤ 1 →
        c / Real.sqrt (scaleZ a) ≤ (shiftedAverage a (u : ℂ)).re := by
  obtain ⟨C, hC, happ⟩ := shiftedAverage_interior_approximation
  obtain ⟨m, hm, hmin⟩ := thetaDensity_interior_lower
  let k : ℝ := m * Real.exp (-1)
  have hk : 0 < k := mul_pos hm (Real.exp_pos _)
  let a₀ : ℝ := max 16 ((2 * C / k) ^ 2)
  have ha₀ : 1 ≤ a₀ := by dsimp [a₀]; linarith [le_max_left (16 : ℝ) ((2 * C / k) ^ 2)]
  refine ⟨k / 2, by positivity, a₀, ha₀, ?_⟩
  intro a ha
  have ha16 : 16 ≤ a := (le_max_left _ _).trans ha
  have ha0 : 0 ≤ a := by linarith
  have haZ := scaleZ_ge_self_of_nonneg ha0
  have hZ16 : 16 ≤ scaleZ a := ha16.trans haZ
  have hZ : 0 < scaleZ a := by linarith
  have hs : 0 < Real.sqrt (scaleZ a) := Real.sqrt_pos.mpr hZ
  have hs2 := Real.sq_sqrt hZ.le
  have hth : (2 * C / k) ^ 2 ≤ scaleZ a := (le_max_right _ _).trans (ha.trans haZ)
  have hroot : 2 * C / k ≤ Real.sqrt (scaleZ a) := by nlinarith
  have hCroot : C ≤ (k / 2) * Real.sqrt (scaleZ a) := by
    have ht := (div_le_iff₀ hk).mp hroot
    nlinarith
  have herr : C / scaleZ a ≤ (k / 2) / Real.sqrt (scaleZ a) := by
    apply (div_le_div_iff₀ hZ hs).mpr
    nlinarith [mul_le_mul_of_nonneg_right hCroot hs.le]
  refine ⟨hZ16, ?_⟩
  intro u hu
  have hmass : Real.exp (-1) / Real.sqrt (scaleZ a) ≤ shiftMass a := by
    rw [shiftMass_eq_multiplier_zero]
    exact shiftMultiplier_zero_lower_sqrt hZ16
  have hmass0 : 0 ≤ shiftMass a := (by positivity : 0 ≤ Real.exp (-1) /
    Real.sqrt (scaleZ a)).trans hmass
  have hmain : k / Real.sqrt (scaleZ a) ≤ shiftMass a * thetaDensity u := by
    calc
      k / Real.sqrt (scaleZ a) = m * (Real.exp (-1) / Real.sqrt (scaleZ a)) := by
        dsimp [k]; ring
      _ ≤ m * shiftMass a := mul_le_mul_of_nonneg_left hmass hm.le
      _ ≤ thetaDensity u * shiftMass a := mul_le_mul_of_nonneg_right (hmin u hu) hmass0
      _ = _ := mul_comm _ _
  have he := (Complex.abs_re_le_norm
    (shiftedAverage a (u : ℂ) - (shiftMass a : ℂ) * complexThetaDensity (u : ℂ))).trans
    (happ a u hZ16 hu)
  rw [complexThetaDensity_ofReal] at he
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] at he
  have hel := (abs_le.mp he).1
  have hsplit : k / Real.sqrt (scaleZ a) =
      (k / 2) / Real.sqrt (scaleZ a) + (k / 2) / Real.sqrt (scaleZ a) := by ring
  linarith

theorem shiftedAverage_continuous_real {a : ℝ} (ha : 16 ≤ scaleZ a) :
    Continuous (fun u : ℝ => shiftedAverage a (u : ℂ)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  have hu : |(u : ℂ).im| < 1 / scaleZ a := by
    simp only [Complex.ofReal_im, abs_zero]
    exact one_div_pos.mpr (by linarith)
  exact (shiftedAverage_analyticOnNhd ha (u : ℂ) hu).continuousAt.comp
    Complex.continuous_ofReal.continuousAt

/-- The hard-truncated average keeps a fixed fraction of its squared norm. -/
theorem shiftedAverage_window_squaredNorm_lower :
    ∃ c > 0, ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ a ≥ a₀,
      c / scaleZ a ≤ squaredNorm (windowCut a (fun u => shiftedAverage a (u : ℂ))) := by
  obtain ⟨c, hc, a₀, ha₀, hl⟩ := shiftedAverage_interior_positive_lower
  refine ⟨2 * c ^ 2, by positivity, a₀, ha₀, ?_⟩
  intro a ha
  obtain ⟨hZ16, hp⟩ := hl a ha
  have ha1 : 1 ≤ a := ha₀.trans ha
  have hZ : 0 < scaleZ a := by linarith
  have hs : 0 < Real.sqrt (scaleZ a) := Real.sqrt_pos.mpr hZ
  have hs2 := Real.sq_sqrt hZ.le
  let f : ℝ → ℂ := fun u => shiftedAverage a (u : ℂ)
  have hf : Continuous f := shiftedAverage_continuous_real hZ16
  have hi : IntegrableOn (fun u => ‖f u‖ ^ 2) (Icc (-a) a) :=
    (hf.norm.pow 2).continuousOn.integrableOn_Icc
  have hsub : Icc (-1 : ℝ) 1 ⊆ Icc (-a) a := by
    intro u hu
    exact ⟨by linarith [hu.1], hu.2.trans ha1⟩
  have hpoint : ∀ u ∈ Icc (-1 : ℝ) 1, c ^ 2 / scaleZ a ≤ ‖f u‖ ^ 2 := by
    intro u hu
    have hn := (hp u (abs_le.mpr hu)).trans (Complex.re_le_norm (f u))
    have hn0 : 0 ≤ c / Real.sqrt (scaleZ a) := by positivity
    have hh := (sq_le_sq₀ hn0 (norm_nonneg (f u))).mpr hn
    rw [div_pow, hs2] at hh
    exact hh
  have hsmall : (∫ u : ℝ in Icc (-1 : ℝ) 1, c ^ 2 / scaleZ a) ≤
      ∫ u : ℝ in Icc (-1 : ℝ) 1, ‖f u‖ ^ 2 := by
    exact setIntegral_mono_on (integrableOn_const isCompact_Icc.measure_ne_top)
      (hi.mono_set hsub) measurableSet_Icc hpoint
  have hlarge := setIntegral_mono_set hi
    (ae_of_all _ (fun u => sq_nonneg ‖f u‖)) (ae_of_all _ (fun u hu => hsub hu))
  have hconst : (∫ u : ℝ in Icc (-1 : ℝ) 1, c ^ 2 / scaleZ a) =
      (2 * c ^ 2) / scaleZ a := by
    rw [setIntegral_const, Real.volume_real_Icc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    simp only [smul_eq_mul]
    ring
  have hcut : (fun u => ‖windowCut a f u‖ ^ 2) =
      (Icc (-a) a).indicator (fun u => ‖f u‖ ^ 2) := by
    funext u
    by_cases hu : u ∈ Icc (-a) a <;> simp [windowCut, hu]
  change _ ≤ ∫ u : ℝ, ‖windowCut a f u‖ ^ 2
  rw [hcut, integral_indicator measurableSet_Icc]
  rw [hconst] at hsmall
  exact hsmall.trans hlarge

end ThetaTrial.Paper
