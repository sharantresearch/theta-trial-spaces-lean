import ThetaTrial.Paper.RadicalCutoff

/-!
# Sesquilinear algebra of the convergent Weil pairing

The first argument is complex linear. Its mixed correlations converge at
every translation for L2 inputs, and all arithmetic additivity uses the
explicit `RadicalCutoff.Domain` convergence data.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Complex MeasureTheory Set
open scoped ComplexConjugate

namespace ThetaTrial.Paper.RadicalCutoff

open Radical RadicalCorrelation

theorem paperFT_add {k l : ℝ → ℂ} {z : ℂ}
    (hk : FourierIntegrableAt k (-z)) (hl : FourierIntegrableAt l (-z)) :
    Zeta23.paperFT (k + l) z = Zeta23.paperFT k z + Zeta23.paperFT l z := by
  have hk' : Integrable (fun u : ℝ => k u * Complex.exp (I * z * (u : ℂ))) := by
    simpa only [FourierIntegrableAt, mul_neg, neg_mul, neg_neg] using hk
  have hl' : Integrable (fun u : ℝ => l u * Complex.exp (I * z * (u : ℂ))) := by
    simpa only [FourierIntegrableAt, mul_neg, neg_mul, neg_neg] using hl
  simp only [Zeta23.paperFT, Pi.add_apply, add_mul]
  exact integral_add hk' hl'

theorem paperFT_smul (c : ℂ) (k : ℝ → ℂ) (z : ℂ) :
    Zeta23.paperFT (c • k) z = c • Zeta23.paperFT k z := by
  simp only [Zeta23.paperFT, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem Domain.add {k l : ℝ → ℂ} (hk : Domain k) (hl : Domain l) : Domain (k + l) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z
    apply ((hk.transform z).add (hl.transform z)).congr
    filter_upwards with u
    simp only [Pi.add_apply, add_mul]
  · have he : gammaTerm (k + l) = gammaTerm k + gammaTerm l := by
      funext r
      simp only [gammaTerm, paperFT_add (hk.transform _) (hl.transform _), add_mul, Pi.add_apply]
    rw [he]
    exact hk.gamma.add hl.gamma
  · have he : primeTerm (k + l) = primeTerm k + primeTerm l := by
      funext n
      simp only [primeTerm, Pi.add_apply]
      ring
    rw [he]
    exact hk.prime.add hl.prime

theorem Domain.smul {k : ℝ → ℂ} (hk : Domain k) (c : ℂ) : Domain (c • k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z
    apply ((hk.transform z).const_mul c).congr
    filter_upwards with u
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  · have he : gammaTerm (c • k) = c • gammaTerm k := by
      funext r
      simp only [gammaTerm, paperFT_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [he]
    exact hk.gamma.smul c
  · have he : primeTerm (c • k) = c • primeTerm k := by
      funext n
      simp only [primeTerm, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he]
    change Summable (fun n => c * primeTerm k n)
    exact hk.prime.mul_left c

theorem fullWeil_add {k l : ℝ → ℂ} (hk : Domain k) (hl : Domain l) :
    fullWeil (k + l) = fullWeil k + fullWeil l := by
  have hg : gammaTerm (k + l) = gammaTerm k + gammaTerm l := by
    funext r
    simp only [gammaTerm, paperFT_add (hk.transform _) (hl.transform _), Pi.add_apply, add_mul]
  have hp : primeTerm (k + l) = primeTerm k + primeTerm l := by
    funext n
    simp only [primeTerm, Pi.add_apply]
    ring
  change Zeta23.paperFT (k + l) (I / 2) + Zeta23.paperFT (k + l) (-I / 2) -
    ∑' n, primeTerm (k + l) n + (1 / (2 * Real.pi) : ℂ) * ∫ r, gammaTerm (k + l) r = _
  rw [paperFT_add (hk.transform _) (hl.transform _), paperFT_add (hk.transform _) (hl.transform _),
    hp, hg]
  simp only [Pi.add_apply]
  rw [hk.prime.tsum_add hl.prime, integral_add hk.gamma hl.gamma]
  unfold fullWeil Zeta23.EF.literatureRHS
  simp only [primeTerm, gammaTerm]
  ring

theorem fullWeil_smul {k : ℝ → ℂ} (hk : Domain k) (c : ℂ) :
    fullWeil (c • k) = c • fullWeil k := by
  have hg : gammaTerm (c • k) = c • gammaTerm k := by
    funext r
    simp only [gammaTerm, paperFT_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hp : primeTerm (c • k) = c • primeTerm k := by
    funext n
    simp only [primeTerm, Pi.smul_apply, smul_eq_mul]
    ring
  change Zeta23.paperFT (c • k) (I / 2) + Zeta23.paperFT (c • k) (-I / 2) -
    ∑' n, primeTerm (c • k) n + (1 / (2 * Real.pi) : ℂ) * ∫ r, gammaTerm (c • k) r = _
  rw [paperFT_smul, paperFT_smul, hp, hg]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hk.prime.tsum_mul_left c, integral_const_mul]
  unfold fullWeil Zeta23.EF.literatureRHS
  simp only [primeTerm, gammaTerm]
  ring

/-- Hölder's inequality bounds the mixed correlation at every translation. -/
theorem l2_correlation_integrable {f h : ℝ → ℂ}
    (hf2 : MemLp f 2) (hh2 : MemLp h 2) (x : ℝ) :
    Integrable (fun u : ℝ => f u * conj (h (u - x))) := by
  have hht : MemLp (fun u : ℝ => h (u - x)) 2 := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      hh2.comp_measurePreserving (measurePreserving_add_right volume (-x))
  have hn : Integrable (fun u : ℝ => ‖f u‖ * ‖h (u - x)‖) :=
    hf2.norm.integrable_mul hht.norm
  apply hn.mono' (hf2.aestronglyMeasurable.mul
    (Complex.continuous_conj.comp_aestronglyMeasurable hht.aestronglyMeasurable))
  filter_upwards with u
  change ‖f u * conj (h (u - x))‖ ≤ ‖f u‖ * ‖h (u - x)‖
  simp only [norm_mul, norm_conj]
  exact le_rfl

theorem weilTest_add_left {f g h : ℝ → ℂ}
    (hf2 : MemLp f 2) (hg2 : MemLp g 2) (hh2 : MemLp h 2) :
    Zeta23.EF.weilTest (f + g) h = Zeta23.EF.weilTest f h + Zeta23.EF.weilTest g h := by
  funext x
  simp only [weilTest_eq_integral, Pi.add_apply, add_mul]
  exact integral_add (l2_correlation_integrable hf2 hh2 x) (l2_correlation_integrable hg2 hh2 x)

theorem weilTest_smul_left (c : ℂ) (f h : ℝ → ℂ) :
    Zeta23.EF.weilTest (c • f) h = c • Zeta23.EF.weilTest f h := by
  funext x
  simp only [weilTest_eq_integral, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem fullPairing_add_left {f g h : ℝ → ℂ}
    (hf2 : MemLp f 2) (hg2 : MemLp g 2) (hh2 : MemLp h 2)
    (dfh : Domain (Zeta23.EF.weilTest f h)) (dgh : Domain (Zeta23.EF.weilTest g h)) :
    fullPairing (f + g) h = fullPairing f h + fullPairing g h := by
  unfold fullPairing
  rw [weilTest_add_left hf2 hg2 hh2, fullWeil_add dfh dgh]

theorem fullPairing_smul_left {f h : ℝ → ℂ}
    (dfh : Domain (Zeta23.EF.weilTest f h)) (c : ℂ) :
    fullPairing (c • f) h = c • fullPairing f h := by
  unfold fullPairing
  rw [weilTest_smul_left, fullWeil_smul dfh c]

theorem fullPairing_add_right {f g h : ℝ → ℂ}
    (hf2 : MemLp f 2) (hg2 : MemLp g 2) (hh2 : MemLp h 2)
    (dfg : Domain (Zeta23.EF.weilTest f g)) (dfh : Domain (Zeta23.EF.weilTest f h)) :
    fullPairing f (g + h) = fullPairing f g + fullPairing f h := by
  have dgf : Domain (Zeta23.EF.weilTest g f) := by
    rw [weilTest_swap]
    exact dfg.tilde
  have dhf : Domain (Zeta23.EF.weilTest h f) := by
    rw [weilTest_swap]
    exact dfh.tilde
  rw [fullPairing_hermitian (g + h) f, fullPairing_add_left hg2 hh2 hf2 dgf dhf, map_add,
    ← fullPairing_hermitian g f, ← fullPairing_hermitian h f]

theorem fullPairing_smul_right {f h : ℝ → ℂ}
    (dfh : Domain (Zeta23.EF.weilTest f h)) (c : ℂ) :
    fullPairing f (c • h) = conj c • fullPairing f h := by
  have dhf : Domain (Zeta23.EF.weilTest h f) := by
    rw [weilTest_swap]
    exact dfh.tilde
  rw [fullPairing_hermitian (c • h) f, fullPairing_smul_left dhf c]
  simp only [smul_eq_mul, map_mul, ← fullPairing_hermitian h f]

#print axioms Domain.add
#print axioms Domain.smul
#print axioms fullPairing_add_left
#print axioms fullPairing_smul_left
#print axioms fullPairing_add_right
#print axioms fullPairing_smul_right

end ThetaTrial.Paper.RadicalCutoff
