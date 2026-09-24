import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3757

noncomputable section

open Filter MeasureTheory
open scoped Interval

def integrand (α x : ℝ) : ℝ :=
  Real.rpow x α * Real.exp (-x)

theorem gap1 (a α b x : ℝ) (haα : a ≤ α) (hαb : α ≤ b)
    (hx : 1 ≤ x) :
    0 < integrand α x := by
  unfold integrand
  exact mul_pos
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) _)
    (Real.exp_pos _)

theorem gap2 (a α b x : ℝ) (haα : a ≤ α) (hαb : α ≤ b)
    (hx : 1 ≤ x) :
    integrand α x ≤ integrand b x := by
  unfold integrand
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hx hαb)
    (Real.exp_nonneg _)

theorem gap3 (a α b x : ℝ) (haα : a ≤ α) (hαb : α ≤ b)
    (hx : 1 ≤ x) :
    0 < integrand b x := by
  unfold integrand
  exact mul_pos
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) _)
    (Real.exp_pos _)

private lemma eventual_identity (b : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      x ^ 2 * integrand b x =
        Real.rpow x (b + 2) / Real.exp x := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold integrand
  rw [Real.exp_neg, div_eq_mul_inv]
  rw [show x ^ 2 = Real.rpow x 2 by
    simpa using (Real.rpow_natCast x 2).symm]
  calc
    Real.rpow x 2 * (Real.rpow x b * (Real.exp x)⁻¹) =
        (Real.rpow x 2 * Real.rpow x b) *
          (Real.exp x)⁻¹ := by ring
    _ = Real.rpow x (2 + b) * (Real.exp x)⁻¹ := by
      exact congrArg (fun z : ℝ => z * (Real.exp x)⁻¹)
        (Real.rpow_add hx 2 b).symm
    _ = Real.rpow x (b + 2) * (Real.exp x)⁻¹ := by
      congr 2
      ring

theorem gap4 (b L : ℝ) :
    Tendsto (fun x : ℝ => x ^ 2 * integrand b x) atTop (nhds L) ↔
      Tendsto
        (fun x : ℝ => Real.rpow x (b + 2) / Real.exp x)
        atTop (nhds L) := by
  exact tendsto_congr' (eventual_identity b)

theorem gap5 (b : ℝ) :
    Tendsto
      (fun x : ℝ => Real.rpow x (b + 2) / Real.exp x)
      atTop (nhds 0) := by
  simpa only [one_mul, neg_mul, Real.exp_neg, div_eq_mul_inv] using
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (b + 2) 1 zero_lt_one)

theorem gap6 (b : ℝ) :
    Tendsto (fun x : ℝ => x ^ 2 * integrand b x) atTop (nhds 0) := by
  exact (gap4 b 0).2 (gap5 b)

private lemma integrableOn_tail (b : ℝ) :
    IntegrableOn (integrand b) (Set.Ioi 1) := by
  let q : ℝ := max b 0
  have hqgt : -1 < q := lt_of_lt_of_le (by norm_num)
    (le_max_right b 0)
  have hq0 :
      IntegrableOn
        (fun x : ℝ => Real.rpow x q *
          Real.exp (-(Real.rpow x 1)))
        (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_rpow hqgt le_rfl
  have hq :
      IntegrableOn (integrand q) (Set.Ioi 1) := by
    refine (hq0.mono_set (Set.Ioi_subset_Ioi zero_le_one)).congr_fun
      ?_ measurableSet_Ioi
    intro x hx
    unfold integrand
    change
      Real.rpow x q * Real.exp (-(Real.rpow x 1)) =
        Real.rpow x q * Real.exp (-x)
    rw [Real.rpow_eq_pow x 1, Real.rpow_one]
  refine Integrable.mono' hq ?_ ?_
  · have hcont : ContinuousOn (integrand b) (Set.Ioi 1) := by
      intro x hx
      unfold integrand
      change ContinuousWithinAt
        (fun y : ℝ => y ^ b * Real.exp (-y))
        (Set.Ioi 1) x
      exact
        ((Real.continuousAt_rpow_const x b
          (Or.inl (ne_of_gt (zero_lt_one.trans hx)))).mul
          continuousAt_neg.rexp).continuousWithinAt
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards
      [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 ≤ x := le_of_lt hx
    have hxb : 0 < integrand b x :=
      gap1 b b b x le_rfl le_rfl hx1
    rw [Real.norm_eq_abs, abs_of_pos hxb]
    exact gap2 b b q x le_rfl (le_max_left b 0) hx1

private lemma tail_tendsto_zero (b : ℝ) :
    Tendsto
      (fun A : ℝ => ∫ x in Set.Ioi A, integrand b x)
      atTop (nhds 0) := by
  have ht :=
    tendsto_setIntegral_of_antitone
      (f := integrand b) (μ := volume)
      (s := fun A : ℝ => Set.Ioi A)
      (fun _ => measurableSet_Ioi)
      (fun _ _ h => Set.Ioi_subset_Ioi h)
      ⟨1, integrableOn_tail b⟩
  have hinter :
      (⋂ A : ℝ, Set.Ioi A) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    have hxx := Set.mem_iInter.mp hx (x + 1)
    exact (lt_irrefl (x + 1)) (hxx.trans (lt_add_one x))
  simpa [hinter] using ht

theorem gap7 (b : ℝ) :
    ∃ L : ℝ,
      Tendsto (fun A : ℝ => ∫ x in (1 : ℝ)..A, integrand b x)
        atTop (nhds L) := by
  refine ⟨∫ x in Set.Ioi 1, integrand b x, ?_⟩
  exact intervalIntegral_tendsto_integral_Ioi
    1 (integrableOn_tail b) tendsto_id

theorem gap8 (a b ε : ℝ) (hε : 0 < ε) :
    ∃ A₀ : ℝ, ∀ A α : ℝ, A₀ < A → a ≤ α → α ≤ b →
      |∫ x in Set.Ioi A, integrand α x| < ε := by
  have hev :
      ∀ᶠ A : ℝ in atTop,
        |∫ x in Set.Ioi A, integrand b x| < ε := by
    have hball :=
      (tail_tendsto_zero b).eventually
        (Metric.ball_mem_nhds (0 : ℝ) hε)
    simpa only [Real.dist_eq, sub_zero] using hball
  obtain ⟨B, hB⟩ := eventually_atTop.1 hev
  refine ⟨max 1 B, ?_⟩
  intro A α hA haα hαb
  have hA1 : 1 < A := (le_max_left 1 B).trans_lt hA
  have hAB : B ≤ A := (le_max_right 1 B).trans hA.le
  have hαint :
      IntegrableOn (integrand α) (Set.Ioi A) :=
    (integrableOn_tail α).mono_set
      (Set.Ioi_subset_Ioi hA1.le)
  have hbint :
      IntegrableOn (integrand b) (Set.Ioi A) :=
    (integrableOn_tail b).mono_set
      (Set.Ioi_subset_Ioi hA1.le)
  have hnonneg :
      0 ≤ ∫ x in Set.Ioi A, integrand α x := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro x hx
    unfold integrand
    exact mul_nonneg
      (Real.rpow_nonneg
        (le_trans (zero_le_one.trans hA1.le) hx.le) _)
      (Real.exp_nonneg _)
  rw [abs_of_nonneg hnonneg]
  calc
    (∫ x in Set.Ioi A, integrand α x) ≤
        ∫ x in Set.Ioi A, integrand b x := by
      apply setIntegral_mono_on hαint hbint measurableSet_Ioi
      intro x hx
      exact gap2 a α b x haα hαb
        (le_trans hA1.le (le_of_lt hx))
    _ ≤ |∫ x in Set.Ioi A, integrand b x| :=
      le_abs_self _
    _ < ε := hB A hAB

theorem gap9 (a b ε : ℝ) (hε : 0 < ε) :
    ∃ A₀ : ℝ, ∀ A α : ℝ, A₀ < A → a ≤ α → α ≤ b →
      |∫ x in Set.Ioi A, integrand α x| < ε := by
  exact gap8 a b ε hε

end

end ProofGap.Exercise3757
