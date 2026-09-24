import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3779

noncomputable section

open Filter MeasureTheory
open scoped Interval

def integrand (α x : ℝ) : ℝ :=
  x / (2 + Real.rpow x α)

def F (α : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), integrand α x

theorem gap1 (x α α₀ : ℝ) (hα₀ : 2 < α₀) (hx : 1 ≤ x)
    (hα : α₀ ≤ α) :
    0 < integrand α x := by
  unfold integrand
  exact div_pos (zero_lt_one.trans_le hx)
    (add_pos_of_pos_of_nonneg (by norm_num)
      (Real.rpow_nonneg (zero_le_one.trans hx) _))

theorem gap2 (x α α₀ : ℝ) (hα₀ : 2 < α₀) (hx : 1 ≤ x)
    (hα : α₀ ≤ α) :
    integrand α x < x / Real.rpow x α := by
  unfold integrand
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hp : 0 < Real.rpow x α :=
    Real.rpow_pos_of_pos hxpos _
  exact (div_lt_div_iff_of_pos_left hxpos
    (add_pos_of_pos_of_nonneg (by norm_num) hp.le) hp).2
    (by linarith)

theorem gap3 (x α α₀ : ℝ) (hα₀ : 2 < α₀) (hx : 1 ≤ x)
    (hα : α₀ ≤ α) :
    x / Real.rpow x α ≤ 1 / Real.rpow x (α₀ - 1) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hpowα : 0 < Real.rpow x α :=
    Real.rpow_pos_of_pos hxpos _
  have hpow0 : 0 < Real.rpow x (α₀ - 1) :=
    Real.rpow_pos_of_pos hxpos _
  rw [div_le_div_iff₀ hpowα hpow0, one_mul]
  calc
    x * Real.rpow x (α₀ - 1) =
        Real.rpow x 1 * Real.rpow x (α₀ - 1) := by
      have hxone : Real.rpow x 1 = x := by
        rw [Real.rpow_eq_pow, Real.rpow_one]
      rw [hxone]
    _ = Real.rpow x (1 + (α₀ - 1)) :=
      (Real.rpow_add hxpos 1 (α₀ - 1)).symm
    _ = Real.rpow x α₀ := by
      congr 2
      ring
    _ ≤ Real.rpow x α :=
      Real.rpow_le_rpow_of_exponent_le hx hα

theorem gap4 (x α α₀ : ℝ) (hα₀ : 2 < α₀) (hx : 1 ≤ x)
    (hα : α₀ ≤ α) :
    0 < 1 / Real.rpow x (α₀ - 1) := by
  exact one_div_pos.mpr
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) _)

private lemma power_tail_integrable (α₀ : ℝ) (hα₀ : 2 < α₀) :
    IntegrableOn
      (fun x : ℝ => 1 / Real.rpow x (α₀ - 1))
      (Set.Ioi 1) := by
  have hpow :
      IntegrableOn (fun x : ℝ => x ^ (1 - α₀)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  refine hpow.congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hxpos : 0 < x := zero_lt_one.trans hx
  change x ^ (1 - α₀) = 1 / Real.rpow x (α₀ - 1)
  rw [one_div, Real.rpow_eq_pow, ← Real.rpow_neg hxpos.le]
  congr 2
  ring

theorem gap5 (α₀ : ℝ) (hα₀ : 2 < α₀) :
    ∃ L : ℝ,
      Tendsto
        (fun A : ℝ => ∫ x in (1 : ℝ)..A,
          1 / Real.rpow x (α₀ - 1))
        atTop (nhds L) := by
  refine
    ⟨∫ x in Set.Ioi 1, 1 / Real.rpow x (α₀ - 1), ?_⟩
  exact intervalIntegral_tendsto_integral_Ioi
    1 (power_tail_integrable α₀ hα₀) tendsto_id

private lemma integrableOn_integrand_tail (α α₀ : ℝ)
    (hα₀ : 2 < α₀) (hα : α₀ ≤ α) :
    IntegrableOn (integrand α) (Set.Ioi 1) := by
  refine Integrable.mono'
    (power_tail_integrable α₀ hα₀) ?_ ?_
  · have hcont : ContinuousOn (integrand α) (Set.Ioi 1) := by
      intro x hx
      unfold integrand
      change ContinuousWithinAt
        (fun y : ℝ => y / (2 + y ^ α)) (Set.Ioi 1) x
      apply ContinuousAt.continuousWithinAt
      apply ContinuousAt.div continuousAt_id
      · exact continuousAt_const.add
          (Real.continuousAt_rpow_const x α
            (Or.inl (ne_of_gt (zero_lt_one.trans hx))))
      · have hp : 0 ≤ x ^ α := by
          rw [← Real.rpow_eq_pow]
          exact Real.rpow_nonneg (zero_le_one.trans hx.le) _
        exact ne_of_gt (add_pos_of_pos_of_nonneg (by norm_num) hp)
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 ≤ x := le_of_lt hx
    have hpos : 0 < integrand α x :=
      gap1 x α α₀ hα₀ hx1 hα
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    exact (gap2 x α α₀ hα₀ hx1 hα).le.trans
      (gap3 x α α₀ hα₀ hx1 hα)

theorem gap6 (α₀ : ℝ) (hα₀ : 2 < α₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ A₀ : ℝ, 1 < A₀ ∧
      ∀ A α : ℝ, A₀ < A → α₀ ≤ α →
        |∫ x in Set.Ioi A, integrand α x| < ε := by
  have hpowerTail :
      Tendsto
        (fun A : ℝ =>
          ∫ x in Set.Ioi A,
            1 / Real.rpow x (α₀ - 1))
        atTop (nhds 0) := by
    have ht :=
      tendsto_setIntegral_of_antitone
        (f := fun x : ℝ => 1 / Real.rpow x (α₀ - 1))
        (μ := volume)
        (s := fun A : ℝ => Set.Ioi A)
        (fun _ => measurableSet_Ioi)
        (fun _ _ h => Set.Ioi_subset_Ioi h)
        ⟨1, power_tail_integrable α₀ hα₀⟩
    have hinter :
        (⋂ A : ℝ, Set.Ioi A) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro x hx
      have hxx := Set.mem_iInter.mp hx (x + 1)
      exact (lt_irrefl (x + 1)) (hxx.trans (lt_add_one x))
    simpa [hinter] using ht
  have hev :
      ∀ᶠ A : ℝ in atTop,
        |∫ x in Set.Ioi A,
          1 / Real.rpow x (α₀ - 1)| < ε := by
    have hball :=
      hpowerTail.eventually (Metric.ball_mem_nhds 0 hε)
    simpa only [Real.dist_eq, sub_zero] using hball
  obtain ⟨B, hB⟩ := eventually_atTop.1 hev
  have hmax : (1 : ℝ) < max 2 B :=
    (show (1 : ℝ) < 2 by norm_num).trans_le
      (le_max_left 2 B)
  refine ⟨max 2 B, hmax, ?_⟩
  intro A α hA hα
  have hA1 : 1 < A := hmax.trans hA
  have hAB : B ≤ A := (le_max_right 2 B).trans hA.le
  have hαint :
      IntegrableOn (integrand α) (Set.Ioi A) :=
    (integrableOn_integrand_tail α α₀ hα₀ hα).mono_set
      (Set.Ioi_subset_Ioi hA1.le)
  have hpint :
      IntegrableOn
        (fun x : ℝ => 1 / Real.rpow x (α₀ - 1))
        (Set.Ioi A) :=
    (power_tail_integrable α₀ hα₀).mono_set
      (Set.Ioi_subset_Ioi hA1.le)
  have hnonneg :
      0 ≤ ∫ x in Set.Ioi A, integrand α x := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro x hx
    have hx1 : 1 ≤ x := hA1.le.trans hx.le
    exact (gap1 x α α₀ hα₀ hx1 hα).le
  rw [abs_of_nonneg hnonneg]
  calc
    (∫ x in Set.Ioi A, integrand α x) ≤
        ∫ x in Set.Ioi A,
          1 / Real.rpow x (α₀ - 1) := by
      apply setIntegral_mono_on hαint hpint measurableSet_Ioi
      intro x hx
      have hx1 : 1 ≤ x := hA1.le.trans hx.le
      exact (gap2 x α α₀ hα₀ hx1 hα).le.trans
        (gap3 x α α₀ hα₀ hx1 hα)
    _ ≤ |∫ x in Set.Ioi A,
          1 / Real.rpow x (α₀ - 1)| :=
      le_abs_self _
    _ < ε := hB A hAB

private def majorant (α₀ x : ℝ) : ℝ :=
  if x ≤ 1 then x / 2
  else 1 / Real.rpow x (α₀ - 1)

private lemma integrableOn_majorant (α₀ : ℝ) (hα₀ : 2 < α₀) :
    IntegrableOn (majorant α₀) (Set.Ioi 0) := by
  have hsmall :
      IntegrableOn (majorant α₀) (Set.Ioc 0 1) := by
    have hlin :
        IntegrableOn (fun x : ℝ => x / 2) (Set.Ioc 0 1) :=
      ((continuous_id.div_const 2).integrableOn_Icc).mono_set
        Set.Ioc_subset_Icc_self
    refine hlin.congr_fun ?_ measurableSet_Ioc
    intro x hx
    simp [majorant, hx.2]
  have hlarge :
      IntegrableOn (majorant α₀) (Set.Ioi 1) := by
    refine (power_tail_integrable α₀ hα₀).congr_fun
      ?_ measurableSet_Ioi
    intro x hx
    have hx' : 1 < x := hx
    have hnot : ¬ x ≤ 1 := not_le.mpr hx'
    simp [majorant, hnot]
  have hu := hsmall.union hlarge
  rw [Set.Ioc_union_Ioi_eq_Ioi zero_le_one] at hu
  exact hu

private lemma continuousOn_integrand_pos (α : ℝ) :
    ContinuousOn (integrand α) (Set.Ioi 0) := by
  intro x hx
  unfold integrand
  change ContinuousWithinAt
    (fun y : ℝ => y / (2 + y ^ α)) (Set.Ioi 0) x
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div continuousAt_id
  · exact continuousAt_const.add
      (Real.continuousAt_rpow_const x α
        (Or.inl (ne_of_gt hx)))
  · have hp : 0 < x ^ α :=
      Real.rpow_pos_of_pos hx α
    exact ne_of_gt (by linarith)

theorem gap7 (α₀ : ℝ) (hα₀ : 2 < α₀) :
    ContinuousOn F (Set.Ici α₀) := by
  intro α hα
  have ht :
      Tendsto
        (fun β : ℝ =>
          ∫ x, integrand β x ∂(volume.restrict (Set.Ioi 0)))
        (nhdsWithin α (Set.Ici α₀))
        (nhds
          (∫ x, integrand α x ∂(volume.restrict (Set.Ioi 0)))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (majorant α₀)
    · filter_upwards [self_mem_nhdsWithin] with β hβ
      exact (continuousOn_integrand_pos β).aestronglyMeasurable
        measurableSet_Ioi
    · filter_upwards [self_mem_nhdsWithin] with β hβ
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxpos : 0 < x := hx
      have hxnorm :
          ‖integrand β x‖ = integrand β x := by
        rw [Real.norm_eq_abs, abs_of_pos]
        unfold integrand
        exact div_pos hxpos
          (add_pos_of_pos_of_nonneg (by norm_num)
            (Real.rpow_nonneg hxpos.le _))
      rw [hxnorm]
      unfold majorant
      split_ifs with hx1
      · unfold integrand
        have hden :
            2 ≤ 2 + Real.rpow x β :=
          le_add_of_nonneg_right (Real.rpow_nonneg hxpos.le _)
        exact (div_le_div_iff₀
          (by linarith : (0 : ℝ) < 2 + Real.rpow x β)
          (by norm_num : (0 : ℝ) < 2)).2
          (by
            have hxnonneg : 0 ≤ x := hxpos.le
            nlinarith)
      · have hxone : 1 ≤ x := le_of_not_ge hx1
        exact (gap2 x β α₀ hα₀ hxone hβ).le.trans
          (gap3 x β α₀ hα₀ hxone hβ)
    · exact integrableOn_majorant α₀ hα₀
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxpos : 0 < x := hx
      have hr :
          ContinuousAt (fun β : ℝ => Real.rpow x β) α := by
        change ContinuousAt (fun β : ℝ => x ^ β) α
        exact Real.continuousAt_const_rpow hxpos.ne'
      have hc :
          ContinuousAt (fun β : ℝ => integrand β x) α := by
        unfold integrand
        apply ContinuousAt.div continuousAt_const
        · exact continuousAt_const.add hr
        · exact ne_of_gt
            (add_pos_of_pos_of_nonneg (by norm_num)
              (Real.rpow_nonneg hxpos.le _))
      exact hc.tendsto.mono_left inf_le_left
  simpa [F] using ht

theorem gap8 :
    ContinuousOn F (Set.Ioi 2) := by
  intro α hα
  have hαgt : 2 < α := hα
  let α₀ : ℝ := (α + 2) / 2
  have hα₀ : 2 < α₀ := by
    dsimp [α₀]
    linarith
  have hα₀α : α₀ < α := by
    dsimp [α₀]
    linarith
  have hcont := gap7 α₀ hα₀
  exact (hcont.continuousAt (Ici_mem_nhds hα₀α)).continuousWithinAt

theorem gap9 :
    ContinuousOn F (Set.Ioi 2) := by
  exact gap8

end

end ProofGap.Exercise3779
