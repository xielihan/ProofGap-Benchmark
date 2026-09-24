import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add

namespace ProofGap.Exercise3970

noncomputable section

open MeasureTheory
open scoped Interval

def intersectionPoints : Set (ℝ × ℝ) :=
  {p | p.1 * p.2 = 1 ∧ p.1 + p.2 = 5 / 2}

def positiveRegion : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ 0 < p.2 ∧
    1 ≤ p.1 * p.2 ∧ p.1 + p.2 ≤ 5 / 2}

def regionIntegral : ℝ :=
  ∫ p in positiveRegion, p.1 * p.2

theorem gap1 :
    intersectionPoints =
      ({((1 / 2 : ℝ), (2 : ℝ)), ((2 : ℝ), (1 / 2 : ℝ))} :
        Set (ℝ × ℝ)) := by
  ext p
  rcases p with ⟨x, y⟩
  simp only [intersectionPoints, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hxy, hsum⟩
    have hy : y = 5 / 2 - x := by
      linarith
    rw [hy] at hxy
    have hfac : (2 * x - 1) * (x - 2) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfac with hx | hx
    · left
      constructor
      · linarith
      · linarith
    · right
      constructor
      · linarith
      · linarith
  · rintro (h | h)
    · rcases h with ⟨rfl, rfl⟩
      norm_num
    · rcases h with ⟨rfl, rfl⟩
      norm_num

theorem gap2 :
    regionIntegral =
      ∫ x in (1 / 2 : ℝ)..2,
        ∫ y in 1 / x..5 / 2 - x, x * y := by
  classical
  let g : ℝ × ℝ → ℝ := fun p => p.1 * p.2
  have hmeas : MeasurableSet positiveRegion := by
    unfold positiveRegion
    measurability
  have hsubset :
      positiveRegion ⊆
        Set.Icc (0 : ℝ) (5 / 2) ×ˢ Set.Icc (0 : ℝ) (5 / 2) := by
    rintro ⟨x, y⟩ ⟨hx, hy, hxy, hsum⟩
    simp only [Set.mem_prod, Set.mem_Icc]
    constructor
    · constructor
      · exact hx.le
      · linarith
    · constructor
      · exact hy.le
      · linarith
  have hgcont : Continuous g := by
    exact continuous_fst.mul continuous_snd
  have hgint : IntegrableOn g positiveRegion volume := by
    have hbox : IsCompact
        (Set.Icc (0 : ℝ) (5 / 2) ×ˢ Set.Icc (0 : ℝ) (5 / 2)) :=
      isCompact_Icc.prod isCompact_Icc
    exact
      (hgcont.continuousOn.integrableOn_compact hbox).mono_set hsubset
  have hxrange : ∀ {x y : ℝ}, (x, y) ∈ positiveRegion →
      x ∈ Set.Icc (1 / 2 : ℝ) 2 := by
    intro x y hp
    rcases hp with ⟨hx, hy, hxy, hsum⟩
    have hyupper : y ≤ 5 / 2 - x := by
      linarith
    have hmulupper : x * y ≤ x * (5 / 2 - x) :=
      mul_le_mul_of_nonneg_left hyupper hx.le
    have hquad : (2 * x - 1) * (x - 2) ≤ 0 := by
      nlinarith
    constructor
    · by_contra h
      have hxlt : x < 1 / 2 := lt_of_not_ge h
      have hp' : 0 < (2 * x - 1) * (x - 2) :=
        mul_pos_of_neg_of_neg (by linarith) (by linarith)
      linarith
    · by_contra h
      have hxlt : 2 < x := lt_of_not_ge h
      have hp' : 0 < (2 * x - 1) * (x - 2) :=
        mul_pos (by linarith) (by linarith)
      linarith
  have hsection : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2,
      (∫ y : ℝ, positiveRegion.indicator g (x, y)) =
        ∫ y in 1 / x..5 / 2 - x, x * y := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
    have hbound : 1 / x ≤ 5 / 2 - x := by
      apply (div_le_iff₀ hxpos).2
      have hnonneg : 0 ≤ 2 * x - 1 := by
        nlinarith [hx.1]
      have hnonpos : x - 2 ≤ 0 := by
        nlinarith [hx.2]
      have hprod : (2 * x - 1) * (x - 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hnonneg hnonpos
      nlinarith
    have hmem : ∀ y : ℝ, (x, y) ∈ positiveRegion ↔
        1 / x ≤ y ∧ y ≤ 5 / 2 - x := by
      intro y
      constructor
      · rintro ⟨_, _, hxy, hsum⟩
        constructor
        · apply (div_le_iff₀ hxpos).2
          nlinarith [hxy]
        · linarith
      · rintro ⟨hylower, hyupper⟩
        have hinvpos : 0 < 1 / x := one_div_pos.mpr hxpos
        have hypos : 0 < y := lt_of_lt_of_le hinvpos hylower
        have hxy : 1 ≤ x * y := by
          have := (div_le_iff₀ hxpos).1 hylower
          nlinarith
        refine ⟨hxpos, hypos, hxy, ?_⟩
        linarith
    have hae : ∀ᵐ y : ℝ ∂volume, y ≠ 1 / x := by
      rw [ae_iff]
      simp
    have hind : ∀ᵐ y : ℝ ∂volume,
        positiveRegion.indicator g (x, y) =
          (Set.Ioc (1 / x) (5 / 2 - x)).indicator (fun y : ℝ => x * y) y := by
      filter_upwards [hae] with y hy
      simp only [Set.indicator_apply, Set.mem_Ioc]
      rw [hmem y]
      by_cases hlow : 1 / x ≤ y
      · have hstrict : 1 / x < y := lt_of_le_of_ne hlow (Ne.symm hy)
        by_cases hu : y ≤ 5 / 2 - x
        · rw [if_pos ⟨hlow, hu⟩, if_pos ⟨hstrict, hu⟩]
        · rw [if_neg (fun h => hu h.2), if_neg (fun h => hu h.2)]
      · have hnstrict : ¬1 / x < y := fun h => hlow h.le
        rw [if_neg (fun h => hlow h.1), if_neg (fun h => hnstrict h.1)]
    calc
      (∫ y : ℝ, positiveRegion.indicator g (x, y)) =
          ∫ y : ℝ,
            (Set.Ioc (1 / x) (5 / 2 - x)).indicator
              (fun y : ℝ => x * y) y :=
        MeasureTheory.integral_congr_ae hind
      _ = ∫ y in Set.Ioc (1 / x) (5 / 2 - x), x * y :=
        MeasureTheory.integral_indicator measurableSet_Ioc
      _ = ∫ y in 1 / x..5 / 2 - x, x * y :=
        (intervalIntegral.integral_of_le hbound).symm
  have houter :
      (∫ x : ℝ, ∫ y : ℝ, positiveRegion.indicator g (x, y)) =
        ∫ x in (1 / 2 : ℝ)..2,
          ∫ y in 1 / x..5 / 2 - x, x * y := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    apply MeasureTheory.integral_congr_ae
    have hae : ∀ᵐ x : ℝ ∂volume, x ≠ 1 / 2 := by
      rw [ae_iff]
      simp
    filter_upwards [hae] with x hxne
    by_cases hx : x ∈ Set.Ioc (1 / 2 : ℝ) 2
    · rw [Set.indicator_of_mem hx]
      exact hsection x ⟨hx.1.le, hx.2⟩
    · simp only [Set.indicator_apply, hx, if_false]
      have hnoreg : ∀ y : ℝ, (x, y) ∉ positiveRegion := by
        intro y hp
        have hrange := hxrange hp
        have hxstrict : 1 / 2 < x := lt_of_le_of_ne hrange.1 (Ne.symm hxne)
        exact hx ⟨hxstrict, hrange.2⟩
      simp [hnoreg, g]
  rw [regionIntegral]
  calc
    (∫ p in positiveRegion, p.1 * p.2) =
        ∫ p : ℝ × ℝ, positiveRegion.indicator g p := by
      symm
      simpa [g] using MeasureTheory.integral_indicator hmeas (f := g)
    _ = ∫ x : ℝ, ∫ y : ℝ, positiveRegion.indicator g (x, y) := by
      have hgint' : Integrable (positiveRegion.indicator g) volume :=
        (integrable_indicator_iff hmeas).2 hgint
      simpa using MeasureTheory.integral_prod _ hgint'
    _ = ∫ x in (1 / 2 : ℝ)..2,
          ∫ y in 1 / x..5 / 2 - x, x * y := houter

theorem gap3 :
    (∫ x in (1 / 2 : ℝ)..2,
        ∫ y in 1 / x..5 / 2 - x, x * y) =
      1 / 2 *
        ∫ x in (1 / 2 : ℝ)..2,
          25 / 4 * x - 5 * x ^ 2 + x ^ 3 - 1 / x := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hxmem
  change (∫ y in 1 / x..5 / 2 - x, x * y) =
    1 / 2 * (25 / 4 * x - 5 * x ^ 2 + x ^ 3 - 1 / x)
  rw [Set.uIcc_of_le (by norm_num)] at hxmem
  have hxpos : 0 < x :=
    lt_of_lt_of_le (by norm_num) hxmem.1
  have hxne : x ≠ 0 := ne_of_gt hxpos
  let F : ℝ → ℝ := fun y => x / 2 * y ^ 2
  have hint : IntervalIntegrable (fun y : ℝ => x * y) volume
      (1 / x) (5 / 2 - x) := by
    have hc : Continuous (fun y : ℝ => x * y) :=
      continuous_const.mul continuous_id
    exact hc.intervalIntegrable (μ := volume) (1 / x) (5 / 2 - x)
  have heval :
      (∫ y in 1 / x..5 / 2 - x, x * y) =
        F (5 / 2 - x) - F (1 / x) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt <;> try exact hint
    intro y hy
    dsimp [F]
    convert ((hasDerivAt_id y).pow 2).const_mul (x / 2) using 1 <;>
      norm_num <;> ring
  rw [heval]
  dsimp [F]
  field_simp [hxne] <;> ring

theorem gap4 :
    1 / 2 *
        (∫ x in (1 / 2 : ℝ)..2,
          25 / 4 * x - 5 * x ^ 2 + x ^ 3 - 1 / x) =
      165 / 128 - Real.log 2 := by
  have hA : IntervalIntegrable (fun x : ℝ => 25 / 4 * x) volume
      (1 / 2) 2 := by
    have hc : Continuous (fun x : ℝ => 25 / 4 * x) :=
      continuous_const.mul continuous_id
    exact hc.intervalIntegrable (μ := volume) (1 / 2) 2
  have hB : IntervalIntegrable (fun x : ℝ => 5 * x ^ 2) volume
      (1 / 2) 2 := by
    have hc : Continuous (fun x : ℝ => 5 * x ^ 2) :=
      continuous_const.mul (continuous_id.pow 2)
    exact hc.intervalIntegrable (μ := volume) (1 / 2) 2
  have hC : IntervalIntegrable (fun x : ℝ => x ^ 3) volume
      (1 / 2) 2 := by
    have hc : Continuous (fun x : ℝ => x ^ 3) :=
      continuous_id.pow 3
    exact hc.intervalIntegrable (μ := volume) (1 / 2) 2
  have hD : IntervalIntegrable (fun x : ℝ => 1 / x) volume
      (1 / 2) 2 := by
    refine (continuousOn_const.div continuousOn_id ?_).intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hx.1)
  have hint : IntervalIntegrable
      (fun x : ℝ => 25 / 4 * x - 5 * x ^ 2 + x ^ 3 - 1 / x)
      volume (1 / 2) 2 :=
    ((hA.sub hB).add hC).sub hD
  let F : ℝ → ℝ := fun x =>
    25 / 8 * x ^ 2 - 5 / 3 * x ^ 3 + 1 / 4 * x ^ 4 - Real.log x
  have heval :
      (∫ x in (1 / 2 : ℝ)..2,
        25 / 4 * x - 5 * x ^ 2 + x ^ 3 - 1 / x) =
        F 2 - F (1 / 2) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt <;> try exact hint
    intro x hx
    have hxpos : 0 < x := by
      rw [Set.uIcc_of_le (by norm_num)] at hx
      exact lt_of_lt_of_le (by norm_num) hx.1
    dsimp [F]
    have h2 := ((hasDerivAt_id x).pow 2).const_mul (25 / 8)
    have h3 := ((hasDerivAt_id x).pow 3).const_mul (5 / 3)
    have h4 := ((hasDerivAt_id x).pow 4).const_mul (1 / 4)
    have hlog := Real.hasDerivAt_log (ne_of_gt hxpos)
    convert (((h2.sub h3).add h4).sub hlog) using 1 <;>
      norm_num <;> ring
  rw [heval]
  dsimp [F]
  have hhalf : Real.log (1 / 2) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
    exact Real.log_inv 2
  rw [hhalf]
  norm_num <;> ring

theorem gap5 :
    regionIntegral = 165 / 128 - Real.log 2 := by
  rw [gap2, gap3, gap4]

end

end ProofGap.Exercise3970
