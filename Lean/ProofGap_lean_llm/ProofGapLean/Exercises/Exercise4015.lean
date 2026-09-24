import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4015

noncomputable section

open MeasureTheory
open scoped Interval

def polarX (r φ : ℝ) : ℝ :=
  r * Real.cos φ

def polarY (r φ : ℝ) : ℝ :=
  r * Real.sin φ

def polarHeight (r φ : ℝ) : ℝ :=
  polarX r φ ^ 2 + polarY r φ ^ 2

def baseRegion : Set (ℝ × ℝ) :=
  {p |
    p.1 ≤ p.1 ^ 2 + p.2 ^ 2 ∧
      p.1 ^ 2 + p.2 ^ 2 ≤ 2 * p.1}

def volume : ℝ :=
  ∫ p in baseRegion, p.1 ^ 2 + p.2 ^ 2

theorem gap1 (r φ : ℝ) (hr : r ≠ 0)
    (hcircle :
      polarX r φ ^ 2 + polarY r φ ^ 2 = polarX r φ) :
    r = Real.cos φ := by
  have htrig : polarX r φ ^ 2 + polarY r φ ^ 2 = r ^ 2 := by
    unfold polarX polarY
    nlinarith [Real.sin_sq_add_cos_sq φ]
  have hfac : r * (r - Real.cos φ) = 0 := by
    rw [htrig] at hcircle
    unfold polarX at hcircle
    nlinarith
  rcases mul_eq_zero.mp hfac with h | h
  · exact (hr h).elim
  · linarith

theorem gap2 (r φ : ℝ) (hr : r ≠ 0)
    (hcircle :
      polarX r φ ^ 2 + polarY r φ ^ 2 = 2 * polarX r φ) :
    r = 2 * Real.cos φ := by
  have htrig : polarX r φ ^ 2 + polarY r φ ^ 2 = r ^ 2 := by
    unfold polarX polarY
    nlinarith [Real.sin_sq_add_cos_sq φ]
  have hfac : r * (r - 2 * Real.cos φ) = 0 := by
    rw [htrig] at hcircle
    unfold polarX at hcircle
    nlinarith
  rcases mul_eq_zero.mp hfac with h | h
  · exact (hr h).elim
  · linarith

theorem gap3 (r φ : ℝ) :
    polarHeight r φ = r ^ 2 := by
  unfold polarHeight polarX polarY
  nlinarith [Real.sin_sq_add_cos_sq φ]

private def polarRegion : Set (ℝ × ℝ) :=
  {p |
    -(Real.pi / 2) < p.2 ∧ p.2 < Real.pi / 2 ∧
      Real.cos p.2 ≤ p.1 ∧ p.1 ≤ 2 * Real.cos p.2}

private theorem polarRegion_measurable : MeasurableSet polarRegion := by
  unfold polarRegion
  measurability

private theorem polar_characterization (p : ℝ × ℝ) :
    p ∈ polarCoord.target ∧ polarCoord.symm p ∈ baseRegion ↔
      p ∈ polarRegion := by
  rcases p with ⟨r, φ⟩
  have htrig :
      (r * Real.cos φ) ^ 2 + (r * Real.sin φ) ^ 2 = r ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq φ]
  constructor
  · rintro ⟨ht, hb⟩
    have ht' : 0 < r ∧ -Real.pi < φ ∧ φ < Real.pi := by
      simpa [polarCoord_target] using ht
    have hb' :
        r * Real.cos φ ≤ r ^ 2 ∧ r ^ 2 ≤ 2 * (r * Real.cos φ) := by
      simpa [baseRegion, polarCoord_symm_apply, htrig] using hb
    have hlower : Real.cos φ ≤ r := by
      by_contra h
      have hlt : r < Real.cos φ := lt_of_not_ge h
      have hpos : 0 < r * (Real.cos φ - r) :=
        mul_pos ht'.1 (sub_pos.mpr hlt)
      nlinarith [hb'.1]
    have hupper : r ≤ 2 * Real.cos φ := by
      nlinarith
    have hcos : 0 < Real.cos φ := by nlinarith
    have hφupper : φ < Real.pi / 2 := by
      by_contra h
      have hle : Real.pi / 2 ≤ φ := le_of_not_gt h
      have hnonpos : Real.cos φ ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le hle (by linarith [Real.pi_pos])
      linarith
    have hφlower : -(Real.pi / 2) < φ := by
      by_contra h
      have hle : φ ≤ -(Real.pi / 2) := le_of_not_gt h
      have hnonposNeg : Real.cos (-φ) ≤ 0 := by
        apply Real.cos_nonpos_of_pi_div_two_le_of_le
        · linarith
        · linarith [Real.pi_pos]
      rw [Real.cos_neg] at hnonposNeg
      linarith
    exact ⟨hφlower, hφupper, hlower, hupper⟩
  · rintro ⟨hφlower, hφupper, hlower, hupper⟩
    have hcos : 0 < Real.cos φ :=
      Real.cos_pos_of_mem_Ioo ⟨hφlower, hφupper⟩
    have hr : 0 < r := lt_of_lt_of_le hcos hlower
    have ht : (r, φ) ∈ polarCoord.target := by
      simp only [polarCoord_target, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
      constructor
      · exact hr
      · constructor <;> linarith [Real.pi_pos]
    have hb : polarCoord.symm (r, φ) ∈ baseRegion := by
      simp only [baseRegion, polarCoord_symm_apply, Set.mem_setOf_eq,
        Prod.fst, Prod.snd, htrig]
      constructor
      · nlinarith
      · nlinarith
    exact ⟨ht, hb⟩

theorem gap4 :
    volume =
      ∫ φ in -Real.pi / 2..Real.pi / 2,
        ∫ r in Real.cos φ..2 * Real.cos φ, r ^ 3 := by
  let f : ℝ × ℝ → ℝ := fun p => p.1 ^ 2 + p.2 ^ 2
  let q : ℝ × ℝ → ℝ := fun p => p.1 ^ 3
  have hbase : MeasurableSet baseRegion := by
    unfold baseRegion
    measurability
  have hpoint : ∀ p : ℝ × ℝ,
      polarCoord.target.indicator
          (fun z => z.1 * baseRegion.indicator f (polarCoord.symm z)) p =
        polarRegion.indicator q p := by
    intro p
    by_cases hp : p ∈ polarRegion
    · have hc := (polar_characterization p).mpr hp
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem hc.1,
        Set.indicator_of_mem hc.2]
      rcases p with ⟨r, φ⟩
      simp only [q, f, polarCoord_symm_apply, Prod.fst, Prod.snd]
      have htrig :
          (r * Real.cos φ) ^ 2 + (r * Real.sin φ) ^ 2 = r ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq φ]
      rw [htrig]
      ring
    · have hc : ¬(p ∈ polarCoord.target ∧ polarCoord.symm p ∈ baseRegion) := by
        intro h
        exact hp ((polar_characterization p).mp h)
      rw [Set.indicator_of_notMem hp]
      by_cases ht : p ∈ polarCoord.target
      · have hb : polarCoord.symm p ∉ baseRegion := fun h => hc ⟨ht, h⟩
        rw [Set.indicator_of_mem ht, Set.indicator_of_notMem hb]
        simp
      · rw [Set.indicator_of_notMem ht]
  have hqcont : Continuous q := by
    dsimp [q]
    fun_prop
  have hsubset :
      polarRegion ⊆
        Set.Icc (0 : ℝ) 2 ×ˢ
          Set.Icc (-Real.pi / 2) (Real.pi / 2) := by
    rintro ⟨r, φ⟩ hp
    have hcospos : 0 < Real.cos φ :=
      Real.cos_pos_of_mem_Ioo ⟨hp.1, hp.2.1⟩
    have hcosle : Real.cos φ ≤ 1 := Real.cos_le_one φ
    exact ⟨⟨hcospos.le.trans hp.2.2.1, hp.2.2.2.trans (by linarith)⟩,
      ⟨by linarith [hp.1], hp.2.1.le⟩⟩
  have hbox :
      IsCompact (Set.Icc (0 : ℝ) 2 ×ˢ
        Set.Icc (-Real.pi / 2) (Real.pi / 2)) :=
    isCompact_Icc.prod isCompact_Icc
  have hqint : IntegrableOn q polarRegion :=
    (hqcont.continuousOn.integrableOn_compact hbox).mono_set hsubset
  have hglobal : Integrable (polarRegion.indicator q) :=
    (integrable_indicator_iff polarRegion_measurable).2 hqint
  have hinner : ∀ φ : ℝ,
      (∫ r : ℝ, polarRegion.indicator q (r, φ)) =
        (Set.Ioo (-Real.pi / 2) (Real.pi / 2)).indicator
          (fun φ => ∫ r in Real.cos φ..2 * Real.cos φ, r ^ 3) φ := by
    intro φ
    by_cases hφ : φ ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2)
    · rw [Set.indicator_of_mem hφ]
      have hcos : 0 < Real.cos φ :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ.1], hφ.2⟩
      have hind :
          (fun r : ℝ => polarRegion.indicator q (r, φ)) =
            (Set.Icc (Real.cos φ) (2 * Real.cos φ)).indicator
              (fun r : ℝ => r ^ 3) := by
        funext r
        have hmem :
            (r, φ) ∈ polarRegion ↔
              r ∈ Set.Icc (Real.cos φ) (2 * Real.cos φ) := by
          constructor
          · intro hp
            exact ⟨hp.2.2.1, hp.2.2.2⟩
          · intro hr
            exact ⟨by linarith [hφ.1], hφ.2, hr.1, hr.2⟩
        by_cases hr : r ∈ Set.Icc (Real.cos φ) (2 * Real.cos φ)
        · rw [Set.indicator_of_mem hr,
            Set.indicator_of_mem (hmem.mpr hr)]
        · rw [Set.indicator_of_notMem hr,
            Set.indicator_of_notMem (fun hp => hr (hmem.mp hp))]
      rw [hind, MeasureTheory.integral_indicator measurableSet_Icc]
      rw [← Measure.restrict_congr_set
        (Ioc_ae_eq_Icc :
          Set.Ioc (Real.cos φ) (2 * Real.cos φ) =ᵐ[MeasureTheory.volume]
            Set.Icc (Real.cos φ) (2 * Real.cos φ))]
      rw [← intervalIntegral.integral_of_le (by linarith)]
    · rw [Set.indicator_of_notMem hφ]
      have hnone : ∀ r : ℝ, (r, φ) ∉ polarRegion := by
        intro r hp
        exact hφ ⟨by linarith [hp.1], hp.2.1⟩
      simp [hnone]
  calc
    volume = ∫ p : ℝ × ℝ, baseRegion.indicator f p := by
      rw [volume, MeasureTheory.integral_indicator hbase]
    _ = ∫ p in polarCoord.target,
          p.1 * baseRegion.indicator f (polarCoord.symm p) := by
          simpa [smul_eq_mul] using
            (integral_comp_polarCoord_symm (baseRegion.indicator f)).symm
    _ = ∫ p : ℝ × ℝ, polarRegion.indicator q p := by
          rw [← MeasureTheory.integral_indicator polarCoord.open_target.measurableSet]
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
    _ = ∫ φ : ℝ, ∫ r : ℝ, polarRegion.indicator q (r, φ) := by
          simpa using MeasureTheory.integral_prod_symm _ hglobal
    _ = ∫ φ : ℝ,
          (Set.Ioo (-Real.pi / 2) (Real.pi / 2)).indicator
            (fun φ => ∫ r in Real.cos φ..2 * Real.cos φ, r ^ 3) φ := by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall hinner
    _ = ∫ φ in Set.Ioo (-Real.pi / 2) (Real.pi / 2),
          ∫ r in Real.cos φ..2 * Real.cos φ, r ^ 3 := by
          rw [MeasureTheory.integral_indicator measurableSet_Ioo]
    _ = ∫ φ in Set.Ioc (-Real.pi / 2) (Real.pi / 2),
          ∫ r in Real.cos φ..2 * Real.cos φ, r ^ 3 := by
          rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    _ = ∫ φ in -Real.pi / 2..Real.pi / 2,
          ∫ r in Real.cos φ..2 * Real.cos φ, r ^ 3 := by
          rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]

private theorem radial_integral (φ : ℝ) :
    (∫ r in Real.cos φ..2 * Real.cos φ, r ^ 3) =
      15 / 4 * Real.cos φ ^ 4 := by
  let F : ℝ → ℝ := fun r => r ^ 4 / 4
  have hd : ∀ r : ℝ, HasDerivAt F (r ^ 3) r := by
    intro r
    convert ((hasDerivAt_id r).pow 4).div_const 4 using 1 <;>
      simp only [id_eq] <;> ring
  have hi : IntervalIntegrable (fun r : ℝ => r ^ 3)
      MeasureTheory.volume (Real.cos φ) (2 * Real.cos φ) :=
    (continuous_id.pow 3).intervalIntegrable _ _
  calc
    _ = F (2 * Real.cos φ) - F (Real.cos φ) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro r hr
        exact hd r
      · exact hi
    _ = _ := by dsimp [F]; ring

private theorem cos4_quarter :
    (∫ φ in (0 : ℝ)..Real.pi / 2, Real.cos φ ^ 4) =
      3 * Real.pi / 16 := by
  rw [show (4 : ℕ) = 2 + 2 by norm_num, integral_cos_pow]
  simp
  ring

private theorem cos4_symmetric :
    (∫ φ in -Real.pi / 2..Real.pi / 2, Real.cos φ ^ 4) =
      3 * Real.pi / 8 := by
  have hcosneg :
      Real.cos (Real.pi * (-1 / 2 : ℝ)) = 0 := by
    rw [show Real.pi * (-1 / 2 : ℝ) = -(Real.pi / 2) by ring,
      Real.cos_neg, Real.cos_pi_div_two]
  have hcospos :
      Real.cos (Real.pi * (1 / 2 : ℝ)) = 0 := by
    rw [show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring,
      Real.cos_pi_div_two]
  rw [show (4 : ℕ) = 2 + 2 by norm_num, integral_cos_pow]
  simp only [integral_cos_sq]
  ring_nf at hcosneg hcospos ⊢
  rw [hcosneg, hcospos]
  ring

private theorem volume_formula : volume = 45 / 32 * Real.pi := by
  rw [gap4]
  calc
    (∫ φ in -Real.pi / 2..Real.pi / 2,
      ∫ r in Real.cos φ..2 * Real.cos φ, r ^ 3) =
        ∫ φ in -Real.pi / 2..Real.pi / 2,
          15 / 4 * Real.cos φ ^ 4 := by
            apply intervalIntegral.integral_congr
            intro φ hφ
            exact radial_integral φ
    _ = 15 / 4 *
        ∫ φ in -Real.pi / 2..Real.pi / 2,
          Real.cos φ ^ 4 := by
            rw [intervalIntegral.integral_const_mul]
    _ = 45 / 32 * Real.pi := by rw [cos4_symmetric]; ring

theorem gap5 :
    volume =
      2 / 4 *
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          16 * Real.cos φ ^ 4 - Real.cos φ ^ 4 := by
  rw [volume_formula]
  have hi : IntervalIntegrable (fun φ : ℝ => Real.cos φ ^ 4)
      MeasureTheory.volume 0 (Real.pi / 2) :=
    (Real.continuous_cos.pow 4).intervalIntegrable _ _
  calc
    45 / 32 * Real.pi =
        2 / 4 * (15 * (3 * Real.pi / 16)) := by ring
    _ = 2 / 4 * (15 *
        ∫ φ in (0 : ℝ)..Real.pi / 2, Real.cos φ ^ 4) := by
          rw [cos4_quarter]
    _ = 2 / 4 *
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          15 * Real.cos φ ^ 4 := by
          rw [intervalIntegral.integral_const_mul]
    _ = _ := by
          congr 1
          apply intervalIntegral.integral_congr
          intro φ hφ
          ring

theorem gap6 :
    2 / 4 *
        (∫ φ in (0 : ℝ)..Real.pi / 2,
          16 * Real.cos φ ^ 4 - Real.cos φ ^ 4) =
      15 / 2 *
        ∫ φ in (0 : ℝ)..Real.pi / 2, Real.cos φ ^ 4 := by
  have hcongr :
      (∫ φ in (0 : ℝ)..Real.pi / 2,
        16 * Real.cos φ ^ 4 - Real.cos φ ^ 4) =
        15 * ∫ φ in (0 : ℝ)..Real.pi / 2,
          Real.cos φ ^ 4 := by
    calc
      _ = ∫ φ in (0 : ℝ)..Real.pi / 2,
          15 * Real.cos φ ^ 4 := by
            apply intervalIntegral.integral_congr
            intro φ hφ
            ring
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  rw [hcongr]
  ring

theorem gap7 :
    volume =
      15 / 2 *
        ∫ φ in (0 : ℝ)..Real.pi / 2, Real.cos φ ^ 4 := by
  rw [volume_formula, cos4_quarter]
  ring

theorem gap8 :
    volume =
      15 / 2 * (3 / 4) * (1 / 2) * (Real.pi / 2) := by
  rw [volume_formula]
  ring

theorem gap9 :
    15 / 2 * (3 / 4) * (1 / 2) * (Real.pi / 2) =
      45 / 32 * Real.pi := by
  ring

theorem gap10 :
    volume = 45 / 32 * Real.pi := by
  exact volume_formula

end

end ProofGap.Exercise4015
