import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise4136

noncomputable section

open MeasureTheory Set
open scoped Interval

abbrev Point3 := ℝ × ℝ × ℝ

def solid (a b c : ℝ) : Set Point3 :=
  {p |
    0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧
      p.1 ^ 2 / a ^ 2 + p.2.1 ^ 2 / b ^ 2 + p.2.2 ^ 2 / c ^ 2 ≤ 1}

def mass (a b c : ℝ) : ℝ :=
  ∫ _p in solid a b c, (1 : ℝ)

def xCentroid (a b c : ℝ) : ℝ :=
  1 / mass a b c * ∫ p in solid a b c, p.1

def yCentroid (a b c : ℝ) : ℝ :=
  1 / mass a b c * ∫ p in solid a b c, p.2.1

def zCentroid (a b c : ℝ) : ℝ :=
  1 / mass a b c * ∫ p in solid a b c, p.2.2

private def unitOctant : Set Point3 :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧
    p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤ 1}

private theorem intervalIntegral_eq_sub_of_hasDerivAt
    {f F : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (f x) x)
    (hf : Continuous f) (l u : ℝ) :
    intervalIntegral f l u volume = F u - F l := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _hx => hF x) (hf.intervalIntegrable (μ := volume) l u)

private theorem quarter_circle (r : ℝ) (hr : 0 ≤ r) :
    intervalIntegral (fun y : ℝ => Real.sqrt (r ^ 2 - y ^ 2))
        0 r volume =
      Real.pi * r ^ 2 / 4 := by
  by_cases hr0 : r = 0
  · subst r
    simp
  let f := fun y : ℝ => Real.sqrt (r ^ 2 - y ^ 2)
  have hf : Continuous f := by
    dsimp only [f]
    fun_prop
  have hneg :
      intervalIntegral f (-r) 0 volume =
        intervalIntegral f 0 r volume := by
    calc
      intervalIntegral f (-r) 0 volume =
          intervalIntegral (fun x : ℝ => f (-x)) 0 r volume := by
        simpa using
          (intervalIntegral.integral_comp_neg
            (f := f) (a := 0) (b := r)).symm
      _ = intervalIntegral f 0 r volume := by
        apply intervalIntegral.integral_congr
        intro x hx
        simp [f]
  have hsplit :
      intervalIntegral f (-r) r volume =
        2 * intervalIntegral f 0 r volume := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (μ := volume) (-r) 0)
      (hf.intervalIntegrable (μ := volume) 0 r)
    rw [hneg] at hadd
    linarith
  have hinside :
      intervalIntegral (fun x : ℝ => f (r * x)) (-1) 1 volume =
        r * (Real.pi / 2) := by
    calc
      intervalIntegral (fun x : ℝ => f (r * x)) (-1) 1 volume =
          intervalIntegral
            (fun x : ℝ => r * Real.sqrt (1 - x ^ 2))
            (-1) 1 volume := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
        have hprod : 0 ≤ (x + 1) * (1 - x) :=
          mul_nonneg (by linarith [hx.1]) (by linarith [hx.2])
        have hone : 0 ≤ 1 - x ^ 2 := by nlinarith
        dsimp only [f]
        rw [show r ^ 2 - (r * x) ^ 2 = r ^ 2 * (1 - x ^ 2) by ring]
        rw [Real.sqrt_mul (sq_nonneg r)]
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hr]
      _ = r * intervalIntegral
          (fun x : ℝ => Real.sqrt (1 - x ^ 2)) (-1) 1 volume := by
        rw [intervalIntegral.integral_const_mul]
      _ = r * (Real.pi / 2) := by
        rw [integral_sqrt_one_sub_sq]
  have hfull :
      intervalIntegral f (-r) r volume =
        Real.pi * r ^ 2 / 2 := by
    calc
      intervalIntegral f (-r) r volume =
          r * intervalIntegral (fun x : ℝ => f (r * x))
            (-1) 1 volume := by
        simpa [smul_eq_mul] using
          (intervalIntegral.smul_integral_comp_mul_left
            (f := f) (a := (-1 : ℝ)) (b := 1) r).symm
      _ = Real.pi * r ^ 2 / 2 := by rw [hinside]; ring
  dsimp only [f] at hsplit hfull ⊢
  linarith

private theorem unitOctant_subset_cube :
    unitOctant ⊆
      Set.Icc (0 : ℝ) 1 ×ˢ
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
  intro p hp
  rcases hp with ⟨hx0, hy0, hz0, hsum⟩
  have hx1 : p.1 ≤ 1 := by
    nlinarith [sq_nonneg p.2.1, sq_nonneg p.2.2,
      sq_nonneg (1 - p.1)]
  have hy1 : p.2.1 ≤ 1 := by
    nlinarith [sq_nonneg p.1, sq_nonneg p.2.2,
      sq_nonneg (1 - p.2.1)]
  have hz1 : p.2.2 ≤ 1 := by
    nlinarith [sq_nonneg p.1, sq_nonneg p.2.1,
      sq_nonneg (1 - p.2.2)]
  exact ⟨⟨hx0, hx1⟩, ⟨⟨hy0, hy1⟩, ⟨hz0, hz1⟩⟩⟩

private theorem integral_unitOctant_eq_iterated
    (f : Point3 → ℝ) (hf : Continuous f) :
    (∫ p in unitOctant, f p ∂volume) =
      intervalIntegral
        (fun x : ℝ =>
          intervalIntegral
            (fun y : ℝ =>
              intervalIntegral (fun z : ℝ => f (x, y, z)) 0
                (Real.sqrt (1 - x ^ 2 - y ^ 2)) volume)
            0 (Real.sqrt (1 - x ^ 2)) volume)
        0 1 volume := by
  classical
  have hs : MeasurableSet unitOctant := by
    unfold unitOctant
    measurability
  have hbox :
      IntegrableOn f
        (Set.Icc (0 : ℝ) 1 ×ˢ
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) volume :=
    hf.continuousOn.integrableOn_compact
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  have hfi : IntegrableOn f unitOctant volume :=
    hbox.mono_set unitOctant_subset_cube
  have hind : Integrable (unitOctant.indicator f) volume :=
    (integrable_indicator_iff hs).2 hfi
  change Integrable (unitOctant.indicator f)
    (volume.prod (volume.prod volume)) at hind
  have hprod :
      (∫ p : Point3, unitOctant.indicator f p
          ∂volume.prod (volume.prod volume)) =
        ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
          unitOctant.indicator f (x, y, z) := by
    rw [MeasureTheory.integral_prod _ hind]
    apply integral_congr_ae
    filter_upwards [hind.prod_right_ae] with x hx
    change
      (∫ yz : ℝ × ℝ, unitOctant.indicator f (x, yz)
          ∂volume.prod volume) =
        ∫ y : ℝ, ∫ z : ℝ, unitOctant.indicator f (x, y, z)
    rw [MeasureTheory.integral_prod _ hx]
  have hsections :
      (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
        unitOctant.indicator f (x, y, z)) =
        ∫ x in Set.Icc (0 : ℝ) 1,
          ∫ y in Set.Icc (0 : ℝ) (Real.sqrt (1 - x ^ 2)),
            ∫ z in Set.Icc (0 : ℝ)
                (Real.sqrt (1 - x ^ 2 - y ^ 2)),
              f (x, y, z) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem hx]
      have hxr : 0 ≤ 1 - x ^ 2 := by
        nlinarith [mul_nonneg (by linarith [hx.2] : 0 ≤ 1 - x)
          (by linarith [hx.1] : 0 ≤ 1 + x)]
      rw [← MeasureTheory.integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy : y ∈ Set.Icc (0 : ℝ) (Real.sqrt (1 - x ^ 2))
      · rw [Set.indicator_of_mem hy]
        have hy2 : y ^ 2 ≤ 1 - x ^ 2 :=
          (Real.le_sqrt hy.1 hxr).1 hy.2
        have hxyr : 0 ≤ 1 - x ^ 2 - y ^ 2 := by linarith
        rw [← MeasureTheory.integral_indicator measurableSet_Icc]
        apply integral_congr_ae
        filter_upwards with z
        by_cases hz :
            z ∈ Set.Icc (0 : ℝ) (Real.sqrt (1 - x ^ 2 - y ^ 2))
        · have hz2 : z ^ 2 ≤ 1 - x ^ 2 - y ^ 2 :=
            (Real.le_sqrt hz.1 hxyr).1 hz.2
          have hu : (x, y, z) ∈ unitOctant :=
            ⟨hx.1, hy.1, hz.1, by linarith⟩
          simp only [Set.indicator_of_mem hz, Set.indicator_of_mem hu]
        · have hnu : (x, y, z) ∉ unitOctant := by
            intro hp
            apply hz
            refine ⟨hp.2.2.1, (Real.le_sqrt hp.2.2.1 hxyr).2 ?_⟩
            linarith [hp.2.2.2]
          simp [Set.indicator, hz, hnu]
      · have hyr :
            (Set.Icc (0 : ℝ) (Real.sqrt (1 - x ^ 2))).indicator
              (fun y =>
                ∫ z in Set.Icc (0 : ℝ)
                    (Real.sqrt (1 - x ^ 2 - y ^ 2)),
                  f (x, y, z)) y = 0 := by
          simp [Set.indicator, hy]
        rw [hyr, ← integral_zero]
        apply integral_congr_ae
        filter_upwards with z
        have hnu : (x, y, z) ∉ unitOctant := by
          intro hp
          apply hy
          refine ⟨hp.2.1, (Real.le_sqrt hp.2.1 hxr).2 ?_⟩
          linarith [hp.2.2.2, sq_nonneg z]
        simp [Set.indicator, hnu]
    · have hxr :
          (Set.Icc (0 : ℝ) 1).indicator
            (fun x =>
              ∫ y in Set.Icc (0 : ℝ) (Real.sqrt (1 - x ^ 2)),
                ∫ z in Set.Icc (0 : ℝ)
                    (Real.sqrt (1 - x ^ 2 - y ^ 2)),
                  f (x, y, z)) x = 0 := by
        simp [Set.indicator, hx]
      rw [hxr, ← integral_zero]
      apply integral_congr_ae
      filter_upwards with y
      rw [← integral_zero]
      apply integral_congr_ae
      filter_upwards with z
      have hnu : (x, y, z) ∉ unitOctant := by
        intro hp
        apply hx
        refine ⟨hp.1, ?_⟩
        nlinarith [hp.2.2.2, sq_nonneg y, sq_nonneg z,
          sq_nonneg (1 - x)]
      simp [Set.indicator, hnu]
  calc
    (∫ p in unitOctant, f p ∂volume) =
        ∫ p : Point3, unitOctant.indicator f p := by
      rw [MeasureTheory.integral_indicator hs]
    _ = ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
          unitOctant.indicator f (x, y, z) := hprod
    _ = ∫ x in Set.Icc (0 : ℝ) 1,
          ∫ y in Set.Icc (0 : ℝ) (Real.sqrt (1 - x ^ 2)),
            ∫ z in Set.Icc (0 : ℝ)
                (Real.sqrt (1 - x ^ 2 - y ^ 2)),
              f (x, y, z) := hsections
    _ = intervalIntegral
          (fun x : ℝ =>
            intervalIntegral
              (fun y : ℝ =>
                intervalIntegral (fun z : ℝ => f (x, y, z)) 0
                  (Real.sqrt (1 - x ^ 2 - y ^ 2)) volume)
              0 (Real.sqrt (1 - x ^ 2)) volume)
          0 1 volume := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      dsimp only
      rw [intervalIntegral.integral_of_le (Real.sqrt_nonneg _)]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro y hy
      dsimp only
      rw [intervalIntegral.integral_of_le (Real.sqrt_nonneg _)]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]

private theorem unitOctant_mass :
    (∫ _p in unitOctant, (1 : ℝ) ∂volume) = Real.pi / 6 := by
  rw [integral_unitOctant_eq_iterated
    (fun _p : Point3 => (1 : ℝ)) continuous_const]
  have harea (x : ℝ) (hx : x ∈ Set.uIcc (0 : ℝ) 1) :
      intervalIntegral
        (fun y : ℝ =>
          intervalIntegral (fun _z : ℝ => (1 : ℝ)) 0
            (Real.sqrt (1 - x ^ 2 - y ^ 2)) volume)
        0 (Real.sqrt (1 - x ^ 2)) volume =
      Real.pi * (1 - x ^ 2) / 4 := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hR : 0 ≤ 1 - x ^ 2 := by
      nlinarith [mul_nonneg (by linarith [hx.2] : 0 ≤ 1 - x)
        (by linarith [hx.1] : 0 ≤ 1 + x)]
    calc
      _ = intervalIntegral
          (fun y : ℝ => Real.sqrt ((Real.sqrt (1 - x ^ 2)) ^ 2 - y ^ 2))
          0 (Real.sqrt (1 - x ^ 2)) volume := by
        apply intervalIntegral.integral_congr
        intro y hy
        simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one]
        rw [Real.sq_sqrt hR]
      _ = Real.pi * (Real.sqrt (1 - x ^ 2)) ^ 2 / 4 :=
        quarter_circle _ (Real.sqrt_nonneg _)
      _ = Real.pi * (1 - x ^ 2) / 4 := by rw [Real.sq_sqrt hR]
  calc
    intervalIntegral
        (fun x : ℝ =>
          intervalIntegral
            (fun y : ℝ =>
              intervalIntegral (fun _z : ℝ => (1 : ℝ)) 0
                (Real.sqrt (1 - x ^ 2 - y ^ 2)) volume)
            0 (Real.sqrt (1 - x ^ 2)) volume)
        0 1 volume =
      intervalIntegral (fun x : ℝ => Real.pi * (1 - x ^ 2) / 4)
        0 1 volume := by
      apply intervalIntegral.integral_congr
      exact harea
    _ = Real.pi / 6 := by
      let F := fun t : ℝ =>
        (Real.pi / 4) * t + (-Real.pi / 12) * t ^ 3
      have hF (t : ℝ) :
          HasDerivAt F (Real.pi * (1 - t ^ 2) / 4) t := by
        dsimp only [F]
        convert
          ((hasDerivAt_id t).const_mul (Real.pi / 4)).add
            (((hasDerivAt_id t).pow 3).const_mul (-Real.pi / 12))
          using 1 <;> simp only [id_eq] <;> ring
      rw [intervalIntegral_eq_sub_of_hasDerivAt hF (by fun_prop)]
      simp [F]
      ring

private theorem unitOctant_xMoment :
    (∫ p in unitOctant, p.1 ∂volume) = Real.pi / 16 := by
  rw [integral_unitOctant_eq_iterated
    (fun p : Point3 => p.1) continuous_fst]
  have harea (x : ℝ) (hx : x ∈ Set.uIcc (0 : ℝ) 1) :
      intervalIntegral
        (fun y : ℝ =>
          intervalIntegral (fun _z : ℝ => x) 0
            (Real.sqrt (1 - x ^ 2 - y ^ 2)) volume)
        0 (Real.sqrt (1 - x ^ 2)) volume =
      x * (Real.pi * (1 - x ^ 2) / 4) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hR : 0 ≤ 1 - x ^ 2 := by
      nlinarith [mul_nonneg (by linarith [hx.2] : 0 ≤ 1 - x)
        (by linarith [hx.1] : 0 ≤ 1 + x)]
    calc
      _ = intervalIntegral
          (fun y : ℝ =>
            x * Real.sqrt ((Real.sqrt (1 - x ^ 2)) ^ 2 - y ^ 2))
          0 (Real.sqrt (1 - x ^ 2)) volume := by
        apply intervalIntegral.integral_congr
        intro y hy
        simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
        rw [Real.sq_sqrt hR]
        ring
      _ = x * intervalIntegral
          (fun y : ℝ =>
            Real.sqrt ((Real.sqrt (1 - x ^ 2)) ^ 2 - y ^ 2))
          0 (Real.sqrt (1 - x ^ 2)) volume := by
        rw [intervalIntegral.integral_const_mul]
      _ = x * (Real.pi * (1 - x ^ 2) / 4) := by
        rw [quarter_circle _ (Real.sqrt_nonneg _), Real.sq_sqrt hR]
  calc
    intervalIntegral
        (fun x : ℝ =>
          intervalIntegral
            (fun y : ℝ =>
              intervalIntegral (fun _z : ℝ => x) 0
                (Real.sqrt (1 - x ^ 2 - y ^ 2)) volume)
            0 (Real.sqrt (1 - x ^ 2)) volume)
        0 1 volume =
      intervalIntegral
        (fun x : ℝ => x * (Real.pi * (1 - x ^ 2) / 4))
        0 1 volume := by
      apply intervalIntegral.integral_congr
      exact harea
    _ = Real.pi / 16 := by
      let F := fun t : ℝ =>
        (Real.pi / 8) * t ^ 2 + (-Real.pi / 16) * t ^ 4
      have hF (t : ℝ) :
          HasDerivAt F (t * (Real.pi * (1 - t ^ 2) / 4)) t := by
        dsimp only [F]
        convert
          (((hasDerivAt_id t).pow 2).const_mul (Real.pi / 8)).add
            (((hasDerivAt_id t).pow 4).const_mul (-Real.pi / 16))
          using 1 <;> simp only [id_eq] <;> ring
      rw [intervalIntegral_eq_sub_of_hasDerivAt hF (by fun_prop)]
      simp [F]
      ring

private def swapXY : Point3 ≃ᵐ Point3 :=
  ((MeasurableEquiv.prodAssoc :
      (ℝ × ℝ) × ℝ ≃ᵐ ℝ × (ℝ × ℝ)).symm).trans
    ((MeasurableEquiv.prodCongr
      (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ)
      (MeasurableEquiv.refl ℝ)).trans
        (MeasurableEquiv.prodAssoc :
          (ℝ × ℝ) × ℝ ≃ᵐ ℝ × (ℝ × ℝ)))

private def swapYZ : Point3 ≃ᵐ Point3 :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
    (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ)

private theorem swapXY_measurePreserving :
    MeasurePreserving swapXY volume volume := by
  have hA :
      MeasurePreserving
        ((MeasurableEquiv.prodAssoc :
          (ℝ × ℝ) × ℝ ≃ᵐ ℝ × (ℝ × ℝ)).symm) volume volume :=
    MeasurePreserving.symm _ MeasureTheory.volume_preserving_prodAssoc
  have hB :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ)
          (MeasurableEquiv.refl ℝ)) volume volume := by
    exact
      (Measure.measurePreserving_swap
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).prod
          (MeasurePreserving.id (volume : Measure ℝ))
  have hC :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc :
          (ℝ × ℝ) × ℝ ≃ᵐ ℝ × (ℝ × ℝ)) volume volume :=
    MeasureTheory.volume_preserving_prodAssoc
  exact hC.comp (hB.comp hA)

private theorem swapYZ_measurePreserving :
    MeasurePreserving swapYZ volume volume := by
  exact
    (MeasurePreserving.id (volume : Measure ℝ)).prod
      (Measure.measurePreserving_swap
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))

private theorem swapXY_preimage_unitOctant :
    swapXY ⁻¹' unitOctant = unitOctant := by
  ext p
  simp only [Set.mem_preimage, unitOctant, Set.mem_setOf_eq]
  change
    (0 ≤ p.2.1 ∧ 0 ≤ p.1 ∧ 0 ≤ p.2.2 ∧
      p.2.1 ^ 2 + p.1 ^ 2 + p.2.2 ^ 2 ≤ 1) ↔
    (0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧
      p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤ 1)
  constructor <;> rintro ⟨h₁, h₂, h₃, h₄⟩ <;>
    exact ⟨h₂, h₁, h₃, by linarith⟩

private theorem swapYZ_preimage_unitOctant :
    swapYZ ⁻¹' unitOctant = unitOctant := by
  ext p
  simp only [Set.mem_preimage, unitOctant, Set.mem_setOf_eq]
  change
    (0 ≤ p.1 ∧ 0 ≤ p.2.2 ∧ 0 ≤ p.2.1 ∧
      p.1 ^ 2 + p.2.2 ^ 2 + p.2.1 ^ 2 ≤ 1) ↔
    (0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧
      p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤ 1)
  constructor <;> rintro ⟨h₁, h₂, h₃, h₄⟩ <;>
    exact ⟨h₁, h₃, h₂, by linarith⟩

private theorem unitOctant_yMoment :
    (∫ p in unitOctant, p.2.1 ∂volume) = Real.pi / 16 := by
  have h := swapXY_measurePreserving.setIntegral_preimage_emb
    swapXY.measurableEmbedding (fun p : Point3 => p.1) unitOctant
  rw [swapXY_preimage_unitOctant] at h
  change
    (∫ p in unitOctant, p.2.1 ∂volume) =
      ∫ p in unitOctant, p.1 ∂volume at h
  exact h.trans unitOctant_xMoment

private theorem unitOctant_zMoment :
    (∫ p in unitOctant, p.2.2 ∂volume) = Real.pi / 16 := by
  have h := swapYZ_measurePreserving.setIntegral_preimage_emb
    swapYZ.measurableEmbedding (fun p : Point3 => p.2.1) unitOctant
  rw [swapYZ_preimage_unitOctant] at h
  change
    (∫ p in unitOctant, p.2.2 ∂volume) =
      ∫ p in unitOctant, p.2.1 ∂volume at h
  exact h.trans unitOctant_yMoment

private theorem ellipsoid_integral
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (f : Point3 → ℝ) :
    (∫ p in solid a b c, f p ∂volume) =
      a * b * c *
        ∫ q in unitOctant, f (a * q.1, b * q.2.1, c * q.2.2) ∂volume := by
  classical
  let E : Point3 ≃ₗ[ℝ] (Fin 3 → ℝ) :=
    { toFun := fun p => ![p.1, p.2.1, p.2.2]
      invFun := fun x => (x 0, x 1, x 2)
      left_inv := by
        intro p
        ext <;> simp
      right_inv := by
        intro x
        funext i
        fin_cases i <;> simp
      map_add' := by
        intro p q
        funext i
        fin_cases i <;> simp
      map_smul' := by
        intro r p
        funext i
        fin_cases i <;> simp }
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    ![![a, 0, 0], ![0, b, 0], ![0, 0, c] ]
  let S : Point3 →ₗ[ℝ] Point3 :=
    (E.symm : (Fin 3 → ℝ) →ₗ[ℝ] Point3) ∘ₗ
      Matrix.toLin' A ∘ₗ (E : Point3 →ₗ[ℝ] (Fin 3 → ℝ))
  have hSapply (p : Point3) :
      S p = (a * p.1, b * p.2.1, c * p.2.2) := by
    ext <;>
      simp [S, E, A, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ] <;>
      ring
  have hSdet : LinearMap.det S = a * b * c := by
    change
      LinearMap.det
          ((E.symm : (Fin 3 → ℝ) →ₗ[ℝ] Point3) ∘ₗ
            Matrix.toLin' A ∘ₗ (E : Point3 →ₗ[ℝ] (Fin 3 → ℝ))) =
        a * b * c
    have hconj :
        LinearMap.det
            ((E.symm : (Fin 3 → ℝ) →ₗ[ℝ] Point3) ∘ₗ
              Matrix.toLin' A ∘ₗ (E : Point3 →ₗ[ℝ] (Fin 3 → ℝ))) =
          LinearMap.det (Matrix.toLin' A) := by
      simpa only [LinearEquiv.symm_symm] using
        (LinearMap.det_conj (Matrix.toLin' A) E.symm)
    rw [hconj]
    simp only [LinearMap.det_toLin']
    rw [Matrix.det_fin_three]
    simp [A]
  have habc : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
  have hSdet_ne : LinearMap.det S ≠ 0 := hSdet.symm ▸ habc.ne'
  let Se : Point3 ≃ₗ[ℝ] Point3 := S.equivOfDetNeZero hSdet_ne
  let N : Point3 ≃ₗ[ℝ] Point3 := Se.symm
  have hSeapply (p : Point3) :
      Se p = (a * p.1, b * p.2.1, c * p.2.2) := by
    simpa [Se] using hSapply p
  have hNapply (p : Point3) :
      N p = (p.1 / a, p.2.1 / b, p.2.2 / c) := by
    have hinv : Se (N p) = p := by
      exact Se.apply_symm_apply p
    rw [hSeapply] at hinv
    apply Prod.ext
    · dsimp
      have hx := congrArg (fun q : Point3 => q.1) hinv
      dsimp at hx
      apply (eq_div_iff ha.ne').2
      nlinarith
    · apply Prod.ext
      · dsimp
        have hy := congrArg (fun q : Point3 => q.2.1) hinv
        dsimp at hy
        apply (eq_div_iff hb.ne').2
        nlinarith
      · dsimp
        have hz := congrArg (fun q : Point3 => q.2.2) hinv
        dsimp at hz
        apply (eq_div_iff hc.ne').2
        nlinarith
  let em : Point3 ≃ᵐ Point3 :=
    N.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hem_apply (p : Point3) : em p = N p := rfl
  have hdiv_nonneg (x d : ℝ) (hd : 0 < d) :
      0 ≤ x / d ↔ 0 ≤ x := by
    constructor
    · intro h
      have hm := mul_nonneg h hd.le
      rwa [div_mul_cancel₀ x hd.ne'] at hm
    · intro h
      exact div_nonneg h hd.le
  have hsolid : solid a b c = em ⁻¹' unitOctant := by
    ext p
    simp only [solid, unitOctant, Set.mem_setOf_eq, Set.mem_preimage,
      hem_apply, hNapply]
    constructor
    · rintro ⟨hx, hy, hz, hs⟩
      refine ⟨(hdiv_nonneg p.1 a ha).2 hx,
        (hdiv_nonneg p.2.1 b hb).2 hy,
        (hdiv_nonneg p.2.2 c hc).2 hz, ?_⟩
      simpa only [div_pow] using hs
    · rintro ⟨hx, hy, hz, hs⟩
      refine ⟨(hdiv_nonneg p.1 a ha).1 hx,
        (hdiv_nonneg p.2.1 b hb).1 hy,
        (hdiv_nonneg p.2.2 c hc).1 hz, ?_⟩
      simpa only [div_pow] using hs
  letI : Measure.IsAddHaarMeasure
      (MeasureTheory.volume : Measure (ℝ × ℝ)) := by
    change Measure.IsAddHaarMeasure
      ((MeasureTheory.volume : Measure ℝ).prod
        (MeasureTheory.volume : Measure ℝ))
    exact Measure.prod.instIsAddHaarMeasure _ _
  letI : Measure.IsAddHaarMeasure
      (MeasureTheory.volume : Measure Point3) := by
    change Measure.IsAddHaarMeasure
      ((MeasureTheory.volume : Measure ℝ).prod
        (MeasureTheory.volume : Measure (ℝ × ℝ)))
    exact Measure.prod.instIsAddHaarMeasure _ _
  have hNdet : LinearMap.det (N : Point3 →ₗ[ℝ] Point3) ≠ 0 :=
    (LinearEquiv.isUnit_det' N).ne_zero
  have hSedet : LinearMap.det (Se : Point3 →ₗ[ℝ] Point3) = a * b * c := by
    simpa [Se] using hSdet
  have hmap :
      Measure.map em volume = ENNReal.ofReal (a * b * c) • volume := by
    change Measure.map (N : Point3 → Point3) volume =
      ENNReal.ofReal (a * b * c) • volume
    have hraw :=
      Measure.map_linearMap_addHaar_eq_smul_addHaar volume hNdet
    rw [LinearEquiv.det_coe_symm, hSedet] at hraw
    simp [abs_of_pos habc] at hraw
    exact hraw
  have hchange := setIntegral_map_equiv (μ := volume) em
    (fun q : Point3 => f (Se q)) unitOctant
  calc
    (∫ p in solid a b c, f p ∂volume) =
        ∫ q in unitOctant, f (Se q) ∂Measure.map em volume := by
      rw [hsolid]
      simpa [em, N] using hchange.symm
    _ = ∫ q in unitOctant, f (Se q)
          ∂(ENNReal.ofReal (a * b * c) • volume) := by rw [hmap]
    _ = a * b * c * ∫ q in unitOctant, f (Se q) ∂volume := by
      simp [Measure.restrict_smul, integral_smul_measure,
        ENNReal.toReal_ofReal habc.le, smul_eq_mul]
    _ = a * b * c *
          ∫ q in unitOctant,
            f (a * q.1, b * q.2.1, c * q.2.2) ∂volume := by
      apply congrArg (fun t : ℝ => a * b * c * t)
      apply MeasureTheory.setIntegral_congr_fun
        (show MeasurableSet unitOctant by
          unfold unitOctant
          measurability)
      intro q hq
      change f (Se q) = f (a * q.1, b * q.2.1, c * q.2.2)
      rw [hSeapply]

private theorem mass_formula
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    mass a b c = Real.pi * a * b * c / 6 := by
  unfold mass
  rw [ellipsoid_integral a b c ha hb hc
    (fun _p : Point3 => (1 : ℝ))]
  rw [unitOctant_mass]
  ring

private theorem x_moment_formula
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∫ p in solid a b c, p.1 ∂volume) =
      Real.pi * a ^ 2 * b * c / 16 := by
  rw [ellipsoid_integral a b c ha hb hc
    (fun p : Point3 => p.1)]
  have hscale :
      (∫ q in unitOctant, a * q.1 ∂volume) =
        a * (∫ q in unitOctant, q.1 ∂volume) := by
    exact MeasureTheory.integral_const_mul a (fun q : Point3 => q.1)
  rw [hscale, unitOctant_xMoment]
  ring

private theorem y_moment_formula
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∫ p in solid a b c, p.2.1 ∂volume) =
      Real.pi * a * b ^ 2 * c / 16 := by
  rw [ellipsoid_integral a b c ha hb hc
    (fun p : Point3 => p.2.1)]
  have hscale :
      (∫ q in unitOctant, b * q.2.1 ∂volume) =
        b * (∫ q in unitOctant, q.2.1 ∂volume) := by
    exact MeasureTheory.integral_const_mul b (fun q : Point3 => q.2.1)
  rw [hscale, unitOctant_yMoment]
  ring

private theorem z_moment_formula
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∫ p in solid a b c, p.2.2 ∂volume) =
      Real.pi * a * b * c ^ 2 / 16 := by
  rw [ellipsoid_integral a b c ha hb hc
    (fun p : Point3 => p.2.2)]
  have hscale :
      (∫ q in unitOctant, c * q.2.2 ∂volume) =
        c * (∫ q in unitOctant, q.2.2 ∂volume) := by
    exact MeasureTheory.integral_const_mul c (fun q : Point3 => q.2.2)
  rw [hscale, unitOctant_zMoment]
  ring

private theorem radial_mass_integral (a b c : ℝ) :
    (∫ φ in (0 : ℝ)..Real.pi / 2,
        ∫ ψ in (0 : ℝ)..Real.pi / 2,
          ∫ r in (0 : ℝ)..1,
            a * b * c * r ^ 2 * Real.cos ψ) =
      Real.pi * a * b * c / 6 := by
  have hr :
      (∫ r in (0 : ℝ)..1, r ^ 2) = (1 : ℝ) / 3 := by
    let F := fun r : ℝ => r ^ 3 / 3
    have hF (r : ℝ) : HasDerivAt F (r ^ 2) r := by
      dsimp only [F]
      convert ((hasDerivAt_id r).pow 3).div_const 3 using 1 <;>
        norm_num <;> ring
    rw [intervalIntegral_eq_sub_of_hasDerivAt hF (by fun_prop)]
    norm_num [F]
  have hψ :
      (∫ ψ in (0 : ℝ)..Real.pi / 2, Real.cos ψ) = 1 := by
    rw [integral_cos]
    rw [Real.sin_pi_div_two, Real.sin_zero]
    norm_num
  calc
    _ = ∫ φ in (0 : ℝ)..Real.pi / 2,
          ∫ ψ in (0 : ℝ)..Real.pi / 2,
            (a * b * c * Real.cos ψ) * ∫ r in (0 : ℝ)..1, r ^ 2 := by
      apply intervalIntegral.integral_congr
      intro φ hφ
      apply intervalIntegral.integral_congr
      intro ψ hψmem
      change
        (∫ r in (0 : ℝ)..1, a * b * c * r ^ 2 * Real.cos ψ) =
          (a * b * c * Real.cos ψ) *
            ∫ r in (0 : ℝ)..1, r ^ 2
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r hrmem
      ring
    _ = ∫ φ in (0 : ℝ)..Real.pi / 2,
          ∫ ψ in (0 : ℝ)..Real.pi / 2,
            a * b * c * Real.cos ψ / 3 := by
      rw [hr]
      apply intervalIntegral.integral_congr
      intro φ hφ
      apply intervalIntegral.integral_congr
      intro ψ hψmem
      ring
    _ = ∫ φ in (0 : ℝ)..Real.pi / 2,
          (a * b * c / 3) *
            ∫ ψ in (0 : ℝ)..Real.pi / 2, Real.cos ψ := by
      apply intervalIntegral.integral_congr
      intro φ hφ
      change
        (∫ ψ in (0 : ℝ)..Real.pi / 2,
            a * b * c * Real.cos ψ / 3) =
          (a * b * c / 3) *
            ∫ ψ in (0 : ℝ)..Real.pi / 2, Real.cos ψ
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro ψ hψmem
      ring
    _ = ∫ _φ in (0 : ℝ)..Real.pi / 2, a * b * c / 3 := by rw [hψ]; simp
    _ = Real.pi * a * b * c / 6 := by
      simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      ring

private theorem radial_xMoment_integral (a b c : ℝ) :
    (∫ φ in (0 : ℝ)..Real.pi / 2,
        ∫ ψ in (0 : ℝ)..Real.pi / 2,
          ∫ r in (0 : ℝ)..1,
            a * b * c * r ^ 2 * Real.cos ψ *
              (a * r * Real.cos φ * Real.cos ψ)) =
      Real.pi * a ^ 2 * b * c / 16 := by
  have hr :
      (∫ r in (0 : ℝ)..1, r ^ 3) = (1 : ℝ) / 4 := by
    let F := fun r : ℝ => r ^ 4 / 4
    have hF (r : ℝ) : HasDerivAt F (r ^ 3) r := by
      dsimp only [F]
      convert ((hasDerivAt_id r).pow 4).div_const 4 using 1 <;>
        norm_num <;> ring
    rw [intervalIntegral_eq_sub_of_hasDerivAt hF (by fun_prop)]
    norm_num [F]
  have hcos :
      (∫ φ in (0 : ℝ)..Real.pi / 2, Real.cos φ) = 1 := by
    rw [integral_cos]
    rw [Real.sin_pi_div_two, Real.sin_zero]
    norm_num
  have hcos2 :
      (∫ ψ in (0 : ℝ)..Real.pi / 2, Real.cos ψ ^ 2) =
        Real.pi / 4 := by
    rw [integral_cos_sq]
    rw [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero]
    ring
  calc
    _ = ∫ φ in (0 : ℝ)..Real.pi / 2,
          ∫ ψ in (0 : ℝ)..Real.pi / 2,
            (a ^ 2 * b * c * Real.cos φ * Real.cos ψ ^ 2) *
              ∫ r in (0 : ℝ)..1, r ^ 3 := by
      apply intervalIntegral.integral_congr
      intro φ hφ
      apply intervalIntegral.integral_congr
      intro ψ hψ
      change
        (∫ r in (0 : ℝ)..1,
            a * b * c * r ^ 2 * Real.cos ψ *
              (a * r * Real.cos φ * Real.cos ψ)) =
          (a ^ 2 * b * c * Real.cos φ * Real.cos ψ ^ 2) *
            ∫ r in (0 : ℝ)..1, r ^ 3
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r hrmem
      ring
    _ = ∫ φ in (0 : ℝ)..Real.pi / 2,
          ∫ ψ in (0 : ℝ)..Real.pi / 2,
            a ^ 2 * b * c / 4 * Real.cos φ * Real.cos ψ ^ 2 := by
      rw [hr]
      apply intervalIntegral.integral_congr
      intro φ hφ
      apply intervalIntegral.integral_congr
      intro ψ hψ
      ring
    _ = ∫ φ in (0 : ℝ)..Real.pi / 2,
          (a ^ 2 * b * c / 4 * Real.cos φ) *
            ∫ ψ in (0 : ℝ)..Real.pi / 2, Real.cos ψ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro φ hφ
      change
        (∫ ψ in (0 : ℝ)..Real.pi / 2,
            a ^ 2 * b * c / 4 * Real.cos φ * Real.cos ψ ^ 2) =
          (a ^ 2 * b * c / 4 * Real.cos φ) *
            ∫ ψ in (0 : ℝ)..Real.pi / 2, Real.cos ψ ^ 2
      rw [← intervalIntegral.integral_const_mul]
    _ = ∫ φ in (0 : ℝ)..Real.pi / 2,
          (Real.pi * a ^ 2 * b * c / 16) * Real.cos φ := by
      rw [hcos2]
      apply intervalIntegral.integral_congr
      intro φ hφ
      ring
    _ = (Real.pi * a ^ 2 * b * c / 16) *
          ∫ φ in (0 : ℝ)..Real.pi / 2, Real.cos φ := by
      rw [intervalIntegral.integral_const_mul]
    _ = Real.pi * a ^ 2 * b * c / 16 := by rw [hcos]; ring

theorem gap1 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    mass a b c =
      ∫ φ in (0 : ℝ)..Real.pi / 2,
        ∫ ψ in (0 : ℝ)..Real.pi / 2,
          ∫ r in (0 : ℝ)..1,
            a * b * c * r ^ 2 * Real.cos ψ := by
  calc
    mass a b c = Real.pi * a * b * c / 6 :=
      mass_formula a b c ha hb hc
    _ = _ := (radial_mass_integral a b c).symm

theorem gap2 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∫ φ in (0 : ℝ)..Real.pi / 2,
        ∫ ψ in (0 : ℝ)..Real.pi / 2,
          ∫ r in (0 : ℝ)..1,
            a * b * c * r ^ 2 * Real.cos ψ) =
      (1 : ℝ) / 6 * Real.pi * a * b * c := by
  rw [radial_mass_integral]
  ring

theorem gap3 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    mass a b c = (1 : ℝ) / 6 * Real.pi * a * b * c := by
  rw [mass_formula a b c ha hb hc]
  ring

theorem gap4 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    xCentroid a b c =
      1 / mass a b c *
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          ∫ ψ in (0 : ℝ)..Real.pi / 2,
            ∫ r in (0 : ℝ)..1,
              a * b * c * r ^ 2 * Real.cos ψ *
                (a * r * Real.cos φ * Real.cos ψ) := by
  unfold xCentroid
  rw [x_moment_formula a b c ha hb hc, radial_xMoment_integral]

theorem gap5 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / mass a b c *
        (∫ φ in (0 : ℝ)..Real.pi / 2,
          ∫ ψ in (0 : ℝ)..Real.pi / 2,
            ∫ r in (0 : ℝ)..1,
              a * b * c * r ^ 2 * Real.cos ψ *
                (a * r * Real.cos φ * Real.cos ψ)) =
      (1 : ℝ) / 16 * Real.pi * a ^ 2 * b * c *
        (6 / (Real.pi * a * b * c)) := by
  rw [mass_formula a b c ha hb hc, radial_xMoment_integral]
  ring

theorem gap6 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (1 : ℝ) / 16 * Real.pi * a ^ 2 * b * c *
        (6 / (Real.pi * a * b * c)) =
      (3 : ℝ) / 8 * a := by
  field_simp [Real.pi_ne_zero, ha.ne', hb.ne', hc.ne']
  <;> ring

theorem gap7 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    xCentroid a b c = (3 : ℝ) / 8 * a := by
  calc
    xCentroid a b c =
        1 / mass a b c *
          ∫ φ in (0 : ℝ)..Real.pi / 2,
            ∫ ψ in (0 : ℝ)..Real.pi / 2,
              ∫ r in (0 : ℝ)..1,
                a * b * c * r ^ 2 * Real.cos ψ *
                  (a * r * Real.cos φ * Real.cos ψ) :=
      gap4 a b c ha hb hc
    _ = (1 : ℝ) / 16 * Real.pi * a ^ 2 * b * c *
          (6 / (Real.pi * a * b * c)) :=
      gap5 a b c ha hb hc
    _ = (3 : ℝ) / 8 * a := gap6 a b c ha hb hc

theorem gap8 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    yCentroid a b c = (3 : ℝ) / 8 * b := by
  unfold yCentroid
  rw [mass_formula a b c ha hb hc, y_moment_formula a b c ha hb hc]
  field_simp [Real.pi_ne_zero, ha.ne', hb.ne', hc.ne']
  <;> ring

theorem gap9 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    zCentroid a b c = (3 : ℝ) / 8 * c := by
  unfold zCentroid
  rw [mass_formula a b c ha hb hc, z_moment_formula a b c ha hb hc]
  field_simp [Real.pi_ne_zero, ha.ne', hb.ne', hc.ne']
  <;> ring

theorem gap10 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (xCentroid a b c, yCentroid a b c, zCentroid a b c) =
      ((3 : ℝ) / 8 * a, (3 : ℝ) / 8 * b, (3 : ℝ) / 8 * c) := by
  rw [gap7 a b c ha hb hc, gap8 a b c ha hb hc, gap9 a b c ha hb hc]

end

end ProofGap.Exercise4136
