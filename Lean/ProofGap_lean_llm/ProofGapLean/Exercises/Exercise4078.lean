import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ProofGap.Exercise4078

noncomputable section

open MeasureTheory
open scoped Interval

def firstOctantBall : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤ 1 ∧
    0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2}

def volumeIntegral : ℝ :=
  ∫ p in firstOctantBall, p.1 * p.2.1 * p.2.2

theorem gap1 :
    volumeIntegral =
      ∫ x in (0 : ℝ)..1,
        ∫ y in (0 : ℝ)..Real.sqrt (1 - x ^ 2),
          ∫ z in (0 : ℝ)..Real.sqrt (1 - x ^ 2 - y ^ 2),
            x * y * z := by
  classical
  let f : (ℝ × ℝ × ℝ) → ℝ := fun p => p.1 * p.2.1 * p.2.2
  have hf : Continuous f :=
    (continuous_fst.mul (continuous_fst.comp continuous_snd)).mul
      (continuous_snd.comp continuous_snd)
  have hclosed : IsClosed firstOctantBall := by
    have hball : IsClosed {p : ℝ × ℝ × ℝ |
        p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤ 1} :=
      isClosed_le
        (((continuous_fst.pow 2).add
          ((continuous_fst.comp continuous_snd).pow 2)).add
          ((continuous_snd.comp continuous_snd).pow 2))
        continuous_const
    have hx : IsClosed {p : ℝ × ℝ × ℝ | 0 ≤ p.1} :=
      isClosed_le continuous_const continuous_fst
    have hy : IsClosed {p : ℝ × ℝ × ℝ | 0 ≤ p.2.1} :=
      isClosed_le continuous_const (continuous_fst.comp continuous_snd)
    have hz : IsClosed {p : ℝ × ℝ × ℝ | 0 ≤ p.2.2} :=
      isClosed_le continuous_const (continuous_snd.comp continuous_snd)
    simpa only [firstOctantBall, Set.setOf_and] using
      hball.inter (hx.inter (hy.inter hz))
  have hsub : firstOctantBall ⊆
      Set.Icc ((0 : ℝ), ((0 : ℝ), (0 : ℝ)))
        ((1 : ℝ), ((1 : ℝ), (1 : ℝ))) := by
    intro p hp
    have hs := hp.1
    have hx0 := hp.2.1
    have hy0 := hp.2.2.1
    have hz0 := hp.2.2.2
    have hx1 : p.1 ≤ 1 := by
      nlinarith [sq_nonneg p.2.1, sq_nonneg p.2.2]
    have hy1 : p.2.1 ≤ 1 := by
      nlinarith [sq_nonneg p.1, sq_nonneg p.2.2]
    have hz1 : p.2.2 ≤ 1 := by
      nlinarith [sq_nonneg p.1, sq_nonneg p.2.1]
    exact ⟨⟨hx0, ⟨hy0, hz0⟩⟩, ⟨hx1, ⟨hy1, hz1⟩⟩⟩
  have hcompact : IsCompact firstOctantBall :=
    isCompact_Icc.of_isClosed_subset hclosed hsub
  have hmeas : MeasurableSet firstOctantBall := hclosed.measurableSet
  have hintOn : IntegrableOn f firstOctantBall volume :=
    ContinuousOn.integrableOn_compact hcompact hf.continuousOn
  have hint : Integrable (firstOctantBall.indicator f) volume := by
    rw [integrable_indicator_iff hmeas]
    exact hintOn
  have hFubini :
      (∫ p, firstOctantBall.indicator f p) =
        ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
          firstOctantBall.indicator f (x, (y, z)) := by
    calc
      (∫ p, firstOctantBall.indicator f p) =
          ∫ x : ℝ, ∫ q : ℝ × ℝ,
            firstOctantBall.indicator f (x, q) := by
        exact MeasureTheory.integral_prod
          (fun p : ℝ × (ℝ × ℝ) => firstOctantBall.indicator f p) hint
      _ = ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
            firstOctantBall.indicator f (x, (y, z)) := by
        apply integral_congr_ae
        filter_upwards [hint.prod_right_ae] with x hx
        exact MeasureTheory.integral_prod
          (fun q : ℝ × ℝ => firstOctantBall.indicator f (x, q)) hx
  have hindicator (x y z : ℝ) :
      firstOctantBall.indicator f (x, (y, z)) =
        if x ∈ Set.Ioc (0 : ℝ) 1 then
          if y ∈ Set.Ioc (0 : ℝ) (Real.sqrt (1 - x ^ 2)) then
            if z ∈ Set.Ioc (0 : ℝ) (Real.sqrt (1 - x ^ 2 - y ^ 2)) then
              x * y * z
            else 0
          else 0
        else 0 := by
    by_cases hzero : x * y * z = 0
    · simp [Set.indicator, f, hzero]
    · have hxne : x ≠ 0 := by
        intro hx
        apply hzero
        simp [hx]
      have hyne : y ≠ 0 := by
        intro hy
        apply hzero
        simp [hy]
      have hzne : z ≠ 0 := by
        intro hz
        apply hzero
        simp [hz]
      have hmem :
          (x, (y, z)) ∈ firstOctantBall ↔
            x ∈ Set.Ioc (0 : ℝ) 1 ∧
            y ∈ Set.Ioc (0 : ℝ) (Real.sqrt (1 - x ^ 2)) ∧
            z ∈ Set.Ioc (0 : ℝ) (Real.sqrt (1 - x ^ 2 - y ^ 2)) := by
        constructor
        · intro hp
          have hs := hp.1
          have hx0 := hp.2.1
          have hy0 := hp.2.2.1
          have hz0 := hp.2.2.2
          have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxne)
          have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hyne)
          have hzpos : 0 < z := lt_of_le_of_ne hz0 (Ne.symm hzne)
          have hx1 : x ≤ 1 := by
            nlinarith [sq_nonneg y, sq_nonneg z]
          have hbase : 0 ≤ 1 - x ^ 2 := by
            nlinarith [sq_nonneg z]
          have hsx : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
            Real.sq_sqrt hbase
          have hyb : y ≤ Real.sqrt (1 - x ^ 2) := by
            nlinarith [Real.sqrt_nonneg (1 - x ^ 2)]
          have hrem : 0 ≤ 1 - x ^ 2 - y ^ 2 := by
            nlinarith [sq_nonneg z]
          have hsr : Real.sqrt (1 - x ^ 2 - y ^ 2) ^ 2 =
              1 - x ^ 2 - y ^ 2 := Real.sq_sqrt hrem
          have hzb : z ≤ Real.sqrt (1 - x ^ 2 - y ^ 2) := by
            nlinarith [Real.sqrt_nonneg (1 - x ^ 2 - y ^ 2)]
          exact ⟨⟨hxpos, hx1⟩, ⟨⟨hypos, hyb⟩, ⟨hzpos, hzb⟩⟩⟩
        · rintro ⟨hxI, hyI, hzI⟩
          have hbase : 0 ≤ 1 - x ^ 2 := by
            nlinarith [mul_nonneg (le_of_lt hxI.1) (sub_nonneg.mpr hxI.2)]
          have hsx : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
            Real.sq_sqrt hbase
          have hsqrtx0 : 0 ≤ Real.sqrt (1 - x ^ 2) :=
            Real.sqrt_nonneg (1 - x ^ 2)
          have hsumy : 0 ≤ y + Real.sqrt (1 - x ^ 2) :=
            add_nonneg (le_of_lt hyI.1) hsqrtx0
          have hysq : y ^ 2 ≤ 1 - x ^ 2 := by
            nlinarith [mul_nonneg (sub_nonneg.mpr hyI.2) hsumy]
          have hrem : 0 ≤ 1 - x ^ 2 - y ^ 2 := by linarith
          have hsr : Real.sqrt (1 - x ^ 2 - y ^ 2) ^ 2 =
              1 - x ^ 2 - y ^ 2 := Real.sq_sqrt hrem
          have hsqrtxy0 : 0 ≤ Real.sqrt (1 - x ^ 2 - y ^ 2) :=
            Real.sqrt_nonneg (1 - x ^ 2 - y ^ 2)
          have hsumz : 0 ≤ z + Real.sqrt (1 - x ^ 2 - y ^ 2) :=
            add_nonneg (le_of_lt hzI.1) hsqrtxy0
          have hzsq : z ^ 2 ≤ 1 - x ^ 2 - y ^ 2 := by
            nlinarith [mul_nonneg (sub_nonneg.mpr hzI.2) hsumz]
          exact ⟨by nlinarith, le_of_lt hxI.1,
            le_of_lt hyI.1, le_of_lt hzI.1⟩
      simp only [Set.indicator, f, hmem]
      split_ifs <;> simp_all
  unfold volumeIntegral
  rw [← MeasureTheory.integral_indicator hmeas, hFubini]
  simp_rw [hindicator]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simp_rw [intervalIntegral.integral_of_le (Real.sqrt_nonneg _)]
  simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
  simp only [Set.indicator_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hxI : x ∈ Set.Ioc (0 : ℝ) 1
  · simp only [hxI, if_true]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hyI : y ∈ Set.Ioc (0 : ℝ) (Real.sqrt (1 - x ^ 2))
    · simp [hyI]
    · simp [hyI]
  · simp [hxI]

theorem gap2 :
    volumeIntegral =
      1 / 2 *
        ∫ x in (0 : ℝ)..1,
          x * ∫ y in (0 : ℝ)..Real.sqrt (1 - x ^ 2),
            y * (1 - x ^ 2 - y ^ 2) := by
  rw [gap1]
  have hz (x y : ℝ) (hxy : 0 ≤ 1 - x ^ 2 - y ^ 2) :
      (∫ z in (0 : ℝ)..Real.sqrt (1 - x ^ 2 - y ^ 2), x * y * z) =
        (1 / 2 : ℝ) * (x * (y * (1 - x ^ 2 - y ^ 2))) := by
    let F : ℝ → ℝ := fun z => x * y * (z * z) / 2
    have hderiv : ∀ z : ℝ, HasDerivAt F (x * y * z) z := by
      intro z
      have hsq := (hasDerivAt_id z).mul (hasDerivAt_id z)
      dsimp [F]
      convert (hsq.const_mul (x * y)).div_const 2 using 1 <;>
        simp <;> ring
    have hint : IntervalIntegrable (fun z : ℝ => x * y * z) volume
        0 (Real.sqrt (1 - x ^ 2 - y ^ 2)) :=
      (continuous_const.mul continuous_id).intervalIntegrable _ _
    have hcalc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := Real.sqrt (1 - x ^ 2 - y ^ 2))
      (f := F) (f' := fun z : ℝ => x * y * z)
      (fun z _ => hderiv z) hint
    dsimp [F] at hcalc
    have hsqrt_mul :
        Real.sqrt (1 - x ^ 2 - y ^ 2) *
            Real.sqrt (1 - x ^ 2 - y ^ 2) =
          1 - x ^ 2 - y ^ 2 := by
      simpa [pow_two] using Real.sq_sqrt hxy
    rw [hcalc]
    simp only [hsqrt_mul]
    ring
  calc
    (∫ x in (0 : ℝ)..1,
        ∫ y in (0 : ℝ)..Real.sqrt (1 - x ^ 2),
          ∫ z in (0 : ℝ)..Real.sqrt (1 - x ^ 2 - y ^ 2), x * y * z) =
        ∫ x in (0 : ℝ)..1,
          (1 / 2 : ℝ) *
            (x * ∫ y in (0 : ℝ)..Real.sqrt (1 - x ^ 2),
              y * (1 - x ^ 2 - y ^ 2)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hx
      have hx_sq : x ^ 2 ≤ 1 := by
        nlinarith [mul_nonneg hx'.1 (sub_nonneg.mpr hx'.2)]
      have hbase : 0 ≤ 1 - x ^ 2 := sub_nonneg.mpr hx_sq
      change (∫ y in (0 : ℝ)..Real.sqrt (1 - x ^ 2),
          ∫ z in (0 : ℝ)..Real.sqrt (1 - x ^ 2 - y ^ 2), x * y * z) = _
      calc
        (∫ y in (0 : ℝ)..Real.sqrt (1 - x ^ 2),
            ∫ z in (0 : ℝ)..Real.sqrt (1 - x ^ 2 - y ^ 2), x * y * z) =
            ∫ y in (0 : ℝ)..Real.sqrt (1 - x ^ 2),
              ((1 / 2 : ℝ) * x) * (y * (1 - x ^ 2 - y ^ 2)) := by
          apply intervalIntegral.integral_congr
          intro y hy
          have hy' : y ∈ Set.Icc (0 : ℝ) (Real.sqrt (1 - x ^ 2)) := by
            simpa [Set.uIcc_of_le (Real.sqrt_nonneg (1 - x ^ 2))] using hy
          have hsqrt : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
            Real.sq_sqrt hbase
          have hsqrt_nonneg : 0 ≤ Real.sqrt (1 - x ^ 2) :=
            Real.sqrt_nonneg (1 - x ^ 2)
          have hprod :
              0 ≤ (Real.sqrt (1 - x ^ 2) - y) *
                (y + Real.sqrt (1 - x ^ 2)) :=
            mul_nonneg (sub_nonneg.mpr hy'.2)
              (add_nonneg hy'.1 hsqrt_nonneg)
          have hysq : y ^ 2 ≤ 1 - x ^ 2 := by
            nlinarith [hprod]
          change (∫ z in (0 : ℝ)..Real.sqrt (1 - x ^ 2 - y ^ 2), x * y * z) = _
          simpa [mul_assoc] using hz x y (sub_nonneg.mpr hysq)
        _ = ((1 / 2 : ℝ) * x) *
              (∫ y in (0 : ℝ)..Real.sqrt (1 - x ^ 2),
                y * (1 - x ^ 2 - y ^ 2)) := by
          rw [intervalIntegral.integral_const_mul]
        _ = (1 / 2 : ℝ) *
              (x * ∫ y in (0 : ℝ)..Real.sqrt (1 - x ^ 2),
                y * (1 - x ^ 2 - y ^ 2)) := by ring
    _ = (1 / 2 : ℝ) *
          ∫ x in (0 : ℝ)..1,
            x * ∫ y in (0 : ℝ)..Real.sqrt (1 - x ^ 2),
              y * (1 - x ^ 2 - y ^ 2) := by
      rw [intervalIntegral.integral_const_mul]

theorem gap3 :
    volumeIntegral =
      1 / 8 * ∫ x in (0 : ℝ)..1, x * (1 - x ^ 2) ^ 2 := by
  rw [gap2]
  have hinner (x : ℝ) (hx : x ∈ Set.uIcc (0 : ℝ) 1) :
      (∫ y in (0 : ℝ)..Real.sqrt (1 - x ^ 2),
        y * (1 - x ^ 2 - y ^ 2)) = (1 - x ^ 2) ^ 2 / 4 := by
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hx
    have hx_sq : x ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hx'.1 (sub_nonneg.mpr hx'.2)]
    have hbase : 0 ≤ 1 - x ^ 2 := sub_nonneg.mpr hx_sq
    let F : ℝ → ℝ := fun y =>
      (1 - x ^ 2) * (y * y) / 2 - (y * y) * (y * y) / 4
    have hderiv : ∀ y : ℝ, HasDerivAt F (y * (1 - x ^ 2 - y ^ 2)) y := by
      intro y
      have hsq := (hasDerivAt_id y).mul (hasDerivAt_id y)
      have hfour := hsq.mul hsq
      dsimp [F]
      convert
        (((hsq.const_mul (1 - x ^ 2)).div_const 2).sub
          (hfour.div_const 4)) using 1 <;>
        simp <;> ring
    have hint : IntervalIntegrable (fun y : ℝ => y * (1 - x ^ 2 - y ^ 2)) volume
        0 (Real.sqrt (1 - x ^ 2)) := by
      exact (continuous_id.mul
        (continuous_const.sub (continuous_id.pow 2))).intervalIntegrable _ _
    have hcalc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := Real.sqrt (1 - x ^ 2))
      (f := F) (f' := fun y : ℝ => y * (1 - x ^ 2 - y ^ 2))
      (fun y _ => hderiv y) hint
    dsimp [F] at hcalc
    have hsqrt_mul :
        Real.sqrt (1 - x ^ 2) * Real.sqrt (1 - x ^ 2) =
          1 - x ^ 2 := by
      simpa [pow_two] using Real.sq_sqrt hbase
    rw [hcalc]
    simp only [hsqrt_mul]
    ring
  have hcongr :
      (∫ x in (0 : ℝ)..1,
        x * ∫ y in (0 : ℝ)..Real.sqrt (1 - x ^ 2),
          y * (1 - x ^ 2 - y ^ 2)) =
        ∫ x in (0 : ℝ)..1, (1 / 4 : ℝ) * (x * (1 - x ^ 2) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    change x * (∫ y in (0 : ℝ)..Real.sqrt (1 - x ^ 2),
      y * (1 - x ^ 2 - y ^ 2)) = _
    rw [hinner x hx]
    ring
  rw [hcongr, intervalIntegral.integral_const_mul]
  ring

theorem gap4 :
    volumeIntegral = 1 / 48 := by
  rw [gap3]
  let F : ℝ → ℝ := fun x =>
    (x * x) / 2 - (x * x) * (x * x) / 2 +
      ((x * x) * (x * x)) * (x * x) / 6
  have hderiv : ∀ x : ℝ, HasDerivAt F (x * (1 - x ^ 2) ^ 2) x := by
    intro x
    have hsq := (hasDerivAt_id x).mul (hasDerivAt_id x)
    have hfour := hsq.mul hsq
    have hsix := hfour.mul hsq
    dsimp [F]
    convert
      (((hsq.div_const 2).sub (hfour.div_const 2)).add
        (hsix.div_const 6)) using 1 <;>
      simp <;> ring
  have hint : IntervalIntegrable (fun x : ℝ => x * (1 - x ^ 2) ^ 2) volume 0 1 := by
    exact (continuous_id.mul
      ((continuous_const.sub (continuous_id.pow 2)).pow 2)).intervalIntegrable _ _
  have hcalc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := (1 : ℝ))
    (f := F) (f' := fun x : ℝ => x * (1 - x ^ 2) ^ 2)
    (fun x _ => hderiv x) hint
  dsimp [F] at hcalc
  rw [hcalc]
  norm_num

end

end ProofGap.Exercise4078
