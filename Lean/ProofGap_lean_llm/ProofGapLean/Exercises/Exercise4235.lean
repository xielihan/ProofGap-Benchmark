import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4235

noncomputable section

open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def curveMap (c z : ℝ) : Vec3 :=
  (Real.sqrt (c * z) * Real.cos (z / c),
    Real.sqrt (c * z) * Real.sin (z / c), z)

def curveSegment (c z₀ : ℝ) : Set Vec3 :=
  curveMap c '' Set.Icc 0 z₀

def derivativeVector (c z : ℝ) : Vec3 :=
  (Real.sqrt c / (2 * Real.sqrt z) * Real.cos (z / c) -
      Real.sqrt (z / c) * Real.sin (z / c),
    Real.sqrt c / (2 * Real.sqrt z) * Real.sin (z / c) +
      Real.sqrt (z / c) * Real.cos (z / c),
    1)

def sqNorm (v : Vec3) : ℝ :=
  v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2

def rawSpeed (c z : ℝ) : ℝ :=
  Real.sqrt (sqNorm (derivativeVector c z))

def intermediateSpeed (c z : ℝ) : ℝ :=
  Real.sqrt (c / (4 * z) + z / c + 1)

def speed (c z : ℝ) : ℝ :=
  (2 * z + c) / Real.sqrt (4 * c * z)

def curveLength (c z₀ : ℝ) : ℝ :=
  ∫ z in (0 : ℝ)..z₀, speed c z

theorem gap1 (c z₀ : ℝ) (hc : 0 < c) (hz₀ : 0 ≤ z₀) :
    curveSegment c z₀ = curveMap c '' Set.Icc 0 z₀ := by
  rfl

theorem gap2 (c z : ℝ) (hc : 0 < c) (hz : 0 < z) :
    rawSpeed c z =
      Real.sqrt
        ((Real.sqrt c / (2 * Real.sqrt z) * Real.cos (z / c) -
              Real.sqrt (z / c) * Real.sin (z / c)) ^ 2 +
          (Real.sqrt c / (2 * Real.sqrt z) * Real.sin (z / c) +
              Real.sqrt (z / c) * Real.cos (z / c)) ^ 2 +
          1) := by
  simp [rawSpeed, sqNorm, derivativeVector]

theorem gap3 (c z : ℝ) (hc : 0 < c) (hz : 0 < z) :
    rawSpeed c z = intermediateSpeed c z := by
  unfold rawSpeed intermediateSpeed sqNorm derivativeVector
  congr 1
  simp only [one_pow]
  have hc0 : 0 ≤ c := hc.le
  have hz0 : 0 ≤ z := hz.le
  have hsc : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc0
  have hsz : Real.sqrt z ^ 2 = z := Real.sq_sqrt hz0
  have hzc0 : 0 ≤ z / c := div_nonneg hz0 hc0
  have hszc : Real.sqrt (z / c) ^ 2 = z / c := Real.sq_sqrt hzc0
  have htrig :
      Real.sin (z / c) ^ 2 + Real.cos (z / c) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  have halg :
      (Real.sqrt c / (2 * Real.sqrt z) * Real.cos (z / c) -
              Real.sqrt (z / c) * Real.sin (z / c)) ^ 2 +
          (Real.sqrt c / (2 * Real.sqrt z) * Real.sin (z / c) +
              Real.sqrt (z / c) * Real.cos (z / c)) ^ 2 +
          1 =
        (Real.sqrt c / (2 * Real.sqrt z)) ^ 2 *
              (Real.sin (z / c) ^ 2 + Real.cos (z / c) ^ 2) +
          Real.sqrt (z / c) ^ 2 *
              (Real.sin (z / c) ^ 2 + Real.cos (z / c) ^ 2) +
          1 := by
    ring
  rw [halg, htrig, hszc]
  field_simp [ne_of_gt hc, Real.sqrt_ne_zero'.mpr hz]
  <;> rw [hsc, hsz]
  <;> ring

theorem gap4 (c z : ℝ) (hc : 0 < c) (hz : 0 < z) :
    intermediateSpeed c z = speed c z := by
  unfold intermediateSpeed speed
  have hcz : 0 < 4 * c * z := by positivity
  have hden : 0 < Real.sqrt (4 * c * z) := Real.sqrt_pos.2 hcz
  have hinside : 0 ≤ c / (4 * z) + z / c + 1 := by positivity
  have hright :
      0 ≤ (2 * z + c) / Real.sqrt (4 * c * z) := by positivity
  rw [Real.sqrt_eq_iff_mul_self_eq hinside hright]
  have hsq :
      Real.sqrt (4 * c * z) ^ 2 = 4 * c * z :=
    Real.sq_sqrt hcz.le
  field_simp [ne_of_gt hc, ne_of_gt hz, ne_of_gt hden]
  rw [show c * 4 * z = 4 * c * z by ring, hsq]
  ring

theorem gap5 (c z : ℝ) (hc : 0 < c) (hz : 0 < z) :
    rawSpeed c z = (2 * z + c) / Real.sqrt (4 * c * z) := by
  rw [gap3 c z hc hz, gap4 c z hc hz]
  rfl

theorem gap6 (c z₀ : ℝ) (hc : 0 < c) (hz₀ : 0 ≤ z₀) :
    curveLength c z₀ =
      ∫ z in (0 : ℝ)..z₀,
        (2 * z + c) / Real.sqrt (4 * c * z) := by
  rfl

theorem gap7 (c z₀ : ℝ) (hc : 0 < c) (hz₀ : 0 ≤ z₀) :
    (∫ z in (0 : ℝ)..z₀,
        (2 * z + c) / Real.sqrt (4 * c * z)) =
      (∫ z in (0 : ℝ)..z₀, Real.sqrt (z / c)) +
        ∫ z in (0 : ℝ)..z₀, Real.sqrt c / (2 * Real.sqrt z) := by
  have hc0 : 0 ≤ c := hc.le
  have hpoint :
      Set.EqOn
        (fun z : ℝ => (2 * z + c) / Real.sqrt (4 * c * z))
        (fun z : ℝ =>
          Real.sqrt (z / c) + Real.sqrt c / (2 * Real.sqrt z))
        (Set.uIcc (0 : ℝ) z₀) := by
    intro z hzmem
    rw [Set.uIcc_of_le hz₀] at hzmem
    rcases hzmem.1.eq_or_lt with rfl | hz
    · simp
    · have hz0 : 0 ≤ z := hz.le
      have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
          Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num)]
      have hsqrt :
          Real.sqrt (4 * c * z) =
            2 * Real.sqrt c * Real.sqrt z := by
        calc
          Real.sqrt (4 * c * z) =
              Real.sqrt (4 * c) * Real.sqrt z := by
                rw [Real.sqrt_mul (by positivity : 0 ≤ 4 * c)]
          _ = (Real.sqrt 4 * Real.sqrt c) * Real.sqrt z := by
                rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
          _ = 2 * Real.sqrt c * Real.sqrt z := by
                rw [hsqrt4]
      have hsqrtDiv :
          Real.sqrt (z / c) = Real.sqrt z / Real.sqrt c :=
        Real.sqrt_div hz0 c
      have hsc : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc0
      have hsz : Real.sqrt z ^ 2 = z := Real.sq_sqrt hz0
      dsimp
      rw [hsqrt, hsqrtDiv]
      field_simp [Real.sqrt_ne_zero'.mpr hc, Real.sqrt_ne_zero'.mpr hz]
      rw [hsc, hsz]
  have hfirst :
      IntervalIntegrable (fun z : ℝ => Real.sqrt (z / c))
        MeasureTheory.volume 0 z₀ :=
    (Real.continuous_sqrt.comp
      (continuous_id.div_const c)).intervalIntegrable 0 z₀
  have hpow :
      IntervalIntegrable (fun z : ℝ => Real.rpow z (-1 / 2 : ℝ))
        MeasureTheory.volume 0 z₀ :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hsecond :
      IntervalIntegrable
        (fun z : ℝ => Real.sqrt c / (2 * Real.sqrt z))
        MeasureTheory.volume 0 z₀ := by
    apply IntervalIntegrable.congr
        (f := fun z : ℝ =>
          (Real.sqrt c / 2) * Real.rpow z (-1 / 2 : ℝ))
    · intro z hzmem
      rw [Set.uIoc_of_le hz₀] at hzmem
      have hz : 0 < z := hzmem.1
      dsimp
      rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
        Real.rpow_neg hz.le, ← Real.sqrt_eq_rpow]
      field_simp [Real.sqrt_ne_zero'.mpr hz]
      <;> ring
    · exact hpow.const_mul _
  calc
    (∫ z in (0 : ℝ)..z₀,
        (2 * z + c) / Real.sqrt (4 * c * z)) =
        ∫ z in (0 : ℝ)..z₀,
          (Real.sqrt (z / c) +
            Real.sqrt c / (2 * Real.sqrt z)) := by
      exact intervalIntegral.integral_congr hpoint
    _ = _ := intervalIntegral.integral_add hfirst hsecond

theorem gap8 (c z₀ : ℝ) (hc : 0 < c) (hz₀ : 0 ≤ z₀) :
    (∫ z in (0 : ℝ)..z₀, Real.sqrt (z / c)) +
        (∫ z in (0 : ℝ)..z₀, Real.sqrt c / (2 * Real.sqrt z)) =
      Real.sqrt (c * z₀) * (1 + 2 * z₀ / (3 * c)) := by
  rcases hz₀.eq_or_lt with rfl | hz₀pos
  · simp
  have hc0 : 0 ≤ c := hc.le
  have hsc : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc0
  have hscne : Real.sqrt c ≠ 0 := Real.sqrt_ne_zero'.mpr hc
  have hhalf :
      (∫ z in (0 : ℝ)..z₀, Real.rpow z (1 / 2 : ℝ)) =
        (2 / 3 : ℝ) * z₀ * Real.sqrt z₀ := by
    calc
      (∫ z in (0 : ℝ)..z₀, Real.rpow z (1 / 2 : ℝ)) =
          (Real.rpow z₀ (3 / 2 : ℝ) -
            Real.rpow 0 (3 / 2 : ℝ)) / (3 / 2 : ℝ) := by
        convert integral_rpow
          (a := (0 : ℝ)) (b := z₀) (r := (1 / 2 : ℝ))
          (Or.inl (by norm_num)) using 1 <;> norm_num
      _ = (2 / 3 : ℝ) * z₀ * Real.sqrt z₀ := by
        have hzero : Real.rpow 0 (3 / 2 : ℝ) = 0 :=
          Real.zero_rpow (by norm_num)
        rw [hzero, sub_zero]
        have hrpow :
            Real.rpow z₀ (3 / 2 : ℝ) =
              z₀ * Real.sqrt z₀ := by
          have hadd :
              Real.rpow z₀ ((1 : ℝ) + 1 / 2) =
                Real.rpow z₀ 1 * Real.rpow z₀ (1 / 2) :=
            Real.rpow_add hz₀pos _ _
          have hone : Real.rpow z₀ 1 = z₀ := Real.rpow_one z₀
          have hsqrt :
              Real.rpow z₀ (1 / 2) = Real.sqrt z₀ :=
            (Real.sqrt_eq_rpow z₀).symm
          calc
            Real.rpow z₀ (3 / 2 : ℝ) =
                Real.rpow z₀ ((1 : ℝ) + 1 / 2) := by norm_num
            _ = Real.rpow z₀ 1 * Real.rpow z₀ (1 / 2) := hadd
            _ = z₀ * Real.sqrt z₀ := by rw [hone, hsqrt]
        rw [hrpow]
        ring
  have hnegHalf :
      (∫ z in (0 : ℝ)..z₀, Real.rpow z (-1 / 2 : ℝ)) =
        2 * Real.sqrt z₀ := by
    calc
      (∫ z in (0 : ℝ)..z₀, Real.rpow z (-1 / 2 : ℝ)) =
          (Real.rpow z₀ (1 / 2 : ℝ) -
            Real.rpow 0 (1 / 2 : ℝ)) / (1 / 2 : ℝ) := by
        convert integral_rpow
          (a := (0 : ℝ)) (b := z₀) (r := (-1 / 2 : ℝ))
          (Or.inl (by norm_num)) using 1 <;> norm_num
      _ = 2 * Real.sqrt z₀ := by
        have hzero : Real.rpow 0 (1 / 2 : ℝ) = 0 :=
          Real.zero_rpow (by norm_num)
        rw [hzero, sub_zero]
        have hsqrt :
            Real.rpow z₀ (1 / 2) = Real.sqrt z₀ :=
          (Real.sqrt_eq_rpow z₀).symm
        rw [hsqrt]
        ring
  have hfirst :
      (∫ z in (0 : ℝ)..z₀, Real.sqrt (z / c)) =
        (Real.sqrt c)⁻¹ *
          ((2 / 3 : ℝ) * z₀ * Real.sqrt z₀) := by
    calc
      (∫ z in (0 : ℝ)..z₀, Real.sqrt (z / c)) =
          ∫ z in (0 : ℝ)..z₀,
            (Real.sqrt c)⁻¹ * Real.rpow z (1 / 2 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro z hzmem
        rw [Set.uIcc_of_le hz₀] at hzmem
        dsimp
        rw [Real.sqrt_div hzmem.1 c, Real.sqrt_eq_rpow]
        simp [div_eq_mul_inv, mul_comm]
      _ = (Real.sqrt c)⁻¹ *
          (∫ z in (0 : ℝ)..z₀, Real.rpow z (1 / 2 : ℝ)) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by rw [hhalf]
  have hsecond :
      (∫ z in (0 : ℝ)..z₀, Real.sqrt c / (2 * Real.sqrt z)) =
        Real.sqrt c * Real.sqrt z₀ := by
    calc
      (∫ z in (0 : ℝ)..z₀, Real.sqrt c / (2 * Real.sqrt z)) =
          ∫ z in (0 : ℝ)..z₀,
            (Real.sqrt c / 2) * Real.rpow z (-1 / 2 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro z hzmem
        rw [Set.uIcc_of_le hz₀] at hzmem
        rcases hzmem.1.eq_or_lt with rfl | hz
        · simp
        · dsimp
          rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
            Real.rpow_neg hz.le, ← Real.sqrt_eq_rpow]
          field_simp [Real.sqrt_ne_zero'.mpr hz]
          <;> ring
      _ = (Real.sqrt c / 2) *
          (∫ z in (0 : ℝ)..z₀, Real.rpow z (-1 / 2 : ℝ)) := by
        rw [intervalIntegral.integral_const_mul]
      _ = Real.sqrt c * Real.sqrt z₀ := by
        rw [hnegHalf]
        ring
  rw [hfirst, hsecond, Real.sqrt_mul hc0]
  field_simp [ne_of_gt hc, hscne]
  rw [hsc]
  ring

theorem gap9 (c z₀ : ℝ) (hc : 0 < c) (hz₀ : 0 ≤ z₀) :
    curveLength c z₀ =
      Real.sqrt (c * z₀) * (1 + 2 * z₀ / (3 * c)) := by
  rw [gap6 c z₀ hc hz₀, gap7 c z₀ hc hz₀, gap8 c z₀ hc hz₀]

end

end ProofGap.Exercise4235

