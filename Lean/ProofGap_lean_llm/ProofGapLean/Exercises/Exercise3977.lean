/- Source: `results/stage1_gpt55/09_重积分与含参积分/exercise_3977_autoformalization_result/exercise_3977.md`. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace ProofGap.Exercise3977

noncomputable section

open MeasureTheory

def openDisk (a : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 < a ^ 2}

def diskMoment (m n : ℕ) (a : ℝ) : ℝ :=
  ∫ p in openDisk a, p.1 ^ m * p.2 ^ n

def angularMoment (m n : ℕ) : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi,
    Real.cos φ ^ m * Real.sin φ ^ n

private theorem measurableSet_openDisk (a : ℝ) :
    MeasurableSet (openDisk a) := by
  change
    MeasurableSet
      ((fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) ⁻¹' Set.Iio (a ^ 2))
  exact
    ((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2))
      isOpen_Iio.measurableSet

private def reflectX : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.neg ℝ) (MeasurableEquiv.refl ℝ)

private def reflectY : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.neg ℝ)

private theorem reflectX_measurePreserving :
    MeasurePreserving reflectX (volume : Measure (ℝ × ℝ)) volume := by
  rw [MeasureTheory.Measure.volume_eq_prod]
  exact
    (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
      (MeasurePreserving.id (volume : Measure ℝ))

private theorem reflectY_measurePreserving :
    MeasurePreserving reflectY (volume : Measure (ℝ × ℝ)) volume := by
  rw [MeasureTheory.Measure.volume_eq_prod]
  exact
    (MeasurePreserving.id (volume : Measure ℝ)).prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))

private theorem reflectX_preimage_openDisk (a : ℝ) :
    reflectX ⁻¹' openDisk a = openDisk a := by
  ext p
  change (-p.1) ^ 2 + p.2 ^ 2 < a ^ 2 ↔
    p.1 ^ 2 + p.2 ^ 2 < a ^ 2
  ring_nf

private theorem reflectY_preimage_openDisk (a : ℝ) :
    reflectY ⁻¹' openDisk a = openDisk a := by
  ext p
  change p.1 ^ 2 + (-p.2) ^ 2 < a ^ 2 ↔
    p.1 ^ 2 + p.2 ^ 2 < a ^ 2
  ring_nf

private theorem integral_eq_neg_of_odd_left
    (m n : ℕ) (a : ℝ) (hm : Odd m) :
    (∫ p in openDisk a, p.1 ^ m * p.2 ^ n) =
      -(∫ p in openDisk a, p.1 ^ m * p.2 ^ n) := by
  have hchange :=
    reflectX_measurePreserving.setIntegral_preimage_emb
      reflectX.measurableEmbedding
      (fun p : ℝ × ℝ => p.1 ^ m * p.2 ^ n) (openDisk a)
  rw [reflectX_preimage_openDisk] at hchange
  have hodd : (-1 : ℝ) ^ m = -1 := by
    rw [Odd.neg_one_pow hm]
  have hleft :
      (∫ p in openDisk a,
          (reflectX p).1 ^ m * (reflectX p).2 ^ n) =
        -(∫ p in openDisk a, p.1 ^ m * p.2 ^ n) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun
    · exact measurableSet_openDisk a
    intro p _
    change (-p.1) ^ m * p.2 ^ n = -(p.1 ^ m * p.2 ^ n)
    rw [neg_pow, hodd]
    ring
  rw [hleft] at hchange
  exact hchange.symm

private theorem integral_eq_neg_of_odd_right
    (m n : ℕ) (a : ℝ) (hn : Odd n) :
    (∫ p in openDisk a, p.1 ^ m * p.2 ^ n) =
      -(∫ p in openDisk a, p.1 ^ m * p.2 ^ n) := by
  have hchange :=
    reflectY_measurePreserving.setIntegral_preimage_emb
      reflectY.measurableEmbedding
      (fun p : ℝ × ℝ => p.1 ^ m * p.2 ^ n) (openDisk a)
  rw [reflectY_preimage_openDisk] at hchange
  have hodd : (-1 : ℝ) ^ n = -1 := by
    rw [Odd.neg_one_pow hn]
  have hleft :
      (∫ p in openDisk a,
          (reflectY p).1 ^ m * (reflectY p).2 ^ n) =
        -(∫ p in openDisk a, p.1 ^ m * p.2 ^ n) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun
    · exact measurableSet_openDisk a
    intro p _
    change p.1 ^ m * (-p.2) ^ n = -(p.1 ^ m * p.2 ^ n)
    rw [neg_pow, hodd]
    ring
  rw [hleft] at hchange
  exact hchange.symm

private theorem odd_diskMoment_zero (m n : ℕ) (a : ℝ)
    (hm : 0 < m) (hn : 0 < n) (hodd : Odd m ∨ Odd n) :
    (∫ p in openDisk a, p.1 ^ m * p.2 ^ n) = 0 := by
  rcases hodd with hodd | hodd
  · linarith [integral_eq_neg_of_odd_left m n a hodd]
  · linarith [integral_eq_neg_of_odd_right m n a hodd]

private def angularFn (m n : ℕ) (φ : ℝ) : ℝ :=
  Real.cos φ ^ m * Real.sin φ ^ n

private theorem angularFn_periodic (m n : ℕ) :
    Function.Periodic (angularFn m n) (2 * Real.pi) := by
  intro φ
  unfold angularFn
  rw [Real.cos_periodic φ, Real.sin_periodic φ]

private theorem polar_moment_pointwise
    (m n : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
    p.1 •
        (openDisk a).indicator
          (fun q : ℝ × ℝ => q.1 ^ m * q.2 ^ n)
          (polarCoord.symm p) =
      (Set.Iio a).indicator
          (fun r : ℝ => r ^ (m + n + 1)) p.1 *
        angularFn m n p.2 := by
  rcases p with ⟨r, φ⟩
  have hr : 0 < r := hp.1
  have htrig :
      (r * Real.cos φ) ^ 2 + (r * Real.sin φ) ^ 2 = r ^ 2 := by
    calc
      _ = r ^ 2 * (Real.cos φ ^ 2 + Real.sin φ ^ 2) := by ring
      _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]
  have hmem :
      polarCoord.symm (r, φ) ∈ openDisk a ↔ r < a := by
    rw [polarCoord_symm_apply]
    simp only [openDisk, Set.mem_setOf_eq]
    rw [htrig]
    exact sq_lt_sq₀ hr.le ha
  simp only [Set.indicator, hmem, Set.mem_Iio, smul_eq_mul]
  by_cases hra : r < a
  · simp only [hra, if_true]
    rw [polarCoord_symm_apply]
    unfold angularFn
    rw [mul_pow, mul_pow]
    rw [show r ^ m * Real.cos φ ^ m * (r ^ n * Real.sin φ ^ n) =
        r ^ (m + n + 1) * (Real.cos φ ^ m * Real.sin φ ^ n) / r by
      field_simp [hr.ne']
      rw [pow_add, pow_succ]
      ring]
    field_simp [hr.ne']
  · simp [hra]

private theorem angular_setIntegral_eq (m n : ℕ) :
    (∫ φ in Set.Ioo (-Real.pi) Real.pi, angularFn m n φ) =
      angularMoment m n := by
  have hshift :=
    (angularFn_periodic m n).intervalIntegral_add_eq (-Real.pi) 0
  have hperiod :
      (∫ φ in -Real.pi..Real.pi, angularFn m n φ) =
        ∫ φ in (0 : ℝ)..2 * Real.pi, angularFn m n φ := by
    convert hshift using 1 <;> ring
  calc
    (∫ φ in Set.Ioo (-Real.pi) Real.pi, angularFn m n φ) =
        ∫ φ in Set.Ioc (-Real.pi) Real.pi, angularFn m n φ :=
      (integral_Ioc_eq_integral_Ioo
        (f := angularFn m n)).symm
    _ = ∫ φ in -Real.pi..Real.pi, angularFn m n φ := by
      rw [intervalIntegral.integral_of_le]
      exact neg_le_self Real.pi_nonneg
    _ = ∫ φ in (0 : ℝ)..2 * Real.pi, angularFn m n φ :=
      hperiod
    _ = angularMoment m n := by rfl

private theorem diskMoment_polar_product
    (m n : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    diskMoment m n a =
      (∫ r in (0 : ℝ)..a, r ^ (m + n + 1)) *
        angularMoment m n := by
  have hp :=
    integral_comp_polarCoord_symm
      ((openDisk a).indicator
        (fun q : ℝ × ℝ => q.1 ^ m * q.2 ^ n))
  rw [integral_indicator (measurableSet_openDisk a)] at hp
  have hprod :
      (∫ p in polarCoord.target,
          p.1 •
            (openDisk a).indicator
              (fun q : ℝ × ℝ => q.1 ^ m * q.2 ^ n)
              (polarCoord.symm p)) =
        (∫ r in Set.Ioi (0 : ℝ),
            (Set.Iio a).indicator
              (fun r : ℝ => r ^ (m + n + 1)) r) *
          ∫ φ in Set.Ioo (-Real.pi) Real.pi,
            angularFn m n φ := by
    rw [polarCoord_target]
    calc
      _ = ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          (Set.Iio a).indicator
              (fun r : ℝ => r ^ (m + n + 1)) p.1 *
            angularFn m n p.2 := by
        apply setIntegral_congr_fun
          (measurableSet_Ioi.prod measurableSet_Ioo)
        intro p hp'
        exact polar_moment_pointwise m n a ha p hp'
      _ = _ := by
        exact setIntegral_prod_mul
          ((Set.Iio a).indicator
            (fun r : ℝ => r ^ (m + n + 1)))
          (angularFn m n)
          (Set.Ioi (0 : ℝ)) (Set.Ioo (-Real.pi) Real.pi)
  have hrad :
      (∫ r in Set.Ioi (0 : ℝ),
          (Set.Iio a).indicator
            (fun r : ℝ => r ^ (m + n + 1)) r) =
        ∫ r in (0 : ℝ)..a, r ^ (m + n + 1) := by
    rw [setIntegral_indicator measurableSet_Iio]
    have hinter :
        Set.Ioi (0 : ℝ) ∩ Set.Iio a = Set.Ioo (0 : ℝ) a := by
      ext r
      simp
    rw [hinter, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le ha]
  unfold diskMoment
  rw [← hp, hprod, hrad, angular_setIntegral_eq]

theorem gap1 (m n : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    diskMoment m n a =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..a,
          r ^ (m + n + 1) * Real.cos φ ^ m * Real.sin φ ^ n := by
  have hinner (φ : ℝ) :
      (∫ r in (0 : ℝ)..a,
          r ^ (m + n + 1) * Real.cos φ ^ m * Real.sin φ ^ n) =
        (∫ r in (0 : ℝ)..a, r ^ (m + n + 1)) *
          angularFn m n φ := by
    calc
      _ = ∫ r in (0 : ℝ)..a,
          r ^ (m + n + 1) *
            (Real.cos φ ^ m * Real.sin φ ^ n) := by
        apply intervalIntegral.integral_congr
        intro r hr
        ring
      _ = (∫ r in (0 : ℝ)..a, r ^ (m + n + 1)) *
          (Real.cos φ ^ m * Real.sin φ ^ n) :=
        intervalIntegral.integral_mul_const
          (r := Real.cos φ ^ m * Real.sin φ ^ n)
          (f := fun r : ℝ => r ^ (m + n + 1))
      _ = _ := by rfl
  rw [diskMoment_polar_product m n a ha]
  unfold angularMoment
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro φ hφ
  exact hinner φ |>.symm

theorem gap2 (m n : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    diskMoment m n a =
      a ^ (m + n + 2) / (m + n + 2 : ℝ) * angularMoment m n := by
  rw [diskMoment_polar_product m n a ha]
  congr 1
  rw [integral_pow]
  norm_num
  congr 1 <;> ring

theorem gap3 (m n : ℕ) :
    angularMoment m n =
      (∫ φ in -Real.pi / 2..Real.pi / 2,
        Real.cos φ ^ m * Real.sin φ ^ n) +
      ∫ φ in Real.pi / 2..3 * Real.pi / 2,
        Real.cos φ ^ m * Real.sin φ ^ n := by
  let F : ℝ → ℝ := angularFn m n
  have hperiod := angularFn_periodic m n
  have hshift := hperiod.intervalIntegral_add_eq 0 (-Real.pi / 2)
  have hfull :
      (∫ φ in (0 : ℝ)..2 * Real.pi, F φ) =
        ∫ φ in -Real.pi / 2..3 * Real.pi / 2, F φ := by
    dsimp [F]
    convert hshift using 1 <;> ring
  have hcont : Continuous F :=
    (Real.continuous_cos.pow m).mul (Real.continuous_sin.pow n)
  unfold angularMoment
  change (∫ φ in (0 : ℝ)..2 * Real.pi, F φ) = _
  rw [hfull]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  rfl

theorem gap4 (m n : ℕ) :
    (∫ φ in Real.pi / 2..3 * Real.pi / 2,
        Real.cos φ ^ m * Real.sin φ ^ n) =
      (-1 : ℝ) ^ m * (-1 : ℝ) ^ n *
        ∫ t in -Real.pi / 2..Real.pi / 2,
          Real.cos t ^ m * Real.sin t ^ n := by
  let F : ℝ → ℝ := angularFn m n
  have htranslate :
      (∫ φ in Real.pi / 2..3 * Real.pi / 2, F φ) =
        ∫ t in -Real.pi / 2..Real.pi / 2, F (t + Real.pi) := by
    convert
      (intervalIntegral.integral_comp_add_right
        (f := F) (a := -Real.pi / 2) (b := Real.pi / 2)
        Real.pi).symm using 1 <;>
      ring
  change (∫ φ in Real.pi / 2..3 * Real.pi / 2, F φ) = _
  rw [htranslate]
  calc
    (∫ t in -Real.pi / 2..Real.pi / 2, F (t + Real.pi)) =
        ∫ t in -Real.pi / 2..Real.pi / 2,
          ((-1 : ℝ) ^ m * (-1 : ℝ) ^ n) * F t := by
      apply intervalIntegral.integral_congr
      intro t ht
      change
        Real.cos (t + Real.pi) ^ m * Real.sin (t + Real.pi) ^ n =
          ((-1 : ℝ) ^ m * (-1 : ℝ) ^ n) *
            (Real.cos t ^ m * Real.sin t ^ n)
      rw [Real.cos_add_pi, Real.sin_add_pi, neg_pow, neg_pow]
      ring
    _ = ((-1 : ℝ) ^ m * (-1 : ℝ) ^ n) *
        ∫ t in -Real.pi / 2..Real.pi / 2, F t :=
      intervalIntegral.integral_const_mul
        (r := (-1 : ℝ) ^ m * (-1 : ℝ) ^ n)
        (f := F)
    _ = _ := by rfl

theorem gap5 (m n : ℕ) (hm : Odd m) (hn : ¬Odd n) :
    (-1 : ℝ) ^ m * (-1 : ℝ) ^ n = -1 := by
  rw [Odd.neg_one_pow hm,
    Even.neg_one_pow (Nat.not_odd_iff_even.mp hn)]
  ring

theorem gap6 (m n : ℕ) (hm : Odd m) (hn : ¬Odd n) :
    angularMoment m n = 0 := by
  rw [gap3 m n, gap4 m n, gap5 m n hm hn]
  ring

theorem gap7 (m n : ℕ) (hn : Odd n) :
    Function.Odd (fun t : ℝ => Real.cos t ^ m * Real.sin t ^ n) := by
  intro t
  change
    Real.cos (-t) ^ m * Real.sin (-t) ^ n =
      -(Real.cos t ^ m * Real.sin t ^ n)
  rw [Real.cos_neg, Real.sin_neg, hn.neg_pow]
  ring

theorem gap8 (m n : ℕ) (hn : Odd n) :
    (∫ t in -Real.pi / 2..Real.pi / 2,
      Real.cos t ^ m * Real.sin t ^ n) =
      0 := by
  let F : ℝ → ℝ :=
    fun t => Real.cos t ^ m * Real.sin t ^ n
  have hodd : Function.Odd F := gap7 m n hn
  have hleft :
      (∫ t in -Real.pi / 2..Real.pi / 2, F (-t)) =
        -(∫ t in -Real.pi / 2..Real.pi / 2, F t) := by
    calc
      _ = ∫ t in -Real.pi / 2..Real.pi / 2, -F t := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact hodd t
      _ = _ := intervalIntegral.integral_neg
  have hsym :
      (∫ t in -Real.pi / 2..Real.pi / 2, F (-t)) =
        ∫ t in -Real.pi / 2..Real.pi / 2, F t := by
    simpa only [neg_div, neg_neg] using
      (intervalIntegral.integral_comp_neg
        (f := F) (a := -Real.pi / 2) (b := Real.pi / 2))
  change (∫ t in -Real.pi / 2..Real.pi / 2, F t) = 0
  linarith

theorem gap9 (m n : ℕ) (a : ℝ) (hodd : Odd m ∨ Odd n) :
    diskMoment m n a = 0 := by
  unfold diskMoment
  rcases hodd with hm | hn
  · linarith [integral_eq_neg_of_odd_left m n a hm]
  · linarith [integral_eq_neg_of_odd_right m n a hn]

theorem gap10 (m n : ℕ) (a : ℝ) (hodd : Odd m ∨ Odd n) :
    diskMoment m n a = 0 := by
  exact gap9 m n a hodd

end

end ProofGap.Exercise3977
