import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4003

noncomputable section

open MeasureTheory
open scoped Interval

def x₁ (x : ℝ) (_y : ℝ) (z : ℝ) : ℝ :=
  x / Real.sqrt 2 - z / Real.sqrt 2

def y₁ (x y z : ℝ) : ℝ :=
  x / Real.sqrt 6 - 2 * y / Real.sqrt 6 + z / Real.sqrt 6

def z₁ (x y z : ℝ) : ℝ :=
  x / Real.sqrt 3 + y / Real.sqrt 3 + z / Real.sqrt 3

def quadraticForm (x y z : ℝ) : ℝ :=
  x ^ 2 + y ^ 2 + z ^ 2 - x * y - x * z - y * z

def crossSectionDisk (a : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ 2 / 3 * a ^ 2}

def crossSectionArea (a : ℝ) : ℝ :=
  ∫ _p in crossSectionDisk a, (1 : ℝ)

theorem gap1 (x y z : ℝ) :
    z₁ x y z = 1 / Real.sqrt 3 * (x + y + z) := by
  unfold z₁
  ring

theorem gap2 (b x y z : ℝ) (hplane : x + y + z = b) :
    1 / Real.sqrt 3 * (x + y + z) = b / Real.sqrt 3 := by
  rw [hplane]
  ring

theorem gap3 (b x y z : ℝ) (hplane : x + y + z = b) :
    z₁ x y z = b / Real.sqrt 3 := by
  rw [gap1, gap2 b x y z hplane]

theorem gap4 (x y z : ℝ) :
    x =
      1 / Real.sqrt 2 * x₁ x y z +
        1 / Real.sqrt 6 * y₁ x y z +
        1 / Real.sqrt 3 * z₁ x y z := by
  have h2 : Real.sqrt (2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have h3 : Real.sqrt (3 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have h6 : Real.sqrt (6 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hs2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs6 : Real.sqrt (6 : ℝ) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  unfold x₁ y₁ z₁
  field_simp [h2, h3, h6]
  rw [hs2, hs3, hs6]
  ring

theorem gap5 (x y z : ℝ) :
    y =
      -Real.sqrt 6 / 3 * y₁ x y z +
        1 / Real.sqrt 3 * z₁ x y z := by
  have h3 : Real.sqrt (3 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have h6 : Real.sqrt (6 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hs3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs6 : Real.sqrt (6 : ℝ) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  unfold y₁ z₁
  field_simp [h3, h6]
  rw [hs3]
  ring

theorem gap6 (x y z : ℝ) :
    z =
      -1 / Real.sqrt 2 * x₁ x y z +
        1 / Real.sqrt 6 * y₁ x y z +
        1 / Real.sqrt 3 * z₁ x y z := by
  have h2 : Real.sqrt (2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have h3 : Real.sqrt (3 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have h6 : Real.sqrt (6 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hs2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs6 : Real.sqrt (6 : ℝ) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  unfold x₁ y₁ z₁
  field_simp [h2, h3, h6]
  rw [hs2, hs3, hs6]
  ring

theorem gap7 (x y z : ℝ) :
    quadraticForm x y z =
      1 / 2 * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by
  unfold quadraticForm
  ring

theorem gap8 (x y z : ℝ) :
    1 / 2 * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) =
      3 / 2 * (x₁ x y z ^ 2 + y₁ x y z ^ 2) := by
  have h2 : Real.sqrt (2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have h6 : Real.sqrt (6 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hs2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs6 : Real.sqrt (6 : ℝ) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  unfold x₁ y₁
  field_simp [h2, h6]
  rw [hs2, hs6]
  ring

theorem gap9 (x y z : ℝ) :
    quadraticForm x y z =
      3 / 2 * (x₁ x y z ^ 2 + y₁ x y z ^ 2) := by
  exact (gap7 x y z).trans (gap8 x y z)

theorem gap10 (a x y z : ℝ) (hq : quadraticForm x y z = a ^ 2) :
    x₁ x y z ^ 2 + y₁ x y z ^ 2 = 2 / 3 * a ^ 2 := by
  have h := gap9 x y z
  rw [hq] at h
  linarith

private theorem crossSectionArea_formula (a : ℝ) (ha : 0 ≤ a) :
    crossSectionArea a = 2 / 3 * Real.pi * a ^ 2 := by
  let s : ℝ := Real.sqrt (2 / 3 : ℝ) * a
  have hs : 0 ≤ s := mul_nonneg (Real.sqrt_nonneg _) ha
  have hsqrt : Real.sqrt (2 / 3 : ℝ) ^ 2 = 2 / 3 :=
    Real.sq_sqrt (by norm_num)
  have hsquare : s ^ 2 = 2 / 3 * a ^ 2 := by
    dsimp [s]
    nlinarith
  have hdisk : MeasurableSet (crossSectionDisk a) := by
    unfold crossSectionDisk
    measurability
  have hpoint : ∀ p : ℝ × ℝ,
      polarCoord.target.indicator
          (fun z =>
            z.1 * (crossSectionDisk a).indicator (fun _ => (1 : ℝ))
              (polarCoord.symm z)) p =
        (Set.Ioc (0 : ℝ) s ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
          (fun z => z.1) p := by
    rintro ⟨r, φ⟩
    have htrig :
        (r * Real.cos φ) ^ 2 + (r * Real.sin φ) ^ 2 = r ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq φ]
    by_cases ht : 0 < r ∧ -Real.pi < φ ∧ φ < Real.pi
    · have hriff : r ^ 2 ≤ s ^ 2 ↔ r ≤ s := by
        constructor <;> intro h <;> nlinarith
      by_cases hr : r ≤ s
      · have htargetmem : (r, φ) ∈ polarCoord.target := by
          simpa [polarCoord_target] using ht
        have hrectmem :
            (r, φ) ∈ Set.Ioc (0 : ℝ) s ×ˢ Set.Ioo (-Real.pi) Real.pi :=
          ⟨⟨ht.1, hr⟩, ht.2⟩
        have hpolarmem : polarCoord.symm (r, φ) ∈ crossSectionDisk a := by
          simp only [polarCoord_symm_apply, crossSectionDisk, Set.mem_setOf_eq,
            htrig, ← hsquare]
          exact hriff.mpr hr
        rw [Set.indicator_of_mem htargetmem, Set.indicator_of_mem hrectmem,
          Set.indicator_of_mem hpolarmem]
        simp
      · have hsq : ¬r ^ 2 ≤ s ^ 2 := by
          intro h
          exact hr (hriff.mp h)
        have htargetmem : (r, φ) ∈ polarCoord.target := by
          simpa [polarCoord_target] using ht
        have hrect :
            (r, φ) ∉ Set.Ioc (0 : ℝ) s ×ˢ Set.Ioo (-Real.pi) Real.pi := by
          intro hp
          exact hr hp.1.2
        have hpolar :
            polarCoord.symm (r, φ) ∉ crossSectionDisk a := by
          simpa [polarCoord_symm_apply, crossSectionDisk, htrig, hsquare] using hsq
        rw [Set.indicator_of_mem htargetmem, Set.indicator_of_notMem hrect,
          Set.indicator_of_notMem hpolar]
        simp
    · have hrect :
          (r, φ) ∉ Set.Ioc (0 : ℝ) s ×ˢ Set.Ioo (-Real.pi) Real.pi := by
        intro hp
        exact ht ⟨hp.1.1, hp.2.1, hp.2.2⟩
      have htarget : (r, φ) ∉ polarCoord.target := by
        simpa [polarCoord_target, Set.mem_prod] using ht
      rw [Set.indicator_of_notMem htarget, Set.indicator_of_notMem hrect]
  have hangle :
      (∫ _φ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ)) =
        2 * Real.pi := by
    rw [MeasureTheory.setIntegral_const]
    simp [Real.pi_pos.le]
    ring
  calc
    crossSectionArea a =
        ∫ p : ℝ × ℝ, (crossSectionDisk a).indicator (fun _ => (1 : ℝ)) p := by
          rw [crossSectionArea, MeasureTheory.integral_indicator hdisk]
    _ = ∫ p in polarCoord.target,
          p.1 * (crossSectionDisk a).indicator (fun _ => (1 : ℝ))
            (polarCoord.symm p) := by
          simpa [smul_eq_mul] using
            (integral_comp_polarCoord_symm
              ((crossSectionDisk a).indicator (fun _ => (1 : ℝ)))).symm
    _ = ∫ p : ℝ × ℝ,
          (Set.Ioc (0 : ℝ) s ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
            (fun z => z.1) p := by
          rw [← MeasureTheory.integral_indicator polarCoord.open_target.measurableSet]
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
    _ = ∫ p in Set.Ioc (0 : ℝ) s ×ˢ Set.Ioo (-Real.pi) Real.pi,
          p.1 * (1 : ℝ) := by
          rw [MeasureTheory.integral_indicator
            (measurableSet_Ioc.prod measurableSet_Ioo)]
          apply MeasureTheory.setIntegral_congr_fun
            (measurableSet_Ioc.prod measurableSet_Ioo)
          intro p hp
          simp
    _ = (∫ r in Set.Ioc (0 : ℝ) s, r) *
          ∫ _φ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
          exact MeasureTheory.setIntegral_prod_mul (fun r : ℝ => r)
            (fun _ : ℝ => 1) (Set.Ioc (0 : ℝ) s)
            (Set.Ioo (-Real.pi) Real.pi)
    _ = (∫ r in (0 : ℝ)..s, r) * (2 * Real.pi) := by
          rw [intervalIntegral.integral_of_le hs, hangle]
    _ = 2 / 3 * Real.pi * a ^ 2 := by
          rw [integral_id, hsquare]
          ring

private theorem semicircle_integral (s : ℝ) (hs : 0 ≤ s) :
    (∫ x in -s..s, Real.sqrt (s ^ 2 - x ^ 2)) =
      Real.pi * s ^ 2 / 2 := by
  rcases hs.eq_or_lt with rfl | hspos
  · simp
  have hs0 : s ≠ 0 := ne_of_gt hspos
  have hpoint : ∀ u : ℝ,
      Real.sqrt (s ^ 2 - (s * u) ^ 2) =
        s * Real.sqrt (1 - u ^ 2) := by
    intro u
    have halg : s ^ 2 - (s * u) ^ 2 = s ^ 2 * (1 - u ^ 2) := by
      ring
    rw [halg, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq_eq_abs,
      abs_of_pos hspos]
  have hcomp :=
    intervalIntegral.integral_comp_mul_left
      (f := fun x : ℝ => Real.sqrt (s ^ 2 - x ^ 2))
      (a := (-1 : ℝ)) (b := 1) hs0
  have hleft :
      (∫ u in (-1 : ℝ)..1, Real.sqrt (s ^ 2 - (s * u) ^ 2)) =
        s * (Real.pi / 2) := by
    calc
      _ = ∫ u in (-1 : ℝ)..1, s * Real.sqrt (1 - u ^ 2) := by
        apply intervalIntegral.integral_congr
        intro u hu
        exact hpoint u
      _ = s * ∫ u in (-1 : ℝ)..1, Real.sqrt (1 - u ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
      _ = s * (Real.pi / 2) := by
        rw [integral_sqrt_one_sub_sq]
  rw [show s * (-1 : ℝ) = -s by ring, mul_one] at hcomp
  rw [hleft] at hcomp
  simp only [smul_eq_mul] at hcomp
  field_simp [hs0] at hcomp ⊢
  nlinarith

private theorem iterated_formula (a : ℝ) (ha : 0 ≤ a) :
    (∫ x in -Real.sqrt (2 / 3) * a..Real.sqrt (2 / 3) * a,
        ∫ y in -Real.sqrt (2 / 3 * a ^ 2 - x ^ 2)..
            Real.sqrt (2 / 3 * a ^ 2 - x ^ 2),
          (1 : ℝ)) =
      2 / 3 * Real.pi * a ^ 2 := by
  let s : ℝ := Real.sqrt (2 / 3 : ℝ) * a
  have hs : 0 ≤ s := mul_nonneg (Real.sqrt_nonneg _) ha
  have hsqrt : Real.sqrt (2 / 3 : ℝ) ^ 2 = 2 / 3 :=
    Real.sq_sqrt (by norm_num)
  have hsquare : s ^ 2 = 2 / 3 * a ^ 2 := by
    dsimp [s]
    nlinarith
  simp_rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_one]
  rw [show -Real.sqrt (2 / 3 : ℝ) * a = -s by
        dsimp [s]
        ring,
      show Real.sqrt (2 / 3 : ℝ) * a = s by rfl]
  change
    (∫ x in -s..s,
      (Real.sqrt (2 / 3 * a ^ 2 - x ^ 2) -
        -Real.sqrt (2 / 3 * a ^ 2 - x ^ 2))) =
      2 / 3 * Real.pi * a ^ 2
  have hrewrite :
      (∫ x in -s..s,
        (Real.sqrt (2 / 3 * a ^ 2 - x ^ 2) -
          -Real.sqrt (2 / 3 * a ^ 2 - x ^ 2))) =
        2 * ∫ x in -s..s, Real.sqrt (s ^ 2 - x ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [hsquare]
    ring
  rw [hrewrite, semicircle_integral s hs, hsquare]
  ring

theorem gap11 (a : ℝ) (ha : 0 ≤ a) :
    crossSectionArea a =
      ∫ x in -Real.sqrt (2 / 3) * a..Real.sqrt (2 / 3) * a,
        ∫ y in -Real.sqrt (2 / 3 * a ^ 2 - x ^ 2)..
            Real.sqrt (2 / 3 * a ^ 2 - x ^ 2),
          (1 : ℝ) := by
  rw [crossSectionArea_formula a ha, iterated_formula a ha]

theorem gap12 (a : ℝ) (ha : 0 ≤ a) :
    (∫ x in -Real.sqrt (2 / 3) * a..Real.sqrt (2 / 3) * a,
        ∫ y in -Real.sqrt (2 / 3 * a ^ 2 - x ^ 2)..
            Real.sqrt (2 / 3 * a ^ 2 - x ^ 2),
          (1 : ℝ)) =
      2 / 3 * Real.pi * a ^ 2 := by
  exact iterated_formula a ha

theorem gap13 (a : ℝ) (ha : 0 ≤ a) :
    crossSectionArea a = 2 / 3 * Real.pi * a ^ 2 := by
  exact crossSectionArea_formula a ha

end

end ProofGap.Exercise4003
