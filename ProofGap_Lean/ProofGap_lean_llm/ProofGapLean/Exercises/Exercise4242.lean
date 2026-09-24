import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4242

noncomputable section

open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def curveMap (a t : ℝ) : Vec3 :=
  (a * t, a / 2 * t ^ 2, a / 3 * t ^ 3)

def rawSpeed (a t : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 + a ^ 2 * t ^ 2 + a ^ 2 * t ^ 4)

def speed (a t : ℝ) : ℝ :=
  a * Real.sqrt (1 + t ^ 2 + t ^ 4)

def density (a y : ℝ) : ℝ :=
  Real.sqrt (2 * y / a)

def weightedLength (a : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    density a (curveMap a t).2.1 * rawSpeed a t

def endpointPrimitive (a u : ℝ) : ℝ :=
  a / 2 *
    ((u + 1 / 2) / 2 * Real.sqrt (1 + u + u ^ 2) +
      3 / 8 * Real.log (u + 1 / 2 + Real.sqrt (1 + u + u ^ 2)))

private def quadratic (u : ℝ) : ℝ :=
  1 + u + u ^ 2

private def primitive (u : ℝ) : ℝ :=
  (u + 1 / 2) / 2 * Real.sqrt (quadratic u) +
    3 / 8 * Real.log (u + 1 / 2 + Real.sqrt (quadratic u))

private theorem quadratic_pos (u : ℝ) : 0 < quadratic u := by
  dsimp [quadratic]
  nlinarith [sq_nonneg (u + 1 / 2)]

private theorem primitive_hasDerivAt (u : ℝ) (hu : 0 ≤ u) :
    HasDerivAt primitive (Real.sqrt (quadratic u)) u := by
  have hq : HasDerivAt quadratic (1 + 2 * u) u := by
    unfold quadratic
    convert
      (((hasDerivAt_const u (1 : ℝ)).add (hasDerivAt_id u)).add
        ((hasDerivAt_id u).pow 2)) using 1 <;>
      simp
  have hs : HasDerivAt (fun x => Real.sqrt (quadratic x))
      ((2 * Real.sqrt (quadratic u))⁻¹ * (1 + 2 * u)) u := by
    simpa [Function.comp_def, div_eq_mul_inv] using
      (Real.hasDerivAt_sqrt (ne_of_gt (quadratic_pos u))).comp u hq
  have hx : HasDerivAt (fun x : ℝ => x + 1 / 2) 1 u := by
    simpa using (hasDerivAt_id u).add_const (1 / 2 : ℝ)
  have hargpos :
      0 < u + 1 / 2 + Real.sqrt (quadratic u) := by
    have hsnonneg := Real.sqrt_nonneg (quadratic u)
    linarith
  have hlog :
      HasDerivAt
        (fun x => Real.log
          (x + 1 / 2 + Real.sqrt (quadratic x)))
        ((u + 1 / 2 + Real.sqrt (quadratic u))⁻¹ *
          (1 + (2 * Real.sqrt (quadratic u))⁻¹ *
            (1 + 2 * u))) u := by
    convert (hx.add hs).log (ne_of_gt hargpos) using 1 <;>
      simp [div_eq_mul_inv, mul_comm]
  have hfull :=
    ((hx.div_const 2).mul hs).add
      (hlog.const_mul (3 / 8 : ℝ))
  convert hfull using 1
  have hspos :
      0 < Real.sqrt (quadratic u) :=
    Real.sqrt_pos.2 (quadratic_pos u)
  have hsquare :
      Real.sqrt (quadratic u) ^ 2 = quadratic u :=
    Real.sq_sqrt (le_of_lt (quadratic_pos u))
  have hdu :
      (2 * Real.sqrt (quadratic u))⁻¹ * (1 + 2 * u) =
        (u + 1 / 2) / Real.sqrt (quadratic u) := by
    field_simp [ne_of_gt hspos]
    ring
  have hlogcoef :
      (u + 1 / 2 + Real.sqrt (quadratic u))⁻¹ *
          (1 + (2 * Real.sqrt (quadratic u))⁻¹ *
            (1 + 2 * u)) =
        1 / Real.sqrt (quadratic u) := by
    rw [hdu]
    field_simp [ne_of_gt hspos, ne_of_gt hargpos]
    ring
  rw [hlogcoef, hdu]
  field_simp [ne_of_gt hspos]
  dsimp [quadratic] at hsquare ⊢
  nlinarith

private theorem integral_sqrt_quadratic :
    (∫ u in (0 : ℝ)..1, Real.sqrt (quadratic u)) =
      primitive 1 - primitive 0 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    apply primitive_hasDerivAt u
    have hu' : u ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
    exact hu'.1
  · apply Continuous.intervalIntegrable
    exact Real.continuous_sqrt.comp (by
      unfold quadratic
      fun_prop)

private theorem transformedPrimitive_hasDerivAt (t : ℝ) :
    HasDerivAt (fun x : ℝ => 1 / 2 * primitive (x ^ 2))
      (t * Real.sqrt (1 + t ^ 2 + t ^ 4)) t := by
  have hsquare :
      HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
    convert (hasDerivAt_id t).pow 2 using 1 <;> simp
  have hcomp :
      HasDerivAt (primitive ∘ fun x : ℝ => x ^ 2)
        (Real.sqrt (quadratic (t ^ 2)) * (2 * t)) t :=
    (primitive_hasDerivAt (t ^ 2) (sq_nonneg t)).comp
      (h := fun x : ℝ => x ^ 2) t hsquare
  have h := hcomp.const_mul (1 / 2 : ℝ)
  convert h using 1 <;> simp [quadratic] <;> ring

private theorem integral_t_sqrt :
    (∫ t in (0 : ℝ)..1,
      t * Real.sqrt (1 + t ^ 2 + t ^ 4)) =
        1 / 2 * (primitive 1 - primitive 0) := by
  calc
    (∫ t in (0 : ℝ)..1,
      t * Real.sqrt (1 + t ^ 2 + t ^ 4)) =
        (1 / 2 * primitive (1 ^ 2)) -
          (1 / 2 * primitive (0 ^ 2)) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun x : ℝ => 1 / 2 * primitive (x ^ 2))
        (f' := fun x : ℝ =>
          x * Real.sqrt (1 + x ^ 2 + x ^ 4))
      · intro t ht
        exact transformedPrimitive_hasDerivAt t
      · apply Continuous.intervalIntegrable
        fun_prop
    _ = 1 / 2 * (primitive 1 - primitive 0) := by
      ring

private theorem endpoint_simplification (a : ℝ) :
    a / 2 * (primitive 1 - primitive 0) =
      a / 8 *
        (3 * Real.sqrt 3 - 1 +
          3 / 2 * Real.log ((3 + 2 * Real.sqrt 3) / 3)) := by
  have hnum : (3 / 2 : ℝ) + Real.sqrt 3 ≠ 0 := by
    positivity
  have hden : (3 / 2 : ℝ) ≠ 0 := by
    norm_num
  have hratio :
      ((3 / 2 : ℝ) + Real.sqrt 3) / (3 / 2) =
        (3 + 2 * Real.sqrt 3) / 3 := by
    ring
  rw [← hratio, Real.log_div hnum hden]
  norm_num [primitive, quadratic]
  ring

theorem gap1 (a t : ℝ) :
    rawSpeed a t =
      Real.sqrt (a ^ 2 + a ^ 2 * t ^ 2 + a ^ 2 * t ^ 4) := by
  rfl

theorem gap2 (a t : ℝ) (ha : 0 < a) :
    rawSpeed a t = speed a t := by
  have harg :
      a ^ 2 + a ^ 2 * t ^ 2 + a ^ 2 * t ^ 4 =
        a ^ 2 * (1 + t ^ 2 + t ^ 4) := by
    ring
  unfold rawSpeed speed
  rw [harg, Real.sqrt_mul (sq_nonneg a),
    Real.sqrt_sq_eq_abs, abs_of_pos ha]

theorem gap3 (a t : ℝ) (ha : 0 < a) :
    rawSpeed a t = a * Real.sqrt (1 + t ^ 2 + t ^ 4) := by
  exact gap2 a t ha

theorem gap4 (a y : ℝ) (ha : 0 < a) (hy : 0 ≤ y) :
    density a y = Real.sqrt (2 * y / a) := by
  rfl

theorem gap5 (a t : ℝ) (ha : 0 < a)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Real.sqrt (2 * (curveMap a t).2.1 / a) = t := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  change Real.sqrt (2 * (a / 2 * t ^ 2) / a) = t
  rw [show 2 * (a / 2 * t ^ 2) / a = t ^ 2 by
    field_simp [ha0]
    <;> ring]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht.1]

theorem gap6 (a t : ℝ) (ha : 0 < a)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    density a (curveMap a t).2.1 = t := by
  exact gap5 a t ha ht

theorem gap7 (a : ℝ) (ha : 0 < a) :
    weightedLength a =
      ∫ t in (0 : ℝ)..1,
        density a (curveMap a t).2.1 * rawSpeed a t := by
  rfl

theorem gap8 (a : ℝ) (ha : 0 < a) :
    weightedLength a =
      a * ∫ t in (0 : ℝ)..1,
        t * Real.sqrt (1 + t ^ 2 + t ^ 4) := by
  unfold weightedLength
  calc
    (∫ t in (0 : ℝ)..1,
      density a (curveMap a t).2.1 * rawSpeed a t) =
        ∫ t in (0 : ℝ)..1,
          a * (t * Real.sqrt (1 + t ^ 2 + t ^ 4)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      change
        density a (curveMap a t).2.1 * rawSpeed a t =
          a * (t * Real.sqrt (1 + t ^ 2 + t ^ 4))
      rw [gap6 a t ha ht', gap3 a t ha]
      ring
    _ = a * ∫ t in (0 : ℝ)..1,
          t * Real.sqrt (1 + t ^ 2 + t ^ 4) := by
      rw [intervalIntegral.integral_const_mul]

theorem gap9 (a : ℝ) (ha : 0 < a) :
    a * (∫ t in (0 : ℝ)..1,
        t * Real.sqrt (1 + t ^ 2 + t ^ 4)) =
      a / 2 *
        ∫ u in (0 : ℝ)..1, Real.sqrt (1 + u + u ^ 2) := by
  have hu :
      (∫ u in (0 : ℝ)..1, Real.sqrt (1 + u + u ^ 2)) =
        primitive 1 - primitive 0 := by
    simpa [quadratic] using integral_sqrt_quadratic
  rw [integral_t_sqrt, hu]
  ring

theorem gap10 (a : ℝ) (ha : 0 < a) :
    weightedLength a =
      a / 2 *
        ∫ u in (0 : ℝ)..1, Real.sqrt (1 + u + u ^ 2) := by
  rw [gap8 a ha, gap9 a ha]

theorem gap11 (a : ℝ) (ha : 0 < a) :
    weightedLength a = endpointPrimitive a 1 - endpointPrimitive a 0 := by
  have hu :
      (∫ u in (0 : ℝ)..1, Real.sqrt (1 + u + u ^ 2)) =
        primitive 1 - primitive 0 := by
    simpa [quadratic] using integral_sqrt_quadratic
  have hep (u : ℝ) :
      endpointPrimitive a u = a / 2 * primitive u := by
    rfl
  rw [gap10 a ha, hu, hep, hep]
  ring

theorem gap12 (a : ℝ) (ha : 0 < a) :
    weightedLength a =
      a / 8 *
        (3 * Real.sqrt 3 - 1 +
          3 / 2 * Real.log ((3 + 2 * Real.sqrt 3) / 3)) := by
  rw [gap11 a ha]
  have hep (u : ℝ) :
      endpointPrimitive a u = a / 2 * primitive u := by
    rfl
  calc
    endpointPrimitive a 1 - endpointPrimitive a 0 =
        a / 2 * (primitive 1 - primitive 0) := by
      rw [hep, hep]
      ring
    _ = a / 8 *
        (3 * Real.sqrt 3 - 1 +
          3 / 2 * Real.log ((3 + 2 * Real.sqrt 3) / 3)) :=
      endpoint_simplification a

end

end ProofGap.Exercise4242
