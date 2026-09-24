import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise4048

noncomputable section

open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def xCoord (r φ : ℝ) : ℝ :=
  r * Real.cos φ

def yCoord (r φ : ℝ) : ℝ :=
  r * Real.sin φ

def zCoord (h r φ : ℝ) : ℝ :=
  h * φ

def dRadial (r φ : ℝ) : Vec3 :=
  (Real.cos φ, Real.sin φ, 0)

def dAngular (h r φ : ℝ) : Vec3 :=
  (-r * Real.sin φ, r * Real.cos φ, h)

def sqNorm (v : Vec3) : ℝ :=
  v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2

def dot (u v : Vec3) : ℝ :=
  u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

def E (r φ : ℝ) : ℝ :=
  sqNorm (dRadial r φ)

def G (h r φ : ℝ) : ℝ :=
  sqNorm (dAngular h r φ)

def F (h r φ : ℝ) : ℝ :=
  dot (dRadial r φ) (dAngular h r φ)

def areaDensity (h r φ : ℝ) : ℝ :=
  Real.sqrt (E r φ * G h r φ - F h r φ ^ 2)

def radialPrimitive (h r : ℝ) : ℝ :=
  r / 2 * Real.sqrt (r ^ 2 + h ^ 2) +
    h ^ 2 / 2 * Real.log (r + Real.sqrt (r ^ 2 + h ^ 2))

def surfaceArea (a h : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi,
    ∫ r in (0 : ℝ)..a, areaDensity h r φ

private theorem radialPrimitive_hasDerivAt (h r : ℝ) (hh : 0 < h) :
    HasDerivAt (radialPrimitive h) (Real.sqrt (r ^ 2 + h ^ 2)) r := by
  have hq : 0 < r ^ 2 + h ^ 2 := by
    nlinarith [sq_nonneg r, sq_nonneg h]
  have hspos : 0 < Real.sqrt (r ^ 2 + h ^ 2) := Real.sqrt_pos.2 hq
  have hsq : Real.sqrt (r ^ 2 + h ^ 2) ^ 2 = r ^ 2 + h ^ 2 :=
    Real.sq_sqrt hq.le
  have hs_ge_abs : |r| ≤ Real.sqrt (r ^ 2 + h ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs r]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg h])
  have hsum_nonneg : 0 ≤ r + Real.sqrt (r ^ 2 + h ^ 2) := by
    nlinarith [neg_abs_le r]
  have hsum_ne : r + Real.sqrt (r ^ 2 + h ^ 2) ≠ 0 := by
    intro hz
    nlinarith [hsq, sq_nonneg h]
  have hsum_pos : 0 < r + Real.sqrt (r ^ 2 + h ^ 2) :=
    lt_of_le_of_ne hsum_nonneg (Ne.symm hsum_ne)
  have hpoly :
      HasDerivAt (fun x : ℝ => x ^ 2 + h ^ 2) (2 * r) r := by
    convert (((hasDerivAt_id r).pow 2).add (hasDerivAt_const r (h ^ 2))) using 1 <;>
      norm_num <;> ring
  have hsqrt :
      HasDerivAt (fun x : ℝ => Real.sqrt (x ^ 2 + h ^ 2))
        (r / Real.sqrt (r ^ 2 + h ^ 2)) r := by
    convert (Real.hasDerivAt_sqrt hq.ne').comp r hpoly using 1 <;>
      field_simp [hspos.ne'] <;> ring
  have hlog :
      HasDerivAt
        (fun x : ℝ => Real.log (x + Real.sqrt (x ^ 2 + h ^ 2)))
        ((1 + r / Real.sqrt (r ^ 2 + h ^ 2)) /
          (r + Real.sqrt (r ^ 2 + h ^ 2))) r := by
    convert
      (Real.hasDerivAt_log hsum_ne).comp r ((hasDerivAt_id r).add hsqrt)
      using 1 <;>
      field_simp [hspos.ne', hsum_ne] <;> ring
  have hratio :
      (1 + r / Real.sqrt (r ^ 2 + h ^ 2)) /
          (r + Real.sqrt (r ^ 2 + h ^ 2)) =
        1 / Real.sqrt (r ^ 2 + h ^ 2) := by
    field_simp [hspos.ne', hsum_ne] <;> ring
  have hderiv :
      1 / 2 * Real.sqrt (r ^ 2 + h ^ 2) +
          r / 2 * (r / Real.sqrt (r ^ 2 + h ^ 2)) +
          (0 * Real.log (r + Real.sqrt (r ^ 2 + h ^ 2)) +
            h ^ 2 / 2 *
              ((1 + r / Real.sqrt (r ^ 2 + h ^ 2)) /
                (r + Real.sqrt (r ^ 2 + h ^ 2)))) =
        Real.sqrt (r ^ 2 + h ^ 2) := by
    rw [hratio]
    field_simp [hspos.ne']
    nlinarith [hsq]
  have htotal :=
    (((hasDerivAt_id r).div_const 2).mul hsqrt).add
      ((hasDerivAt_const r (h ^ 2 / 2)).mul hlog)
  have htotal' :
      HasDerivAt (radialPrimitive h)
        (1 / 2 * Real.sqrt (r ^ 2 + h ^ 2) +
          r / 2 * (r / Real.sqrt (r ^ 2 + h ^ 2)) +
          (0 * Real.log (r + Real.sqrt (r ^ 2 + h ^ 2)) +
            h ^ 2 / 2 *
              ((1 + r / Real.sqrt (r ^ 2 + h ^ 2)) /
                (r + Real.sqrt (r ^ 2 + h ^ 2))))) r := by
    simpa only [radialPrimitive, id_eq] using htotal
  rw [hderiv] at htotal'
  exact htotal'

theorem gap1 (r φ : ℝ) :
    E r φ = sqNorm (dRadial r φ) := by
  rfl

theorem gap2 (r φ : ℝ) :
    sqNorm (dRadial r φ) = 1 := by
  simp [sqNorm, dRadial, Real.cos_sq_add_sin_sq]

theorem gap3 (r φ : ℝ) :
    E r φ = 1 := by
  rw [gap1, gap2]

theorem gap4 (h r φ : ℝ) :
    G h r φ = sqNorm (dAngular h r φ) := by
  rfl

theorem gap5 (h r φ : ℝ) :
    sqNorm (dAngular h r φ) = r ^ 2 + h ^ 2 := by
  simp only [sqNorm, dAngular, Prod.fst, Prod.snd]
  calc
    (-r * Real.sin φ) ^ 2 + (r * Real.cos φ) ^ 2 + h ^ 2 =
        r ^ 2 * (Real.cos φ ^ 2 + Real.sin φ ^ 2) + h ^ 2 := by ring
    _ = r ^ 2 + h ^ 2 := by rw [Real.cos_sq_add_sin_sq]; ring

theorem gap6 (h r φ : ℝ) :
    G h r φ = r ^ 2 + h ^ 2 := by
  rw [gap4, gap5]

theorem gap7 (h r φ : ℝ) :
    F h r φ = dot (dRadial r φ) (dAngular h r φ) := by
  rfl

theorem gap8 (h r φ : ℝ) :
    dot (dRadial r φ) (dAngular h r φ) = 0 := by
  simp only [dot, dRadial, dAngular, Prod.fst, Prod.snd]
  ring

theorem gap9 (h r φ : ℝ) :
    F h r φ = 0 := by
  rw [gap7, gap8]

theorem gap10 (h r φ : ℝ) :
    areaDensity h r φ = Real.sqrt (r ^ 2 + h ^ 2) := by
  simp [areaDensity, gap3, gap6, gap9]

theorem gap11 (a h : ℝ) (ha : 0 ≤ a) :
    surfaceArea a h =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..a, Real.sqrt (r ^ 2 + h ^ 2) := by
  simp [surfaceArea, gap10]

theorem gap12 (a h : ℝ) (ha : 0 ≤ a) (hh : 0 < h) :
    surfaceArea a h =
      2 * Real.pi * (radialPrimitive h a - radialPrimitive h 0) := by
  rw [gap11 a h ha]
  have hcont : Continuous (fun r : ℝ => Real.sqrt (r ^ 2 + h ^ 2)) :=
    Real.continuous_sqrt.comp ((continuous_id.pow 2).add continuous_const)
  have hinner :
      (∫ r in (0 : ℝ)..a, Real.sqrt (r ^ 2 + h ^ 2)) =
        radialPrimitive h a - radialPrimitive h 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => radialPrimitive_hasDerivAt h r hh)
      (hcont.intervalIntegrable (0 : ℝ) a)
  simp_rw [hinner]
  simp
  ring

theorem gap13 (a h : ℝ) (ha : 0 ≤ a) (hh : 0 < h) :
    surfaceArea a h =
      Real.pi * a * Real.sqrt (a ^ 2 + h ^ 2) +
        Real.pi * h ^ 2 *
          Real.log ((a + Real.sqrt (a ^ 2 + h ^ 2)) / h) := by
  rw [gap12 a h ha hh]
  have hzero : Real.sqrt ((0 : ℝ) ^ 2 + h ^ 2) = h := by
    norm_num [Real.sqrt_sq_eq_abs, abs_of_pos hh]
  have hq : 0 < a ^ 2 + h ^ 2 := by
    nlinarith [sq_nonneg a, sq_nonneg h]
  have hspos : 0 < Real.sqrt (a ^ 2 + h ^ 2) := Real.sqrt_pos.2 hq
  have hapos : 0 < a + Real.sqrt (a ^ 2 + h ^ 2) := by
    nlinarith
  rw [Real.log_div hapos.ne' hh.ne']
  unfold radialPrimitive
  rw [hzero]
  ring

end

end ProofGap.Exercise4048
