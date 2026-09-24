import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise4062

noncomputable section

open MeasureTheory
open scoped Interval

def radialTerm (a x : ℝ) : ℝ :=
  2 * a * x - x ^ 2

def upperBoundary (a x : ℝ) : ℝ :=
  a - Real.sqrt (radialTerm a x)

def Ix (a : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..a,
    ∫ y in (0 : ℝ)..upperBoundary a x, y ^ 2

def Iy (a : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..a,
    ∫ x in (0 : ℝ)..upperBoundary a y, x ^ 2

def sqrtPrimitive (a x : ℝ) : ℝ :=
  (x - a) / 2 * Real.sqrt (radialTerm a x) +
    a ^ 2 / 2 * Real.arcsin ((x - a) / a)

def elementaryPrimitive (a x : ℝ) : ℝ :=
  1 / 3 *
    (a ^ 3 * x - 3 * a ^ 2 * sqrtPrimitive a x +
      3 * a ^ 2 * x ^ 2 - a * x ^ 3)

private theorem radial_sqrt_pow_integral (a : ℝ) (ha : 0 < a) (n : ℕ) :
    (∫ x in (0 : ℝ)..a, Real.sqrt (radialTerm a x) ^ n) =
      ∫ t in (0 : ℝ)..Real.pi / 2,
        a ^ (n + 1) * Real.cos t ^ (n + 1) := by
  let m : ℝ → ℝ := fun t => a - a * Real.sin t
  let F : ℝ → ℝ := fun x => Real.sqrt (radialTerm a x) ^ n
  let G : ℝ → ℝ := fun y => ∫ x in (0 : ℝ)..y, F x
  have hradCont : Continuous (fun x : ℝ => radialTerm a x) := by
    simpa [radialTerm] using
      ((continuous_const.mul continuous_id).sub (continuous_id.pow 2) :
        Continuous (fun x : ℝ => (2 * a) * x - x ^ 2))
  have hFCont : Continuous F := by
    exact (Real.continuous_sqrt.comp hradCont).pow n
  have hmCont : Continuous m := by
    exact continuous_const.sub (continuous_const.mul Real.continuous_sin)
  have hmDeriv : ∀ t : ℝ, HasDerivAt m (-a * Real.cos t) t := by
    intro t
    change HasDerivAt (fun u : ℝ => a - a * Real.sin u)
      (-a * Real.cos t) t
    convert (hasDerivAt_const (x := t) a).sub
      ((Real.hasDerivAt_sin t).const_mul a) using 1 <;> ring
  have hG : ∀ y : ℝ, HasDerivAt G (F y) y := by
    intro y
    change HasDerivAt (fun z : ℝ => ∫ x in (0 : ℝ)..z, F x) (F y) y
    exact intervalIntegral.integral_hasDerivAt_right
      (hFCont.intervalIntegrable 0 y)
      hFCont.stronglyMeasurable.stronglyMeasurableAtFilter
      hFCont.continuousAt
  have hnegCos : Continuous (fun t : ℝ => -a * Real.cos t) :=
    continuous_const.mul Real.continuous_cos
  have hHCont : Continuous (fun t : ℝ => F (m t) * (-a * Real.cos t)) :=
    (hFCont.comp hmCont).mul hnegCos
  have hcomp : ∀ t ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun u : ℝ => G (m u))
        (F (m t) * (-a * Real.cos t)) t := by
    intro t ht
    exact (hG (m t)).comp t (hmDeriv t)
  have hchange :
      (∫ t in (0 : ℝ)..Real.pi / 2,
        F (m t) * (-a * Real.cos t)) =
        -(∫ x in (0 : ℝ)..a, F x) := by
    have hi : IntervalIntegrable
        (fun t : ℝ => F (m t) * (-a * Real.cos t)) volume
        0 (Real.pi / 2) :=
      hHCont.intervalIntegrable 0 (Real.pi / 2)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hcomp hi
    calc
      (∫ t in (0 : ℝ)..Real.pi / 2,
        F (m t) * (-a * Real.cos t)) =
          G (m (Real.pi / 2)) - G (m 0) := hftc
      _ = -(∫ x in (0 : ℝ)..a, F x) := by
        simp [G, m, Real.sin_zero, Real.sin_pi_div_two]
  have hpoint : ∀ t ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
      Real.sqrt (radialTerm a (m t)) = a * Real.cos t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
      rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at ht
      exact ht
    have hcos : 0 ≤ Real.cos t := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor
      · have hp : 0 ≤ Real.pi / 2 := by positivity
        exact (neg_nonpos.mpr hp).trans ht'.1
      · exact ht'.2
    have hr : radialTerm a (m t) = (a * Real.cos t) ^ 2 := by
      calc
        radialTerm a (m t) =
            a ^ 2 * (1 - Real.sin t ^ 2) := by
              dsimp [m]
              unfold radialTerm
              ring
        _ = a ^ 2 * Real.cos t ^ 2 := by
              rw [← Real.sin_sq_add_cos_sq t]
              ring
        _ = (a * Real.cos t) ^ 2 := by ring
    rw [hr, Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg ha.le hcos)]
  have hleft :
      (∫ t in (0 : ℝ)..Real.pi / 2,
        F (m t) * (-a * Real.cos t)) =
        -(∫ t in (0 : ℝ)..Real.pi / 2,
          a ^ (n + 1) * Real.cos t ^ (n + 1)) := by
    calc
      (∫ t in (0 : ℝ)..Real.pi / 2,
        F (m t) * (-a * Real.cos t)) =
          ∫ t in (0 : ℝ)..Real.pi / 2,
            -(a ^ (n + 1) * Real.cos t ^ (n + 1)) := by
              apply intervalIntegral.integral_congr
              intro t ht
              dsimp [F]
              rw [hpoint t ht, mul_pow]
              simp only [pow_succ]
              ring
      _ = -(∫ t in (0 : ℝ)..Real.pi / 2,
          a ^ (n + 1) * Real.cos t ^ (n + 1)) := by
            rw [intervalIntegral.integral_neg]
  have hneg :
      -(∫ t in (0 : ℝ)..Real.pi / 2,
          a ^ (n + 1) * Real.cos t ^ (n + 1)) =
        -(∫ x in (0 : ℝ)..a, F x) :=
    hleft.symm.trans hchange
  exact (neg_inj.mp hneg).symm

theorem gap1 (a : ℝ) (ha : 0 < a) :
    Ix a =
      ∫ x in (0 : ℝ)..a,
        ∫ y in (0 : ℝ)..a - Real.sqrt (2 * a * x - x ^ 2),
          y ^ 2 := by
  rfl

theorem gap2 (a : ℝ) (ha : 0 < a) :
    Ix a =
      1 / 3 *
        ∫ x in (0 : ℝ)..a,
          (a ^ 3 - 3 * a ^ 2 * Real.sqrt (radialTerm a x) +
            3 * a * radialTerm a x -
            Real.sqrt (radialTerm a x) ^ 3) := by
  rw [gap1 a ha, ← intervalIntegral.integral_const_mul]
  have hpow : ∀ b : ℝ,
      (∫ y in (0 : ℝ)..b, y ^ 2) = b ^ 3 / 3 := by
    intro b
    have hd : ∀ y ∈ Set.uIcc (0 : ℝ) b,
        HasDerivAt (fun z : ℝ => z ^ 3 / 3) (y ^ 2) y := by
      intro y hy
      convert ((hasDerivAt_id y).pow 3).div_const 3 using 1 <;>
        simp only [id_eq] <;> ring
    have hi : IntervalIntegrable (fun y : ℝ => y ^ 2) volume 0 b :=
      (continuous_id.pow 2).intervalIntegrable 0 b
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Set.Icc (0 : ℝ) a := by
    rw [Set.uIcc_of_le (le_of_lt ha)] at hx
    exact hx
  have hr : 0 ≤ radialTerm a x := by
    unfold radialTerm
    nlinarith [hx'.1, hx'.2]
  have hs : Real.sqrt (radialTerm a x) ^ 2 = radialTerm a x :=
    Real.sq_sqrt hr
  change
    (∫ y in (0 : ℝ)..a - Real.sqrt (radialTerm a x), y ^ 2) =
      1 / 3 *
        (a ^ 3 - 3 * a ^ 2 * Real.sqrt (radialTerm a x) +
          3 * a * radialTerm a x - Real.sqrt (radialTerm a x) ^ 3)
  rw [hpow]
  nlinarith [hs]

theorem gap3 (a : ℝ) (ha : 0 < a) :
    Ix a =
      (elementaryPrimitive a a - elementaryPrimitive a 0) -
        1 / 3 *
          ∫ x in (0 : ℝ)..a, Real.sqrt (radialTerm a x) ^ 3 := by
  rw [gap2 a ha]
  have hradCont : Continuous (fun x : ℝ => radialTerm a x) := by
    simpa [radialTerm] using
      ((continuous_const.mul continuous_id).sub (continuous_id.pow 2) :
        Continuous (fun x : ℝ => (2 * a) * x - x ^ 2))
  have hrootCont : Continuous (fun x : ℝ => Real.sqrt (radialTerm a x)) :=
    Real.continuous_sqrt.comp hradCont
  have hpolyCont : Continuous
      (fun x : ℝ => a ^ 3 + 3 * a * radialTerm a x) := by
    exact continuous_const.add (continuous_const.mul hradCont)
  have hscaledCont : Continuous
      (fun x : ℝ => (3 * a ^ 2) * Real.sqrt (radialTerm a x)) :=
    continuous_const.mul hrootCont
  have hcubeCont : Continuous
      (fun x : ℝ => Real.sqrt (radialTerm a x) ^ 3) :=
    hrootCont.pow 3
  have hpolyInt : IntervalIntegrable
      (fun x : ℝ => a ^ 3 + 3 * a * radialTerm a x) volume 0 a :=
    hpolyCont.intervalIntegrable 0 a
  have hscaledInt : IntervalIntegrable
      (fun x : ℝ => (3 * a ^ 2) * Real.sqrt (radialTerm a x)) volume 0 a :=
    hscaledCont.intervalIntegrable 0 a
  have hcubeInt : IntervalIntegrable
      (fun x : ℝ => Real.sqrt (radialTerm a x) ^ 3) volume 0 a :=
    hcubeCont.intervalIntegrable 0 a
  have hpoly :
      (∫ x in (0 : ℝ)..a, a ^ 3 + 3 * a * radialTerm a x) =
        3 * a ^ 4 := by
    have hd : ∀ x ∈ Set.uIcc (0 : ℝ) a,
        HasDerivAt
          (fun z : ℝ => a ^ 3 * z + 3 * a ^ 2 * z ^ 2 - a * z ^ 3)
          (a ^ 3 + 3 * a * radialTerm a x) x := by
      intro x hx
      convert (((hasDerivAt_id x).const_mul (a ^ 3)).add
        (((hasDerivAt_id x).pow 2).const_mul (3 * a ^ 2))).sub
        (((hasDerivAt_id x).pow 3).const_mul a) using 1 <;>
        simp only [id_eq, radialTerm] <;> ring
    calc
      (∫ x in (0 : ℝ)..a, a ^ 3 + 3 * a * radialTerm a x) =
          (a ^ 3 * a + 3 * a ^ 2 * a ^ 2 - a * a ^ 3) -
            (a ^ 3 * 0 + 3 * a ^ 2 * 0 ^ 2 - a * 0 ^ 3) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt hd hpolyInt
      _ = 3 * a ^ 4 := by ring
  have hdecomp :
      (∫ x in (0 : ℝ)..a,
        a ^ 3 - 3 * a ^ 2 * Real.sqrt (radialTerm a x) +
          3 * a * radialTerm a x - Real.sqrt (radialTerm a x) ^ 3) =
        (∫ x in (0 : ℝ)..a, a ^ 3 + 3 * a * radialTerm a x) -
          3 * a ^ 2 *
            (∫ x in (0 : ℝ)..a, Real.sqrt (radialTerm a x)) -
          (∫ x in (0 : ℝ)..a, Real.sqrt (radialTerm a x) ^ 3) := by
    calc
      (∫ x in (0 : ℝ)..a,
        a ^ 3 - 3 * a ^ 2 * Real.sqrt (radialTerm a x) +
          3 * a * radialTerm a x - Real.sqrt (radialTerm a x) ^ 3) =
          ∫ x in (0 : ℝ)..a,
            (a ^ 3 + 3 * a * radialTerm a x) -
              (3 * a ^ 2) * Real.sqrt (radialTerm a x) -
              Real.sqrt (radialTerm a x) ^ 3 := by
            apply intervalIntegral.integral_congr
            intro x hx
            ring
      _ = (∫ x in (0 : ℝ)..a, a ^ 3 + 3 * a * radialTerm a x) -
          (∫ x in (0 : ℝ)..a,
            (3 * a ^ 2) * Real.sqrt (radialTerm a x)) -
          (∫ x in (0 : ℝ)..a, Real.sqrt (radialTerm a x) ^ 3) := by
            rw [intervalIntegral.integral_sub
                (hpolyInt.sub hscaledInt) hcubeInt,
              intervalIntegral.integral_sub hpolyInt hscaledInt]
      _ = (∫ x in (0 : ℝ)..a, a ^ 3 + 3 * a * radialTerm a x) -
          3 * a ^ 2 *
            (∫ x in (0 : ℝ)..a, Real.sqrt (radialTerm a x)) -
          (∫ x in (0 : ℝ)..a, Real.sqrt (radialTerm a x) ^ 3) := by
            rw [intervalIntegral.integral_const_mul]
  have hcosDeriv : ∀ t : ℝ,
      HasDerivAt
        (fun u : ℝ => u / 2 + Real.sin (2 * u) / 4)
        (Real.cos t ^ 2) t := by
    intro t
    have h2 : HasDerivAt (fun u : ℝ => 2 * u) 2 t := by
      simpa only [id_eq, mul_one] using
        (hasDerivAt_id t).const_mul 2
    have hs2 : HasDerivAt (fun u : ℝ => Real.sin (2 * u))
        (2 * Real.cos (2 * t)) t := by
      convert (Real.hasDerivAt_sin (2 * t)).comp t h2 using 1 <;> ring
    have hF := ((hasDerivAt_id t).div_const 2).add (hs2.div_const 4)
    have hc2 : Real.cos (2 * t) = 2 * Real.cos t ^ 2 - 1 := by
      simpa using Real.cos_two_mul t
    convert hF using 1
    rw [hc2]
    ring
  have hcos2 :
      (∫ t in (0 : ℝ)..Real.pi / 2, Real.cos t ^ 2) = Real.pi / 4 := by
    have hi : IntervalIntegrable (fun t : ℝ => Real.cos t ^ 2) volume
        0 (Real.pi / 2) :=
      (Real.continuous_cos.pow 2).intervalIntegrable 0 (Real.pi / 2)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hcosDeriv t) hi
    have hpi : (2 : ℝ) * (Real.pi / 2) = Real.pi := by ring
    have hftc' :
        (∫ t in (0 : ℝ)..Real.pi / 2, Real.cos t ^ 2) =
          Real.pi / 2 / 2 := by
      simpa only [hpi, Real.sin_pi, mul_zero, Real.sin_zero, zero_div,
        zero_add, add_zero, sub_zero] using hftc
    calc
      (∫ t in (0 : ℝ)..Real.pi / 2, Real.cos t ^ 2) =
          Real.pi / 2 / 2 := hftc'
      _ = Real.pi / 4 := by ring
  have hroot :
      (∫ x in (0 : ℝ)..a, Real.sqrt (radialTerm a x)) =
        a ^ 2 * Real.pi / 4 := by
    have h := radial_sqrt_pow_integral a ha 1
    simp only [pow_one] at h
    rw [h, intervalIntegral.integral_const_mul, hcos2]
    ring
  have helem :
      elementaryPrimitive a a - elementaryPrimitive a 0 =
        a ^ 4 * (1 - Real.pi / 4) := by
    unfold elementaryPrimitive sqrtPrimitive
    have hne : a ≠ 0 := ne_of_gt ha
    simp [radialTerm, hne, Real.arcsin_zero]
    ring
  rw [hdecomp, hpoly, hroot, helem]
  ring

theorem gap4 (a : ℝ) (ha : 0 < a) :
    Ix a =
      a ^ 4 * (1 - Real.pi / 4) -
        1 / 3 *
          ∫ t in (0 : ℝ)..Real.pi / 2, a ^ 4 * Real.cos t ^ 4 := by
  rw [gap3 a ha]
  have helem :
      elementaryPrimitive a a - elementaryPrimitive a 0 =
        a ^ 4 * (1 - Real.pi / 4) := by
    unfold elementaryPrimitive sqrtPrimitive
    have hne : a ≠ 0 := ne_of_gt ha
    simp [radialTerm, hne, Real.arcsin_zero]
    ring
  rw [helem, radial_sqrt_pow_integral a ha 3]

theorem gap5 (a : ℝ) (ha : 0 < a) :
    Ix a =
      a ^ 4 * (1 - Real.pi / 4) -
        a ^ 4 / 3 * (3 / 4 : ℝ) * (1 / 2 : ℝ) *
          (Real.pi / 2) := by
  rw [gap4 a ha]
  have hderiv : ∀ t : ℝ,
      HasDerivAt
        (fun u : ℝ => 3 * u / 8 + Real.sin (2 * u) / 4 +
          Real.sin (4 * u) / 32)
        (Real.cos t ^ 4) t := by
    intro t
    have h2 : HasDerivAt (fun u : ℝ => 2 * u) 2 t := by
      simpa only [id_eq, mul_one] using
        (hasDerivAt_id t).const_mul 2
    have h4 : HasDerivAt (fun u : ℝ => 4 * u) 4 t := by
      simpa only [id_eq, mul_one] using
        (hasDerivAt_id t).const_mul 4
    have hs2 : HasDerivAt (fun u : ℝ => Real.sin (2 * u))
        (2 * Real.cos (2 * t)) t := by
      convert (Real.hasDerivAt_sin (2 * t)).comp t h2 using 1 <;> ring
    have hs4 : HasDerivAt (fun u : ℝ => Real.sin (4 * u))
        (4 * Real.cos (4 * t)) t := by
      convert (Real.hasDerivAt_sin (4 * t)).comp t h4 using 1 <;> ring
    have hF :=
      ((((hasDerivAt_id t).const_mul 3).div_const 8).add
        (hs2.div_const 4)).add (hs4.div_const 32)
    have hc2 : Real.cos (2 * t) = 2 * Real.cos t ^ 2 - 1 := by
      simpa using Real.cos_two_mul t
    have hc4 : Real.cos (4 * t) = 2 * Real.cos (2 * t) ^ 2 - 1 := by
      convert Real.cos_two_mul (2 * t) using 1 <;> ring
    convert hF using 1
    rw [hc4, hc2]
    ring
  have hcos :
      (∫ t in (0 : ℝ)..Real.pi / 2, Real.cos t ^ 4) =
        3 / 4 * (1 / 2 : ℝ) * (Real.pi / 2) := by
    have hi : IntervalIntegrable (fun t : ℝ => Real.cos t ^ 4) volume
        0 (Real.pi / 2) :=
      (Real.continuous_cos.pow 4).intervalIntegrable 0 (Real.pi / 2)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderiv t) hi
    have h2pi : (2 : ℝ) * (Real.pi / 2) = Real.pi := by ring
    have h4pi : (4 : ℝ) * (Real.pi / 2) = 2 * Real.pi := by ring
    have hftc' :
        (∫ t in (0 : ℝ)..Real.pi / 2, Real.cos t ^ 4) =
          3 * (Real.pi / 2) / 8 := by
      simpa only [h2pi, h4pi, Real.sin_pi, Real.sin_two_pi, mul_zero,
        Real.sin_zero, zero_div, zero_add, add_zero, sub_zero] using hftc
    calc
      (∫ t in (0 : ℝ)..Real.pi / 2, Real.cos t ^ 4) =
          3 * (Real.pi / 2) / 8 := hftc'
      _ = 3 / 4 * (1 / 2 : ℝ) * (Real.pi / 2) := by ring
  rw [intervalIntegral.integral_const_mul, hcos]
  ring

theorem gap6 (a : ℝ) :
    a ^ 4 * (1 - Real.pi / 4) -
        a ^ 4 / 3 * (3 / 4 : ℝ) * (1 / 2 : ℝ) *
          (Real.pi / 2) =
      a ^ 4 / 16 * (16 - 5 * Real.pi) := by
  ring

theorem gap7 (a : ℝ) (ha : 0 < a) :
    Ix a = a ^ 4 / 16 * (16 - 5 * Real.pi) := by
  exact (gap5 a ha).trans (gap6 a)

theorem gap8 (a : ℝ) (ha : 0 < a) :
    Iy a = Ix a := by
  rfl

theorem gap9 (a : ℝ) (ha : 0 < a) :
    Ix a = a ^ 4 / 16 * (16 - 5 * Real.pi) := by
  exact gap7 a ha

theorem gap10 (a : ℝ) (ha : 0 < a) :
    Iy a = a ^ 4 / 16 * (16 - 5 * Real.pi) := by
  calc
    Iy a = Ix a := gap8 a ha
    _ = a ^ 4 / 16 * (16 - 5 * Real.pi) := gap9 a ha

end

end ProofGap.Exercise4062
