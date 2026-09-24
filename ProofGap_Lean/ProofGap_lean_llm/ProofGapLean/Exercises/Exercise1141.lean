import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1141

noncomputable section

def x (a t : ℝ) : ℝ := a * Real.cos t
def y (a t : ℝ) : ℝ := a * Real.sin t
def cot (t : ℝ) : ℝ := Real.cos t / Real.sin t
def d1 (a t : ℝ) : ℝ := deriv (y a) t / deriv (x a) t
def d2 (a t : ℝ) : ℝ := deriv (d1 a) t / deriv (x a) t
def d3 (a t : ℝ) : ℝ := deriv (d2 a) t / deriv (x a) t

theorem gap1 (a t : ℝ) (ha : a ≠ 0) (hs : Real.sin t ≠ 0) :
    d1 a t = a * Real.cos t / (-a * Real.sin t) := by
  have hy : HasDerivAt (y a) (a * Real.cos t) t := by
    simpa [y] using (Real.hasDerivAt_sin t).const_mul a
  have hx : HasDerivAt (x a) (-a * Real.sin t) t := by
    simpa [x, mul_neg, neg_mul] using
      (Real.hasDerivAt_cos t).const_mul a
  unfold d1
  rw [hy.deriv, hx.deriv]

theorem gap2 (a t : ℝ) (ha : a ≠ 0) (hs : Real.sin t ≠ 0) :
    a * Real.cos t / (-a * Real.sin t) = -cot t := by
  unfold cot
  field_simp [ha, hs] <;> ring

theorem gap3 (a t : ℝ) (ha : a ≠ 0) (hs : Real.sin t ≠ 0) :
    d1 a t = -cot t := by
  exact (gap1 a t ha hs).trans (gap2 a t ha hs)

theorem gap4 (a t : ℝ) (ha : a ≠ 0) (hs : Real.sin t ≠ 0) :
    d2 a t = (1 / Real.sin t ^ 2) / (-a * Real.sin t) := by
  have hd1raw : ∀ u : ℝ,
      d1 a u = a * Real.cos u / (-a * Real.sin u) := by
    intro u
    have hy : HasDerivAt (y a) (a * Real.cos u) u := by
      simpa [y] using (Real.hasDerivAt_sin u).const_mul a
    have hx : HasDerivAt (x a) (-a * Real.sin u) u := by
      simpa [x, mul_neg, neg_mul] using
        (Real.hasDerivAt_cos u).const_mul a
    unfold d1
    rw [hy.deriv, hx.deriv]
  have hd1 : d1 a = fun u : ℝ => -cot u := by
    funext u
    by_cases hu : Real.sin u = 0
    · rw [hd1raw u]
      simp [cot, hu]
    · exact gap3 a u ha hu
  have hraw :=
    ((Real.hasDerivAt_cos t).div (Real.hasDerivAt_sin t) hs).neg
  have hcoef :
      - (((-Real.sin t) * Real.sin t -
          Real.cos t * Real.cos t) / Real.sin t ^ 2) =
        1 / Real.sin t ^ 2 := by
    calc
      - (((-Real.sin t) * Real.sin t -
          Real.cos t * Real.cos t) / Real.sin t ^ 2) =
          (Real.sin t ^ 2 + Real.cos t ^ 2) / Real.sin t ^ 2 := by ring
      _ = 1 / Real.sin t ^ 2 := by rw [Real.sin_sq_add_cos_sq]
  rw [hcoef] at hraw
  have hcot : HasDerivAt (fun u : ℝ => -cot u)
      (1 / Real.sin t ^ 2) t := by
    simpa only [cot] using hraw
  have hx : HasDerivAt (x a) (-a * Real.sin t) t := by
    simpa [x, mul_neg, neg_mul] using
      (Real.hasDerivAt_cos t).const_mul a
  unfold d2
  rw [hd1, hcot.deriv, hx.deriv]

theorem gap5 (a t : ℝ) (ha : a ≠ 0) (hs : Real.sin t ≠ 0) :
    (1 / Real.sin t ^ 2) / (-a * Real.sin t) =
      -1 / (a * Real.sin t ^ 3) := by
  field_simp [ha, hs] <;> ring

theorem gap6 (a t : ℝ) (ha : a ≠ 0) (hs : Real.sin t ≠ 0) :
    d2 a t = -1 / (a * Real.sin t ^ 3) := by
  exact (gap4 a t ha hs).trans (gap5 a t ha hs)

theorem gap7 (a t : ℝ) (ha : a ≠ 0) (hs : Real.sin t ≠ 0) :
    d3 a t =
      (3 * Real.cos t / (a * Real.sin t ^ 4)) / (-a * Real.sin t) := by
  have hsin : ∀ᶠ u in nhds t, Real.sin u ≠ 0 :=
    Real.continuous_sin.continuousAt.eventually_ne hs
  have hd2 :
      d2 a =ᶠ[nhds t]
        (fun u : ℝ => -1 / (a * Real.sin u ^ 3)) := by
    filter_upwards [hsin] with u hu
    exact gap6 a u ha hu
  have hconst : HasDerivAt (fun _ : ℝ => (-1 : ℝ)) 0 t := by
    simpa using (hasDerivAt_const (x := t) (-1 : ℝ))
  have hpow := (Real.hasDerivAt_sin t).pow 3
  change HasDerivAt (fun u : ℝ => Real.sin u ^ 3)
      (3 * Real.sin t ^ (3 - 1) * Real.cos t) t at hpow
  have hquot := hconst.div
    (hpow.const_mul a)
    (mul_ne_zero ha (pow_ne_zero 3 hs))
  have hformula :
      HasDerivAt (fun u : ℝ => -1 / (a * Real.sin u ^ 3))
        (3 * Real.cos t / (a * Real.sin t ^ 4)) t := by
    convert hquot using 1 <;> field_simp [ha, hs] <;> ring
  have hd2der : HasDerivAt (d2 a)
      (3 * Real.cos t / (a * Real.sin t ^ 4)) t :=
    hformula.congr_of_eventuallyEq hd2
  have hx : HasDerivAt (x a) (-a * Real.sin t) t := by
    simpa [x, mul_neg, neg_mul] using
      (Real.hasDerivAt_cos t).const_mul a
  unfold d3
  rw [hd2der.deriv, hx.deriv]

theorem gap8 (a t : ℝ) (ha : a ≠ 0) (hs : Real.sin t ≠ 0) :
    (3 * Real.cos t / (a * Real.sin t ^ 4)) / (-a * Real.sin t) =
      -(3 * Real.cos t) / (a ^ 2 * Real.sin t ^ 5) := by
  field_simp [ha, hs] <;> ring

theorem gap9 (a t : ℝ) (ha : a ≠ 0) (hs : Real.sin t ≠ 0) :
    d3 a t = -(3 * Real.cos t) / (a ^ 2 * Real.sin t ^ 5) := by
  exact (gap7 a t ha hs).trans (gap8 a t ha hs)

end

end ProofGap.Exercise1141
