import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1042

noncomputable section

def x (a : ℝ) (t : ℝ) : ℝ := a * Real.cosh t
def y (b : ℝ) (t : ℝ) : ℝ := b * Real.sinh t
def coth (t : ℝ) : ℝ := Real.cosh t / Real.sinh t
def slope (a b t : ℝ) : ℝ := deriv (y b) t / deriv (x a) t

theorem gap1 (b t : ℝ) :
    HasDerivAt (y b) (b * Real.cosh t) t := by
  have hneg : HasDerivAt (fun s : ℝ => -s) (-1) t := by
    simpa using (hasDerivAt_id t).neg
  have hexpneg := (Real.hasDerivAt_exp (-t)).comp t hneg
  have hy : y b = fun s : ℝ => b * ((Real.exp s - Real.exp (-s)) / 2) := by
    funext s
    simp only [y, Real.sinh_eq]
  rw [hy, Real.cosh_eq]
  simpa only [Function.comp_apply, mul_neg, mul_one, sub_neg_eq_add] using
    (((Real.hasDerivAt_exp t).sub hexpneg).div_const (2 : ℝ)).const_mul b

theorem gap2 (a t : ℝ) :
    HasDerivAt (x a) (a * Real.sinh t) t := by
  have hneg : HasDerivAt (fun s : ℝ => -s) (-1) t := by
    simpa using (hasDerivAt_id t).neg
  have hexpneg := (Real.hasDerivAt_exp (-t)).comp t hneg
  have hx : x a = fun s : ℝ => a * ((Real.exp s + Real.exp (-s)) / 2) := by
    funext s
    simp only [x, Real.cosh_eq]
  rw [hx, Real.sinh_eq]
  simpa only [Function.comp_apply, mul_neg, mul_one, sub_eq_add_neg] using
    (((Real.hasDerivAt_exp t).add hexpneg).div_const (2 : ℝ)).const_mul a

theorem gap3 (a b t : ℝ) (ha : a ≠ 0) (ht : Real.sinh t ≠ 0) :
    slope a b t = b * Real.cosh t / (a * Real.sinh t) := by
  unfold slope
  rw [(gap1 b t).deriv, (gap2 a t).deriv]

theorem gap4 (a b t : ℝ) (ha : a ≠ 0) (ht : Real.sinh t ≠ 0) :
    b * Real.cosh t / (a * Real.sinh t) = (b / a) * coth t := by
  rw [coth]
  field_simp [ha, ht]

theorem gap5 (a b t : ℝ) (ha : a ≠ 0) (ht : Real.sinh t ≠ 0) :
    slope a b t = (b / a) * coth t := by
  calc
    slope a b t = b * Real.cosh t / (a * Real.sinh t) := gap3 a b t ha ht
    _ = (b / a) * coth t := gap4 a b t ha ht

end

end ProofGap.Exercise1042
