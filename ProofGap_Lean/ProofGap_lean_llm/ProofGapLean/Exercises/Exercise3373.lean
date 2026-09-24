import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise3373

noncomputable section

def secondDeriv (y : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv y) x

def IsC2Solution (ε : ℝ) (y : ℝ → ℝ) : Prop :=
  Differentiable ℝ y ∧ Differentiable ℝ (deriv y) ∧
    ∀ x, y x - ε * Real.sin (y x) = x

private theorem denominator_pos (ε a : ℝ) (hεpos : 0 < ε) (hεlt : ε < 1) :
    0 < 1 - ε * Real.cos a := by
  have hc : ε * Real.cos a ≤ ε * 1 :=
    mul_le_mul_of_nonneg_left (Real.cos_le_one a) (le_of_lt hεpos)
  linarith

theorem gap1 (ε : ℝ) (y : ℝ → ℝ)
    (hεpos : 0 < ε) (hεlt : ε < 1) (hy : IsC2Solution ε y) :
    ∀ x,
      deriv y x - ε * deriv y x * Real.cos (y x) = 1 := by
  intro x
  have hdy : HasDerivAt y (deriv y x) x :=
    hy.1.differentiableAt.hasDerivAt
  have hsin :
      HasDerivAt (fun z => Real.sin (y z))
        (Real.cos (y x) * deriv y x) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sin (y x)).comp x hdy
  have hleft :
      HasDerivAt
        (fun z => y z - ε * Real.sin (y z))
        (deriv y x - ε * deriv y x * Real.cos (y x)) x := by
    convert hdy.sub (hsin.const_mul ε) using 1 <;> ring
  have heq :
      (fun z => y z - ε * Real.sin (y z)) = (fun z : ℝ => z) := by
    funext z
    exact hy.2.2 z
  rw [heq] at hleft
  exact hleft.unique (hasDerivAt_id x)

theorem gap2 (ε : ℝ) (y : ℝ → ℝ)
    (hεpos : 0 < ε) (hεlt : ε < 1) (hy : IsC2Solution ε y) :
    ∀ x, deriv y x = 1 / (1 - ε * Real.cos (y x)) := by
  intro x
  have hd : 0 < 1 - ε * Real.cos (y x) :=
    denominator_pos ε (y x) hεpos hεlt
  apply (eq_div_iff (ne_of_gt hd)).2
  calc
    deriv y x * (1 - ε * Real.cos (y x)) =
        deriv y x - ε * deriv y x * Real.cos (y x) := by ring
    _ = 1 := gap1 ε y hεpos hεlt hy x

theorem gap3 (ε : ℝ) (y : ℝ → ℝ)
    (hεpos : 0 < ε) (hεlt : ε < 1) (hy : IsC2Solution ε y) :
    ∀ x,
      secondDeriv y x =
        -(ε * deriv y x * Real.sin (y x)) /
          (1 - ε * Real.cos (y x)) ^ 2 := by
  intro x
  have hdy : HasDerivAt y (deriv y x) x :=
    hy.1.differentiableAt.hasDerivAt
  have hddy : HasDerivAt (deriv y) (secondDeriv y x) x := by
    simpa only [secondDeriv] using hy.2.1.differentiableAt.hasDerivAt
  have hcos :
      HasDerivAt (fun z => Real.cos (y z))
        (-Real.sin (y x) * deriv y x) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_cos (y x)).comp x hdy
  have hleft :
      HasDerivAt
        (fun z => deriv y z - ε * deriv y z * Real.cos (y z))
        (secondDeriv y x -
          ((ε * secondDeriv y x) * Real.cos (y x) +
            (ε * deriv y x) *
              (-Real.sin (y x) * deriv y x))) x := by
    exact hddy.sub ((hddy.const_mul ε).mul hcos)
  have heq :
      (fun z => deriv y z - ε * deriv y z * Real.cos (y z)) =
        (fun _ : ℝ => 1) := by
    funext z
    exact gap1 ε y hεpos hεlt hy z
  rw [heq] at hleft
  have hz :
      secondDeriv y x -
          ((ε * secondDeriv y x) * Real.cos (y x) +
            (ε * deriv y x) *
              (-Real.sin (y x) * deriv y x)) = 0 :=
    hleft.unique (hasDerivAt_const x 1)
  have hd : 0 < 1 - ε * Real.cos (y x) :=
    denominator_pos ε (y x) hεpos hεlt
  have hne : 1 - ε * Real.cos (y x) ≠ 0 := ne_of_gt hd
  have hfirst :
      deriv y x * (1 - ε * Real.cos (y x)) = 1 :=
    (eq_div_iff hne).mp (gap2 ε y hεpos hεlt hy x)
  have himp :
      secondDeriv y x * (1 - ε * Real.cos (y x)) =
        -(ε * (deriv y x) ^ 2 * Real.sin (y x)) := by
    nlinarith [hz]
  apply (eq_div_iff (pow_ne_zero 2 hne)).2
  calc
    secondDeriv y x * (1 - ε * Real.cos (y x)) ^ 2 =
        (secondDeriv y x * (1 - ε * Real.cos (y x))) *
          (1 - ε * Real.cos (y x)) := by ring
    _ = -(ε * (deriv y x) ^ 2 * Real.sin (y x)) *
          (1 - ε * Real.cos (y x)) := by rw [himp]
    _ = -(ε * deriv y x * Real.sin (y x)) *
          (deriv y x * (1 - ε * Real.cos (y x))) := by ring
    _ = -(ε * deriv y x * Real.sin (y x)) * 1 := by rw [hfirst]
    _ = -(ε * deriv y x * Real.sin (y x)) := by ring

theorem gap4 (ε : ℝ) (y : ℝ → ℝ)
    (hεpos : 0 < ε) (hεlt : ε < 1) (hy : IsC2Solution ε y) :
    ∀ x,
      -(ε * deriv y x * Real.sin (y x)) /
          (1 - ε * Real.cos (y x)) ^ 2 =
        -(ε * Real.sin (y x)) /
          (1 - ε * Real.cos (y x)) ^ 3 := by
  intro x
  have hd : 0 < 1 - ε * Real.cos (y x) :=
    denominator_pos ε (y x) hεpos hεlt
  have hne : 1 - ε * Real.cos (y x) ≠ 0 := ne_of_gt hd
  rw [gap2 ε y hεpos hεlt hy x]
  field_simp [hne]
  <;> ring

theorem gap5 (ε : ℝ) (y : ℝ → ℝ)
    (hεpos : 0 < ε) (hεlt : ε < 1) (hy : IsC2Solution ε y) :
    ∀ x,
      secondDeriv y x =
        -(ε * Real.sin (y x)) /
          (1 - ε * Real.cos (y x)) ^ 3 := by
  intro x
  calc
    secondDeriv y x =
        -(ε * deriv y x * Real.sin (y x)) /
          (1 - ε * Real.cos (y x)) ^ 2 :=
      gap3 ε y hεpos hεlt hy x
    _ = -(ε * Real.sin (y x)) /
          (1 - ε * Real.cos (y x)) ^ 3 :=
      gap4 ε y hεpos hεlt hy x

end

end ProofGap.Exercise3373
