import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise3907

noncomputable section

open MeasureTheory
open scoped Interval

theorem gap1 :
    (∫ x in (0 : ℝ)..1, ∫ y in x ^ 2..x, x * y ^ 2) =
      ∫ x in (0 : ℝ)..1, x ^ 4 / 3 - x ^ 7 / 3 := by
  apply intervalIntegral.integral_congr
  intro x hx
  change (∫ y in x ^ 2..x, x * y ^ 2) = x ^ 4 / 3 - x ^ 7 / 3
  let F : ℝ → ℝ := fun z => x * (z * z * z / 3)
  have hderiv :
      ∀ y ∈ Set.uIcc (x ^ 2) x,
        HasDerivAt F (x * y ^ 2) y := by
    intro y hy
    have h1 : HasDerivAt (fun z : ℝ => z) 1 y := hasDerivAt_id y
    have h2 :
        HasDerivAt (fun z : ℝ => z * z) (1 * y + y * 1) y :=
      h1.mul h1
    have h3 :
        HasDerivAt (fun z : ℝ => z * z * z)
          ((1 * y + y * 1) * y + (y * y) * 1) y :=
      h2.mul h1
    dsimp [F]
    convert (h3.div_const 3).const_mul x using 1 <;>
      norm_num <;> ring_nf <;> simp
  have hint :
      IntervalIntegrable (fun y : ℝ => x * y ^ 2) volume (x ^ 2) x := by
    simpa only [id_eq] using
      (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable
        (μ := volume) (x ^ 2) x
  calc
    (∫ y in x ^ 2..x, x * y ^ 2) = F x - F (x ^ 2) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    _ = x ^ 4 / 3 - x ^ 7 / 3 := by
      dsimp [F]
      ring

theorem gap2 :
    (∫ x in (0 : ℝ)..1, x ^ 4 / 3 - x ^ 7 / 3) =
      1 / 40 := by
  let F : ℝ → ℝ := fun z =>
    (z * z * z * z * z) / 15 -
      (z * z * z * z * z * z * z * z) / 24
  have hderiv :
      ∀ x ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt F (x ^ 4 / 3 - x ^ 7 / 3) x := by
    intro x hx
    have h1 : HasDerivAt (fun z : ℝ => z) 1 x := hasDerivAt_id x
    have h2 : HasDerivAt (fun z : ℝ => z * z) _ x := h1.mul h1
    have h3 : HasDerivAt (fun z : ℝ => z * z * z) _ x := h2.mul h1
    have h4 : HasDerivAt (fun z : ℝ => z * z * z * z) _ x := h3.mul h1
    have h5 : HasDerivAt (fun z : ℝ => z * z * z * z * z) _ x :=
      h4.mul h1
    have h6 : HasDerivAt (fun z : ℝ => z * z * z * z * z * z) _ x :=
      h5.mul h1
    have h7 :
        HasDerivAt (fun z : ℝ => z * z * z * z * z * z * z) _ x :=
      h6.mul h1
    have h8 :
        HasDerivAt (fun z : ℝ => z * z * z * z * z * z * z * z) _ x :=
      h7.mul h1
    dsimp [F]
    convert (h5.div_const 15).sub (h8.div_const 24) using 1 <;>
      norm_num <;> ring
  have hint :
      IntervalIntegrable (fun x : ℝ => x ^ 4 / 3 - x ^ 7 / 3)
        volume 0 1 := by
    simpa only [id_eq] using
      (((continuous_id.pow 4).div_const 3).sub
        ((continuous_id.pow 7).div_const 3)).intervalIntegrable
          (μ := volume) (0 : ℝ) 1
  calc
    (∫ x in (0 : ℝ)..1, x ^ 4 / 3 - x ^ 7 / 3) = F 1 - F 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    _ = 1 / 40 := by
      norm_num [F]

theorem gap3 :
    (∫ x in (0 : ℝ)..1, ∫ y in x ^ 2..x, x * y ^ 2) =
      1 / 40 := by
  rw [gap1, gap2]

end

end ProofGap.Exercise3907
