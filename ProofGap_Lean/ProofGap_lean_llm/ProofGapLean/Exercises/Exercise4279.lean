import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise4279

noncomputable section

open scoped Interval

abbrev Point3 := ℝ × ℝ × ℝ

def curve (t : ℝ) : Point3 :=
  (t, t ^ 2, t ^ 3)

def field (p : Point3) : Point3 :=
  (p.2.1 ^ 2 - p.2.2 ^ 2, 2 * p.2.1 * p.2.2, -p.1 ^ 2)

def dot (u v : Point3) : ℝ :=
  u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

def tangent (γ : ℝ → Point3) (t : ℝ) : Point3 :=
  (deriv (fun s => (γ s).1) t,
    deriv (fun s => (γ s).2.1) t,
    deriv (fun s => (γ s).2.2) t)

def lineIntegral : ℝ :=
  ∫ t in (0 : ℝ)..1, dot (field (curve t)) (tangent curve t)

def rawIntegrand (t : ℝ) : ℝ :=
  t ^ 4 - t ^ 6 + 2 * t ^ 2 * t ^ 3 * (2 * t) -
    t ^ 2 * (3 * t ^ 2)

def simplifiedIntegrand (t : ℝ) : ℝ :=
  3 * t ^ 6 - 2 * t ^ 4

theorem gap1 :
    lineIntegral = ∫ t in (0 : ℝ)..1, rawIntegrand t := by
  unfold lineIntegral
  apply congrArg (fun f : ℝ → ℝ => ∫ t in (0 : ℝ)..1, f t)
  funext t
  have hd1 : deriv (fun s : ℝ => s) t = 1 := by
    simpa using (hasDerivAt_id t).deriv
  have hd2 : deriv (fun s : ℝ => s ^ 2) t = 2 * t := by
    simpa using ((hasDerivAt_id t).pow 2).deriv
  have hd3 : deriv (fun s : ℝ => s ^ 3) t = 3 * t ^ 2 := by
    simpa using ((hasDerivAt_id t).pow 3).deriv
  simp [dot, field, curve, tangent, rawIntegrand, hd1, hd2, hd3] <;> ring

theorem gap2 :
    (∫ t in (0 : ℝ)..1, rawIntegrand t) =
      ∫ t in (0 : ℝ)..1, simplifiedIntegrand t := by
  apply congrArg (fun f : ℝ → ℝ => ∫ t in (0 : ℝ)..1, f t)
  funext t
  unfold rawIntegrand simplifiedIntegrand
  ring

theorem gap3 :
    (∫ t in (0 : ℝ)..1, simplifiedIntegrand t) = (1 : ℝ) / 35 := by
  let F : ℝ → ℝ := fun t => (3 / 7) * t ^ 7 - (2 / 5) * t ^ 5
  have hderiv : ∀ t : ℝ, HasDerivAt F (simplifiedIntegrand t) t := by
    intro t
    have h5 : HasDerivAt (fun s : ℝ => s ^ 5) (5 * t ^ 4) t := by
      simpa using ((hasDerivAt_id t).pow 5)
    have h7 : HasDerivAt (fun s : ℝ => s ^ 7) (7 * t ^ 6) t := by
      simpa using ((hasDerivAt_id t).pow 7)
    have hleft : HasDerivAt (fun s : ℝ => (3 / 7) * s ^ 7) (3 * t ^ 6) t := by
      convert (hasDerivAt_const t (3 / 7 : ℝ)).mul h7 using 1 <;>
        (try funext s) <;>
        simp <;>
        ring
    have hright : HasDerivAt (fun s : ℝ => (2 / 5) * s ^ 5) (2 * t ^ 4) t := by
      convert (hasDerivAt_const t (2 / 5 : ℝ)).mul h5 using 1 <;>
        (try funext s) <;>
        simp <;>
        ring
    simpa [F, simplifiedIntegrand] using hleft.sub hright
  have hint : IntervalIntegrable simplifiedIntegrand MeasureTheory.volume 0 1 := by
    simpa only [simplifiedIntegrand] using
      ((continuous_const.mul (continuous_id.pow 6)).sub
        (continuous_const.mul (continuous_id.pow 4))).intervalIntegrable 0 1
  calc
    (∫ t in (0 : ℝ)..1, simplifiedIntegrand t) = F 1 - F 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hderiv t) hint
    _ = (1 : ℝ) / 35 := by
      norm_num [F]

theorem gap4 :
    lineIntegral = (1 : ℝ) / 35 := by
  calc
    lineIntegral = ∫ t in (0 : ℝ)..1, rawIntegrand t := gap1
    _ = ∫ t in (0 : ℝ)..1, simplifiedIntegrand t := gap2
    _ = (1 : ℝ) / 35 := gap3

end

end ProofGap.Exercise4279
