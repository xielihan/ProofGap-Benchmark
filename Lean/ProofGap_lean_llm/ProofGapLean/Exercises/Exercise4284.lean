import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4284

noncomputable section

open scoped Interval

abbrev Point3 := ℝ × ℝ × ℝ

def field (p : Point3) : Point3 :=
  (p.1, p.2.1 ^ 2, -p.2.2 ^ 3)

def potential (p : Point3) : ℝ :=
  p.1 ^ 2 / 2 + p.2.1 ^ 3 / 3 - p.2.2 ^ 4 / 4

def lineIntegral (γ : ℝ → Point3) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    (field (γ t)).1 * deriv (fun s => (γ s).1) t +
      (field (γ t)).2.1 * deriv (fun s => (γ s).2.1) t +
      (field (γ t)).2.2 * deriv (fun s => (γ s).2.2) t

def AdmissiblePath (γ : ℝ → Point3) (start finish : Point3) : Prop :=
  ContDiff ℝ 1 γ ∧ γ 0 = start ∧ γ 1 = finish

theorem gap1 (γ : ℝ → Point3)
    (hγ : AdmissiblePath γ (1, 1, 1) (2, 3, -4)) :
    lineIntegral γ =
      potential (2, 3, -4) - potential (1, 1, 1) := by
  rcases hγ with ⟨hγc, h0, h1⟩
  have hprojx :
      ContDiff ℝ 1 (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).contDiff
  have hprojrest :
      ContDiff ℝ 1 (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) :=
    (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).contDiff
  have hprojy :
      ContDiff ℝ 1 (ContinuousLinearMap.fst ℝ ℝ ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).contDiff
  have hprojz :
      ContDiff ℝ 1 (ContinuousLinearMap.snd ℝ ℝ ℝ) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).contDiff
  have hx : ContDiff ℝ 1 (fun t => (γ t).1) := by
    simpa using hprojx.comp hγc
  have hrest : ContDiff ℝ 1 (fun t => (γ t).2) := by
    simpa using hprojrest.comp hγc
  have hy : ContDiff ℝ 1 (fun t => (γ t).2.1) := by
    simpa using hprojy.comp hrest
  have hz : ContDiff ℝ 1 (fun t => (γ t).2.2) := by
    simpa using hprojz.comp hrest
  have hF : ContDiff ℝ 1 (fun t => potential (γ t)) := by
    simpa only [potential] using
      (((hx.pow 2).div_const 2).add
        ((hy.pow 3).div_const 3)).sub
        ((hz.pow 4).div_const 4)
  have hderiv (t : ℝ) :
      HasDerivAt (fun s => potential (γ s))
        ((γ t).1 * deriv (fun s => (γ s).1) t +
          (γ t).2.1 ^ 2 * deriv (fun s => (γ s).2.1) t +
          (-(γ t).2.2 ^ 3) * deriv (fun s => (γ s).2.2) t) t := by
    have hxt : HasDerivAt (fun s => (γ s).1)
        (deriv (fun s => (γ s).1) t) t :=
      (hx.differentiable (by norm_num) t).hasDerivAt
    have hyt : HasDerivAt (fun s => (γ s).2.1)
        (deriv (fun s => (γ s).2.1) t) t :=
      (hy.differentiable (by norm_num) t).hasDerivAt
    have hzt : HasDerivAt (fun s => (γ s).2.2)
        (deriv (fun s => (γ s).2.2) t) t :=
      (hz.differentiable (by norm_num) t).hasDerivAt
    convert
      (((hxt.mul hxt).div_const 2).add
        (((hyt.mul hyt).mul hyt).div_const 3)).sub
        ((((hzt.mul hzt).mul hzt).mul hzt).div_const 4) using 1 <;>
      norm_num [potential] <;> try ring
    funext s
    simp <;> ring
  have hFderivCont :
      Continuous (fun t => deriv (fun s => potential (γ s)) t) := by
    change Continuous (fun t : ℝ =>
      (fderiv ℝ (fun s => potential (γ s)) t) (1 : ℝ))
    exact
      (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hIeq :
      (fun t : ℝ =>
        (γ t).1 * deriv (fun s => (γ s).1) t +
          (γ t).2.1 ^ 2 * deriv (fun s => (γ s).2.1) t +
          (-(γ t).2.2 ^ 3) * deriv (fun s => (γ s).2.2) t) =
      (fun t : ℝ => deriv (fun s => potential (γ s)) t) := by
    funext t
    exact (hderiv t).deriv.symm
  have hIcont : Continuous (fun t : ℝ =>
      (γ t).1 * deriv (fun s => (γ s).1) t +
        (γ t).2.1 ^ 2 * deriv (fun s => (γ s).2.1) t +
        (-(γ t).2.2 ^ 3) * deriv (fun s => (γ s).2.2) t) := by
    rw [hIeq]
    exact hFderivCont
  have hFTC :
      (∫ t in (0 : ℝ)..1,
        (γ t).1 * deriv (fun s => (γ s).1) t +
          (γ t).2.1 ^ 2 * deriv (fun s => (γ s).2.1) t +
          (-(γ t).2.2 ^ 3) * deriv (fun s => (γ s).2.2) t) =
        potential (γ 1) - potential (γ 0) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s => potential (γ s))
      (f' := fun t =>
        (γ t).1 * deriv (fun s => (γ s).1) t +
          (γ t).2.1 ^ 2 * deriv (fun s => (γ s).2.1) t +
          (-(γ t).2.2 ^ 3) * deriv (fun s => (γ s).2.2) t)
      (a := (0 : ℝ)) (b := 1)
      (fun t _ => hderiv t)
      hIcont.continuousOn.intervalIntegrable
  calc
    lineIntegral γ =
        ∫ t in (0 : ℝ)..1,
          (γ t).1 * deriv (fun s => (γ s).1) t +
            (γ t).2.1 ^ 2 * deriv (fun s => (γ s).2.1) t +
            (-(γ t).2.2 ^ 3) * deriv (fun s => (γ s).2.2) t := by
      rfl
    _ = potential (γ 1) - potential (γ 0) := hFTC
    _ = potential (2, 3, -4) - potential (1, 1, 1) := by
      rw [h1, h0]

theorem gap2 :
    potential (2, 3, -4) - potential (1, 1, 1) =
      -(643 : ℝ) / 12 := by
  norm_num [potential]

theorem gap3 (γ : ℝ → Point3)
    (hγ : AdmissiblePath γ (1, 1, 1) (2, 3, -4)) :
    lineIntegral γ = -(643 : ℝ) / 12 := by
  rw [gap1 γ hγ, gap2]

end

end ProofGap.Exercise4284
