import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4285

noncomputable section

open scoped Interval

abbrev Point3 := ℝ × ℝ × ℝ

def field (p : Point3) : Point3 :=
  (p.2.1 * p.2.2, p.1 * p.2.2, p.1 * p.2.1)

def potential (p : Point3) : ℝ :=
  p.1 * p.2.1 * p.2.2

def lineIntegral (γ : ℝ → Point3) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    (field (γ t)).1 * deriv (fun s => (γ s).1) t +
      (field (γ t)).2.1 * deriv (fun s => (γ s).2.1) t +
      (field (γ t)).2.2 * deriv (fun s => (γ s).2.2) t

def AdmissiblePath (γ : ℝ → Point3) (start finish : Point3) : Prop :=
  ContDiff ℝ 1 γ ∧ γ 0 = start ∧ γ 1 = finish

theorem gap1 (γ : ℝ → Point3)
    (hγ : AdmissiblePath γ (1, 2, 3) (6, 1, 1)) :
    lineIntegral γ =
      potential (6, 1, 1) - potential (1, 2, 3) := by
  have hxC : ContDiff ℝ 1 (fun t => (γ t).1) := hγ.1.fst
  have hyC : ContDiff ℝ 1 (fun t => (γ t).2.1) := hγ.1.snd.fst
  have hzC : ContDiff ℝ 1 (fun t => (γ t).2.2) := hγ.1.snd.snd
  have hxd : Differentiable ℝ (fun t => (γ t).1) :=
    hxC.differentiable (by norm_num)
  have hyd : Differentiable ℝ (fun t => (γ t).2.1) :=
    hyC.differentiable (by norm_num)
  have hzd : Differentiable ℝ (fun t => (γ t).2.2) :=
    hzC.differentiable (by norm_num)
  have continuous_deriv_of_contDiff
      (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
      Continuous (fun t => deriv f t) := by
    simpa only [deriv] using
      (hf.continuous_fderiv (by norm_num)).clm_apply
        (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))
  have hd (t : ℝ) :
      HasDerivAt (fun s => potential (γ s))
        ((field (γ t)).1 * deriv (fun s => (γ s).1) t +
          (field (γ t)).2.1 * deriv (fun s => (γ s).2.1) t +
          (field (γ t)).2.2 * deriv (fun s => (γ s).2.2) t) t := by
    have hx : HasDerivAt (fun s => (γ s).1)
        (deriv (fun s => (γ s).1) t) t :=
      hxd.differentiableAt.hasDerivAt
    have hy : HasDerivAt (fun s => (γ s).2.1)
        (deriv (fun s => (γ s).2.1) t) t :=
      hyd.differentiableAt.hasDerivAt
    have hz : HasDerivAt (fun s => (γ s).2.2)
        (deriv (fun s => (γ s).2.2) t) t :=
      hzd.differentiableAt.hasDerivAt
    convert (hx.mul hy).mul hz using 1 <;>
      simp only [potential, field, Pi.mul_apply] <;> ring_nf
  have hdx : Continuous (fun t => deriv (fun s => (γ s).1) t) :=
    continuous_deriv_of_contDiff _ hxC
  have hdy : Continuous (fun t => deriv (fun s => (γ s).2.1) t) :=
    continuous_deriv_of_contDiff _ hyC
  have hdz : Continuous (fun t => deriv (fun s => (γ s).2.2) t) :=
    continuous_deriv_of_contDiff _ hzC
  have hcont : Continuous (fun t =>
      (field (γ t)).1 * deriv (fun s => (γ s).1) t +
        (field (γ t)).2.1 * deriv (fun s => (γ s).2.1) t +
        (field (γ t)).2.2 * deriv (fun s => (γ s).2.2) t) := by
    simpa only [field] using
      (((hyC.continuous.mul hzC.continuous).mul hdx).add
        ((hxC.continuous.mul hzC.continuous).mul hdy)).add
        ((hxC.continuous.mul hyC.continuous).mul hdz)
  have hftc :
      (∫ t in (0 : ℝ)..1,
        (field (γ t)).1 * deriv (fun s => (γ s).1) t +
          (field (γ t)).2.1 * deriv (fun s => (γ s).2.1) t +
          (field (γ t)).2.2 * deriv (fun s => (γ s).2.2) t) =
        potential (γ 1) - potential (γ 0) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hd t) (hcont.intervalIntegrable 0 1)
  simpa [lineIntegral, hγ.2.1, hγ.2.2] using hftc

theorem gap2 :
    potential (6, 1, 1) - potential (1, 2, 3) = 0 := by
  norm_num [potential]

theorem gap3 (γ : ℝ → Point3)
    (hγ : AdmissiblePath γ (1, 2, 3) (6, 1, 1)) :
    lineIntegral γ = 0 := by
  calc
    lineIntegral γ = potential (6, 1, 1) - potential (1, 2, 3) := gap1 γ hγ
    _ = 0 := gap2

end

end ProofGap.Exercise4285
