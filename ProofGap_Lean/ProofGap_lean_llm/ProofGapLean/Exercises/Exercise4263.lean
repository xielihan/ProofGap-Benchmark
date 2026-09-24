import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise4263

noncomputable section

open scoped Interval

abbrev Point := ℝ × ℝ

def field (z : Point) : Point :=
  (z.2 / z.1 ^ 2, -z.1 / z.1 ^ 2)

def potential (z : Point) : ℝ :=
  -z.2 / z.1

def HasCoordinateGradientAt
    (U : Point → ℝ) (V : Point) (z : Point) : Prop :=
  HasDerivAt (fun x => U (x, z.2)) V.1 z.1 ∧
    HasDerivAt (fun y => U (z.1, y)) V.2 z.2

def AdmissiblePath (γ : ℝ → Point) (start finish : Point) : Prop :=
  ContDiff ℝ 1 γ ∧ γ 0 = start ∧ γ 1 = finish ∧
    ∀ t, t ∈ Set.Icc (0 : ℝ) 1 → (γ t).1 ≠ 0

def lineIntegral (γ : ℝ → Point) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    (field (γ t)).1 * deriv (fun s => (γ s).1) t +
      (field (γ t)).2 * deriv (fun s => (γ s).2) t

def exactDifferentialIntegral (γ : ℝ → Point) : ℝ :=
  ∫ t in (0 : ℝ)..1, deriv (fun s => potential (γ s)) t

private theorem potential_hasDerivAt_along
    (γ : ℝ → Point) (t : ℝ)
    (hx : DifferentiableAt ℝ (fun s => (γ s).1) t)
    (hy : DifferentiableAt ℝ (fun s => (γ s).2) t)
    (hne : (γ t).1 ≠ 0) :
    HasDerivAt (fun s => potential (γ s))
      ((field (γ t)).1 * deriv (fun s => (γ s).1) t +
        (field (γ t)).2 * deriv (fun s => (γ s).2) t) t := by
  have hraw := hy.hasDerivAt.neg.div hx.hasDerivAt hne
  change HasDerivAt (fun s => potential (γ s))
    ((-deriv (fun s => (γ s).2) t * (γ t).1 -
        (-(γ t).2) * deriv (fun s => (γ s).1) t) /
        (γ t).1 ^ 2) t at hraw
  have hcoef :
      ((-deriv (fun s => (γ s).2) t) * (γ t).1 -
          (-(γ t).2) * deriv (fun s => (γ s).1) t) /
          (γ t).1 ^ 2 =
        (field (γ t)).1 * deriv (fun s => (γ s).1) t +
          (field (γ t)).2 * deriv (fun s => (γ s).2) t := by
    simp only [field]
    field_simp [hne]
    <;> ring
  rw [hcoef] at hraw
  exact hraw

theorem gap1 (z : Point) (hz : z.1 ≠ 0) :
    HasCoordinateGradientAt potential (field z) z := by
  rw [HasCoordinateGradientAt]
  constructor
  · simpa [potential, field] using
      ((hasDerivAt_const z.1 (-z.2)).div (hasDerivAt_id z.1) hz)
  · simpa [potential, field] using
      ((hasDerivAt_id z.2).neg.div (hasDerivAt_const z.2 z.1) hz)

theorem gap2 (γ : ℝ → Point)
    (hγ : AdmissiblePath γ (2, 1) (1, 2)) :
    lineIntegral γ = exactDifferentialIntegral γ := by
  rcases hγ with ⟨hcont, hstart, hfinish, hnonzero⟩
  have hfst : ContDiff ℝ 1 (fun z : Point => z.1) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).contDiff
  have hsnd : ContDiff ℝ 1 (fun z : Point => z.2) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).contDiff
  have hcx : ContDiff ℝ 1 (fun t => (γ t).1) := by
    simpa only [Function.comp_apply] using hfst.comp hcont
  have hcy : ContDiff ℝ 1 (fun t => (γ t).2) := by
    simpa only [Function.comp_apply] using hsnd.comp hcont
  have hx : Differentiable ℝ (fun t => (γ t).1) :=
    hcx.differentiable (by norm_num)
  have hy : Differentiable ℝ (fun t => (γ t).2) :=
    hcy.differentiable (by norm_num)
  unfold lineIntegral exactDifferentialIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  exact
    (potential_hasDerivAt_along γ t (hx t) (hy t) (hnonzero t ht')).deriv.symm

theorem gap3 (γ : ℝ → Point)
    (hγ : AdmissiblePath γ (2, 1) (1, 2)) :
    lineIntegral γ = potential (1, 2) - potential (2, 1) := by
  rcases hγ with ⟨hcont, hstart, hfinish, hnonzero⟩
  have hfst : ContDiff ℝ 1 (fun z : Point => z.1) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).contDiff
  have hsnd : ContDiff ℝ 1 (fun z : Point => z.2) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).contDiff
  have hcx : ContDiff ℝ 1 (fun t => (γ t).1) := by
    simpa only [Function.comp_apply] using hfst.comp hcont
  have hcy : ContDiff ℝ 1 (fun t => (γ t).2) := by
    simpa only [Function.comp_apply] using hsnd.comp hcont
  have hx : Differentiable ℝ (fun t => (γ t).1) :=
    hcx.differentiable (by norm_num)
  have hy : Differentiable ℝ (fun t => (γ t).2) :=
    hcy.differentiable (by norm_num)
  have hfdx : Continuous (fun t =>
      fderiv ℝ (fun s => (γ s).1) t) :=
    hcx.continuous_fderiv (by norm_num)
  have hfdy : Continuous (fun t =>
      fderiv ℝ (fun s => (γ s).2) t) :=
    hcy.continuous_fderiv (by norm_num)
  have hdx : Continuous (fun t => deriv (fun s => (γ s).1) t) := by
    change Continuous (fun t =>
      (fderiv ℝ (fun s => (γ s).1) t) (1 : ℝ))
    exact hfdx.clm_apply continuous_const
  have hdy : Continuous (fun t => deriv (fun s => (γ s).2) t) := by
    change Continuous (fun t =>
      (fderiv ℝ (fun s => (γ s).2) t) (1 : ℝ))
    exact hfdy.clm_apply continuous_const
  let g : ℝ → ℝ := fun t =>
    (field (γ t)).1 * deriv (fun s => (γ s).1) t +
      (field (γ t)).2 * deriv (fun s => (γ s).2) t
  have hg : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    have hden : ∀ t ∈ Set.Icc (0 : ℝ) 1, (γ t).1 ^ 2 ≠ 0 := by
      intro t ht
      exact pow_ne_zero 2 (hnonzero t ht)
    have hg' :=
      (((hcy.continuous.continuousOn.div
          (hcx.continuous.pow 2).continuousOn hden).mul
          hdx.continuousOn).add
        ((hcx.continuous.neg.continuousOn.div
          (hcx.continuous.pow 2).continuousOn hden).mul
          hdy.continuousOn))
    simpa only [g, field] using hg'
  have hhas : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => potential (γ s)) (g t) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    simpa only [g] using
      potential_hasDerivAt_along γ t (hx t) (hy t) (hnonzero t ht')
  have hgU : ContinuousOn g (Set.uIcc (0 : ℝ) 1) := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hg
  have hint : IntervalIntegrable g MeasureTheory.volume 0 1 :=
    hgU.intervalIntegrable
  have hfund :
      (∫ t in (0 : ℝ)..1, g t) =
        potential (γ 1) - potential (γ 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hhas hint
  simpa only [lineIntegral, g, hfinish, hstart] using hfund

theorem gap4 (γ : ℝ → Point)
    (hγ : AdmissiblePath γ (2, 1) (1, 2)) :
    lineIntegral γ = -(3 : ℝ) / 2 := by
  rw [gap3 γ hγ]
  norm_num [potential]

end

end ProofGap.Exercise4263
