import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise4264

noncomputable section

open scoped Interval

abbrev Point := ℝ × ℝ

def potential (z : Point) : ℝ :=
  Real.sqrt (z.1 ^ 2 + z.2 ^ 2)

def field (z : Point) : Point :=
  (z.1 / potential z, z.2 / potential z)

def HasCoordinateGradientAt
    (U : Point → ℝ) (V : Point) (z : Point) : Prop :=
  HasDerivAt (fun x => U (x, z.2)) V.1 z.1 ∧
    HasDerivAt (fun y => U (z.1, y)) V.2 z.2

def AdmissiblePath (γ : ℝ → Point) (start finish : Point) : Prop :=
  ContDiff ℝ 1 γ ∧ γ 0 = start ∧ γ 1 = finish ∧
    ∀ t, t ∈ Set.Icc (0 : ℝ) 1 → γ t ≠ (0, 0)

def lineIntegral (γ : ℝ → Point) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    (field (γ t)).1 * deriv (fun s => (γ s).1) t +
      (field (γ t)).2 * deriv (fun s => (γ s).2) t

def exactDifferentialIntegral (γ : ℝ → Point) : ℝ :=
  ∫ t in (0 : ℝ)..1, deriv (fun s => potential (γ s)) t

private theorem sumSqPos (z : Point) (hz : z ≠ (0, 0)) :
    0 < z.1 ^ 2 + z.2 ^ 2 := by
  have hx : 0 ≤ z.1 ^ 2 := sq_nonneg z.1
  have hy : 0 ≤ z.2 ^ 2 := sq_nonneg z.2
  by_contra h
  have hle : z.1 ^ 2 + z.2 ^ 2 ≤ 0 := le_of_not_gt h
  have hx0 : z.1 = 0 := by nlinarith
  have hy0 : z.2 = 0 := by nlinarith
  apply hz
  exact Prod.ext hx0 hy0

private theorem potentialPos (z : Point) (hz : z ≠ (0, 0)) :
    0 < potential z := by
  rw [potential]
  exact Real.sqrt_pos.2 (sumSqPos z hz)

private theorem pathPotentialHasDerivAt
    (γ : ℝ → Point) (t : ℝ) (hγ : ContDiff ℝ 1 γ)
    (ht : γ t ≠ (0, 0)) :
    HasDerivAt (fun s => potential (γ s))
      ((field (γ t)).1 * deriv (fun s => (γ s).1) t +
        (field (γ t)).2 * deriv (fun s => (γ s).2) t) t := by
  have hx : HasDerivAt (fun s => (γ s).1)
      (deriv (fun s => (γ s).1) t) t :=
    (hγ.fst.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hy : HasDerivAt (fun s => (γ s).2)
      (deriv (fun s => (γ s).2) t) t :=
    (hγ.snd.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hq : 0 < (γ t).1 ^ 2 + (γ t).2 ^ 2 := sumSqPos (γ t) ht
  have hrad : HasDerivAt
      (fun s => (γ s).1 ^ 2 + (γ s).2 ^ 2)
      (2 * (γ t).1 * deriv (fun s => (γ s).1) t +
        2 * (γ t).2 * deriv (fun s => (γ s).2) t) t := by
    simpa [pow_two] using (hx.pow 2).add (hy.pow 2)
  have hroot :=
    (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp t hrad
  have hsqrt : Real.sqrt ((γ t).1 ^ 2 + (γ t).2 ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq)
  have heq :
      (2 * Real.sqrt ((γ t).1 ^ 2 + (γ t).2 ^ 2))⁻¹ *
          (2 * (γ t).1 * deriv (fun s => (γ s).1) t +
            2 * (γ t).2 * deriv (fun s => (γ s).2) t) =
        (field (γ t)).1 * deriv (fun s => (γ s).1) t +
          (field (γ t)).2 * deriv (fun s => (γ s).2) t := by
    dsimp [field, potential]
    field_simp [hsqrt]
  rw [← heq]
  simpa [potential] using hroot

private theorem scalarDerivContinuousOfContDiffOne
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (fun t => deriv f t) := by
  have hsnd : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.2) :=
    (contDiff_id : ContDiff ℝ 1 (fun p : ℝ × ℝ => p)).snd
  have hfamily : ContDiff ℝ 1
      (Function.uncurry (fun (_ : ℝ) (s : ℝ) => f s)) := by
    simpa [Function.uncurry] using hf.comp hsnd
  have hid : ContDiff ℝ 0 (fun t : ℝ => t) := contDiff_id
  have hfd : ContDiff ℝ 0 (fun t : ℝ => fderiv ℝ f t) := by
    simpa using hfamily.fderiv hid (by norm_num)
  change Continuous (fun t : ℝ => (fderiv ℝ f t) 1)
  exact hfd.continuous.clm_apply continuous_const

theorem gap1 (z : Point) (hz : z ≠ (0, 0)) :
    HasCoordinateGradientAt potential (field z) z := by
  rw [HasCoordinateGradientAt]
  constructor
  · have hid : ContDiff ℝ 1 (fun x : ℝ => x) := contDiff_id
    have hc : ContDiff ℝ 1 (fun _ : ℝ => z.2) := contDiff_const
    have hcd : ContDiff ℝ 1 (fun x : ℝ => (x, z.2)) := hid.prodMk hc
    have hz' : (z.1, z.2) ≠ (0, 0) := by
      simpa using hz
    simpa using pathPotentialHasDerivAt
      (fun x : ℝ => (x, z.2)) z.1 hcd hz'
  · have hc : ContDiff ℝ 1 (fun _ : ℝ => z.1) := contDiff_const
    have hid : ContDiff ℝ 1 (fun y : ℝ => y) := contDiff_id
    have hcd : ContDiff ℝ 1 (fun y : ℝ => (z.1, y)) := hc.prodMk hid
    have hz' : (z.1, z.2) ≠ (0, 0) := by
      simpa using hz
    simpa using pathPotentialHasDerivAt
      (fun y : ℝ => (z.1, y)) z.2 hcd hz'

theorem gap2 (γ : ℝ → Point)
    (hγ : AdmissiblePath γ (1, 0) (6, 8)) :
    lineIntegral γ = exactDifferentialIntegral γ := by
  unfold lineIntegral exactDifferentialIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  exact (pathPotentialHasDerivAt γ t hγ.1 (hγ.2.2.2 t ht')).deriv.symm

theorem gap3 (γ : ℝ → Point)
    (hγ : AdmissiblePath γ (1, 0) (6, 8)) :
    exactDifferentialIntegral γ =
      potential (6, 8) - potential (1, 0) := by
  let D : ℝ → ℝ := fun t =>
    (field (γ t)).1 * deriv (fun s => (γ s).1) t +
      (field (γ t)).2 * deriv (fun s => (γ s).2) t
  have hpot : Continuous (fun t => potential (γ t)) := by
    simpa [potential] using
      Real.continuous_sqrt.comp
        ((hγ.1.fst.continuous.pow 2).add (hγ.1.snd.continuous.pow 2))
  have hpot_ne : ∀ t ∈ Set.Icc (0 : ℝ) 1, potential (γ t) ≠ 0 := by
    intro t ht
    exact ne_of_gt (potentialPos (γ t) (hγ.2.2.2 t ht))
  have hf1 : ContinuousOn (fun t => (field (γ t)).1) (Set.Icc (0 : ℝ) 1) := by
    simpa [field] using
      hγ.1.fst.continuous.continuousOn.div hpot.continuousOn hpot_ne
  have hf2 : ContinuousOn (fun t => (field (γ t)).2) (Set.Icc (0 : ℝ) 1) := by
    simpa [field] using
      hγ.1.snd.continuous.continuousOn.div hpot.continuousOn hpot_ne
  have hd1 : Continuous (fun t => deriv (fun s => (γ s).1) t) := by
    simpa using scalarDerivContinuousOfContDiffOne (hγ.1.fst)
  have hd2 : Continuous (fun t => deriv (fun s => (γ s).2) t) := by
    simpa using scalarDerivContinuousOfContDiffOne (hγ.1.snd)
  have hD : ContinuousOn D (Set.Icc (0 : ℝ) 1) := by
    dsimp [D]
    exact (hf1.mul hd1.continuousOn).add (hf2.mul hd2.continuousOn)
  have hDu : ContinuousOn D [[(0 : ℝ), 1]] := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hD
  have hDint : IntervalIntegrable D MeasureTheory.volume (0 : ℝ) 1 :=
    hDu.intervalIntegrable
  have hftc :
      (∫ t in (0 : ℝ)..1, D t) =
        potential (γ 1) - potential (γ 0) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := 1)
      (f := fun t => potential (γ t)) (f' := D) ?_ hDint
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    simpa [D] using
      pathPotentialHasDerivAt γ t hγ.1 (hγ.2.2.2 t ht')
  unfold exactDifferentialIntegral
  calc
    (∫ t in (0 : ℝ)..1, deriv (fun s => potential (γ s)) t) =
        ∫ t in (0 : ℝ)..1, D t := by
          apply intervalIntegral.integral_congr
          intro t ht
          have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
            simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
          simpa [D] using
            (pathPotentialHasDerivAt γ t hγ.1 (hγ.2.2.2 t ht')).deriv
    _ = potential (6, 8) - potential (1, 0) := by
      simpa [hγ.2.1, hγ.2.2.1] using hftc

theorem gap4 :
    potential (6, 8) - potential (1, 0) = 9 := by
  have hs : Real.sqrt (100 : ℝ) ^ 2 = 100 :=
    Real.sq_sqrt (by norm_num)
  have hn : 0 ≤ Real.sqrt (100 : ℝ) := Real.sqrt_nonneg _
  have h100 : Real.sqrt (100 : ℝ) = 10 := by
    nlinarith
  norm_num [potential, h100]

theorem gap5 (γ : ℝ → Point)
    (hγ : AdmissiblePath γ (1, 0) (6, 8)) :
    lineIntegral γ = 9 := by
  rw [gap2 γ hγ, gap3 γ hγ, gap4]

end

end ProofGap.Exercise4264
