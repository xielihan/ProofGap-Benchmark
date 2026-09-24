import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3438

noncomputable section

open scoped Interval

def d1 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv f x

def d2 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv f) x

def weight (p : ℝ → ℝ) (x₀ x : ℝ) : ℝ :=
  Real.exp (-(1 / 2 : ℝ) * ∫ ξ in x₀..x, p ξ)

private theorem _root_.ContDiff.deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (deriv f) := by
  exact ((contDiff_succ_iff_deriv (n := 1)).mp (by simpa using hf)).2.2

theorem gap1 (p u y : ℝ → ℝ) (x₀ : ℝ)
    (hRepresentation : ∀ x, y x = u x * weight p x₀ x)
    (hp : Continuous p)
    (hu : ContDiff ℝ 1 u) :
    ∀ x,
      d1 y x =
        d1 u x * weight p x₀ x -
          (1 / 2 : ℝ) * u x * p x * weight p x₀ x := by
  intro x
  have hpStrong :
      StronglyMeasurableAtFilter p (nhds x) MeasureTheory.volume :=
    hp.stronglyMeasurable.stronglyMeasurableAtFilter
  have hIntegral :
      HasDerivAt (fun z => ∫ ξ in x₀..z, p ξ) (p x) x :=
    intervalIntegral.integral_hasDerivAt_right
      (hp.intervalIntegrable x₀ x)
      hpStrong
      hp.continuousAt
  have hInner :
      HasDerivAt (fun z => -(1 / 2 : ℝ) * ∫ ξ in x₀..z, p ξ)
        (-(1 / 2 : ℝ) * p x) x := by
    convert ((hasDerivAt_const x (-(1 / 2 : ℝ))).mul hIntegral) using 1 <;> ring
  have hWeight :
      HasDerivAt (weight p x₀)
        (-(1 / 2 : ℝ) * p x * weight p x₀ x) x := by
    unfold weight
    convert (Real.hasDerivAt_exp _).comp x hInner using 1 <;> ring
  have huAt : HasDerivAt u (deriv u x) x :=
    ((hu.differentiable (by norm_num)).differentiableAt).hasDerivAt
  have hy : y = fun z => u z * weight p x₀ z := funext hRepresentation
  unfold d1
  rw [hy]
  convert (huAt.mul hWeight).deriv using 1 <;> ring

theorem gap2 (p u y : ℝ → ℝ) (x₀ : ℝ)
    (hRepresentation : ∀ x, y x = u x * weight p x₀ x)
    (hp : ContDiff ℝ 1 p)
    (hu : ContDiff ℝ 2 u) :
    ∀ x,
      d2 y x =
        d2 u x * weight p x₀ x -
          p x * d1 u x * weight p x₀ x +
          (1 / 4 : ℝ) * u x * (p x) ^ 2 * weight p x₀ x -
          (1 / 2 : ℝ) * u x * d1 p x * weight p x₀ x := by
  intro x
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hdu : ContDiff ℝ 1 (deriv u) := hu.deriv
  have hFirst := gap1 p u y x₀ hRepresentation hp.continuous hu1
  let v : ℝ → ℝ := fun z => d1 u z - (1 / 2 : ℝ) * u z * p z
  have hc : ContDiff ℝ 1 (fun _ : ℝ => (1 / 2 : ℝ)) := contDiff_const
  have hv : ContDiff ℝ 1 v := by
    dsimp [v, d1]
    exact hdu.sub ((hc.mul hu1).mul hp)
  have hvRepresentation :
      ∀ z, deriv y z = v z * weight p x₀ z := by
    intro z
    change d1 y z = v z * weight p x₀ z
    rw [hFirst z]
    dsimp [v]
    ring
  have hVFirst :=
    gap1 p v (deriv y) x₀ hvRepresentation hp.continuous hv
  have hduAt :
      HasDerivAt (deriv u) (deriv (deriv u) x) x :=
    ((hdu.differentiable (by norm_num)).differentiableAt).hasDerivAt
  have huAt : HasDerivAt u (deriv u x) x :=
    ((hu1.differentiable (by norm_num)).differentiableAt).hasDerivAt
  have hpAt : HasDerivAt p (deriv p x) x :=
    ((hp.differentiable (by norm_num)).differentiableAt).hasDerivAt
  have hvAt :
      HasDerivAt v
        (d2 u x - (1 / 2 : ℝ) *
          (d1 u x * p x + u x * d1 p x)) x := by
    dsimp [v, d1, d2]
    convert
      hduAt.sub
        (((hasDerivAt_const x (1 / 2 : ℝ)).mul huAt).mul hpAt) using 1 <;>
      simp only [Pi.mul_apply] <;> ring
  have hdv :
      d1 v x =
        d2 u x - (1 / 2 : ℝ) *
          (d1 u x * p x + u x * d1 p x) :=
    hvAt.deriv
  change d1 (deriv y) x = _
  rw [hVFirst x, hdv]
  dsimp [v]
  ring

theorem gap3 (p q u y : ℝ → ℝ) (x₀ : ℝ)
    (hODE :
      ∀ x, d2 y x + p x * d1 y x + q x * y x = 0)
    (hRepresentation : ∀ x, y x = u x * weight p x₀ x)
    (hFirst :
      ∀ x,
        d1 y x =
          d1 u x * weight p x₀ x -
            (1 / 2 : ℝ) * u x * p x * weight p x₀ x)
    (hSecond :
      ∀ x,
        d2 y x =
          d2 u x * weight p x₀ x -
            p x * d1 u x * weight p x₀ x +
            (1 / 4 : ℝ) * u x * (p x) ^ 2 * weight p x₀ x -
            (1 / 2 : ℝ) * u x * d1 p x * weight p x₀ x) :
    ∀ x,
      d2 u x +
          (q x - (1 / 4 : ℝ) * (p x) ^ 2 -
            (1 / 2 : ℝ) * d1 p x) * u x =
        0 := by
  intro x
  have hWeightNe : weight p x₀ x ≠ 0 := by
    unfold weight
    exact Real.exp_ne_zero _
  have hFactor :
      (d2 u x +
          (q x - (1 / 4 : ℝ) * (p x) ^ 2 -
            (1 / 2 : ℝ) * d1 p x) * u x) *
          weight p x₀ x = 0 := by
    calc
      (d2 u x +
            (q x - (1 / 4 : ℝ) * (p x) ^ 2 -
              (1 / 2 : ℝ) * d1 p x) * u x) *
          weight p x₀ x =
          d2 y x + p x * d1 y x + q x * y x := by
            rw [hSecond x, hFirst x, hRepresentation x]
            ring
      _ = 0 := hODE x
  exact (mul_eq_zero.mp hFactor).resolve_right hWeightNe

end

end ProofGap.Exercise3438
