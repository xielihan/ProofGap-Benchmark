import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ProofGap.Exercise4269

noncomputable section

open scoped Interval

abbrev Point := ℝ × ℝ

def field (z : Point) : Point :=
  (Real.exp z.1 * Real.cos z.2, -Real.exp z.1 * Real.sin z.2)

def potential (z : Point) : ℝ :=
  Real.exp z.1 * Real.cos z.2

def coordinateDifferential (V v : Point) : ℝ :=
  V.1 * v.1 + V.2 * v.2

def differential (U : Point → ℝ) (z v : Point) : ℝ :=
  deriv (fun x => U (x, z.2)) z.1 * v.1 +
    deriv (fun y => U (z.1, y)) z.2 * v.2

def AdmissiblePath (γ : ℝ → Point) (start finish : Point) : Prop :=
  ContDiff ℝ 1 γ ∧ γ 0 = start ∧ γ 1 = finish

def lineIntegral (γ : ℝ → Point) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    (field (γ t)).1 * deriv (fun s => (γ s).1) t +
      (field (γ t)).2 * deriv (fun s => (γ s).2) t

def exactDifferentialIntegral (γ : ℝ → Point) : ℝ :=
  ∫ t in (0 : ℝ)..1, deriv (fun s => potential (γ s)) t

theorem gap1 (z v : Point) :
    coordinateDifferential (field z) v = differential potential z v := by
  have hx :
      deriv (fun x : ℝ => Real.exp x * Real.cos z.2) z.1 =
        Real.exp z.1 * Real.cos z.2 :=
    ((Real.hasDerivAt_exp z.1).mul_const (Real.cos z.2)).deriv
  have hy :
      deriv (fun y : ℝ => Real.exp z.1 * Real.cos y) z.2 =
        -Real.exp z.1 * Real.sin z.2 := by
    convert ((Real.hasDerivAt_cos z.2).const_mul (Real.exp z.1)).deriv using 1 <;>
      ring
  unfold coordinateDifferential field differential potential
  rw [hx, hy]

theorem gap2 (a b : ℝ) (γ : ℝ → Point)
    (hγ : AdmissiblePath γ (0, 0) (a, b)) :
    lineIntegral γ = exactDifferentialIntegral γ := by
  have hγdiff : Differentiable ℝ γ :=
    hγ.1.differentiable (by simp)
  unfold lineIntegral exactDifferentialIntegral
  apply congrArg (fun f : ℝ → ℝ => ∫ t in (0 : ℝ)..1, f t)
  funext t
  have hx : HasDerivAt (fun s : ℝ => (γ s).1)
      (deriv (fun s : ℝ => (γ s).1) t) t :=
    (hγdiff t).fst.hasDerivAt
  have hy : HasDerivAt (fun s : ℝ => (γ s).2)
      (deriv (fun s : ℝ => (γ s).2) t) t :=
    (hγdiff t).snd.hasDerivAt
  have hp :=
    ((Real.hasDerivAt_exp (γ t).1).comp t hx).mul
      ((Real.hasDerivAt_cos (γ t).2).comp t hy)
  have hpotential : HasDerivAt (fun s : ℝ => potential (γ s))
      ((field (γ t)).1 * deriv (fun s : ℝ => (γ s).1) t +
        (field (γ t)).2 * deriv (fun s : ℝ => (γ s).2) t) t := by
    convert hp using 1 <;> simp [potential, field] <;> ring
  exact hpotential.deriv.symm

theorem gap3 (a b : ℝ) (γ : ℝ → Point)
    (hγ : AdmissiblePath γ (0, 0) (a, b)) :
    exactDifferentialIntegral γ = potential (a, b) - potential (0, 0) := by
  have hF : ContDiff ℝ 1 (fun t : ℝ => potential (γ t)) := by
    unfold potential
    exact
      (Real.contDiff_exp.comp hγ.1.fst).mul
        (Real.contDiff_cos.comp hγ.1.snd)
  unfold exactDifferentialIntegral
  calc
    (∫ t in (0 : ℝ)..1, deriv (fun s => potential (γ s)) t) =
        potential (γ 1) - potential (γ 0) := by
      exact intervalIntegral.integral_deriv_eq_sub
        (fun t _ => hF.differentiable (by simp) t)
        ((hF.continuous_deriv (by simp)).intervalIntegrable (0 : ℝ) 1)
    _ = potential (a, b) - potential (0, 0) := by
      rw [hγ.2.2, hγ.2.1]

theorem gap4 (a b : ℝ) :
    potential (a, b) - potential (0, 0) =
      Real.exp a * Real.cos b - 1 := by
  simp [potential]

theorem gap5 (a b : ℝ) (γ : ℝ → Point)
    (hγ : AdmissiblePath γ (0, 0) (a, b)) :
    lineIntegral γ = Real.exp a * Real.cos b - 1 := by
  calc
    lineIntegral γ = exactDifferentialIntegral γ := gap2 a b γ hγ
    _ = potential (a, b) - potential (0, 0) := gap3 a b γ hγ
    _ = Real.exp a * Real.cos b - 1 := gap4 a b

end

end ProofGap.Exercise4269
