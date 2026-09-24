import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.OrderClosed

namespace ProofGap.Exercise1137

noncomputable section

def y (a : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.rpow a (u x)

def secondDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (fun t => deriv f t) x

def TwiceDifferentiableAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ ε > 0,
    DifferentiableOn ℝ f (Set.Ioo (x - ε) (x + ε)) ∧
      DifferentiableAt ℝ (fun t => deriv f t) x

private theorem hasDerivAt_y (a : ℝ) (u : ℝ → ℝ) (x : ℝ) (ha : 0 < a)
    (hu : DifferentiableAt ℝ u x) :
    HasDerivAt (y a u)
      (Real.rpow a (u x) * Real.log a * deriv u x) x := by
  have h :=
    (Real.hasDerivAt_exp (Real.log a * u x)).comp x
      ((hasDerivAt_const x (Real.log a)).mul hu.hasDerivAt)
  have h' :
      HasDerivAt (fun t => Real.exp (Real.log a * u t))
        (Real.exp (Real.log a * u x) * (Real.log a * deriv u x)) x := by
    simpa only [Function.comp_def, zero_mul, zero_add] using h
  have heq :
      (fun t => Real.rpow a (u t)) =
        (fun t => Real.exp (Real.log a * u t)) := by
    funext t
    exact Real.rpow_def_of_pos ha (u t)
  have hr :
      HasDerivAt (fun t => Real.rpow a (u t))
        (Real.exp (Real.log a * u x) * (Real.log a * deriv u x)) x := by
    rw [heq]
    exact h'
  have hax : Real.rpow a (u x) = Real.exp (Real.log a * u x) :=
    Real.rpow_def_of_pos ha (u x)
  simpa only [y, hax, mul_assoc] using hr

theorem gap1 (a : ℝ) (u : ℝ → ℝ) (x : ℝ) (ha : 0 < a)
    (hu : DifferentiableAt ℝ u x) :
    deriv (y a u) x =
      Real.rpow a (u x) * Real.log a * deriv u x := by
  exact (hasDerivAt_y a u x ha hu).deriv

theorem gap2 (a : ℝ) (u : ℝ → ℝ) (x : ℝ) (ha : 0 < a)
    (hu : TwiceDifferentiableAt u x) :
    secondDeriv (y a u) x =
      Real.rpow a (u x) * Real.log a ^ 2 * deriv u x ^ 2 +
        Real.rpow a (u x) * Real.log a * secondDeriv u x := by
  rcases hu with ⟨ε, hε, huOn, hdu⟩
  have hxI : x ∈ Set.Ioo (x - ε) (x + ε) :=
    ⟨sub_lt_self x hε, lt_add_of_pos_right x hε⟩
  have hI : Set.Ioo (x - ε) (x + ε) ∈ nhds x :=
    isOpen_Ioo.mem_nhds hxI
  have huAt : DifferentiableAt ℝ u x :=
    (huOn x hxI).differentiableAt hI
  have hloc : ∀ᶠ t in nhds x, DifferentiableAt ℝ u t := by
    exact Filter.mem_of_superset hI (fun t ht =>
      (huOn t ht).differentiableAt (isOpen_Ioo.mem_nhds ht))
  have heq :
      (fun t => deriv (y a u) t) =ᶠ[nhds x]
        (fun t => y a u t * Real.log a * deriv u t) :=
    hloc.mono (fun t ht => (hasDerivAt_y a u t ha ht).deriv)
  have hg :
      HasDerivAt (fun t => y a u t * Real.log a * deriv u t)
        (Real.rpow a (u x) * Real.log a ^ 2 * deriv u x ^ 2 +
          Real.rpow a (u x) * Real.log a * secondDeriv u x) x := by
    convert
      (((hasDerivAt_y a u x ha huAt).mul_const (Real.log a)).mul
        hdu.hasDerivAt) using 1 <;>
      simp only [secondDeriv, y] <;> ring
  change deriv (fun t => deriv (y a u) t) x = _
  exact (hg.congr_of_eventuallyEq heq).deriv

theorem gap3 (a : ℝ) (u : ℝ → ℝ) (x : ℝ) :
    Real.rpow a (u x) * Real.log a ^ 2 * deriv u x ^ 2 +
        Real.rpow a (u x) * Real.log a * secondDeriv u x =
      Real.rpow a (u x) * Real.log a *
        (Real.log a * deriv u x ^ 2 + secondDeriv u x) := by
  ring

theorem gap4 (a : ℝ) (u : ℝ → ℝ) (x : ℝ) (ha : 0 < a)
    (hu : TwiceDifferentiableAt u x) :
    secondDeriv (y a u) x =
      Real.rpow a (u x) * Real.log a *
        (Real.log a * deriv u x ^ 2 + secondDeriv u x) := by
  calc
    secondDeriv (y a u) x =
        Real.rpow a (u x) * Real.log a ^ 2 * deriv u x ^ 2 +
          Real.rpow a (u x) * Real.log a * secondDeriv u x :=
      gap2 a u x ha hu
    _ = Real.rpow a (u x) * Real.log a *
          (Real.log a * deriv u x ^ 2 + secondDeriv u x) :=
      gap3 a u x

end

end ProofGap.Exercise1137
