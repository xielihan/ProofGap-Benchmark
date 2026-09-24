import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1121

noncomputable section

def y (u : ℝ → ℝ) (x : ℝ) : ℝ := u x ^ 2

def secondDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (fun t => deriv f t) x

def TwiceDifferentiableAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ ε > 0,
    DifferentiableOn ℝ f (Set.Ioo (x - ε) (x + ε)) ∧
      DifferentiableAt ℝ (fun t => deriv f t) x

private theorem Set.isOpen_Ioo {a b : ℝ} : IsOpen (_root_.Set.Ioo a b) := by
  exact _root_.isOpen_Ioo

theorem gap1 (u : ℝ → ℝ) (x : ℝ) (hu : DifferentiableAt ℝ u x) :
    deriv (y u) x = 2 * u x * deriv u x := by
  have hy : y u = fun t => u t * u t := by
    funext t
    unfold y
    exact pow_two (u t)
  rw [hy]
  calc
    deriv (fun t => u t * u t) x =
        deriv u x * u x + u x * deriv u x :=
      (hu.hasDerivAt.mul hu.hasDerivAt).deriv
    _ = 2 * u x * deriv u x := by ring

theorem gap2 (u : ℝ → ℝ) (x : ℝ) (hu : TwiceDifferentiableAt u x) :
    secondDeriv (y u) x =
      2 * deriv u x ^ 2 + 2 * u x * secondDeriv u x := by
  rcases hu with ⟨ε, hε, hu_on, hdu⟩
  have hx : x ∈ Set.Ioo (x - ε) (x + ε) := by
    exact ⟨sub_lt_self x hε, lt_add_of_pos_right x hε⟩
  have hu_x : DifferentiableAt ℝ u x :=
    hu_on.differentiableAt (Set.isOpen_Ioo.mem_nhds hx)
  have hformula :
      (fun t => deriv (y u) t) =ᶠ[nhds x]
        (fun t => 2 * u t * deriv u t) := by
    filter_upwards [Set.isOpen_Ioo.mem_nhds hx] with t ht
    exact gap1 u t (hu_on.differentiableAt (Set.isOpen_Ioo.mem_nhds ht))
  calc
    secondDeriv (y u) x =
        deriv (fun t => 2 * u t * deriv u t) x := by
      unfold secondDeriv
      exact hformula.deriv_eq
    _ = 2 * deriv u x ^ 2 + 2 * u x * secondDeriv u x := by
      convert ((hu_x.hasDerivAt.const_mul 2).mul hdu.hasDerivAt).deriv using 1 <;>
        simp [secondDeriv, pow_two] <;> ring

theorem gap3 (u : ℝ → ℝ) (x : ℝ) :
    2 * deriv u x ^ 2 + 2 * u x * secondDeriv u x =
      2 * (deriv u x ^ 2 + u x * secondDeriv u x) := by
  ring

theorem gap4 (u : ℝ → ℝ) (x : ℝ) (hu : TwiceDifferentiableAt u x) :
    secondDeriv (y u) x =
      2 * (deriv u x ^ 2 + u x * secondDeriv u x) := by
  exact (gap2 u x hu).trans (gap3 u x)

end

end ProofGap.Exercise1121
