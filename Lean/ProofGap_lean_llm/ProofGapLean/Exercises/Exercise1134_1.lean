import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1134_1

noncomputable section

def y (u v : ℝ → ℝ) (x : ℝ) : ℝ := u x * v x
def secondDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (fun t => deriv f t) x

def TwiceDifferentiableAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ ε > 0,
    DifferentiableOn ℝ f (Set.Ioo (x - ε) (x + ε)) ∧
      DifferentiableAt ℝ (fun t => deriv f t) x

theorem gap1 (u v : ℝ → ℝ) (x : ℝ)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    deriv (y u v) x = u x * deriv v x + v x * deriv u x := by
  simpa [y, add_comm, mul_comm] using
    (hu.hasDerivAt.mul hv.hasDerivAt).deriv

theorem gap2 (u v : ℝ → ℝ) (x : ℝ)
    (hu : TwiceDifferentiableAt u x) (hv : TwiceDifferentiableAt v x) :
    secondDeriv (y u v) x =
      deriv u x * deriv v x + u x * secondDeriv v x +
        deriv v x * deriv u x + v x * secondDeriv u x := by
  rcases hu with ⟨εu, hεu, huOn, hu'⟩
  rcases hv with ⟨εv, hεv, hvOn, hv'⟩
  have hxu : x ∈ Set.Ioo (x - εu) (x + εu) := by
    exact ⟨sub_lt_self x hεu, lt_add_of_pos_right x hεu⟩
  have hxv : x ∈ Set.Ioo (x - εv) (x + εv) := by
    exact ⟨sub_lt_self x hεv, lt_add_of_pos_right x hεv⟩
  have hu0 : DifferentiableAt ℝ u x :=
    huOn.differentiableAt (Ioo_mem_nhds hxu.1 hxu.2)
  have hv0 : DifferentiableAt ℝ v x :=
    hvOn.differentiableAt (Ioo_mem_nhds hxv.1 hxv.2)
  have hderiv :
      (fun t => deriv (y u v) t) =ᶠ[nhds x]
        (fun t => u t * deriv v t + v t * deriv u t) := by
    filter_upwards [Ioo_mem_nhds hxu.1 hxu.2,
      Ioo_mem_nhds hxv.1 hxv.2] with t htu htv
    exact gap1 u v t
      (huOn.differentiableAt (Ioo_mem_nhds htu.1 htu.2))
      (hvOn.differentiableAt (Ioo_mem_nhds htv.1 htv.2))
  have hu2 :
      HasDerivAt (fun t => deriv u t) (secondDeriv u x) x := by
    simpa [secondDeriv] using hu'.hasDerivAt
  have hv2 :
      HasDerivAt (fun t => deriv v t) (secondDeriv v x) x := by
    simpa [secondDeriv] using hv'.hasDerivAt
  have hprod1 :
      HasDerivAt (fun t => u t * deriv v t)
        (deriv u x * deriv v x + u x * secondDeriv v x) x := by
    exact hu0.hasDerivAt.mul hv2
  have hprod2 :
      HasDerivAt (fun t => v t * deriv u t)
        (deriv v x * deriv u x + v x * secondDeriv u x) x := by
    exact hv0.hasDerivAt.mul hu2
  have hsum :
      HasDerivAt (fun t => u t * deriv v t + v t * deriv u t)
        ((deriv u x * deriv v x + u x * secondDeriv v x) +
          (deriv v x * deriv u x + v x * secondDeriv u x)) x := by
    exact hprod1.add hprod2
  have hcalc :
      deriv (fun t => u t * deriv v t + v t * deriv u t) x =
        (deriv u x * deriv v x + u x * secondDeriv v x) +
          (deriv v x * deriv u x + v x * secondDeriv u x) :=
    hsum.deriv
  calc
    secondDeriv (y u v) x =
        deriv (fun t => u t * deriv v t + v t * deriv u t) x := by
      unfold secondDeriv
      exact hderiv.deriv_eq
    _ = deriv u x * deriv v x + u x * secondDeriv v x +
          deriv v x * deriv u x + v x * secondDeriv u x := by
      simpa [add_assoc] using hcalc

theorem gap3 (u v : ℝ → ℝ) (x : ℝ) :
    deriv u x * deriv v x + u x * secondDeriv v x +
        deriv v x * deriv u x + v x * secondDeriv u x =
      u x * secondDeriv v x + 2 * deriv u x * deriv v x +
        v x * secondDeriv u x := by
  ring

theorem gap4 (u v : ℝ → ℝ) (x : ℝ)
    (hu : TwiceDifferentiableAt u x) (hv : TwiceDifferentiableAt v x) :
    secondDeriv (y u v) x =
      u x * secondDeriv v x + 2 * deriv u x * deriv v x +
        v x * secondDeriv u x := by
  calc
    secondDeriv (y u v) x =
        deriv u x * deriv v x + u x * secondDeriv v x +
          deriv v x * deriv u x + v x * secondDeriv u x :=
      gap2 u v x hu hv
    _ = u x * secondDeriv v x + 2 * deriv u x * deriv v x +
          v x * secondDeriv u x :=
      gap3 u v x

end

end ProofGap.Exercise1134_1
