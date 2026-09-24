import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1118

noncomputable section

def y (f : ℝ → ℝ) (x : ℝ) : ℝ := Real.log (f x)

def secondDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (fun t => deriv f t) x

def TwiceDifferentiableAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ ε > 0,
    DifferentiableOn ℝ f (Set.Ioo (x - ε) (x + ε)) ∧
      DifferentiableAt ℝ (fun t => deriv f t) x

theorem gap1 (f : ℝ → ℝ) (x : ℝ) (hf : DifferentiableAt ℝ f x)
    (hpos : 0 < f x) :
    deriv (y f) x = deriv f x / f x := by
  change deriv (fun t => Real.log (f t)) x = deriv f x / f x
  simpa [div_eq_mul_inv, mul_comm] using
    ((Real.hasDerivAt_log (ne_of_gt hpos)).comp x hf.hasDerivAt).deriv

theorem gap2 (f : ℝ → ℝ) (x : ℝ) (hf : TwiceDifferentiableAt f x)
    (hpos : 0 < f x) :
    secondDeriv (y f) x =
      (f x * secondDeriv f x - deriv f x ^ 2) / f x ^ 2 := by
  rcases hf with ⟨ε, hε, hfOn, hderiv⟩
  have hxmem : x ∈ Set.Ioo (x - ε) (x + ε) := by
    constructor
    · exact sub_lt_self x hε
    · exact lt_add_of_pos_right x hε
  have hfat : DifferentiableAt ℝ f x :=
    hfOn.differentiableAt (isOpen_Ioo.mem_nhds hxmem)
  have heq :
      (fun t => deriv (y f) t) =ᶠ[nhds x]
        (fun t => deriv f t / f t) := by
    filter_upwards
      [isOpen_Ioo.mem_nhds hxmem,
        hfat.continuousAt.eventually (isOpen_Ioi.mem_nhds hpos)] with t ht htpos
    exact gap1 f t
      (hfOn.differentiableAt (isOpen_Ioo.mem_nhds ht)) htpos
  unfold secondDeriv
  calc
    deriv (fun t => deriv (y f) t) x =
        deriv (fun t => deriv f t / f t) x := heq.deriv_eq
    _ = (deriv (fun t => deriv f t) x * f x -
          deriv f x * deriv f x) / f x ^ 2 := by
      exact (hderiv.hasDerivAt.div hfat.hasDerivAt (ne_of_gt hpos)).deriv
    _ = (f x * deriv (fun t => deriv f t) x - deriv f x ^ 2) /
          f x ^ 2 := by ring

end

end ProofGap.Exercise1118
