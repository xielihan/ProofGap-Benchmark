import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.OrderClosed

namespace ProofGap.Exercise1127

noncomputable section

def d₂ (f : ℝ → ℝ) (x : ℝ) : ℝ := deriv (fun t => deriv f t) x
def d₃ (f : ℝ → ℝ) (x : ℝ) : ℝ := deriv (fun t => d₂ f t) x

def TwiceDifferentiableAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ ε > 0,
    DifferentiableOn ℝ f (Set.Ioo (x - ε) (x + ε)) ∧
      DifferentiableAt ℝ (fun t => deriv f t) x

def ThreeTimesDifferentiableAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ ε > 0,
    DifferentiableOn ℝ f (Set.Ioo (x - ε) (x + ε)) ∧
      DifferentiableOn ℝ (fun t => deriv f t) (Set.Ioo (x - ε) (x + ε)) ∧
      DifferentiableAt ℝ (fun t => d₂ f t) x

def y (f : ℝ → ℝ) (x : ℝ) : ℝ := f (Real.exp x)

private theorem secondDerivCompExp
    (f : ℝ → ℝ) (s : Set ℝ) (hs : IsOpen s)
    (hf : DifferentiableOn ℝ f s) (x : ℝ) (hx : Real.exp x ∈ s)
    (hdf : DifferentiableAt ℝ (fun t => deriv f t) (Real.exp x)) :
    d₂ (y f) x =
      Real.exp (2 * x) * d₂ f (Real.exp x) +
        Real.exp x * deriv f (Real.exp x) := by
  have hevent : ∀ᶠ t in nhds x, Real.exp t ∈ s :=
    (Real.hasDerivAt_exp x).continuousAt.eventually (hs.mem_nhds hx)
  have hderiv_eq :
      (fun t => deriv (y f) t) =ᶠ[nhds x]
        (fun t => Real.exp t * deriv f (Real.exp t)) := by
    filter_upwards [hevent] with t ht
    have hft : DifferentiableAt ℝ f (Real.exp t) :=
      (hf (Real.exp t) ht).differentiableAt (hs.mem_nhds ht)
    have hcomp := hft.hasDerivAt.comp t (Real.hasDerivAt_exp t)
    simpa [y, Function.comp_def, mul_comm] using hcomp.deriv
  have hcomp : HasDerivAt (fun t : ℝ => deriv f (Real.exp t))
      (d₂ f (Real.exp x) * Real.exp x) x := by
    simpa [d₂] using hdf.hasDerivAt.comp x (Real.hasDerivAt_exp x)
  have hprod : HasDerivAt
      (fun t : ℝ => Real.exp t * deriv f (Real.exp t))
      (Real.exp x * deriv f (Real.exp x) +
        Real.exp x * (d₂ f (Real.exp x) * Real.exp x)) x :=
    (Real.hasDerivAt_exp x).mul hcomp
  have he2 : Real.exp (2 * x) = Real.exp x * Real.exp x := by
    rw [show (2 : ℝ) * x = x + x by ring, Real.exp_add]
  change deriv (fun t => deriv (y f) t) x = _
  calc
    deriv (fun t => deriv (y f) t) x =
        deriv (fun t => Real.exp t * deriv f (Real.exp t)) x :=
      Filter.EventuallyEq.deriv_eq hderiv_eq
    _ = Real.exp x * deriv f (Real.exp x) +
        Real.exp x * (d₂ f (Real.exp x) * Real.exp x) := hprod.deriv
    _ = Real.exp (2 * x) * d₂ f (Real.exp x) +
        Real.exp x * deriv f (Real.exp x) := by
      rw [he2]
      ring

theorem gap1 (f : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f (Real.exp x)) :
    deriv (y f) x = Real.exp x * deriv f (Real.exp x) := by
  change deriv (fun t : ℝ => f (Real.exp t)) x = _
  simpa only [mul_comm] using
    (hf.hasDerivAt.comp x (Real.hasDerivAt_exp x)).deriv

theorem gap2 (f : ℝ → ℝ) (x : ℝ)
    (hf : TwiceDifferentiableAt f (Real.exp x)) :
    d₂ (y f) x =
      Real.exp (2 * x) * d₂ f (Real.exp x) +
        Real.exp x * deriv f (Real.exp x) := by
  rcases hf with ⟨ε, hε, hf, hdf⟩
  exact secondDerivCompExp f (Set.Ioo (Real.exp x - ε) (Real.exp x + ε))
    isOpen_Ioo hf x
    ⟨sub_lt_self _ hε, lt_add_of_pos_right _ hε⟩ hdf

theorem gap3 (f : ℝ → ℝ) (x : ℝ)
    (hf : ThreeTimesDifferentiableAt f (Real.exp x)) :
    d₃ (y f) x =
      Real.exp (3 * x) * d₃ f (Real.exp x) +
        3 * Real.exp (2 * x) * d₂ f (Real.exp x) +
        Real.exp x * deriv f (Real.exp x) := by
  rcases hf with ⟨ε, hε, hf₁, hf₂, hf₃⟩
  let s : Set ℝ := Set.Ioo (Real.exp x - ε) (Real.exp x + ε)
  have hz : Real.exp x ∈ s :=
    ⟨sub_lt_self _ hε, lt_add_of_pos_right _ hε⟩
  have hevent : ∀ᶠ t in nhds x, Real.exp t ∈ s :=
    (Real.hasDerivAt_exp x).continuousAt.eventually (isOpen_Ioo.mem_nhds hz)
  have hsecond_eq :
      (fun t => d₂ (y f) t) =ᶠ[nhds x]
        (fun t => Real.exp (2 * t) * d₂ f (Real.exp t) +
          Real.exp t * deriv f (Real.exp t)) := by
    filter_upwards [hevent] with t ht
    exact secondDerivCompExp f s isOpen_Ioo hf₁ t ht
      ((hf₂ (Real.exp t) ht).differentiableAt (isOpen_Ioo.mem_nhds ht))
  have hderiv : DifferentiableAt ℝ (fun t => deriv f t) (Real.exp x) :=
    (hf₂ _ hz).differentiableAt (isOpen_Ioo.mem_nhds hz)
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
    simpa using (hasDerivAt_id x).const_mul 2
  have hexp2 : HasDerivAt (fun t : ℝ => Real.exp (2 * t))
      (Real.exp (2 * x) * 2) x := by
    simpa using (Real.hasDerivAt_exp (2 * x)).comp x hlin
  have hd2comp : HasDerivAt (fun t : ℝ => d₂ f (Real.exp t))
      (d₃ f (Real.exp x) * Real.exp x) x := by
    simpa [d₃] using hf₃.hasDerivAt.comp x (Real.hasDerivAt_exp x)
  have hderivcomp : HasDerivAt (fun t : ℝ => deriv f (Real.exp t))
      (d₂ f (Real.exp x) * Real.exp x) x := by
    simpa [d₂] using hderiv.hasDerivAt.comp x (Real.hasDerivAt_exp x)
  have hfirst : HasDerivAt
      (fun t : ℝ => Real.exp (2 * t) * d₂ f (Real.exp t))
      ((Real.exp (2 * x) * 2) * d₂ f (Real.exp x) +
        Real.exp (2 * x) * (d₃ f (Real.exp x) * Real.exp x)) x :=
    hexp2.mul hd2comp
  have hsecond : HasDerivAt
      (fun t : ℝ => Real.exp t * deriv f (Real.exp t))
      (Real.exp x * deriv f (Real.exp x) +
        Real.exp x * (d₂ f (Real.exp x) * Real.exp x)) x :=
    (Real.hasDerivAt_exp x).mul hderivcomp
  have hsum : HasDerivAt
      (fun t : ℝ => Real.exp (2 * t) * d₂ f (Real.exp t) +
        Real.exp t * deriv f (Real.exp t))
      (((Real.exp (2 * x) * 2) * d₂ f (Real.exp x) +
          Real.exp (2 * x) * (d₃ f (Real.exp x) * Real.exp x)) +
        (Real.exp x * deriv f (Real.exp x) +
          Real.exp x * (d₂ f (Real.exp x) * Real.exp x))) x :=
    hfirst.add hsecond
  have he2 : Real.exp (2 * x) = Real.exp x * Real.exp x := by
    rw [show (2 : ℝ) * x = x + x by ring, Real.exp_add]
  have he3 : Real.exp (3 * x) = Real.exp (2 * x) * Real.exp x := by
    rw [show (3 : ℝ) * x = 2 * x + x by ring, Real.exp_add]
  change deriv (fun t => d₂ (y f) t) x = _
  calc
    deriv (fun t => d₂ (y f) t) x =
        deriv (fun t => Real.exp (2 * t) * d₂ f (Real.exp t) +
          Real.exp t * deriv f (Real.exp t)) x :=
      Filter.EventuallyEq.deriv_eq hsecond_eq
    _ = (((Real.exp (2 * x) * 2) * d₂ f (Real.exp x) +
          Real.exp (2 * x) * (d₃ f (Real.exp x) * Real.exp x)) +
        (Real.exp x * deriv f (Real.exp x) +
          Real.exp x * (d₂ f (Real.exp x) * Real.exp x))) := hsum.deriv
    _ = Real.exp (3 * x) * d₃ f (Real.exp x) +
          3 * Real.exp (2 * x) * d₂ f (Real.exp x) +
          Real.exp x * deriv f (Real.exp x) := by
      rw [he3, he2]
      ring

end

end ProofGap.Exercise1127
