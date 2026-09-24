import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3376

noncomputable section

def curveEquation (k x y : ℝ) : Prop :=
  1 + x * y = k * (x - y)

def IsCurveParam (k : ℝ) (D : Set ℝ) (x y : ℝ → ℝ) : Prop :=
  IsOpen D ∧ DifferentiableOn ℝ x D ∧
    DifferentiableOn ℝ y D ∧
      ∀ t ∈ D, curveEquation k (x t) (y t)

theorem gap1 (k : ℝ) (D : Set ℝ) (x y : ℝ → ℝ)
    (h : IsCurveParam k D x y) :
    ∀ t ∈ D,
      x t * deriv y t + y t * deriv x t =
        k * (deriv x t - deriv y t) := by
  intro t ht
  rcases h with ⟨hD, hxD, hyD, hcurve⟩
  have hx : HasDerivAt x (deriv x t) t :=
    (hxD.differentiableAt (hD.mem_nhds ht)).hasDerivAt
  have hy : HasDerivAt y (deriv y t) t :=
    (hyD.differentiableAt (hD.mem_nhds ht)).hasDerivAt
  have heq :
      (fun s => 1 + x s * y s) =ᶠ[nhds t]
        (fun s => k * (x s - y s)) := by
    filter_upwards [hD.mem_nhds ht] with s hs
    simpa [curveEquation] using hcurve s hs
  have hl :
      HasDerivAt (fun s => 1 + x s * y s)
        (x t * deriv y t + y t * deriv x t) t := by
    convert (hasDerivAt_const (x := t) (1 : ℝ)).add (hx.mul hy) using 1 <;> ring
  have hr :
      HasDerivAt (fun s => k * (x s - y s))
        (k * (deriv x t - deriv y t)) t := by
    convert (hasDerivAt_const (x := t) k).mul (hx.sub hy) using 1 <;> ring
  exact (hl.congr_of_eventuallyEq heq.symm).unique hr

theorem gap2 (k : ℝ) (D : Set ℝ) (x y : ℝ → ℝ)
    (h : IsCurveParam k D x y) :
    ∀ t ∈ D,
      (x t - y t) * (x t * deriv y t + y t * deriv x t) =
        (k * (x t - y t)) * (deriv x t - deriv y t) := by
  intro t ht
  rw [gap1 k D x y h t ht]
  ring

theorem gap3 (k : ℝ) (D : Set ℝ) (x y : ℝ → ℝ)
    (h : IsCurveParam k D x y) :
    ∀ t ∈ D,
      (k * (x t - y t)) * (deriv x t - deriv y t) =
        (1 + x t * y t) * (deriv x t - deriv y t) := by
  intro t ht
  have hc : 1 + x t * y t = k * (x t - y t) := by
    simpa [curveEquation] using h.2.2.2 t ht
  rw [← hc]

theorem gap4 (k : ℝ) (D : Set ℝ) (x y : ℝ → ℝ)
    (h : IsCurveParam k D x y) :
    ∀ t ∈ D,
      (x t - y t) * (x t * deriv y t + y t * deriv x t) =
        (1 + x t * y t) * (deriv x t - deriv y t) := by
  intro t ht
  calc
    (x t - y t) * (x t * deriv y t + y t * deriv x t) =
        (k * (x t - y t)) * (deriv x t - deriv y t) :=
      gap2 k D x y h t ht
    _ = (1 + x t * y t) * (deriv x t - deriv y t) :=
      gap3 k D x y h t ht

theorem gap5 (k : ℝ) (D : Set ℝ) (x y : ℝ → ℝ)
    (h : IsCurveParam k D x y) :
    ∀ t ∈ D,
      deriv x t / (1 + (x t) ^ 2) =
        deriv y t / (1 + (y t) ^ 2) := by
  intro t ht
  have hrel := gap4 k D x y h t ht
  have hcross :
      deriv x t * (1 + (y t) ^ 2) =
        deriv y t * (1 + (x t) ^ 2) := by
    nlinarith only [hrel]
  have hxne : 1 + (x t) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (x t)]
  have hyne : 1 + (y t) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (y t)]
  exact (div_eq_div_iff hxne hyne).2 hcross

theorem gap6 (k : ℝ) (D : Set ℝ) (x y : ℝ → ℝ)
    (h : IsCurveParam k D x y) :
    ∀ t ∈ D,
      deriv x t / (1 + (x t) ^ 2) =
        deriv y t / (1 + (y t) ^ 2) := by
  exact gap5 k D x y h

end

end ProofGap.Exercise3376
