import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3381

noncomputable section

def curveEquation (x y : ℝ) : Prop :=
  x ^ 2 - x * y + 2 * y ^ 2 + x - y - 1 = 0

def secondDeriv (y : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv y) x

def thirdDeriv (y : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (fun t => secondDeriv y t) x

def IsC3BranchAtBasePoint (D : Set ℝ) (y : ℝ → ℝ) : Prop :=
  IsOpen D ∧ 0 ∈ D ∧ y 0 = 1 ∧
    DifferentiableOn ℝ y D ∧
      DifferentiableOn ℝ (deriv y) D ∧
        DifferentiableOn ℝ (secondDeriv y) D ∧
          (∀ x ∈ D, curveEquation x (y x)) ∧
            ∀ x ∈ D, -x + 4 * y x - 1 ≠ 0

private theorem exercise3381_local_derivative_eq_zero
    {D : Set ℝ} {f : ℝ → ℝ} {x f' : ℝ}
    (hD : IsOpen D) (hx : x ∈ D)
    (hf : ∀ z ∈ D, f z = 0)
    (hderiv : HasDerivAt f f' x) :
    f' = 0 := by
  have heq : f =ᶠ[nhds x] (fun _ : ℝ => 0) := by
    apply Filter.mem_of_superset (hD.mem_nhds hx)
    intro z hz
    exact hf z hz
  have hzero : HasDerivAt f 0 x :=
    (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq
  exact hderiv.unique hzero

theorem gap1 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC3BranchAtBasePoint D y) :
    ∀ x ∈ D,
      2 * x - y x - x * deriv y x +
        4 * y x * deriv y x + 1 - deriv y x = 0 := by
  intro x hx
  have hyx : HasDerivAt y (deriv y x) x :=
    ((h.2.2.2.1 x hx).differentiableAt
      (h.1.mem_nhds hx)).hasDerivAt
  have hcalc0 := (hasDerivAt_id x).mul (hasDerivAt_id x)
  have hcalc1 := hcalc0.sub ((hasDerivAt_id x).mul hyx)
  have hcalc2 := hcalc1.add ((hyx.mul hyx).const_mul 2)
  have hcalc3 := hcalc2.add (hasDerivAt_id x)
  have hcalc4 := hcalc3.sub hyx
  have hcalc5 := hcalc4.sub (hasDerivAt_const x (1 : ℝ))
  have hcalc : HasDerivAt
      (fun t : ℝ =>
        t ^ 2 - t * y t + 2 * (y t) ^ 2 + t - y t - 1)
      (2 * x - y x - x * deriv y x +
        4 * y x * deriv y x + 1 - deriv y x) x := by
    convert hcalc5 using 1
    · funext t
      simp [id]
      ring
    · simp [id]
      ring
  refine exercise3381_local_derivative_eq_zero h.1 hx ?_ hcalc
  intro t ht
  simpa [curveEquation] using h.2.2.2.2.2.2.1 t ht

theorem gap2 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC3BranchAtBasePoint D y) :
    deriv y 0 = 0 := by
  have hfirst := gap1 D y h 0 h.2.1
  rw [h.2.2.1] at hfirst
  linarith

theorem gap3 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC3BranchAtBasePoint D y) :
    ∀ x ∈ D,
      2 - deriv y x - deriv y x - x * secondDeriv y x +
        4 * (deriv y x) ^ 2 + 4 * y x * secondDeriv y x -
        secondDeriv y x = 0 := by
  intro x hx
  have hyx : HasDerivAt y (deriv y x) x :=
    ((h.2.2.2.1 x hx).differentiableAt
      (h.1.mem_nhds hx)).hasDerivAt
  have hdyx : HasDerivAt (deriv y) (secondDeriv y x) x := by
    simpa [secondDeriv] using
      (((h.2.2.2.2.1 x hx).differentiableAt
        (h.1.mem_nhds hx)).hasDerivAt)
  have hcalc0 := (hasDerivAt_id x).const_mul 2
  have hcalc1 := hcalc0.sub hyx
  have hcalc2 := hcalc1.sub ((hasDerivAt_id x).mul hdyx)
  have hcalc3 := hcalc2.add ((hyx.const_mul 4).mul hdyx)
  have hcalc4 := hcalc3.add (hasDerivAt_const x (1 : ℝ))
  have hcalc5 := hcalc4.sub hdyx
  have hcalc : HasDerivAt
      (fun t : ℝ =>
        2 * t - y t - t * deriv y t +
          4 * y t * deriv y t + 1 - deriv y t)
      (2 - deriv y x - deriv y x - x * secondDeriv y x +
        4 * (deriv y x) ^ 2 + 4 * y x * secondDeriv y x -
        secondDeriv y x) x := by
    convert hcalc5 using 1 <;> simp [id] <;> ring
  exact exercise3381_local_derivative_eq_zero h.1 hx (gap1 D y h) hcalc

theorem gap4 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC3BranchAtBasePoint D y) :
    secondDeriv y 0 = -(2 / 3) := by
  have hsecond := gap3 D y h 0 h.2.1
  rw [h.2.2.1, gap2 D y h] at hsecond
  linarith

theorem gap5 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC3BranchAtBasePoint D y) :
    ∀ x ∈ D,
      -3 * secondDeriv y x - x * thirdDeriv y x +
        12 * deriv y x * secondDeriv y x +
        4 * y x * thirdDeriv y x - thirdDeriv y x = 0 := by
  intro x hx
  have hyx : HasDerivAt y (deriv y x) x :=
    ((h.2.2.2.1 x hx).differentiableAt
      (h.1.mem_nhds hx)).hasDerivAt
  have hdyx : HasDerivAt (deriv y) (secondDeriv y x) x := by
    simpa [secondDeriv] using
      (((h.2.2.2.2.1 x hx).differentiableAt
        (h.1.mem_nhds hx)).hasDerivAt)
  have hsecondx : HasDerivAt (secondDeriv y) (thirdDeriv y x) x := by
    simpa [thirdDeriv] using
      (((h.2.2.2.2.2.1 x hx).differentiableAt
        (h.1.mem_nhds hx)).hasDerivAt)
  have hcalc0 := hasDerivAt_const x (2 : ℝ)
  have hcalc1 := hcalc0.sub hdyx
  have hcalc2 := hcalc1.sub hdyx
  have hcalc3 := hcalc2.sub ((hasDerivAt_id x).mul hsecondx)
  have hcalc4 := hcalc3.add ((hdyx.mul hdyx).const_mul 4)
  have hcalc5 := hcalc4.add ((hyx.const_mul 4).mul hsecondx)
  have hcalc6 := hcalc5.sub hsecondx
  have hcalc : HasDerivAt
      (fun t : ℝ =>
        2 - deriv y t - deriv y t - t * secondDeriv y t +
          4 * (deriv y t) ^ 2 + 4 * y t * secondDeriv y t -
          secondDeriv y t)
      (-3 * secondDeriv y x - x * thirdDeriv y x +
        12 * deriv y x * secondDeriv y x +
        4 * y x * thirdDeriv y x - thirdDeriv y x) x := by
    convert hcalc6 using 1
    · funext t
      simp [id]
      ring
    · simp [id]
      ring
  exact exercise3381_local_derivative_eq_zero h.1 hx (gap3 D y h) hcalc

theorem gap6 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC3BranchAtBasePoint D y) :
    thirdDeriv y 0 = -(2 / 3) := by
  have hthird := gap5 D y h 0 h.2.1
  rw [h.2.2.1, gap2 D y h, gap4 D y h] at hthird
  linarith

end

end ProofGap.Exercise3381
