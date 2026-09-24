import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3380

noncomputable section

def curveEquation (x y : ℝ) : Prop :=
  x ^ 2 + x * y + y ^ 2 = 3

def secondDeriv (y : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv y) x

def thirdDeriv (y : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (fun t => secondDeriv y t) x

def IsC3Branch (D : Set ℝ) (y : ℝ → ℝ) : Prop :=
  IsOpen D ∧ DifferentiableOn ℝ y D ∧
    DifferentiableOn ℝ (deriv y) D ∧
      DifferentiableOn ℝ (secondDeriv y) D ∧
        (∀ x ∈ D, curveEquation x (y x)) ∧
          ∀ x ∈ D, x + 2 * y x ≠ 0

theorem gap1 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC3Branch D y) :
    ∀ x ∈ D,
      2 * x + y x + x * deriv y x +
        2 * y x * deriv y x = 0 := by
  intro x hx
  have hy : HasDerivAt y (deriv y x) x :=
    ((h.2.1 x hx).differentiableAt (h.1.mem_nhds hx)).hasDerivAt
  have hcalc :
      HasDerivAt
        (fun t : ℝ => t ^ 2 + t * y t + y t ^ 2)
        (2 * x + y x + x * deriv y x + 2 * y x * deriv y x) x := by
    convert ((((hasDerivAt_id x).pow 2).add
      ((hasDerivAt_id x).mul hy)).add (hy.pow 2)) using 1 <;>
      simp [id] <;> ring
  have heq :
      (fun t : ℝ => t ^ 2 + t * y t + y t ^ 2) =ᶠ[nhds x]
        (fun _ : ℝ => (3 : ℝ)) := by
    filter_upwards [h.1.mem_nhds hx] with t ht
    simpa [curveEquation] using h.2.2.2.2.1 t ht
  rw [← hcalc.deriv, heq.deriv_eq]
  simpa using (hasDerivAt_const x (3 : ℝ)).deriv

theorem gap2 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC3Branch D y) :
    ∀ x ∈ D,
      deriv y x = -(2 * x + y x) / (x + 2 * y x) := by
  intro x hx
  have hn : x + 2 * y x ≠ 0 := h.2.2.2.2.2 x hx
  have hfirst := gap1 D y h x hx
  apply (eq_div_iff hn).2
  nlinarith

theorem gap3 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC3Branch D y) :
    ∀ x ∈ D,
      secondDeriv y x =
        -(((2 + deriv y x) * (x + 2 * y x) -
          (1 + 2 * deriv y x) * (2 * x + y x)) /
            (x + 2 * y x) ^ 2) := by
  intro x hx
  have hy : HasDerivAt y (deriv y x) x :=
    ((h.2.1 x hx).differentiableAt (h.1.mem_nhds hx)).hasDerivAt
  have hn : x + 2 * y x ≠ 0 := h.2.2.2.2.2 x hx
  have hnum :
      HasDerivAt (fun t : ℝ => 2 * t + y t) (2 + deriv y x) x := by
    convert ((hasDerivAt_id x).const_mul 2).add hy using 1 <;> ring
  have hden :
      HasDerivAt (fun t : ℝ => t + 2 * y t) (1 + 2 * deriv y x) x := by
    convert (hasDerivAt_id x).add (hy.const_mul 2) using 1 <;> ring
  have hquot :
      HasDerivAt
        (fun t : ℝ => -(2 * t + y t) / (t + 2 * y t))
        (((-(2 + deriv y x)) * (x + 2 * y x) -
          (-(2 * x + y x)) * (1 + 2 * deriv y x)) /
            (x + 2 * y x) ^ 2) x := by
    simpa only using hnum.neg.div hden hn
  have halg :
      ((-(2 + deriv y x)) * (x + 2 * y x) -
          (-(2 * x + y x)) * (1 + 2 * deriv y x)) /
            (x + 2 * y x) ^ 2 =
        -(((2 + deriv y x) * (x + 2 * y x) -
          (1 + 2 * deriv y x) * (2 * x + y x)) /
            (x + 2 * y x) ^ 2) := by
    ring
  have heq :
      deriv y =ᶠ[nhds x]
        (fun t : ℝ => -(2 * t + y t) / (t + 2 * y t)) := by
    filter_upwards [h.1.mem_nhds hx] with t ht
    simpa using gap2 D y h t ht
  calc
    secondDeriv y x = deriv (deriv y) x := rfl
    _ = deriv (fun t : ℝ => -(2 * t + y t) / (t + 2 * y t)) x :=
      heq.deriv_eq
    _ = ((-(2 + deriv y x)) * (x + 2 * y x) -
          (-(2 * x + y x)) * (1 + 2 * deriv y x)) /
            (x + 2 * y x) ^ 2 := hquot.deriv
    _ = -(((2 + deriv y x) * (x + 2 * y x) -
          (1 + 2 * deriv y x) * (2 * x + y x)) /
            (x + 2 * y x) ^ 2) := halg

theorem gap4 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC3Branch D y) :
    ∀ x ∈ D,
      -(((2 + deriv y x) * (x + 2 * y x) -
          (1 + 2 * deriv y x) * (2 * x + y x)) /
            (x + 2 * y x) ^ 2) =
        -(18 / (x + 2 * y x) ^ 3) := by
  intro x hx
  have hn : x + 2 * y x ≠ 0 := h.2.2.2.2.2 x hx
  have hc := h.2.2.2.2.1 x hx
  have hd := gap2 D y h x hx
  unfold curveEquation at hc
  rw [hd]
  field_simp [hn]
  nlinarith [hc]

theorem gap5 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC3Branch D y) :
    ∀ x ∈ D,
      secondDeriv y x = -(18 / (x + 2 * y x) ^ 3) := by
  intro x hx
  calc
    secondDeriv y x =
        -(((2 + deriv y x) * (x + 2 * y x) -
          (1 + 2 * deriv y x) * (2 * x + y x)) /
            (x + 2 * y x) ^ 2) := gap3 D y h x hx
    _ = -(18 / (x + 2 * y x) ^ 3) := gap4 D y h x hx

theorem gap6 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC3Branch D y) :
    ∀ x ∈ D,
      thirdDeriv y x =
        54 / (x + 2 * y x) ^ 4 * (1 + 2 * deriv y x) := by
  intro x hx
  have hy : HasDerivAt y (deriv y x) x :=
    ((h.2.1 x hx).differentiableAt (h.1.mem_nhds hx)).hasDerivAt
  have hn : x + 2 * y x ≠ 0 := h.2.2.2.2.2 x hx
  have hden :
      HasDerivAt (fun t : ℝ => t + 2 * y t) (1 + 2 * deriv y x) x := by
    convert (hasDerivAt_id x).add (hy.const_mul 2) using 1 <;> ring
  have hden3 :
      HasDerivAt
        (fun t : ℝ => (t + 2 * y t) ^ 3)
        (3 * (x + 2 * y x) ^ 2 * (1 + 2 * deriv y x)) x := by
    simpa using (hden.pow 3)
  have hrhs :
      HasDerivAt
        (fun t : ℝ => -(18 / (t + 2 * y t) ^ 3))
        (54 / (x + 2 * y x) ^ 4 * (1 + 2 * deriv y x)) x := by
    have hraw :=
      ((hasDerivAt_const x (18 : ℝ)).div hden3
        (pow_ne_zero 3 hn)).neg
    convert hraw using 1
    field_simp [hn]
    <;> ring
  have heq :
      secondDeriv y =ᶠ[nhds x]
        (fun t : ℝ => -(18 / (t + 2 * y t) ^ 3)) := by
    filter_upwards [h.1.mem_nhds hx] with t ht
    simpa using gap5 D y h t ht
  calc
    thirdDeriv y x = deriv (secondDeriv y) x := rfl
    _ = deriv (fun t : ℝ => -(18 / (t + 2 * y t) ^ 3)) x :=
      heq.deriv_eq
    _ = 54 / (x + 2 * y x) ^ 4 * (1 + 2 * deriv y x) :=
      hrhs.deriv

theorem gap7 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC3Branch D y) :
    ∀ x ∈ D,
      54 / (x + 2 * y x) ^ 4 * (1 + 2 * deriv y x) =
        -(162 * x / (x + 2 * y x) ^ 5) := by
  intro x hx
  have hn : x + 2 * y x ≠ 0 := h.2.2.2.2.2 x hx
  have hd := gap2 D y h x hx
  rw [hd]
  field_simp [hn]
  ring

theorem gap8 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC3Branch D y) :
    ∀ x ∈ D,
      thirdDeriv y x = -(162 * x / (x + 2 * y x) ^ 5) := by
  intro x hx
  calc
    thirdDeriv y x =
        54 / (x + 2 * y x) ^ 4 * (1 + 2 * deriv y x) :=
      gap6 D y h x hx
    _ = -(162 * x / (x + 2 * y x) ^ 5) := gap7 D y h x hx

end

end ProofGap.Exercise3380
