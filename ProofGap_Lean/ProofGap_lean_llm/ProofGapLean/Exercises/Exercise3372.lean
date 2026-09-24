import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3372

noncomputable section

def implicitEquation (y : ℝ → ℝ) (x : ℝ) : Prop :=
  Real.log (Real.sqrt (x ^ 2 + y x ^ 2)) =
    Real.arctan (y x / x)

def secondDeriv (y : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv y) x

def IsC2Branch (D : Set ℝ) (y : ℝ → ℝ) : Prop :=
  IsOpen D ∧ DifferentiableOn ℝ y D ∧
    DifferentiableOn ℝ (deriv y) D ∧
      (∀ x ∈ D, implicitEquation y x) ∧
        ∀ x ∈ D, x ≠ 0 ∧ x - y x ≠ 0

theorem gap1 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch D y) :
    ∀ x ∈ D,
      (x + y x * deriv y x) / (x ^ 2 + y x ^ 2) =
        (x * deriv y x - y x) / (x ^ 2 + y x ^ 2) := by
  intro x hx
  have hx0 : x ≠ 0 := (h.2.2.2.2 x hx).1
  have hyAt : DifferentiableAt ℝ y x :=
    (h.2.1 x hx).differentiableAt (h.1.mem_nhds hx)
  have hy' : HasDerivAt y (deriv y x) x := hyAt.hasDerivAt
  have hpos : 0 < x ^ 2 + y x ^ 2 := by
    nlinarith [sq_pos_of_ne_zero hx0, sq_nonneg (y x)]
  have hu' :
      HasDerivAt (fun t : ℝ => t ^ 2 + y t ^ 2)
        (2 * x + 2 * y x * deriv y x) x := by
    convert ((hasDerivAt_id x).pow 2).add (hy'.pow 2) using 1
    simp only [id_eq]
    ring
  have hspos : 0 < Real.sqrt (x ^ 2 + y x ^ 2) := Real.sqrt_pos.2 hpos
  have hleft :
      HasDerivAt
        (fun t : ℝ => Real.log (Real.sqrt (t ^ 2 + y t ^ 2)))
        ((x + y x * deriv y x) / (x ^ 2 + y x ^ 2)) x := by
    convert
      (Real.hasDerivAt_log hspos.ne').comp x
        ((Real.hasDerivAt_sqrt hpos.ne').comp x hu') using 1
    field_simp [hspos.ne']
    rw [Real.sq_sqrt hpos.le]
  have hdiv :
      HasDerivAt (fun t : ℝ => y t / t)
        ((x * deriv y x - y x) / x ^ 2) x := by
    convert hy'.div (hasDerivAt_id x) hx0 using 1
    simp only [id_eq]
    ring
  let u : ℝ → ℝ := fun t => y t / t
  have hu :
      HasDerivAt u ((x * deriv y x - y x) / x ^ 2) x := by
    simpa [u] using hdiv
  have hcomp :
      HasDerivAt
        (Real.arctan ∘ u)
        (1 / (1 + (u x) ^ 2) *
          ((x * deriv y x - y x) / x ^ 2)) x :=
    (Real.hasDerivAt_arctan (u x)).comp x hu
  have hone : 1 + (y x / x) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (y x / x)]
  have hcoef :
      1 / (1 + (y x / x) ^ 2) *
          ((x * deriv y x - y x) / x ^ 2) =
        (x * deriv y x - y x) / (x ^ 2 + y x ^ 2) := by
    field_simp [hx0, hpos.ne', hone] <;> ring
  have hright :
      HasDerivAt
        (fun t : ℝ => Real.arctan (y t / t))
        ((x * deriv y x - y x) / (x ^ 2 + y x ^ 2)) x := by
    simpa only [Function.comp_apply, u, hcoef] using hcomp
  have hevent :
      (fun t : ℝ => Real.log (Real.sqrt (t ^ 2 + y t ^ 2))) =ᶠ[nhds x]
        (fun t : ℝ => Real.arctan (y t / t)) := by
    filter_upwards [h.1.mem_nhds hx] with z hz
    simpa [implicitEquation] using h.2.2.2.1 z hz
  calc
    (x + y x * deriv y x) / (x ^ 2 + y x ^ 2) =
        deriv (fun t : ℝ => Real.log (Real.sqrt (t ^ 2 + y t ^ 2))) x :=
      hleft.deriv.symm
    _ = deriv (fun t : ℝ => Real.arctan (y t / t)) x := hevent.deriv_eq
    _ = (x * deriv y x - y x) / (x ^ 2 + y x ^ 2) := hright.deriv

theorem gap2 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch D y) :
    ∀ x ∈ D, deriv y x = (x + y x) / (x - y x) := by
  intro x hx
  have hx0 : x ≠ 0 := (h.2.2.2.2 x hx).1
  have hxy : x - y x ≠ 0 := (h.2.2.2.2 x hx).2
  have hden : x ^ 2 + y x ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hx0, sq_nonneg (y x)]
  have hi := gap1 D y h x hx
  field_simp [hden] at hi
  apply (eq_div_iff hxy).2
  nlinarith [hi]

theorem gap3 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch D y) :
    ∀ x ∈ D,
      secondDeriv y x =
        ((x - y x) * (1 + deriv y x) -
          (x + y x) * (1 - deriv y x)) / (x - y x) ^ 2 := by
  intro x hx
  have hxy : x - y x ≠ 0 := (h.2.2.2.2 x hx).2
  have hyAt : DifferentiableAt ℝ y x :=
    (h.2.1 x hx).differentiableAt (h.1.mem_nhds hx)
  have hy' : HasDerivAt y (deriv y x) x := hyAt.hasDerivAt
  have hquot :
      HasDerivAt (fun t : ℝ => (t + y t) / (t - y t))
        (((x - y x) * (1 + deriv y x) -
            (x + y x) * (1 - deriv y x)) / (x - y x) ^ 2) x := by
    convert
      ((hasDerivAt_id x).add hy').div
        ((hasDerivAt_id x).sub hy') hxy using 1 <;>
      simp only [Pi.add_apply, Pi.sub_apply, id_eq] <;>
      field_simp [hxy] <;>
      ring
  have hevent :
      deriv y =ᶠ[nhds x] (fun t : ℝ => (t + y t) / (t - y t)) := by
    filter_upwards [h.1.mem_nhds hx] with z hz
    exact gap2 D y h z hz
  calc
    secondDeriv y x = deriv (deriv y) x := rfl
    _ = deriv (fun t : ℝ => (t + y t) / (t - y t)) x := hevent.deriv_eq
    _ = ((x - y x) * (1 + deriv y x) -
          (x + y x) * (1 - deriv y x)) / (x - y x) ^ 2 := hquot.deriv

theorem gap4 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch D y) :
    ∀ x ∈ D,
      ((x - y x) * (1 + deriv y x) -
          (x + y x) * (1 - deriv y x)) / (x - y x) ^ 2 =
        2 * (x * deriv y x - y x) / (x - y x) ^ 2 := by
  intro x hx
  ring

theorem gap5 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch D y) :
    ∀ x ∈ D,
      2 * (x * deriv y x - y x) / (x - y x) ^ 2 =
        (2 * x * (x + y x) - 2 * y x * (x - y x)) /
          (x - y x) ^ 3 := by
  intro x hx
  have hxy : x - y x ≠ 0 := (h.2.2.2.2 x hx).2
  rw [gap2 D y h x hx]
  field_simp [hxy] <;> ring

theorem gap6 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch D y) :
    ∀ x ∈ D,
      (2 * x * (x + y x) - 2 * y x * (x - y x)) /
          (x - y x) ^ 3 =
        2 * (x ^ 2 + y x ^ 2) / (x - y x) ^ 3 := by
  intro x hx
  ring

theorem gap7 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch D y) :
    ∀ x ∈ D,
      secondDeriv y x =
        2 * (x ^ 2 + y x ^ 2) / (x - y x) ^ 3 := by
  intro x hx
  calc
    secondDeriv y x =
        ((x - y x) * (1 + deriv y x) -
          (x + y x) * (1 - deriv y x)) / (x - y x) ^ 2 :=
      gap3 D y h x hx
    _ = 2 * (x * deriv y x - y x) / (x - y x) ^ 2 :=
      gap4 D y h x hx
    _ = (2 * x * (x + y x) - 2 * y x * (x - y x)) /
          (x - y x) ^ 3 := gap5 D y h x hx
    _ = 2 * (x ^ 2 + y x ^ 2) / (x - y x) ^ 3 :=
      gap6 D y h x hx

theorem gap8 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch D y) :
    ∀ x ∈ D,
      (x + y x * deriv y x) / (x ^ 2 + y x ^ 2) =
        (x * deriv y x - y x) / (x ^ 2 + y x ^ 2) := by
  exact gap1 D y h

theorem gap9 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch D y) :
    ∀ x ∈ D, deriv y x = (x + y x) / (x - y x) := by
  exact gap2 D y h

theorem gap10 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch D y) :
    ∀ x ∈ D,
      1 + (deriv y x) ^ 2 + y x * secondDeriv y x =
        x * secondDeriv y x := by
  intro x hx
  have hxy : x - y x ≠ 0 := (h.2.2.2.2 x hx).2
  rw [gap2 D y h x hx, gap7 D y h x hx]
  field_simp [hxy] <;> ring

theorem gap11 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch D y) :
    ∀ x ∈ D,
      secondDeriv y x =
        (1 + (deriv y x) ^ 2) / (x - y x) := by
  intro x hx
  have hxy : x - y x ≠ 0 := (h.2.2.2.2 x hx).2
  have hi := gap10 D y h x hx
  apply (eq_div_iff hxy).2
  nlinarith [hi]

theorem gap12 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch D y) :
    ∀ x ∈ D,
      (1 + (deriv y x) ^ 2) / (x - y x) =
        ((x - y x) ^ 2 + (x + y x) ^ 2) / (x - y x) ^ 3 := by
  intro x hx
  have hxy : x - y x ≠ 0 := (h.2.2.2.2 x hx).2
  rw [gap2 D y h x hx]
  field_simp [hxy] <;> ring

theorem gap13 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch D y) :
    ∀ x ∈ D,
      ((x - y x) ^ 2 + (x + y x) ^ 2) / (x - y x) ^ 3 =
        2 * (x ^ 2 + y x ^ 2) / (x - y x) ^ 3 := by
  intro x hx
  ring

theorem gap14 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch D y) :
    ∀ x ∈ D,
      secondDeriv y x =
        2 * (x ^ 2 + y x ^ 2) / (x - y x) ^ 3 := by
  exact gap7 D y h

end

end ProofGap.Exercise3372
