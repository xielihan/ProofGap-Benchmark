import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3371

noncomputable section

def curveEquation (a x y : ℝ) : Prop :=
  x ^ 2 + 2 * x * y - y ^ 2 = a ^ 2

def secondDeriv (y : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv y) x

def IsC2Branch (a : ℝ) (D : Set ℝ) (y : ℝ → ℝ) : Prop :=
  IsOpen D ∧ DifferentiableOn ℝ y D ∧
    DifferentiableOn ℝ (deriv y) D ∧
      (∀ x ∈ D, curveEquation a x (y x)) ∧
        ∀ x ∈ D, y x ≠ x

theorem gap1 (a : ℝ) (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch a D y) :
    ∀ x ∈ D,
      2 * x + 2 * y x + 2 * x * deriv y x -
        2 * y x * deriv y x = 0 := by
  intro x hx
  rcases h with ⟨hD, hy, hdy, hcurve, hne⟩
  have hyx : DifferentiableAt ℝ y x :=
    (hy x hx).differentiableAt (hD.mem_nhds hx)
  have hpoly :
      HasDerivAt
        (fun t : ℝ => t ^ 2 + 2 * t * y t - y t ^ 2)
        (2 * x + 2 * y x + 2 * x * deriv y x -
          2 * y x * deriv y x) x := by
    convert
      ((((hasDerivAt_id x).mul (hasDerivAt_id x)).add
        (((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x)).mul
          hyx.hasDerivAt)).sub
        (hyx.hasDerivAt.mul hyx.hasDerivAt)) using 1 <;>
      (try funext t) <;> simp [id_eq] <;> ring
  have hevent :
      (fun t : ℝ => t ^ 2 + 2 * t * y t - y t ^ 2) =ᶠ[nhds x]
        (fun _ : ℝ => a ^ 2) := by
    filter_upwards [hD.mem_nhds hx] with z hz
    simpa [curveEquation] using hcurve z hz
  have hsame :
      HasDerivAt (fun _ : ℝ => a ^ 2)
        (2 * x + 2 * y x + 2 * x * deriv y x -
          2 * y x * deriv y x) x :=
    hpoly.congr_of_eventuallyEq hevent.symm
  exact hsame.unique (hasDerivAt_const x (a ^ 2))

theorem gap2 (a : ℝ) (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch a D y) :
    ∀ x ∈ D, deriv y x = (y x + x) / (y x - x) := by
  intro x hx
  rcases h with ⟨hD, hy, hdy, hcurve, hne⟩
  have hden : y x - x ≠ 0 := sub_ne_zero.mpr (hne x hx)
  apply (eq_div_iff hden).2
  nlinarith [gap1 a D y ⟨hD, hy, hdy, hcurve, hne⟩ x hx]

theorem gap3 (a : ℝ) (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch a D y) :
    ∀ x ∈ D,
      secondDeriv y x =
        ((y x - x) * (deriv y x + 1) -
          (y x + x) * (deriv y x - 1)) / (y x - x) ^ 2 := by
  intro x hx
  rcases h with ⟨hD, hy, hdy, hcurve, hne⟩
  have hyx : DifferentiableAt ℝ y x :=
    (hy x hx).differentiableAt (hD.mem_nhds hx)
  have hdyx : DifferentiableAt ℝ (deriv y) x :=
    (hdy x hx).differentiableAt (hD.mem_nhds hx)
  have hden : y x - x ≠ 0 := sub_ne_zero.mpr (hne x hx)
  have hquot0 :
      HasDerivAt
        (fun t : ℝ => (y t + t) / (y t - t))
        (((deriv y x + 1) * (y x - x) -
          (y x + x) * (deriv y x - 1)) / (y x - x) ^ 2) x := by
    simpa using
      ((hyx.hasDerivAt.add (hasDerivAt_id x)).div
        (hyx.hasDerivAt.sub (hasDerivAt_id x)) hden)
  have hquot :
      HasDerivAt
        (fun t : ℝ => (y t + t) / (y t - t))
        (((y x - x) * (deriv y x + 1) -
          (y x + x) * (deriv y x - 1)) / (y x - x) ^ 2) x := by
    convert hquot0 using 1 <;> ring
  have hevent :
      deriv y =ᶠ[nhds x] (fun t : ℝ => (y t + t) / (y t - t)) := by
    filter_upwards [hD.mem_nhds hx] with z hz
    exact gap2 a D y ⟨hD, hy, hdy, hcurve, hne⟩ z hz
  have hsame :
      HasDerivAt (fun t : ℝ => (y t + t) / (y t - t))
        (deriv (deriv y) x) x :=
    hdyx.hasDerivAt.congr_of_eventuallyEq hevent.symm
  simpa [secondDeriv] using hsame.unique hquot

theorem gap4 (a : ℝ) (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch a D y) :
    ∀ x ∈ D,
      ((y x - x) * (deriv y x + 1) -
          (y x + x) * (deriv y x - 1)) / (y x - x) ^ 2 =
        (2 * y x - 2 * x * deriv y x) / (y x - x) ^ 2 := by
  intro x hx
  ring

theorem gap5 (a : ℝ) (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch a D y) :
    ∀ x ∈ D,
      (2 * y x - 2 * x * deriv y x) / (y x - x) ^ 2 =
        (2 * y x * (y x - x) - 2 * x * (y x + x)) /
          (y x - x) ^ 3 := by
  intro x hx
  have hne : y x ≠ x := h.2.2.2.2 x hx
  have hden : y x - x ≠ 0 := sub_ne_zero.mpr hne
  rw [gap2 a D y h x hx]
  field_simp [hden] <;> ring

theorem gap6 (a : ℝ) (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch a D y) :
    ∀ x ∈ D,
      (2 * y x * (y x - x) - 2 * x * (y x + x)) /
          (y x - x) ^ 3 =
        2 * (y x ^ 2 - 2 * x * y x - x ^ 2) /
          (y x - x) ^ 3 := by
  intro x hx
  ring

theorem gap7 (a : ℝ) (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch a D y) :
    ∀ x ∈ D,
      2 * (y x ^ 2 - 2 * x * y x - x ^ 2) /
          (y x - x) ^ 3 =
        -(2 * a ^ 2) / (y x - x) ^ 3 := by
  intro x hx
  have hc := h.2.2.2.1 x hx
  unfold curveEquation at hc
  have hn : y x ^ 2 - 2 * x * y x - x ^ 2 = -(a ^ 2) := by
    nlinarith
  rw [hn]
  ring

theorem gap8 (a : ℝ) (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch a D y) :
    ∀ x ∈ D,
      -(2 * a ^ 2) / (y x - x) ^ 3 =
        2 * a ^ 2 / (x - y x) ^ 3 := by
  intro x hx
  have hden : y x - x ≠ 0 :=
    sub_ne_zero.mpr (h.2.2.2.2 x hx)
  rw [show x - y x = -(y x - x) by ring]
  field_simp [hden] <;> ring

theorem gap9 (a : ℝ) (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch a D y) :
    ∀ x ∈ D,
      secondDeriv y x = 2 * a ^ 2 / (x - y x) ^ 3 := by
  intro x hx
  calc
    secondDeriv y x =
        ((y x - x) * (deriv y x + 1) -
          (y x + x) * (deriv y x - 1)) / (y x - x) ^ 2 :=
      gap3 a D y h x hx
    _ = (2 * y x - 2 * x * deriv y x) / (y x - x) ^ 2 :=
      gap4 a D y h x hx
    _ = (2 * y x * (y x - x) - 2 * x * (y x + x)) /
          (y x - x) ^ 3 := gap5 a D y h x hx
    _ = 2 * (y x ^ 2 - 2 * x * y x - x ^ 2) /
          (y x - x) ^ 3 := gap6 a D y h x hx
    _ = -(2 * a ^ 2) / (y x - x) ^ 3 := gap7 a D y h x hx
    _ = 2 * a ^ 2 / (x - y x) ^ 3 := gap8 a D y h x hx

theorem gap10 (a : ℝ) (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch a D y) :
    ∀ x ∈ D,
      2 * x + 2 * x * deriv y x + 2 * y x -
        2 * y x * deriv y x = 0 := by
  intro x hx
  nlinarith [gap1 a D y h x hx]

theorem gap11 (a : ℝ) (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch a D y) :
    ∀ x ∈ D, deriv y x = (y x + x) / (y x - x) := by
  exact gap2 a D y h

theorem gap12 (a : ℝ) (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch a D y) :
    ∀ x ∈ D,
      1 + 2 * deriv y x - (deriv y x) ^ 2 +
        (x - y x) * secondDeriv y x = 0 := by
  intro x hx
  have hne : y x ≠ x := h.2.2.2.2 x hx
  have hden : y x - x ≠ 0 := sub_ne_zero.mpr hne
  have hden' : x - y x ≠ 0 := sub_ne_zero.mpr hne.symm
  have hc := h.2.2.2.1 x hx
  unfold curveEquation at hc
  rw [gap2 a D y h x hx, gap9 a D y h x hx]
  field_simp [hden, hden'] <;> nlinarith [hc]

theorem gap13 (a : ℝ) (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch a D y) :
    ∀ x ∈ D,
      secondDeriv y x =
        (1 + 2 * deriv y x - (deriv y x) ^ 2) / (y x - x) := by
  intro x hx
  have hden : y x - x ≠ 0 := sub_ne_zero.mpr (h.2.2.2.2 x hx)
  apply (eq_div_iff hden).2
  nlinarith [gap12 a D y h x hx]

theorem gap14 (a : ℝ) (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch a D y) :
    ∀ x ∈ D,
      (1 + 2 * deriv y x - (deriv y x) ^ 2) / (y x - x) =
        (1 + 2 * ((y x + x) / (y x - x)) -
          ((y x + x) / (y x - x)) ^ 2) / (y x - x) := by
  intro x hx
  rw [gap11 a D y h x hx]

theorem gap15 (a : ℝ) (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch a D y) :
    ∀ x ∈ D,
      (1 + 2 * ((y x + x) / (y x - x)) -
          ((y x + x) / (y x - x)) ^ 2) / (y x - x) =
        2 * a ^ 2 / (x - y x) ^ 3 := by
  intro x hx
  have hne : y x ≠ x := h.2.2.2.2 x hx
  have hden : y x - x ≠ 0 := sub_ne_zero.mpr hne
  have hc := h.2.2.2.1 x hx
  unfold curveEquation at hc
  have hfrac :
      1 + 2 * ((y x + x) / (y x - x)) -
          ((y x + x) / (y x - x)) ^ 2 =
        -(2 * a ^ 2) / (y x - x) ^ 2 := by
    field_simp [hden] <;> nlinarith [hc]
  calc
    (1 + 2 * ((y x + x) / (y x - x)) -
          ((y x + x) / (y x - x)) ^ 2) / (y x - x) =
        (-(2 * a ^ 2) / (y x - x) ^ 2) / (y x - x) := by
      rw [hfrac]
    _ = -(2 * a ^ 2) / (y x - x) ^ 3 := by
      field_simp [hden] <;> ring
    _ = 2 * a ^ 2 / (x - y x) ^ 3 := gap8 a D y h x hx

theorem gap16 (a : ℝ) (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch a D y) :
    ∀ x ∈ D,
      secondDeriv y x = 2 * a ^ 2 / (x - y x) ^ 3 := by
  exact gap9 a D y h

end

end ProofGap.Exercise3371
