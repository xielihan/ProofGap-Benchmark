import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3375

noncomputable section

def ratio (y : ℝ → ℝ) (x : ℝ) : ℝ :=
  y x / x

def secondDeriv (y : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv y) x

def IsC2Solution (D : Set ℝ) (y : ℝ → ℝ) : Prop :=
  IsOpen D ∧ DifferentiableOn ℝ y D ∧
    DifferentiableOn ℝ (deriv y) D ∧
      ∀ x ∈ D, x ≠ 0 ∧
        y x = 2 * x * Real.arctan (ratio y x)

private theorem ratio_deriv_eq (y : ℝ → ℝ) (x : ℝ)
    (hy : DifferentiableAt ℝ y x) (hx : x ≠ 0) :
    deriv (ratio y) x = (x * deriv y x - y x) / x ^ 2 := by
  change deriv (fun z : ℝ => y z / z) x = _
  have hq := hy.hasDerivAt.div (hasDerivAt_id x) hx
  convert hq.deriv using 1 <;> simp [id] <;> ring

theorem gap1 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Solution D y) :
    ∀ x ∈ D, ratio y x = 2 * Real.arctan (ratio y x) := by
  intro x hx
  rcases h.2.2.2 x hx with ⟨hx0, hy⟩
  calc
    ratio y x = y x / x := rfl
    _ = (2 * x * Real.arctan (ratio y x)) / x := by rw [hy]
    _ = 2 * Real.arctan (ratio y x) := by
      field_simp [hx0] <;> ring

theorem gap2 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Solution D y) :
    ∀ x ∈ D, (ratio y x) ^ 2 ≠ 1 := by
  intro x hx hsq
  have hfix := gap1 D y h x hx
  have hprod :
      (ratio y x - 1) * (ratio y x + 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hprod with hminus | hplus
  · have hr : ratio y x = 1 := by linarith
    rw [hr, Real.arctan_one] at hfix
    nlinarith [Real.pi_gt_three]
  · have hr : ratio y x = -1 := by linarith
    have hatan : Real.arctan (-1) = -(Real.pi / 4) := by
      rw [Real.arctan_neg, Real.arctan_one]
    rw [hr, hatan] at hfix
    nlinarith [Real.pi_gt_three]

theorem gap3 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Solution D y) :
    ∀ x ∈ D,
      deriv (ratio y) x =
        2 * deriv (ratio y) x / (1 + (ratio y x) ^ 2) := by
  intro x hx
  have hx0 : x ≠ 0 := (h.2.2.2 x hx).1
  have hy : DifferentiableAt ℝ y x :=
    (h.2.1 x hx).differentiableAt (h.1.mem_nhds hx)
  have hr : DifferentiableAt ℝ (ratio y) x := by
    change DifferentiableAt ℝ (fun z : ℝ => y z / z) x
    exact hy.div differentiableAt_id hx0
  have heq :
      ratio y =ᶠ[nhds x]
        (fun z => 2 * Real.arctan (ratio y z)) := by
    exact Filter.Eventually.mono (h.1.mem_nhds hx)
      (fun z hz => gap1 D y h z hz)
  have ha :=
    (Real.hasDerivAt_arctan (ratio y x)).comp x hr.hasDerivAt
  have harctan :
      HasDerivAt (fun z => 2 * Real.arctan (ratio y z))
        (2 * deriv (ratio y) x / (1 + (ratio y x) ^ 2)) x := by
    convert ha.const_mul 2 using 1 <;> ring
  calc
    deriv (ratio y) x =
        deriv (fun z => 2 * Real.arctan (ratio y z)) x := heq.deriv_eq
    _ = 2 * deriv (ratio y) x / (1 + (ratio y x) ^ 2) :=
      harctan.deriv

theorem gap4 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Solution D y) :
    ∀ x ∈ D, deriv (ratio y) x = 0 := by
  intro x hx
  have hd := gap3 D y h x hx
  have hden : 1 + (ratio y x) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (ratio y x)]
  field_simp [hden] at hd
  have hprod :
      deriv (ratio y) x * ((ratio y x) ^ 2 - 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hprod with hzero | hsquare
  · exact hzero
  · exfalso
    apply gap2 D y h x hx
    nlinarith

theorem gap5 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Solution D y) :
    ∀ x ∈ D, (x * deriv y x - y x) / x ^ 2 = 0 := by
  intro x hx
  have hx0 : x ≠ 0 := (h.2.2.2 x hx).1
  have hy : DifferentiableAt ℝ y x :=
    (h.2.1 x hx).differentiableAt (h.1.mem_nhds hx)
  rw [← ratio_deriv_eq y x hy hx0]
  exact gap4 D y h x hx

theorem gap6 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Solution D y) :
    ∀ x ∈ D, deriv y x = y x / x := by
  intro x hx
  have hx0 : x ≠ 0 := (h.2.2.2 x hx).1
  have hz := gap5 D y h x hx
  field_simp [hx0] at hz ⊢ <;> nlinarith

theorem gap7 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Solution D y) :
    ∀ x ∈ D,
      secondDeriv y x = (x * deriv y x - y x) / x ^ 2 := by
  intro x hx
  have hx0 : x ≠ 0 := (h.2.2.2 x hx).1
  have hy : DifferentiableAt ℝ y x :=
    (h.2.1 x hx).differentiableAt (h.1.mem_nhds hx)
  have heq : deriv y =ᶠ[nhds x] ratio y := by
    exact Filter.Eventually.mono (h.1.mem_nhds hx)
      (fun z hz => by simpa [ratio] using gap6 D y h z hz)
  calc
    secondDeriv y x = deriv (deriv y) x := rfl
    _ = deriv (ratio y) x := heq.deriv_eq
    _ = (x * deriv y x - y x) / x ^ 2 :=
      ratio_deriv_eq y x hy hx0

theorem gap8 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Solution D y) :
    ∀ x ∈ D, (x * deriv y x - y x) / x ^ 2 = 0 := by
  exact gap5 D y h

theorem gap9 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Solution D y) :
    ∀ x ∈ D, secondDeriv y x = 0 := by
  intro x hx
  calc
    secondDeriv y x = (x * deriv y x - y x) / x ^ 2 :=
      gap7 D y h x hx
    _ = 0 := gap8 D y h x hx

end

end ProofGap.Exercise3375
