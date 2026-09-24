import ProofGapLean.Prelude.Core
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise361_2

noncomputable section

def f (a b c d x : ℝ) : ℝ := (a * x + b) / (c * x + d)
def domain (c d : ℝ) : Set ℝ := {x | c * x + d ≠ 0}
def centerX (c d : ℝ) : ℝ := -d / c
def centerY (a c : ℝ) : ℝ := a / c
def verticalDisplacement (a b c d t : ℝ) : ℝ :=
  f a b c d (centerX c d + t) - centerY a c

def IsGraphCenter (g : ℝ → ℝ) (D : Set ℝ) (x₀ y₀ : ℝ) : Prop :=
  ∀ t, x₀ + t ∈ D → x₀ - t ∈ D →
    g (x₀ + t) + g (x₀ - t) = 2 * y₀

/-- Exercise 361_2, gap 1; guard both points by the rational domain. -/
theorem gap1 (a b c d : ℝ) (hc : c ≠ 0) : ∀ t, t ≠ 0 →
    f a b c d (centerX c d + t) +
      f a b c d (centerX c d - t) = 2 * centerY a c := by
  intro t ht
  have hp : c * (centerX c d + t) + d = c * t := by
    unfold centerX
    field_simp [hc]
    <;> ring
  have hm : c * (centerX c d - t) + d = -(c * t) := by
    unfold centerX
    field_simp [hc]
    <;> ring
  unfold f
  rw [hp, hm]
  unfold centerX centerY
  field_simp [hc, ht]
  <;> ring

/-- Exercise 361_2, gap 2; bind the vertical displacement instead of quantifying an arbitrary `y`. -/
theorem gap2 (a b c d t : ℝ) (hc : c ≠ 0) (ht : t ≠ 0) :
    verticalDisplacement a b c d t + centerY a c =
      f a b c d (centerX c d + t) := by
  unfold verticalDisplacement
  ring

/-- Exercise 361_2, gap 3; state reflection of the two vertical displacements. -/
theorem gap3 (a b c d t : ℝ) (hc : c ≠ 0) (ht : t ≠ 0) :
    -verticalDisplacement a b c d t + centerY a c =
      f a b c d (centerX c d - t) := by
  unfold verticalDisplacement
  have h := gap1 a b c d hc t ht
  linarith

/-- Exercise 361_2, gap 4; make the center coordinate a defined quantity and require `c≠0`. -/
theorem gap4 (c d : ℝ) (hc : c ≠ 0) :
    centerX c d = -d / c := by
  rfl

/-- Exercise 361_2, gap 5; make the center ordinate a defined quantity and require `c≠0`. -/
theorem gap5 (a c : ℝ) (hc : c ≠ 0) :
    centerY a c = a / c := by
  rfl

/-- Exercise 361_2, gap 6; use graph-center symmetry only where both rational values are defined. -/
theorem gap6 (a b c d : ℝ) (hc : c ≠ 0) :
    IsGraphCenter (f a b c d) (domain c d) (centerX c d) (centerY a c) := by
  unfold IsGraphCenter
  intro t hplus hminus
  change c * (centerX c d + t) + d ≠ 0 at hplus
  have ht : t ≠ 0 := by
    intro ht
    subst t
    apply hplus
    unfold centerX
    field_simp [hc]
    <;> ring
  exact gap1 a b c d hc t ht

end

end ProofGap.Exercise361_2
