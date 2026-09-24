import ProofGapLean.Prelude.Core
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise364

noncomputable section

def IsCenter (f : ℝ → ℝ) (a y : ℝ) : Prop :=
  ∀ x, f (a + x) - y = y - f (a - x)

def phi (f : ℝ → ℝ) (a b y₀ y₁ x : ℝ) : ℝ :=
  f x + (y₀ - y₁) / (b - a) * x

/-- Source: `proof_gap/exercise_364/1.txt`. -/
theorem gap1 (f : ℝ → ℝ) (a y₀ : ℝ) (ha : IsCenter f a y₀) :
    ∀ x, f (a + x) - y₀ = y₀ - f (a - x) := by
  simpa [IsCenter] using ha

/-- Source: `proof_gap/exercise_364/2.txt`. -/
theorem gap2 (f : ℝ → ℝ) (b y₁ : ℝ) (hb : IsCenter f b y₁) :
    ∀ x, f (b + x) - y₁ = y₁ - f (b - x) := by
  simpa [IsCenter] using hb

/-- Source: `proof_gap/exercise_364/3.txt`. -/
theorem gap3 (f : ℝ → ℝ) (a b y₀ : ℝ) (ha : IsCenter f a y₀) :
    ∀ x, f (b + x) - y₀ = y₀ - f (2 * a - b - x) := by
  intro x
  convert ha (b - a + x) using 1 <;> ring

/-- Source: `proof_gap/exercise_364/4.txt`. -/
theorem gap4 (f : ℝ → ℝ) (a b y₀ y₁ : ℝ)
    (ha : IsCenter f a y₀) (hb : IsCenter f b y₁) : ∀ x,
    2 * y₁ - f (b - x) = 2 * y₀ - f (2 * a - b - x) := by
  intro x
  have h_b := hb x
  have h_a := gap3 f a b y₀ ha x
  linarith

/-- Source: `proof_gap/exercise_364/5.txt`. -/
theorem gap5 (f : ℝ → ℝ) (a b y₀ y₁ : ℝ)
    (ha : IsCenter f a y₀) (hb : IsCenter f b y₁) : ∀ x,
    f (b - x) = 2 * (y₁ - y₀) + f (2 * a - b - x) := by
  intro x
  have h := gap4 f a b y₀ y₁ ha hb x
  linarith

/-- Source: `proof_gap/exercise_364/6.txt`. -/
theorem gap6 (f : ℝ → ℝ) (a b y₀ y₁ : ℝ)
    (ha : IsCenter f a y₀) (hb : IsCenter f b y₁) : ∀ x,
    f x = 2 * (y₁ - y₀) + f (2 * a - 2 * b + x) := by
  intro x
  convert gap5 f a b y₀ y₁ ha hb (b - x) using 1 <;> ring

/-- Source: `proof_gap/exercise_364/7.txt`. -/
theorem gap7 (f : ℝ → ℝ) (a b y₀ y₁ : ℝ)
    (ha : IsCenter f a y₀) (hb : IsCenter f b y₁) : ∀ x,
    f x = 2 * (y₀ - y₁) + f (2 * (b - a) + x) := by
  intro x
  convert gap6 f b a y₁ y₀ hb ha x using 1 <;> ring

/-- Source: `proof_gap/exercise_364/8.txt`. -/
theorem gap8 (f : ℝ → ℝ) (a b y₀ y₁ : ℝ) (hab : b ≠ a) : ∀ x,
    f x = -(y₀ - y₁) / (b - a) * x + phi f a b y₀ y₁ x := by
  intro x
  unfold phi
  ring

/-- Source: `proof_gap/exercise_364/9.txt`. -/
theorem gap9 (f : ℝ → ℝ) (a b y₀ y₁ : ℝ) (hab : b ≠ a) : ∀ x,
    f (x + 2 * (b - a)) =
      -(y₀ - y₁) / (b - a) * (x + 2 * (b - a)) +
        phi f a b y₀ y₁ (x + 2 * (b - a)) := by
  intro x
  exact gap8 f a b y₀ y₁ hab (x + 2 * (b - a))

/-- Source: `proof_gap/exercise_364/10.txt`. -/
theorem gap10 (f : ℝ → ℝ) (a b y₀ y₁ : ℝ) (hab : b ≠ a) : ∀ x,
    f x - f (x + 2 * (b - a)) =
      2 * (y₀ - y₁) + phi f a b y₀ y₁ x -
        phi f a b y₀ y₁ (x + 2 * (b - a)) := by
  intro x
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab
  unfold phi
  field_simp [hba] <;> ring

/-- Source: `proof_gap/exercise_364/11.txt`. -/
theorem gap11 (f : ℝ → ℝ) (a b y₀ y₁ : ℝ) (hab : b ≠ a)
    (ha : IsCenter f a y₀) (hb : IsCenter f b y₁) : ∀ x,
    phi f a b y₀ y₁ x = phi f a b y₀ y₁ (x + 2 * (b - a)) := by
  intro x
  have hf :
      f x = 2 * (y₀ - y₁) + f (x + 2 * (b - a)) := by
    convert gap7 f a b y₀ y₁ ha hb x using 1 <;> ring
  have hphi := gap10 f a b y₀ y₁ hab x
  linarith

/-- Source: `proof_gap/exercise_364/12.txt`. -/
theorem gap12 (f : ℝ → ℝ) (a b y₀ y₁ : ℝ) (hab : b ≠ a)
    (ha : IsCenter f a y₀) (hb : IsCenter f b y₁) :
    Function.Periodic (phi f a b y₀ y₁) (2 * (b - a)) := by
  intro x
  symm
  exact gap11 f a b y₀ y₁ hab ha hb x

/-- Source: `proof_gap/exercise_364/13.txt`. -/
theorem gap13 (f : ℝ → ℝ) (a b y₀ y₁ : ℝ) (hab : b ≠ a)
    (hy : y₀ = y₁) : ∀ x, f x = phi f a b y₀ y₁ x := by
  intro x
  simp [phi, hy]

/-- Source: `proof_gap/exercise_364/14.txt`. -/
theorem gap14 (f : ℝ → ℝ) (a b y₀ y₁ : ℝ) (hab : b ≠ a)
    (ha : IsCenter f a y₀) (hb : IsCenter f b y₁)
    (hy : y₀ = y₁) :
    Function.Periodic f (2 * (b - a)) := by
  have hp := gap12 f a b y₀ y₁ hab ha hb
  intro x
  calc
    f (x + 2 * (b - a)) =
        phi f a b y₀ y₁ (x + 2 * (b - a)) :=
      gap13 f a b y₀ y₁ hab hy (x + 2 * (b - a))
    _ = phi f a b y₀ y₁ x := hp x
    _ = f x := (gap13 f a b y₀ y₁ hab hy x).symm

/-- Source: `proof_gap/exercise_364/15.txt`; move the function witness outside the point quantifier. -/
theorem gap15 (f : ℝ → ℝ) (a b y₀ y₁ : ℝ) (hab : b ≠ a)
    (ha : IsCenter f a y₀) (hb : IsCenter f b y₁) :
    ∃ psi : ℝ → ℝ,
      Function.Periodic psi (2 * (b - a)) ∧
        (∀ x, f x = -(y₀ - y₁) / (b - a) * x + psi x) ∧
        (y₀ = y₁ → Function.Periodic f (2 * (b - a))) := by
  refine ⟨phi f a b y₀ y₁, ?_, ?_, ?_⟩
  · exact gap12 f a b y₀ y₁ hab ha hb
  · exact gap8 f a b y₀ y₁ hab
  · intro hy
    exact gap14 f a b y₀ y₁ hab ha hb hy

end

end ProofGap.Exercise364
