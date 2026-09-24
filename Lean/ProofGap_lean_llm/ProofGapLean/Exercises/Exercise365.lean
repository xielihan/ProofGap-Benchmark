import ProofGapLean.Prelude.Core
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise365

noncomputable section

def IsCenter (f : ℝ → ℝ) (a y : ℝ) : Prop :=
  ∀ x, f (a + x) - y = y - f (a - x)

def IsAxis (f : ℝ → ℝ) (b : ℝ) : Prop :=
  ∀ x, f (b + x) = f (b - x)

/-- Exercise 365, gap 1. -/
theorem gap1 (f : ℝ → ℝ) (a y₀ : ℝ) (ha : IsCenter f a y₀) :
    ∀ x, f (a + x) - y₀ = y₀ - f (a - x) := by
  exact ha

/-- Exercise 365, gap 2. -/
theorem gap2 (f : ℝ → ℝ) (b : ℝ) (hb : IsAxis f b) :
    ∀ x, f (b + x) = f (b - x) := by
  exact hb

/-- Exercise 365, gap 3. -/
theorem gap3 (f : ℝ → ℝ) (a b y₀ : ℝ) (ha : IsCenter f a y₀) :
    ∀ x, f (b + x) = 2 * y₀ - f (2 * a - b - x) := by
  intro x
  have h := ha (b + x - a)
  rw [show a + (b + x - a) = b + x by ring,
      show a - (b + x - a) = 2 * a - b - x by ring] at h
  linarith

/-- Exercise 365, gap 4. -/
theorem gap4 (f : ℝ → ℝ) (a b y₀ : ℝ)
    (ha : IsCenter f a y₀) (hb : IsAxis f b) : ∀ x,
    f (b - x) = 2 * y₀ - f (2 * a - b - x) := by
  intro x
  calc
    f (b - x) = f (b + x) := (hb x).symm
    _ = 2 * y₀ - f (2 * a - b - x) := gap3 f a b y₀ ha x

/-- Exercise 365, gap 5. -/
theorem gap5 (f : ℝ → ℝ) (a b y₀ : ℝ)
    (ha : IsCenter f a y₀) (hb : IsAxis f b) : ∀ x,
    f x = 2 * y₀ - f (2 * a - 2 * b + x) := by
  intro x
  have h := gap4 f a b y₀ ha hb (b - x)
  rw [show b - (b - x) = x by ring,
      show 2 * a - b - (b - x) = 2 * a - 2 * b + x by ring] at h
  exact h

/-- Exercise 365, gap 6. -/
theorem gap6 (f : ℝ → ℝ) (a b y₀ : ℝ)
    (ha : IsCenter f a y₀) (hb : IsAxis f b) : ∀ x,
    f (2 * b - 2 * a + x) = 2 * y₀ - f x := by
  intro x
  have h := gap5 f a b y₀ ha hb (2 * b - 2 * a + x)
  rw [show 2 * a - 2 * b + (2 * b - 2 * a + x) = x by ring] at h
  exact h

/-- Exercise 365, gap 7. -/
theorem gap7 (f : ℝ → ℝ) (a b y₀ : ℝ)
    (ha : IsCenter f a y₀) (hb : IsAxis f b) : ∀ x,
    f (2 * a - 2 * b + x) = f (2 * b - 2 * a + x) := by
  intro x
  have h5 := gap5 f a b y₀ ha hb x
  have h6 := gap6 f a b y₀ ha hb x
  linarith

/-- Exercise 365, gap 8. -/
theorem gap8 (f : ℝ → ℝ) (a b y₀ : ℝ)
    (ha : IsCenter f a y₀) (hb : IsAxis f b) : ∀ x,
    f x = f (4 * (b - a) + x) := by
  intro x
  have h := gap7 f a b y₀ ha hb (2 * b - 2 * a + x)
  rw [show 2 * a - 2 * b + (2 * b - 2 * a + x) = x by ring,
      show 2 * b - 2 * a + (2 * b - 2 * a + x) = 4 * (b - a) + x by ring] at h
  exact h

/-- Exercise 365, gap 9. -/
theorem gap9 (f : ℝ → ℝ) (a b y₀ : ℝ)
    (ha : IsCenter f a y₀) (hb : IsAxis f b) :
    Function.Periodic f (4 * (b - a)) := by
  intro x
  simpa [add_comm] using (gap8 f a b y₀ ha hb x).symm

/-- Exercise 365, gap 10. -/
theorem gap10 (f : ℝ → ℝ) (a b y₀ : ℝ)
    (ha : IsCenter f a y₀) (hb : IsAxis f b) :
    Function.Periodic f (4 * (b - a)) := by
  exact gap9 f a b y₀ ha hb

end

end ProofGap.Exercise365
