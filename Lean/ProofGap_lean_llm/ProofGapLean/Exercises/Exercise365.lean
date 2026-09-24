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

/-- Source: `proof_gap/exercise_365/1.txt`. -/
theorem gap1 (f : ℝ → ℝ) (a y₀ : ℝ) (ha : IsCenter f a y₀) :
    ∀ x, f (a + x) - y₀ = y₀ - f (a - x) := by
  exact ha

/-- Source: `proof_gap/exercise_365/2.txt`. -/
theorem gap2 (f : ℝ → ℝ) (b : ℝ) (hb : IsAxis f b) :
    ∀ x, f (b + x) = f (b - x) := by
  exact hb

/-- Source: `proof_gap/exercise_365/3.txt`. -/
theorem gap3 (f : ℝ → ℝ) (a b y₀ : ℝ) (ha : IsCenter f a y₀) :
    ∀ x, f (b + x) = 2 * y₀ - f (2 * a - b - x) := by
  intro x
  have h := ha (b + x - a)
  rw [show a + (b + x - a) = b + x by ring,
      show a - (b + x - a) = 2 * a - b - x by ring] at h
  linarith

/-- Source: `proof_gap/exercise_365/4.txt`. -/
theorem gap4 (f : ℝ → ℝ) (a b y₀ : ℝ)
    (ha : IsCenter f a y₀) (hb : IsAxis f b) : ∀ x,
    f (b - x) = 2 * y₀ - f (2 * a - b - x) := by
  intro x
  calc
    f (b - x) = f (b + x) := (hb x).symm
    _ = 2 * y₀ - f (2 * a - b - x) := gap3 f a b y₀ ha x

/-- Source: `proof_gap/exercise_365/5.txt`. -/
theorem gap5 (f : ℝ → ℝ) (a b y₀ : ℝ)
    (ha : IsCenter f a y₀) (hb : IsAxis f b) : ∀ x,
    f x = 2 * y₀ - f (2 * a - 2 * b + x) := by
  intro x
  have h := gap4 f a b y₀ ha hb (b - x)
  rw [show b - (b - x) = x by ring,
      show 2 * a - b - (b - x) = 2 * a - 2 * b + x by ring] at h
  exact h

/-- Source: `proof_gap/exercise_365/6.txt`. -/
theorem gap6 (f : ℝ → ℝ) (a b y₀ : ℝ)
    (ha : IsCenter f a y₀) (hb : IsAxis f b) : ∀ x,
    f (2 * b - 2 * a + x) = 2 * y₀ - f x := by
  intro x
  have h := gap5 f a b y₀ ha hb (2 * b - 2 * a + x)
  rw [show 2 * a - 2 * b + (2 * b - 2 * a + x) = x by ring] at h
  exact h

/-- Source: `proof_gap/exercise_365/7.txt`. -/
theorem gap7 (f : ℝ → ℝ) (a b y₀ : ℝ)
    (ha : IsCenter f a y₀) (hb : IsAxis f b) : ∀ x,
    f (2 * a - 2 * b + x) = f (2 * b - 2 * a + x) := by
  intro x
  have h5 := gap5 f a b y₀ ha hb x
  have h6 := gap6 f a b y₀ ha hb x
  linarith

/-- Source: `proof_gap/exercise_365/8.txt`. -/
theorem gap8 (f : ℝ → ℝ) (a b y₀ : ℝ)
    (ha : IsCenter f a y₀) (hb : IsAxis f b) : ∀ x,
    f x = f (4 * (b - a) + x) := by
  intro x
  have h := gap7 f a b y₀ ha hb (2 * b - 2 * a + x)
  rw [show 2 * a - 2 * b + (2 * b - 2 * a + x) = x by ring,
      show 2 * b - 2 * a + (2 * b - 2 * a + x) = 4 * (b - a) + x by ring] at h
  exact h

/-- Source: `proof_gap/exercise_365/9.txt`. -/
theorem gap9 (f : ℝ → ℝ) (a b y₀ : ℝ)
    (ha : IsCenter f a y₀) (hb : IsAxis f b) :
    Function.Periodic f (4 * (b - a)) := by
  intro x
  simpa [add_comm] using (gap8 f a b y₀ ha hb x).symm

/-- Source: `proof_gap/exercise_365/10.txt`. -/
theorem gap10 (f : ℝ → ℝ) (a b y₀ : ℝ)
    (ha : IsCenter f a y₀) (hb : IsAxis f b) :
    Function.Periodic f (4 * (b - a)) := by
  exact gap9 f a b y₀ ha hb

end

end ProofGap.Exercise365
