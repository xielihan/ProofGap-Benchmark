import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3561

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ

inductive SurfaceIndex
  | one
  | two
  | three
  deriving DecidableEq

def surface1 (a : ℝ) : Set Point3 :=
  {p | p.x ^ 2 + p.y ^ 2 + p.z ^ 2 = 2 * a * p.x}

def surface2 (b : ℝ) : Set Point3 :=
  {p | p.x ^ 2 + p.y ^ 2 + p.z ^ 2 = 2 * b * p.y}

def surface3 (c : ℝ) : Set Point3 :=
  {p | p.x ^ 2 + p.y ^ 2 + p.z ^ 2 = 2 * c * p.z}

def normalAt (a b c : ℝ) (i : SurfaceIndex) (p : Point3) : Point3 :=
  match i with
  | .one => ⟨2 * (p.x - a), 2 * p.y, 2 * p.z⟩
  | .two => ⟨2 * p.x, 2 * (p.y - b), 2 * p.z⟩
  | .three => ⟨2 * p.x, 2 * p.y, 2 * (p.z - c)⟩

def dot (u v : Point3) : ℝ :=
  u.x * v.x + u.y * v.y + u.z * v.z

def pairwiseOrthogonal (a b c : ℝ) (p : Point3) : Prop :=
  ∀ i j : SurfaceIndex, i ≠ j →
    dot (normalAt a b c i p) (normalAt a b c j p) = 0

theorem gap1 (a b c : ℝ) :
    ∀ p : Point3, p ∈ surface1 a → p ∈ surface2 b →
      normalAt a b c .one p =
        ⟨2 * (p.x - a), 2 * p.y, 2 * p.z⟩ := by
  intro p _ _
  rfl

theorem gap2 (a b c : ℝ) :
    ∀ p : Point3, p ∈ surface1 a → p ∈ surface2 b →
      normalAt a b c .two p =
        ⟨2 * p.x, 2 * (p.y - b), 2 * p.z⟩ := by
  intro p _ _
  rfl

theorem gap3 (a b c : ℝ) :
    ∀ p : Point3, p ∈ surface1 a → p ∈ surface2 b →
      dot (normalAt a b c .one p) (normalAt a b c .two p) =
        4 * (p.x * (p.x - a) + p.y * (p.y - b) + p.z ^ 2) := by
  intro p _ _
  dsimp [dot, normalAt]
  ring

theorem gap4 (a b : ℝ) :
    ∀ p : Point3,
      4 * (p.x * (p.x - a) + p.y * (p.y - b) + p.z ^ 2) =
        2 * (2 * p.x ^ 2 + 2 * p.y ^ 2 + 2 * p.z ^ 2 -
          2 * a * p.x - 2 * b * p.y) := by
  intro p
  ring

theorem gap5 (a b c : ℝ) :
    ∀ p : Point3, p ∈ surface1 a → p ∈ surface2 b →
      dot (normalAt a b c .one p) (normalAt a b c .two p) =
        2 * (2 * p.x ^ 2 + 2 * p.y ^ 2 + 2 * p.z ^ 2 -
          2 * a * p.x - 2 * b * p.y) := by
  intro p h1 h2
  calc
    dot (normalAt a b c .one p) (normalAt a b c .two p) =
        4 * (p.x * (p.x - a) + p.y * (p.y - b) + p.z ^ 2) :=
      gap3 a b c p h1 h2
    _ = 2 * (2 * p.x ^ 2 + 2 * p.y ^ 2 + 2 * p.z ^ 2 -
          2 * a * p.x - 2 * b * p.y) := gap4 a b p

theorem gap6 (a b c : ℝ) :
    ∀ p : Point3, p ∈ surface1 a → p ∈ surface2 b →
      dot (normalAt a b c .one p) (normalAt a b c .two p) =
        2 * ((p.x ^ 2 + p.y ^ 2 + p.z ^ 2 - 2 * a * p.x) +
          (p.x ^ 2 + p.y ^ 2 + p.z ^ 2 - 2 * b * p.y)) := by
  intro p h1 h2
  calc
    dot (normalAt a b c .one p) (normalAt a b c .two p) =
        2 * (2 * p.x ^ 2 + 2 * p.y ^ 2 + 2 * p.z ^ 2 -
          2 * a * p.x - 2 * b * p.y) := gap5 a b c p h1 h2
    _ = 2 * ((p.x ^ 2 + p.y ^ 2 + p.z ^ 2 - 2 * a * p.x) +
          (p.x ^ 2 + p.y ^ 2 + p.z ^ 2 - 2 * b * p.y)) := by
      ring

theorem gap7 (a b : ℝ) :
    ∀ p : Point3, p ∈ surface1 a → p ∈ surface2 b →
      2 * ((p.x ^ 2 + p.y ^ 2 + p.z ^ 2 - 2 * a * p.x) +
          (p.x ^ 2 + p.y ^ 2 + p.z ^ 2 - 2 * b * p.y)) = 0 := by
  intro p h1 h2
  change p.x ^ 2 + p.y ^ 2 + p.z ^ 2 = 2 * a * p.x at h1
  change p.x ^ 2 + p.y ^ 2 + p.z ^ 2 = 2 * b * p.y at h2
  nlinarith [h1, h2]

theorem gap8 (a b c : ℝ) :
    ∀ p : Point3, p ∈ surface1 a → p ∈ surface2 b →
      dot (normalAt a b c .one p) (normalAt a b c .two p) = 0 := by
  intro p h1 h2
  calc
    dot (normalAt a b c .one p) (normalAt a b c .two p) =
        2 * ((p.x ^ 2 + p.y ^ 2 + p.z ^ 2 - 2 * a * p.x) +
          (p.x ^ 2 + p.y ^ 2 + p.z ^ 2 - 2 * b * p.y)) :=
      gap6 a b c p h1 h2
    _ = 0 := gap7 a b p h1 h2

theorem gap9 (a b c : ℝ) :
    ∀ p : Point3, p ∈ surface1 a → p ∈ surface2 b →
      p ∈ surface3 c → pairwiseOrthogonal a b c p := by
  intro p h1 h2 h3 i j hij
  change p.x ^ 2 + p.y ^ 2 + p.z ^ 2 = 2 * a * p.x at h1
  change p.x ^ 2 + p.y ^ 2 + p.z ^ 2 = 2 * b * p.y at h2
  change p.x ^ 2 + p.y ^ 2 + p.z ^ 2 = 2 * c * p.z at h3
  cases i <;> cases j
  · exact (hij rfl).elim
  · dsimp [dot, normalAt]
    nlinarith [h1, h2]
  · dsimp [dot, normalAt]
    nlinarith [h1, h3]
  · dsimp [dot, normalAt]
    nlinarith [h1, h2]
  · exact (hij rfl).elim
  · dsimp [dot, normalAt]
    nlinarith [h2, h3]
  · dsimp [dot, normalAt]
    nlinarith [h1, h3]
  · dsimp [dot, normalAt]
    nlinarith [h2, h3]
  · exact (hij rfl).elim

theorem gap10 (a b c : ℝ)
    (S₁ S₂ S₃ : Set Point3)
    (hSurfaces :
      S₁ = surface1 a ∧ S₂ = surface2 b ∧ S₃ = surface3 c) :
    ∀ p : Point3, p ∈ S₁ → p ∈ S₂ → p ∈ S₃ →
      pairwiseOrthogonal a b c p := by
  intro p hp1 hp2 hp3
  rw [hSurfaces.1] at hp1
  rw [hSurfaces.2.1] at hp2
  rw [hSurfaces.2.2] at hp3
  exact gap9 a b c p hp1 hp2 hp3

end

end ProofGap.Exercise3561
