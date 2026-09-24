import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3205

noncomputable section

open scoped Topology

def jointFunction (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  f p.1 p.2

def xProjection (G : Set (ℝ × ℝ)) : Set ℝ :=
  {x | ∃ y, (x, y) ∈ G}

def HorizontalSectionsContinuous
    (f : ℝ → ℝ → ℝ) (G : Set (ℝ × ℝ)) : Prop :=
  ∀ y : ℝ, ContinuousOn (fun x : ℝ => f x y) (xProjection G)

def VerticallyUniform
    (f : ℝ → ℝ → ℝ) (G : Set (ℝ × ℝ)) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x y₁ y₂ : ℝ,
    (x, y₁) ∈ G → (x, y₂) ∈ G →
      |y₁ - y₂| < δ → |f x y₁ - f x y₂| < ε

private theorem abs_add (a b : ℝ) : |a + b| ≤ |a| + |b| :=
  abs_add_le a b

theorem gap1 (f : ℝ → ℝ → ℝ) (G : Set (ℝ × ℝ))
    (hvertical : VerticallyUniform f G) :
    ∀ ε > 0, ∃ δ₁ > 0, ∀ x y₁ y₂ : ℝ,
      (x, y₁) ∈ G → (x, y₂) ∈ G →
        |y₁ - y₂| < δ₁ → |f x y₁ - f x y₂| < ε / 2 := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, hδ₁prop⟩ :=
    hvertical (ε / 2) (by linarith)
  exact ⟨δ₁, hδ₁, hδ₁prop⟩

theorem gap2 (f : ℝ → ℝ → ℝ) (G : Set (ℝ × ℝ))
    (hhorizontal : HorizontalSectionsContinuous f G) :
    ∀ x₀ y₀ : ℝ, (x₀, y₀) ∈ G →
      ∀ ε > 0, ∃ δ₂ > 0, ∀ x : ℝ,
        x ∈ xProjection G → |x - x₀| < δ₂ →
          |f x y₀ - f x₀ y₀| < ε / 2 := by
  intro x₀ y₀ hp₀ ε hε
  have hx₀ : x₀ ∈ xProjection G := ⟨y₀, hp₀⟩
  obtain ⟨δ₂, hδ₂, hcont⟩ :=
    (Metric.continuousWithinAt_iff.mp
      (hhorizontal y₀ x₀ hx₀)) (ε / 2) (by linarith)
  refine ⟨δ₂, hδ₂, ?_⟩
  intro x hx hdist
  have hdist' : dist x x₀ < δ₂ := by
    simpa [Real.dist_eq] using hdist
  simpa [Real.dist_eq] using hcont hx hdist'

theorem gap3 (G : Set (ℝ × ℝ)) (hopen : IsOpen G) :
    ∀ p₀ ∈ G, ∃ δ > 0, Metric.ball p₀ δ ⊆ G := by
  intro p₀ hp₀
  exact (Metric.isOpen_iff.mp hopen) p₀ hp₀

theorem gap4 :
    ∀ x₀ y₀ x y δ : ℝ,
      dist (x, y) (x₀, y₀) < δ → |x - x₀| < δ := by
  intro x₀ y₀ x y δ hdist
  have hdist' : max (dist x x₀) (dist y y₀) < δ := by
    simpa [Prod.dist_eq] using hdist
  have hx : dist x x₀ < δ :=
    lt_of_le_of_lt (le_max_left _ _) hdist'
  simpa [Real.dist_eq] using hx

theorem gap5 :
    ∀ δ₁ δ₂ : ℝ, min δ₁ δ₂ ≤ δ₂ := by
  intro δ₁ δ₂
  exact min_le_right δ₁ δ₂

theorem gap6 :
    ∀ x₀ y₀ x y δ : ℝ,
      dist (x, y) (x₀, y₀) < δ → |y - y₀| < δ := by
  intro x₀ y₀ x y δ hdist
  have hdist' : max (dist x x₀) (dist y y₀) < δ := by
    simpa [Prod.dist_eq] using hdist
  have hy : dist y y₀ < δ :=
    lt_of_le_of_lt (le_max_right _ _) hdist'
  simpa [Real.dist_eq] using hy

theorem gap7 :
    ∀ δ₁ δ₂ : ℝ, min δ₁ δ₂ ≤ δ₁ := by
  intro δ₁ δ₂
  exact min_le_left δ₁ δ₂

theorem gap8 (f : ℝ → ℝ → ℝ) :
    ∀ x₀ y₀ x y : ℝ,
      |f x y - f x₀ y₀| ≤
        |f x y - f x y₀| + |f x y₀ - f x₀ y₀| := by
  intro x₀ y₀ x y
  have hrewrite :
      f x y - f x₀ y₀ =
        (f x y - f x y₀) + (f x y₀ - f x₀ y₀) := by
    ring
  rw [hrewrite]
  exact abs_add _ _

theorem gap9 (f : ℝ → ℝ → ℝ) :
    ∀ x₀ y₀ x y ε : ℝ,
      |f x y - f x y₀| < ε / 2 →
      |f x y₀ - f x₀ y₀| < ε / 2 →
        |f x y - f x y₀| + |f x y₀ - f x₀ y₀| <
          ε / 2 + ε / 2 := by
  intro x₀ y₀ x y ε hvertical hhorizontal
  linarith

theorem gap10 :
    ∀ ε : ℝ, ε / 2 + ε / 2 = ε := by
  intro ε
  ring

theorem gap11 (f : ℝ → ℝ → ℝ) :
    ∀ x₀ y₀ x y ε : ℝ,
      |f x y - f x₀ y₀| ≤
          |f x y - f x y₀| + |f x y₀ - f x₀ y₀| →
      |f x y - f x y₀| + |f x y₀ - f x₀ y₀| < ε →
        |f x y - f x₀ y₀| < ε := by
  intro x₀ y₀ x y ε htriangle hsum
  linarith

theorem gap12 (f : ℝ → ℝ → ℝ) (G : Set (ℝ × ℝ))
    (hopen : IsOpen G)
    (hhorizontal : HorizontalSectionsContinuous f G)
    (hvertical : VerticallyUniform f G) :
    ∀ p₀ ∈ G, ContinuousAt (jointFunction f) p₀ := by
  intro p₀ hp₀
  rcases p₀ with ⟨x₀, y₀⟩
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, hv⟩ := gap1 f G hvertical ε hε
  obtain ⟨δ₂, hδ₂, hh⟩ :=
    gap2 f G hhorizontal x₀ y₀ hp₀ ε hε
  obtain ⟨δG, hδG, hball⟩ :=
    gap3 G hopen (x₀, y₀) hp₀
  let δ : ℝ := min δG (min δ₁ δ₂)
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min hδG (lt_min hδ₁ hδ₂)
  have hδGle : δ ≤ δG := by
    dsimp [δ]
    exact min_le_left _ _
  have hδ₁le : δ ≤ δ₁ := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ₂le : δ ≤ δ₂ := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨δ, hδpos, ?_⟩
  intro p hpdist
  rcases p with ⟨x, y⟩
  have hpGdist : dist (x, y) (x₀, y₀) < δG :=
    lt_of_lt_of_le hpdist hδGle
  have hpG : (x, y) ∈ G := by
    apply hball
    exact hpGdist
  have hxd : |x - x₀| < δ :=
    gap4 x₀ y₀ x y δ hpdist
  have hyd : |y - y₀| < δ :=
    gap6 x₀ y₀ x y δ hpdist
  have hxδG : |x - x₀| < δG :=
    lt_of_lt_of_le hxd hδGle
  have hxδ₂ : |x - x₀| < δ₂ :=
    lt_of_lt_of_le hxd hδ₂le
  have hyδ₁ : |y - y₀| < δ₁ :=
    lt_of_lt_of_le hyd hδ₁le
  have hxy₀G : (x, y₀) ∈ G := by
    apply hball
    simpa [Prod.dist_eq, Real.dist_eq] using hxδG
  have hxproj : x ∈ xProjection G := ⟨y, hpG⟩
  have hvbound : |f x y - f x y₀| < ε / 2 :=
    hv x y y₀ hpG hxy₀G hyδ₁
  have hhbound : |f x y₀ - f x₀ y₀| < ε / 2 :=
    hh x hxproj hxδ₂
  have hsum :
      |f x y - f x y₀| + |f x y₀ - f x₀ y₀| < ε := by
    calc
      |f x y - f x y₀| + |f x y₀ - f x₀ y₀| <
          ε / 2 + ε / 2 :=
        gap9 f x₀ y₀ x y ε hvbound hhbound
      _ = ε := gap10 ε
  have hfinal : |f x y - f x₀ y₀| < ε :=
    gap11 f x₀ y₀ x y ε (gap8 f x₀ y₀ x y) hsum
  simpa [jointFunction, Real.dist_eq] using hfinal

theorem gap13 (f : ℝ → ℝ → ℝ) (G : Set (ℝ × ℝ))
    (hopen : IsOpen G)
    (hhorizontal : HorizontalSectionsContinuous f G)
    (hvertical : VerticallyUniform f G) :
    ContinuousOn (jointFunction f) G := by
  intro p hp
  exact
    (gap12 f G hopen hhorizontal hvertical p hp).continuousWithinAt

theorem gap14 (f : ℝ → ℝ → ℝ) (G : Set (ℝ × ℝ))
    (hopen : IsOpen G)
    (hhorizontal : HorizontalSectionsContinuous f G)
    (hvertical : VerticallyUniform f G) :
    ContinuousOn (jointFunction f) G := by
  exact gap13 f G hopen hhorizontal hvertical

end

end ProofGap.Exercise3205
