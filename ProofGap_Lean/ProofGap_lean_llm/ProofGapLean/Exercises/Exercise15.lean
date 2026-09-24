import ProofGapLean.Prelude.Core
import Mathlib.Data.Real.Archimedean

/-!
# Exercise 15

Semantic formalization of Exercise 15, gaps 1,...,13.
The source discusses existence and characterization of suprema and infima.
-/

namespace ProofGap.Exercise15

def NoMaximum (A : Set ℝ) : Prop :=
  ¬ ∃ m : ℝ, IsGreatest A m

def nonUpperBounds (A : Set ℝ) : Set ℝ :=
  (upperBounds A)ᶜ

def MaximumIsUpperBound : Prop :=
  ∀ A : Set ℝ, ∀ m : ℝ, IsGreatest A m →
    ∀ a : ℝ, a ∈ A → a ≤ m

def MaximumIsLeastUpperBound : Prop :=
  ∀ A : Set ℝ, ∀ m : ℝ, IsGreatest A m →
    ∀ M : ℝ, (∀ a : ℝ, a ∈ A → a ≤ M) → m ≤ M

def MaximumEqualsSupremum : Prop :=
  ∀ A : Set ℝ, ∀ m : ℝ, IsGreatest A m → m = sSup A

def MembersAreNotUpperBounds : Prop :=
  ∀ A : Set ℝ, NoMaximum A → A ⊆ nonUpperBounds A

def NonUpperBoundsNonempty : Prop :=
  ∀ A : Set ℝ, A.Nonempty → NoMaximum A → (nonUpperBounds A).Nonempty

def PreserveNonemptyAssumption : Prop :=
  ∀ A : Set ℝ, A.Nonempty → NoMaximum A → A.Nonempty

def SeparateNonUpperAndUpperBounds : Prop :=
  ∀ A : Set ℝ, NoMaximum A →
    ∀ u : ℝ, u ∈ nonUpperBounds A →
      ∀ v : ℝ, v ∈ upperBounds A → u < v

def LeastUpperBoundIsUpperBound : Prop :=
  ∀ A : Set ℝ, ∀ β : ℝ, NoMaximum A →
    IsLeast (upperBounds A) β →
    ∀ a : ℝ, a ∈ A → a ≤ β

def LeastUpperBoundIsLeast : Prop :=
  ∀ A : Set ℝ, ∀ β : ℝ, NoMaximum A →
    IsLeast (upperBounds A) β →
    ∀ M : ℝ, (∀ a : ℝ, a ∈ A → a ≤ M) → β ≤ M

def LeastUpperBoundEqualsSupremum : Prop :=
  ∀ A : Set ℝ, ∀ β : ℝ, NoMaximum A →
    IsLeast (upperBounds A) β → β = sSup A

def SupremumExists : Prop :=
  ∀ A : Set ℝ, A.Nonempty → BddAbove A →
    ∃ β : ℝ, IsLUB A β ∧ β = sSup A

def InfimumExists : Prop :=
  ∀ A : Set ℝ, A.Nonempty → BddBelow A →
    ∃ α : ℝ, IsGLB A α ∧ α = sInf A

/--
Exercise 15, gap 1.

The two source binders named `m` shadow one another.  They are unified into the
actual maximum witness.
-/
theorem gap1 : MaximumIsUpperBound := by
  intro A m hgreatest a ha
  exact hgreatest.2 ha

/-- Exercise 15, gap 2; uses the same repaired witness scope. -/
theorem gap2
    (h1 : MaximumIsUpperBound) :
    MaximumIsLeastUpperBound := by
  intro A m hgreatest M hupper
  exact hupper m hgreatest.1

/-- Exercise 15, gap 3; uses the same repaired witness scope. -/
theorem gap3
    (h1 : MaximumIsUpperBound)
    (h2 : MaximumIsLeastUpperBound) :
    MaximumEqualsSupremum := by
  intro A m hgreatest
  exact hgreatest.csSup_eq.symm

/-- Exercise 15, gap 4. -/
theorem gap4
    (h1 : MaximumIsUpperBound)
    (h2 : MaximumIsLeastUpperBound)
    (h3 : MaximumEqualsSupremum) :
    MembersAreNotUpperBounds := by
  intro A hnomax a ha
  change a ∉ upperBounds A
  intro haupper
  exact hnomax ⟨a, ha, haupper⟩

/--
Exercise 15, gap 5.

The missing nonemptiness premise is explicit.
-/
theorem gap5
    (h4 : MembersAreNotUpperBounds) :
    NonUpperBoundsNonempty := by
  intro A hA hnomax
  rcases hA with ⟨a, ha⟩
  exact ⟨a, h4 A hnomax ha⟩

/--
Exercise 15, gap 6.

`NoMaximum A` alone does not imply `A.Nonempty` (the empty set is a
counterexample), so nonemptiness is restored as a premise.
-/
theorem gap6
    (h4 : MembersAreNotUpperBounds)
    (h5 : NonUpperBoundsNonempty) :
    PreserveNonemptyAssumption := by
  intro A hA hnomax
  exact hA

/-- Exercise 15, gap 7. -/
theorem gap7
    (h4 : MembersAreNotUpperBounds)
    (h5 : NonUpperBoundsNonempty)
    (h6 : PreserveNonemptyAssumption) :
    SeparateNonUpperAndUpperBounds := by
  intro A hnomax u hu v hv
  change u ∉ upperBounds A at hu
  by_contra hnlt
  apply hu
  intro a ha
  exact (hv ha).trans (le_of_not_gt hnlt)

/-- Exercise 15, gap 8. -/
theorem gap8
    (h7 : SeparateNonUpperAndUpperBounds) :
    LeastUpperBoundIsUpperBound := by
  intro A β hnomax hleast a ha
  exact hleast.1 ha

/-- Exercise 15, gap 9. -/
theorem gap9
    (h8 : LeastUpperBoundIsUpperBound) :
    LeastUpperBoundIsLeast := by
  intro A β hnomax hleast M hupper
  exact hleast.2 hupper

/-- Exercise 15, gap 10. -/
theorem gap10
    (h8 : LeastUpperBoundIsUpperBound)
    (h9 : LeastUpperBoundIsLeast) :
    LeastUpperBoundEqualsSupremum := by
  intro A β hnomax hleast
  have hA : A.Nonempty := by
    by_contra hnot
    have hempty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hnot
    have hsmaller : β - 1 ∈ upperBounds A := by
      intro a ha
      rw [hempty] at ha
      simp at ha
    have := hleast.2 hsmaller
    linarith
  have hlub : IsLUB A β := hleast
  exact (hlub.csSup_eq hA).symm

/-- Exercise 15, gap 11. -/
theorem gap11
    (h3 : MaximumEqualsSupremum)
    (h10 : LeastUpperBoundEqualsSupremum) :
    SupremumExists := by
  intro A hA hbdd
  exact ⟨sSup A, isLUB_csSup hA hbdd, rfl⟩

/-- Exercise 15, gap 12. -/
theorem gap12
    (h11 : SupremumExists) :
    InfimumExists := by
  intro A hA hbdd
  exact ⟨sInf A, isGLB_csInf hA hbdd, rfl⟩

/-- Exercise 15, gap 13. -/
theorem gap13
    (h11 : SupremumExists)
    (h12 : InfimumExists) :
    InfimumExists ∧ SupremumExists := by
  exact ⟨h12, h11⟩

end ProofGap.Exercise15
