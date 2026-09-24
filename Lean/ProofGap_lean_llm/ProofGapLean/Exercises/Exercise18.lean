import ProofGapLean.Prelude.Core
import Mathlib.Data.Real.Archimedean

/-!
# Exercise 18

Semantic formalization of Exercise 18, gaps 1,...,15.

The source notation `{x}` denotes an arbitrary set of real numbers, not a
singleton.  We therefore fix a set `X` and define `negSet X = {-x | x ∈ X}`.
Nonemptiness and two-sided boundedness are made explicit so that all finite
suprema and infima used by the exercise have their intended meaning.
-/

namespace ProofGap.Exercise18

/-- The pointwise additive inverse of a set. -/
def negSet (X : Set ℝ) : Set ℝ :=
  {y | ∃ x ∈ X, y = -x}

/-- Conditions implicitly required by the source's use of finite extrema. -/
def Admissible (X : Set ℝ) : Prop :=
  X.Nonempty ∧ BddAbove X ∧ BddBelow X

def InfIsLowerBound (X : Set ℝ) : Prop :=
  ∀ x ∈ X, sInf (negSet X) ≤ -x

def InfIsApproached (X : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ x ∈ X, -x < sInf (negSet X) + ε

def NegInfIsUpperBound (X : Set ℝ) : Prop :=
  ∀ x ∈ X, x ≤ -sInf (negSet X)

def NegInfIsApproached (X : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ x ∈ X, -sInf (negSet X) - ε < x

def SupIsUpperBound (X : Set ℝ) : Prop :=
  ∀ x ∈ X, -x ≤ sSup (negSet X)

def SupIsApproached (X : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ x ∈ X, sSup (negSet X) - ε < -x

def NegSupIsLowerBound (X : Set ℝ) : Prop :=
  ∀ x ∈ X, -sSup (negSet X) ≤ x

def NegSupIsApproached (X : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ x ∈ X, x < -sSup (negSet X) + ε

private lemma negSet_nonempty {X : Set ℝ} (hX : X.Nonempty) :
    (negSet X).Nonempty := by
  rcases hX with ⟨x, hx⟩
  exact ⟨-x, x, hx, rfl⟩

private lemma negSet_bddBelow {X : Set ℝ} (hX : BddAbove X) :
    BddBelow (negSet X) := by
  rcases hX with ⟨M, hM⟩
  refine ⟨-M, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  linarith [hM hx]

private lemma negSet_bddAbove {X : Set ℝ} (hX : BddBelow X) :
    BddAbove (negSet X) := by
  rcases hX with ⟨m, hm⟩
  refine ⟨-m, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  linarith [hm hx]

/-- Exercise 18, gap 1. -/
theorem gap1
    (X : Set ℝ)
    (hX : Admissible X) :
    InfIsLowerBound X := by
  intro x hx
  exact (isGLB_csInf (negSet_nonempty hX.1) (negSet_bddBelow hX.2.1)).1
    ⟨x, hx, rfl⟩

/-- Exercise 18, gap 2. -/
theorem gap2
    (X : Set ℝ)
    (hX : Admissible X)
    (h1 : InfIsLowerBound X) :
    InfIsApproached X := by
  intro ε hε
  rcases exists_lt_of_csInf_lt (negSet_nonempty hX.1)
      (lt_add_of_pos_right _ hε) with ⟨y, hy, hylt⟩
  rcases hy with ⟨x, hx, rfl⟩
  exact ⟨x, hx, hylt⟩

/-- Exercise 18, gap 3. -/
theorem gap3
    (X : Set ℝ)
    (h1 : InfIsLowerBound X) :
    NegInfIsUpperBound X := by
  intro x hx
  linarith [h1 x hx]

/-- Exercise 18, gap 4. -/
theorem gap4
    (X : Set ℝ)
    (h2 : InfIsApproached X) :
    NegInfIsApproached X := by
  intro ε hε
  rcases h2 ε hε with ⟨x, hx, hlt⟩
  exact ⟨x, hx, by linarith⟩

/-- Exercise 18, gap 5. -/
theorem gap5
    (X : Set ℝ)
    (hX : Admissible X)
    (h3 : NegInfIsUpperBound X)
    (h4 : NegInfIsApproached X) :
    -sInf (negSet X) = sSup X := by
  have hlub : IsLUB X (-sInf (negSet X)) := by
    constructor
    · exact h3
    · intro M hM
      by_contra hnot
      have hlt : M < -sInf (negSet X) := lt_of_not_ge hnot
      let ε : ℝ := (-sInf (negSet X) - M) / 2
      have hε : 0 < ε := by dsimp [ε]; linarith
      rcases h4 ε hε with ⟨x, hx, hxlt⟩
      have hxle := hM hx
      dsimp [ε] at hxlt
      linarith
  exact (hlub.csSup_eq hX.1).symm

/-- Exercise 18, gap 6. -/
theorem gap6
    (X : Set ℝ)
    (h5 : -sInf (negSet X) = sSup X) :
    sInf (negSet X) = -sSup X := by
  linarith

/-- Exercise 18, gap 7. -/
theorem gap7
    (X : Set ℝ)
    (h6 : sInf (negSet X) = -sSup X) :
    sInf (negSet X) = -sSup X := by
  exact h6

/-- Exercise 18, gap 8. -/
theorem gap8
    (X : Set ℝ)
    (hX : Admissible X)
    (h7 : sInf (negSet X) = -sSup X) :
    SupIsUpperBound X := by
  intro x hx
  exact (isLUB_csSup (negSet_nonempty hX.1) (negSet_bddAbove hX.2.2)).1
    ⟨x, hx, rfl⟩

/-- Exercise 18, gap 9. -/
theorem gap9
    (X : Set ℝ)
    (hX : Admissible X)
    (h8 : SupIsUpperBound X) :
    SupIsApproached X := by
  intro ε hε
  rcases exists_lt_of_lt_csSup (negSet_nonempty hX.1)
      (sub_lt_self _ hε) with ⟨y, hy, hygt⟩
  rcases hy with ⟨x, hx, rfl⟩
  exact ⟨x, hx, hygt⟩

/-- Exercise 18, gap 10. -/
theorem gap10
    (X : Set ℝ)
    (h8 : SupIsUpperBound X) :
    NegSupIsLowerBound X := by
  intro x hx
  linarith [h8 x hx]

/-- Exercise 18, gap 11. -/
theorem gap11
    (X : Set ℝ)
    (h9 : SupIsApproached X) :
    NegSupIsApproached X := by
  intro ε hε
  rcases h9 ε hε with ⟨x, hx, hlt⟩
  exact ⟨x, hx, by linarith⟩

/-- Exercise 18, gap 12. -/
theorem gap12
    (X : Set ℝ)
    (hX : Admissible X)
    (h10 : NegSupIsLowerBound X)
    (h11 : NegSupIsApproached X) :
    -sSup (negSet X) = sInf X := by
  have hglb : IsGLB X (-sSup (negSet X)) := by
    constructor
    · exact h10
    · intro M hM
      by_contra hnot
      have hlt : -sSup (negSet X) < M := lt_of_not_ge hnot
      let ε : ℝ := (M + sSup (negSet X)) / 2
      have hε : 0 < ε := by dsimp [ε]; linarith
      rcases h11 ε hε with ⟨x, hx, hxlt⟩
      have hMle := hM hx
      dsimp [ε] at hxlt
      linarith
  exact (hglb.csInf_eq hX.1).symm

/-- Exercise 18, gap 13. -/
theorem gap13
    (X : Set ℝ)
    (h12 : -sSup (negSet X) = sInf X) :
    sSup (negSet X) = -sInf X := by
  linarith

/-- Exercise 18, gap 14. -/
theorem gap14
    (X : Set ℝ)
    (h13 : sSup (negSet X) = -sInf X) :
    sSup (negSet X) = -sInf X := by
  exact h13

/-- Exercise 18, gap 15. -/
theorem gap15
    (X : Set ℝ)
    (h7 : sInf (negSet X) = -sSup X)
    (h14 : sSup (negSet X) = -sInf X) :
    sInf (negSet X) = -sSup X ∧
      sSup (negSet X) = -sInf X := by
  exact ⟨h7, h14⟩

end ProofGap.Exercise18
