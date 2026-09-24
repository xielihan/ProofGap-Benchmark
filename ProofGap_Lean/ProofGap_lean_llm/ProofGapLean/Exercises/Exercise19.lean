import ProofGapLean.Prelude.Core
import Mathlib.Data.Real.Archimedean

/-!
# Exercise 19

Semantic formalization of Exercise 19, gaps 1,...,8.
The source notation `{x}` and `{y}` denotes arbitrary real sets.  Their
Minkowski sum is represented explicitly, with the nonempty bounded hypotheses
needed for finite suprema and infima.
-/

namespace ProofGap.Exercise19

def sumSet (X Y : Set ℝ) : Set ℝ :=
  {z | ∃ x ∈ X, ∃ y ∈ Y, z = x + y}

def AdmissiblePair (X Y : Set ℝ) : Prop :=
  X.Nonempty ∧ Y.Nonempty ∧
    BddBelow X ∧ BddBelow Y ∧ BddAbove X ∧ BddAbove Y

def SeparateLowerBounds (X Y : Set ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, sInf X ≤ x ∧ sInf Y ≤ y

def SeparateInfApproximations (X Y : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ x ∈ X, ∃ y ∈ Y,
      x < sInf X + ε / 2 ∧ y < sInf Y + ε / 2

def SumLowerBound (X Y : Set ℝ) : Prop :=
  ∀ z ∈ sumSet X Y, sInf X + sInf Y ≤ z

def SumInfApproximation (X Y : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ z ∈ sumSet X Y, z < sInf X + sInf Y + ε

/-- Exercise 19, gap 1. -/
theorem gap1
    (X Y : Set ℝ)
    (hXY : AdmissiblePair X Y) :
    SeparateLowerBounds X Y := by
  rcases hXY with ⟨hX, hY, hXbelow, hYbelow, hXabove, hYabove⟩
  intro x hx y hy
  exact ⟨(isGLB_csInf hX hXbelow).1 hx,
    (isGLB_csInf hY hYbelow).1 hy⟩

/-- Exercise 19, gap 2. -/
theorem gap2
    (X Y : Set ℝ)
    (hXY : AdmissiblePair X Y)
    (h1 : SeparateLowerBounds X Y) :
    SeparateInfApproximations X Y := by
  rcases hXY with ⟨hX, hY, hXbelow, hYbelow, hXabove, hYabove⟩
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  rcases exists_lt_of_csInf_lt hX (lt_add_of_pos_right _ hhalf) with
    ⟨x, hx, hxlt⟩
  rcases exists_lt_of_csInf_lt hY (lt_add_of_pos_right _ hhalf) with
    ⟨y, hy, hylt⟩
  exact ⟨x, hx, y, hy, hxlt, hylt⟩

/-- Exercise 19, gap 3. -/
theorem gap3
    (X Y : Set ℝ)
    (h1 : SeparateLowerBounds X Y) :
    SumLowerBound X Y := by
  intro z hz
  rcases hz with ⟨x, hx, y, hy, rfl⟩
  rcases h1 x hx y hy with ⟨hxl, hyl⟩
  linarith

/-- Exercise 19, gap 4. -/
theorem gap4
    (X Y : Set ℝ)
    (h2 : SeparateInfApproximations X Y) :
    SumInfApproximation X Y := by
  intro ε hε
  rcases h2 ε hε with ⟨x, hx, y, hy, hxlt, hylt⟩
  refine ⟨x + y, ⟨x, hx, y, hy, rfl⟩, ?_⟩
  linarith

/-- Exercise 19, gap 5. -/
theorem gap5
    (X Y : Set ℝ)
    (hXY : AdmissiblePair X Y)
    (h3 : SumLowerBound X Y)
    (h4 : SumInfApproximation X Y) :
    sInf X + sInf Y = sInf (sumSet X Y) := by
  rcases hXY with ⟨hX, hY, hXbelow, hYbelow, hXabove, hYabove⟩
  have hsum : (sumSet X Y).Nonempty := by
    rcases hX with ⟨x, hx⟩
    rcases hY with ⟨y, hy⟩
    exact ⟨x + y, x, hx, y, hy, rfl⟩
  have hglb : IsGLB (sumSet X Y) (sInf X + sInf Y) := by
    constructor
    · exact h3
    · intro M hM
      by_contra hnot
      have hlt : sInf X + sInf Y < M := lt_of_not_ge hnot
      let ε : ℝ := (M - (sInf X + sInf Y)) / 2
      have hε : 0 < ε := by dsimp [ε]; linarith
      rcases h4 ε hε with ⟨z, hz, hzlt⟩
      have hMle := hM hz
      dsimp [ε] at hzlt
      linarith
  exact (hglb.csInf_eq hsum).symm

/-- Exercise 19, gap 6. -/
theorem gap6
    (X Y : Set ℝ)
    (h5 : sInf X + sInf Y = sInf (sumSet X Y)) :
    sInf (sumSet X Y) = sInf X + sInf Y := by
  exact h5.symm

/-- Exercise 19, gap 7. -/
theorem gap7
    (X Y : Set ℝ)
    (hXY : AdmissiblePair X Y)
    (h6 : sInf (sumSet X Y) = sInf X + sInf Y) :
    sSup (sumSet X Y) = sSup X + sSup Y := by
  rcases hXY with ⟨hX, hY, hXbelow, hYbelow, hXabove, hYabove⟩
  have hsum : (sumSet X Y).Nonempty := by
    rcases hX with ⟨x, hx⟩
    rcases hY with ⟨y, hy⟩
    exact ⟨x + y, x, hx, y, hy, rfl⟩
  have hlub : IsLUB (sumSet X Y) (sSup X + sSup Y) := by
    constructor
    · intro z hz
      rcases hz with ⟨x, hx, y, hy, rfl⟩
      have hxl := (isLUB_csSup hX hXabove).1 hx
      have hyl := (isLUB_csSup hY hYabove).1 hy
      linarith
    · intro M hM
      by_contra hnot
      have hlt : M < sSup X + sSup Y := lt_of_not_ge hnot
      let ε : ℝ := (sSup X + sSup Y - M) / 2
      have hε : 0 < ε := by dsimp [ε]; linarith
      have hhalf : 0 < ε / 2 := by linarith
      rcases exists_lt_of_lt_csSup hX (sub_lt_self _ hhalf) with
        ⟨x, hx, hxgt⟩
      rcases exists_lt_of_lt_csSup hY (sub_lt_self _ hhalf) with
        ⟨y, hy, hygt⟩
      have hxy_le := hM ⟨x, hx, y, hy, rfl⟩
      dsimp [ε] at hxgt hygt
      linarith
  exact hlub.csSup_eq hsum

/-- Exercise 19, gap 8. -/
theorem gap8
    (X Y : Set ℝ)
    (h6 : sInf (sumSet X Y) = sInf X + sInf Y)
    (h7 : sSup (sumSet X Y) = sSup X + sSup Y) :
    sInf (sumSet X Y) = sInf X + sInf Y ∧
      sSup (sumSet X Y) = sSup X + sSup Y := by
  exact ⟨h6, h7⟩

end ProofGap.Exercise19
