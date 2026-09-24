import ProofGapLean.Prelude.Core
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise399

noncomputable section

def imageOn (f : ℝ → ℝ) (a b : ℝ) : Set ℝ :=
  {y | ∃ x ∈ Set.Ioo a b, y = f x}

def lowerValue (f : ℝ → ℝ) (a b : ℝ) : ℝ := sInf (imageOn f a b)
def upperValue (f : ℝ → ℝ) (a b : ℝ) : ℝ := sSup (imageOn f a b)
def sumFn (f₁ f₂ : ℝ → ℝ) (x : ℝ) : ℝ := f₁ x + f₂ x

/-- Exercise 399, gap 1; restrict the point to the common interval. -/
theorem gap1 (f₁ : ℝ → ℝ) (a b : ℝ)
    (hbelow : BddBelow (imageOn f₁ a b)) :
    ∀ x ∈ Set.Ioo a b, lowerValue f₁ a b ≤ f₁ x := by
  intro x hx
  apply csInf_le hbelow
  exact ⟨x, hx, rfl⟩

/-- Exercise 399, gap 2; restrict the point to the common interval. -/
theorem gap2 (f₁ : ℝ → ℝ) (a b : ℝ)
    (habove : BddAbove (imageOn f₁ a b)) :
    ∀ x ∈ Set.Ioo a b, f₁ x ≤ upperValue f₁ a b := by
  intro x hx
  apply le_csSup habove
  exact ⟨x, hx, rfl⟩

/-- Exercise 399, gap 3; restrict the point to the common interval. -/
theorem gap3 (f₂ : ℝ → ℝ) (a b : ℝ)
    (hbelow : BddBelow (imageOn f₂ a b)) :
    ∀ x ∈ Set.Ioo a b, lowerValue f₂ a b ≤ f₂ x := by
  intro x hx
  apply csInf_le hbelow
  exact ⟨x, hx, rfl⟩

/-- Exercise 399, gap 4; restrict the point to the common interval. -/
theorem gap4 (f₂ : ℝ → ℝ) (a b : ℝ)
    (habove : BddAbove (imageOn f₂ a b)) :
    ∀ x ∈ Set.Ioo a b, f₂ x ≤ upperValue f₂ a b := by
  intro x hx
  apply le_csSup habove
  exact ⟨x, hx, rfl⟩

/-- Exercise 399, gap 5; restrict the point to the common interval. -/
theorem gap5 (f₁ f₂ : ℝ → ℝ) (a b : ℝ)
    (hbelow₁ : BddBelow (imageOn f₁ a b))
    (hbelow₂ : BddBelow (imageOn f₂ a b)) :
    ∀ x ∈ Set.Ioo a b,
      lowerValue f₁ a b + lowerValue f₂ a b ≤ f₁ x + f₂ x := by
  intro x hx
  exact add_le_add (gap1 f₁ a b hbelow₁ x hx) (gap3 f₂ a b hbelow₂ x hx)

/-- Exercise 399, gap 6; add the boundedness/nonempty hypotheses needed by real `sInf`. -/
theorem gap6 (f₁ f₂ : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hbelow₁ : BddBelow (imageOn f₁ a b))
    (hbelow₂ : BddBelow (imageOn f₂ a b)) :
    lowerValue f₁ a b + lowerValue f₂ a b ≤
      lowerValue (sumFn f₁ f₂) a b := by
  apply le_csInf
  · refine ⟨sumFn f₁ f₂ ((a + b) / 2), ?_⟩
    refine ⟨(a + b) / 2, ?_, rfl⟩
    constructor <;> linarith
  · intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact gap5 f₁ f₂ a b hbelow₁ hbelow₂ x hx

/-- Exercise 399, gap 7; restrict the point to the common interval. -/
theorem gap7 (f₁ f₂ : ℝ → ℝ) (a b : ℝ)
    (habove₁ : BddAbove (imageOn f₁ a b))
    (habove₂ : BddAbove (imageOn f₂ a b)) :
    ∀ x ∈ Set.Ioo a b,
      f₁ x + f₂ x ≤ upperValue f₁ a b + upperValue f₂ a b := by
  intro x hx
  exact add_le_add (gap2 f₁ a b habove₁ x hx) (gap4 f₂ a b habove₂ x hx)

/-- Exercise 399, gap 8; add the boundedness/nonempty hypotheses needed by real `sSup`. -/
theorem gap8 (f₁ f₂ : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (habove₁ : BddAbove (imageOn f₁ a b))
    (habove₂ : BddAbove (imageOn f₂ a b)) :
    upperValue (sumFn f₁ f₂) a b ≤
      upperValue f₁ a b + upperValue f₂ a b := by
  apply csSup_le
  · refine ⟨sumFn f₁ f₂ ((a + b) / 2), ?_⟩
    refine ⟨(a + b) / 2, ?_, rfl⟩
    constructor <;> linarith
  · intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact gap7 f₁ f₂ a b habove₁ habove₂ x hx

/-- Exercise 399, gap 9; replace vacuous “is real” premises by actual boundedness. -/
theorem gap9 (f₁ f₂ : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hmono₁ : MonotoneOn f₁ (Set.Ioo a b))
    (hmono₂ : MonotoneOn f₂ (Set.Ioo a b))
    (hbelow₁ : BddBelow (imageOn f₁ a b))
    (hbelow₂ : BddBelow (imageOn f₂ a b)) :
    lowerValue (sumFn f₁ f₂) a b =
      lowerValue f₁ a b + lowerValue f₂ a b := by
  have hm : (a + b) / 2 ∈ Set.Ioo a b := by
    constructor <;> linarith
  have hne₁ : (imageOn f₁ a b).Nonempty :=
    ⟨f₁ ((a + b) / 2), ⟨(a + b) / 2, hm, rfl⟩⟩
  have hne₂ : (imageOn f₂ a b).Nonempty :=
    ⟨f₂ ((a + b) / 2), ⟨(a + b) / 2, hm, rfl⟩⟩
  have hbelowSum : BddBelow (imageOn (sumFn f₁ f₂) a b) := by
    refine ⟨lowerValue f₁ a b + lowerValue f₂ a b, ?_⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact gap5 f₁ f₂ a b hbelow₁ hbelow₂ x hx
  apply le_antisymm
  · by_contra hnot
    have hstrict :
        lowerValue f₁ a b + lowerValue f₂ a b <
          lowerValue (sumFn f₁ f₂) a b := lt_of_not_ge hnot
    let δ : ℝ :=
      (lowerValue (sumFn f₁ f₂) a b -
        (lowerValue f₁ a b + lowerValue f₂ a b)) / 4
    have hδ : 0 < δ := by
      dsimp [δ]
      linarith
    have hex₁ : ∃ y ∈ imageOn f₁ a b, y < lowerValue f₁ a b + δ := by
      by_contra hn
      have hall : ∀ y ∈ imageOn f₁ a b, lowerValue f₁ a b + δ ≤ y := by
        intro y hy
        exact le_of_not_gt (fun hlt => hn ⟨y, hy, hlt⟩)
      have hbad : lowerValue f₁ a b + δ ≤ lowerValue f₁ a b := by
        exact le_csInf hne₁ hall
      linarith
    have hex₂ : ∃ y ∈ imageOn f₂ a b, y < lowerValue f₂ a b + δ := by
      by_contra hn
      have hall : ∀ y ∈ imageOn f₂ a b, lowerValue f₂ a b + δ ≤ y := by
        intro y hy
        exact le_of_not_gt (fun hlt => hn ⟨y, hy, hlt⟩)
      have hbad : lowerValue f₂ a b + δ ≤ lowerValue f₂ a b := by
        exact le_csInf hne₂ hall
      linarith
    rcases hex₁ with ⟨_, ⟨x₁, hx₁, rfl⟩, hclose₁⟩
    rcases hex₂ with ⟨_, ⟨x₂, hx₂, rfl⟩, hclose₂⟩
    have hx : min x₁ x₂ ∈ Set.Ioo a b := by
      constructor
      · exact lt_min hx₁.1 hx₂.1
      · exact lt_of_le_of_lt (min_le_left x₁ x₂) hx₁.2
    have hf₁ : f₁ (min x₁ x₂) ≤ f₁ x₁ :=
      hmono₁ hx hx₁ (min_le_left x₁ x₂)
    have hf₂ : f₂ (min x₁ x₂) ≤ f₂ x₂ :=
      hmono₂ hx hx₂ (min_le_right x₁ x₂)
    have hsum :=
      gap1 (sumFn f₁ f₂) a b hbelowSum (min x₁ x₂) hx
    dsimp [sumFn] at hsum
    dsimp [δ] at hδ hclose₁ hclose₂ ⊢
    nlinarith
  · exact gap6 f₁ f₂ a b hab hbelow₁ hbelow₂

/-- Exercise 399, gap 10; replace vacuous “is real” premises by actual boundedness. -/
theorem gap10 (f₁ f₂ : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hmono₁ : MonotoneOn f₁ (Set.Ioo a b))
    (hmono₂ : MonotoneOn f₂ (Set.Ioo a b))
    (habove₁ : BddAbove (imageOn f₁ a b))
    (habove₂ : BddAbove (imageOn f₂ a b)) :
    upperValue (sumFn f₁ f₂) a b =
      upperValue f₁ a b + upperValue f₂ a b := by
  have hm : (a + b) / 2 ∈ Set.Ioo a b := by
    constructor <;> linarith
  have hne₁ : (imageOn f₁ a b).Nonempty :=
    ⟨f₁ ((a + b) / 2), ⟨(a + b) / 2, hm, rfl⟩⟩
  have hne₂ : (imageOn f₂ a b).Nonempty :=
    ⟨f₂ ((a + b) / 2), ⟨(a + b) / 2, hm, rfl⟩⟩
  have haboveSum : BddAbove (imageOn (sumFn f₁ f₂) a b) := by
    refine ⟨upperValue f₁ a b + upperValue f₂ a b, ?_⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact gap7 f₁ f₂ a b habove₁ habove₂ x hx
  apply le_antisymm
  · exact gap8 f₁ f₂ a b hab habove₁ habove₂
  · by_contra hnot
    have hstrict :
        upperValue (sumFn f₁ f₂) a b <
          upperValue f₁ a b + upperValue f₂ a b := lt_of_not_ge hnot
    let δ : ℝ :=
      (upperValue f₁ a b + upperValue f₂ a b -
        upperValue (sumFn f₁ f₂) a b) / 4
    have hδ : 0 < δ := by
      dsimp [δ]
      linarith
    have hex₁ : ∃ y ∈ imageOn f₁ a b, upperValue f₁ a b - δ < y := by
      by_contra hn
      have hall : ∀ y ∈ imageOn f₁ a b, y ≤ upperValue f₁ a b - δ := by
        intro y hy
        exact le_of_not_gt (fun hgt => hn ⟨y, hy, hgt⟩)
      have hbad : upperValue f₁ a b ≤ upperValue f₁ a b - δ := by
        exact csSup_le hne₁ hall
      linarith
    have hex₂ : ∃ y ∈ imageOn f₂ a b, upperValue f₂ a b - δ < y := by
      by_contra hn
      have hall : ∀ y ∈ imageOn f₂ a b, y ≤ upperValue f₂ a b - δ := by
        intro y hy
        exact le_of_not_gt (fun hgt => hn ⟨y, hy, hgt⟩)
      have hbad : upperValue f₂ a b ≤ upperValue f₂ a b - δ := by
        exact csSup_le hne₂ hall
      linarith
    rcases hex₁ with ⟨_, ⟨x₁, hx₁, rfl⟩, hclose₁⟩
    rcases hex₂ with ⟨_, ⟨x₂, hx₂, rfl⟩, hclose₂⟩
    have hx : max x₁ x₂ ∈ Set.Ioo a b := by
      constructor
      · exact lt_of_lt_of_le hx₁.1 (le_max_left x₁ x₂)
      · exact max_lt hx₁.2 hx₂.2
    have hf₁ : f₁ x₁ ≤ f₁ (max x₁ x₂) :=
      hmono₁ hx₁ hx (le_max_left x₁ x₂)
    have hf₂ : f₂ x₂ ≤ f₂ (max x₁ x₂) :=
      hmono₂ hx₂ hx (le_max_right x₁ x₂)
    have hsum :=
      gap2 (sumFn f₁ f₂) a b haboveSum (max x₁ x₂) hx
    dsimp [sumFn] at hsum
    dsimp [δ] at hδ hclose₁ hclose₂ ⊢
    nlinarith

def f₁ (x : ℝ) : ℝ := x ^ 2
def f₂ (x : ℝ) : ℝ := -x ^ 2

/-- Exercise 399, gap 11; specialize the omitted counterexample interval to `(0,1)`. -/
theorem gap11 : lowerValue f₁ 0 1 = 0 := by
  have hne : (imageOn f₁ 0 1).Nonempty :=
    ⟨f₁ (1 / 2 : ℝ), ⟨(1 / 2 : ℝ), by norm_num, rfl⟩⟩
  have hbelow : BddBelow (imageOn f₁ 0 1) := by
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    simpa [f₁] using sq_nonneg x
  have hnonneg : 0 ≤ lowerValue f₁ 0 1 := by
    apply le_csInf hne
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    simpa [f₁] using sq_nonneg x
  apply le_antisymm
  · by_contra hnot
    have hpos : 0 < lowerValue f₁ 0 1 := lt_of_not_ge hnot
    by_cases hle : lowerValue f₁ 0 1 ≤ 1
    · have hx : lowerValue f₁ 0 1 / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith
      have hcs :
          lowerValue f₁ 0 1 ≤ f₁ (lowerValue f₁ 0 1 / 2) := by
        apply csInf_le hbelow
        exact ⟨lowerValue f₁ 0 1 / 2, hx, rfl⟩
      dsimp [f₁] at hcs
      nlinarith
    · have hx : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
      have hcs : lowerValue f₁ 0 1 ≤ f₁ (1 / 2 : ℝ) := by
        apply csInf_le hbelow
        exact ⟨(1 / 2 : ℝ), hx, rfl⟩
      norm_num [f₁] at hcs
      linarith
  · exact hnonneg

/-- Exercise 399, gap 12; specialize the omitted counterexample interval to `(0,1)`. -/
theorem gap12 : upperValue f₁ 0 1 = 1 := by
  have hne : (imageOn f₁ 0 1).Nonempty :=
    ⟨f₁ (1 / 2 : ℝ), ⟨(1 / 2 : ℝ), by norm_num, rfl⟩⟩
  have habove : BddAbove (imageOn f₁ 0 1) := by
    refine ⟨1, ?_⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hp : 0 < x * (1 - x) := mul_pos hx.1 (sub_pos.mpr hx.2)
    dsimp [f₁]
    nlinarith
  have hupper : upperValue f₁ 0 1 ≤ 1 := by
    apply csSup_le hne
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hp : 0 < x * (1 - x) := mul_pos hx.1 (sub_pos.mpr hx.2)
    dsimp [f₁]
    nlinarith
  apply le_antisymm
  · exact hupper
  · have hquarter : f₁ (1 / 2 : ℝ) ≤ upperValue f₁ 0 1 := by
      apply le_csSup habove
      exact ⟨(1 / 2 : ℝ), by norm_num, rfl⟩
    norm_num [f₁] at hquarter
    by_contra hnot
    have hlt : upperValue f₁ 0 1 < 1 := lt_of_not_ge hnot
    let x : ℝ := (upperValue f₁ 0 1 + 1) / 2
    have hx : x ∈ Set.Ioo (0 : ℝ) 1 := by
      dsimp [x]
      constructor <;> linarith
    have hle : f₁ x ≤ upperValue f₁ 0 1 := by
      apply le_csSup habove
      exact ⟨x, hx, rfl⟩
    have hs : 0 < (1 - upperValue f₁ 0 1) * (1 - upperValue f₁ 0 1) :=
      mul_pos (sub_pos.mpr hlt) (sub_pos.mpr hlt)
    dsimp [f₁, x] at hle
    nlinarith

/-- Exercise 399, gap 13; specialize the omitted counterexample interval to `(0,1)`. -/
theorem gap13 : lowerValue f₂ 0 1 = -1 := by
  have hne₁ : (imageOn f₁ 0 1).Nonempty :=
    ⟨f₁ (1 / 2 : ℝ), ⟨(1 / 2 : ℝ), by norm_num, rfl⟩⟩
  have hne₂ : (imageOn f₂ 0 1).Nonempty :=
    ⟨f₂ (1 / 2 : ℝ), ⟨(1 / 2 : ℝ), by norm_num, rfl⟩⟩
  have habove₁ : BddAbove (imageOn f₁ 0 1) := by
    refine ⟨1, ?_⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hp : 0 < x * (1 - x) := mul_pos hx.1 (sub_pos.mpr hx.2)
    dsimp [f₁]
    nlinarith
  have hbelow₂ : BddBelow (imageOn f₂ 0 1) := by
    refine ⟨-1, ?_⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hp : 0 < x * (1 - x) := mul_pos hx.1 (sub_pos.mpr hx.2)
    dsimp [f₂]
    nlinarith
  have hu : upperValue f₁ 0 1 ≤ -lowerValue f₂ 0 1 := by
    apply csSup_le hne₁
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hp := gap1 f₂ 0 1 hbelow₂ x hx
    dsimp [f₁, f₂] at hp ⊢
    linarith
  apply le_antisymm
  · rw [gap12] at hu
    linarith
  · apply le_csInf hne₂
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hp : 0 < x * (1 - x) := mul_pos hx.1 (sub_pos.mpr hx.2)
    dsimp [f₂]
    nlinarith

/-- Exercise 399, gap 14; specialize the omitted counterexample interval to `(0,1)`. -/
theorem gap14 : upperValue f₂ 0 1 = 0 := by
  have hne₁ : (imageOn f₁ 0 1).Nonempty :=
    ⟨f₁ (1 / 2 : ℝ), ⟨(1 / 2 : ℝ), by norm_num, rfl⟩⟩
  have hne₂ : (imageOn f₂ 0 1).Nonempty :=
    ⟨f₂ (1 / 2 : ℝ), ⟨(1 / 2 : ℝ), by norm_num, rfl⟩⟩
  have hbelow₁ : BddBelow (imageOn f₁ 0 1) := by
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    simpa [f₁] using sq_nonneg x
  have habove₂ : BddAbove (imageOn f₂ 0 1) := by
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    dsimp [f₂]
    exact neg_nonpos.mpr (sq_nonneg x)
  have hl : -upperValue f₂ 0 1 ≤ lowerValue f₁ 0 1 := by
    apply le_csInf hne₁
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hp := gap2 f₂ 0 1 habove₂ x hx
    dsimp [f₁, f₂] at hp ⊢
    linarith
  apply le_antisymm
  · apply csSup_le hne₂
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    dsimp [f₂]
    exact neg_nonpos.mpr (sq_nonneg x)
  · rw [gap11] at hl
    linarith

/-- Exercise 399, gap 15. -/
theorem gap15 : ∀ x, f₁ x + f₂ x = 0 := by
  intro x
  simp [f₁, f₂]

/-- Exercise 399, gap 16. -/
theorem gap16 :
    lowerValue (sumFn f₁ f₂) 0 1 = upperValue (sumFn f₁ f₂) 0 1 := by
  have himage : imageOn (sumFn f₁ f₂) 0 1 = {0} := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨x, hx, rfl⟩
      simp [sumFn, f₁, f₂]
    · intro hy
      have hy0 : y = 0 := by simpa using hy
      subst y
      refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
      simp [sumFn, f₁, f₂]
  simp [lowerValue, upperValue, himage]

/-- Exercise 399, gap 17. -/
theorem gap17 : upperValue (sumFn f₁ f₂) 0 1 = 0 := by
  have himage : imageOn (sumFn f₁ f₂) 0 1 = {0} := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨x, hx, rfl⟩
      simp [sumFn, f₁, f₂]
    · intro hy
      have hy0 : y = 0 := by simpa using hy
      subst y
      refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
      simp [sumFn, f₁, f₂]
  simp [upperValue, himage]

/-- Exercise 399, gap 18. -/
theorem gap18 : lowerValue (sumFn f₁ f₂) 0 1 = 0 := by
  calc
    lowerValue (sumFn f₁ f₂) 0 1 = upperValue (sumFn f₁ f₂) 0 1 := gap16
    _ = 0 := gap17

/-- Exercise 399, gap 19. -/
theorem gap19 :
    lowerValue (sumFn f₁ f₂) 0 1 >
      lowerValue f₁ 0 1 + lowerValue f₂ 0 1 := by
  rw [gap18, gap11, gap13]
  norm_num

/-- Exercise 399, gap 20. -/
theorem gap20 :
    upperValue (sumFn f₁ f₂) 0 1 <
      upperValue f₁ 0 1 + upperValue f₂ 0 1 := by
  rw [gap17, gap12, gap14]
  norm_num

/-- Exercise 399, gap 21. -/
theorem gap21 :
    lowerValue (sumFn f₁ f₂) 0 1 ≥
        lowerValue f₁ 0 1 + lowerValue f₂ 0 1 ∧
      upperValue (sumFn f₁ f₂) 0 1 ≤
        upperValue f₁ 0 1 + upperValue f₂ 0 1 := by
  exact ⟨le_of_lt gap19, le_of_lt gap20⟩

end

end ProofGap.Exercise399
