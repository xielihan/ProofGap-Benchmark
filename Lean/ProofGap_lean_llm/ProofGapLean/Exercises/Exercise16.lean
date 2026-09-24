import ProofGapLean.Prelude.Core
import Mathlib.Data.Real.Archimedean

/-!
# Exercise 16

Semantic formalization of `proof_gap/exercise_16/{1,...,10}.txt`.
The source set consists exactly of rational numbers strictly between zero and
one.
-/

namespace ProofGap.Exercise16

def E : Set ℚ :=
  {x | 0 < x ∧ x < 1}

/-- The rational set embedded into `ℝ`, where supremum and infimum exist. -/
def EReal : Set ℝ :=
  (fun q : ℚ => (q : ℝ)) '' E

def maximumPoints (S : Set ℚ) : Set ℚ :=
  {a | a ∈ S ∧ ∀ b : ℚ, b ∈ S → b ≤ a}

def minimumPoints (S : Set ℚ) : Set ℚ :=
  {a | a ∈ S ∧ ∀ b : ℚ, b ∈ S → a ≤ b}

def RaiseFraction : Prop :=
  ∀ m n : ℕ, (m : ℚ) / (n : ℚ) ∈ E →
    ((m + 1 : ℕ) : ℚ) / ((n + 1 : ℕ) : ℚ) ∈ E

def RaiseFractionStrictly : Prop :=
  ∀ m n : ℕ, (m : ℚ) / (n : ℚ) ∈ E →
    (m : ℚ) / (n : ℚ) <
      ((m + 1 : ℕ) : ℚ) / ((n + 1 : ℕ) : ℚ)

def SquareFraction : Prop :=
  ∀ m n : ℕ, (m : ℚ) / (n : ℚ) ∈ E →
    (m : ℚ) ^ 2 / (n : ℚ) ^ 2 ∈ E

def SquareFractionStrictlyLower : Prop :=
  ∀ m n : ℕ, (m : ℚ) / (n : ℚ) ∈ E →
    (m : ℚ) ^ 2 / (n : ℚ) ^ 2 < (m : ℚ) / (n : ℚ)

def NoMaximum : Prop :=
  ¬ ∃ a : ℚ, a ∈ E ∧ ∀ b : ℚ, b ∈ E → b ≤ a

def NoMinimum : Prop :=
  ¬ ∃ a : ℚ, a ∈ E ∧ ∀ b : ℚ, b ∈ E → a ≤ b

/-- Source: `proof_gap/exercise_16/1.txt`. -/
theorem gap1 : RaiseFraction := by
  intro m n hmem
  rcases hmem with ⟨hpos, hlt⟩
  have hn : 0 < n := by
    by_contra hnpos
    have hnzero : n = 0 := by omega
    subst n
    norm_num at hpos
  have hnq : 0 < (n : ℚ) := by exact_mod_cast hn
  have hmnq : (m : ℚ) < n := (div_lt_one hnq).mp hlt
  have hmn : m < n := by exact_mod_cast hmnq
  constructor
  · positivity
  · norm_num only [Nat.cast_add, Nat.cast_one]
    apply (div_lt_one (by positivity : (0 : ℚ) < n + 1)).2
    exact_mod_cast Nat.add_lt_add_right hmn 1

/-- Source: `proof_gap/exercise_16/2.txt`. -/
theorem gap2
    (h1 : RaiseFraction) :
    RaiseFractionStrictly := by
  intro m n hmem
  rcases hmem with ⟨hpos, hlt⟩
  have hn : 0 < n := by
    by_contra hnpos
    have hnzero : n = 0 := by omega
    subst n
    norm_num at hpos
  have hnq : 0 < (n : ℚ) := by exact_mod_cast hn
  have hmn : (m : ℚ) < n := (div_lt_one hnq).mp hlt
  norm_num only [Nat.cast_add, Nat.cast_one]
  rw [div_lt_div_iff₀ hnq (by positivity : (0 : ℚ) < n + 1)]
  norm_num
  nlinarith

/-- Source: `proof_gap/exercise_16/3.txt`. -/
theorem gap3
    (h1 : RaiseFraction)
    (h2 : RaiseFractionStrictly) :
    SquareFraction := by
  intro m n hmem
  rcases hmem with ⟨hpos, hlt⟩
  rw [← div_pow]
  constructor
  · positivity
  · have hsq_lt :
        ((m : ℚ) / (n : ℚ)) ^ 2 < (m : ℚ) / (n : ℚ) := by
      nlinarith [mul_pos hpos (sub_pos.mpr hlt)]
    exact hsq_lt.trans hlt

/-- Source: `proof_gap/exercise_16/4.txt`. -/
theorem gap4
    (h1 : RaiseFraction)
    (h2 : RaiseFractionStrictly)
    (h3 : SquareFraction) :
    SquareFractionStrictlyLower := by
  intro m n hmem
  rcases hmem with ⟨hpos, hlt⟩
  rw [← div_pow]
  nlinarith [mul_pos hpos (sub_pos.mpr hlt)]

/-- Source: `proof_gap/exercise_16/5.txt`. -/
theorem gap5
    (h1 : RaiseFraction)
    (h2 : RaiseFractionStrictly) :
    NoMaximum := by
  rintro ⟨a, ha, hgreatest⟩
  let b : ℚ := (a + 1) / 2
  have hb : b ∈ E := by
    constructor <;> dsimp [b] <;> linarith [ha.1, ha.2]
  have hab : a < b := by
    dsimp [b]
    linarith [ha.2]
  exact (not_lt_of_ge (hgreatest b hb)) hab

/-- Source: `proof_gap/exercise_16/6.txt`. -/
theorem gap6
    (h3 : SquareFraction)
    (h4 : SquareFractionStrictlyLower) :
    NoMinimum := by
  rintro ⟨a, ha, hleast⟩
  let b : ℚ := a / 2
  have hb : b ∈ E := by
    constructor <;> dsimp [b] <;> linarith [ha.1, ha.2]
  have hba : b < a := by
    dsimp [b]
    linarith [ha.1]
  exact (not_lt_of_ge (hleast b hb)) hba

/-- Source: `proof_gap/exercise_16/7.txt`. -/
theorem gap7
    (h5 : NoMaximum) :
    maximumPoints E = ∅ := by
  ext a
  simp only [Set.mem_empty_iff_false, iff_false]
  intro ha
  exact h5 ⟨a, ha.1, ha.2⟩

/-- Source: `proof_gap/exercise_16/8.txt`. -/
theorem gap8
    (h6 : NoMinimum) :
    minimumPoints E = ∅ := by
  ext a
  simp only [Set.mem_empty_iff_false, iff_false]
  intro ha
  exact h6 ⟨a, ha.1, ha.2⟩

/-- Source: `proof_gap/exercise_16/9.txt`. -/
theorem gap9
    (h5 : NoMaximum)
    (h7 : maximumPoints E = ∅) :
    sSup EReal = 1 := by
  have hne : EReal.Nonempty := by
    refine ⟨((1 / 2 : ℚ) : ℝ), 1 / 2, ?_, rfl⟩
    constructor <;> norm_num
  have hlub : IsLUB EReal (1 : ℝ) := by
    constructor
    · intro x hx
      rcases hx with ⟨q, hq, rfl⟩
      change (q : ℝ) ≤ 1
      exact_mod_cast hq.2.le
    · intro M hupper
      by_contra hnot
      have hMlt : M < 1 := lt_of_not_ge hnot
      have hmax : max M 0 < (1 : ℝ) := max_lt hMlt zero_lt_one
      rcases exists_rat_btwn hmax with ⟨q, hqmax, hqone⟩
      have hqzero : (0 : ℝ) < q :=
        (le_max_right M 0).trans_lt hqmax
      have hqE : q ∈ E := by
        constructor
        · exact_mod_cast hqzero
        · exact_mod_cast hqone
      have hqreal : (q : ℝ) ∈ EReal := ⟨q, hqE, rfl⟩
      have hqle := hupper hqreal
      linarith [lt_of_le_of_lt (le_max_left M 0) hqmax]
  exact hlub.csSup_eq hne

/-- Source: `proof_gap/exercise_16/10.txt`. -/
theorem gap10
    (h6 : NoMinimum)
    (h8 : minimumPoints E = ∅)
    (h9 : sSup EReal = 1) :
    sInf EReal = 0 := by
  have hne : EReal.Nonempty := by
    refine ⟨((1 / 2 : ℚ) : ℝ), 1 / 2, ?_, rfl⟩
    constructor <;> norm_num
  have hglb : IsGLB EReal (0 : ℝ) := by
    constructor
    · intro x hx
      rcases hx with ⟨q, hq, rfl⟩
      change (0 : ℝ) ≤ (q : ℝ)
      exact_mod_cast hq.1.le
    · intro M hlower
      by_contra hnot
      have hMpos : 0 < M := lt_of_not_ge hnot
      have hmin : (0 : ℝ) < min M 1 := lt_min hMpos zero_lt_one
      rcases exists_rat_btwn hmin with ⟨q, hqzero, hqmin⟩
      have hqone : (q : ℝ) < 1 :=
        hqmin.trans_le (min_le_right M 1)
      have hqE : q ∈ E := by
        constructor
        · exact_mod_cast hqzero
        · exact_mod_cast hqone
      have hqreal : (q : ℝ) ∈ EReal := ⟨q, hqE, rfl⟩
      have hMle := hlower hqreal
      linarith [hqmin.trans_le (min_le_left M 1)]
  exact hglb.csInf_eq hne

end ProofGap.Exercise16
