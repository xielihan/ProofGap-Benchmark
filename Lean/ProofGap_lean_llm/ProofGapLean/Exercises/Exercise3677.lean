import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3677

noncomputable section

def objective (q : ℝ × ℝ) : ℝ :=
  q.1 ^ 2 - q.1 * q.2 + q.2 ^ 2

def diamond : Set (ℝ × ℝ) :=
  {q | |q.1| + |q.2| ≤ 1}

def interiorCritical (q : ℝ × ℝ) : Prop :=
  2 * q.1 - q.2 = 0 ∧ 2 * q.2 - q.1 = 0 ∧
    |q.1| + |q.2| < 1

def edgeCritical (q : ℝ × ℝ) (lambda : ℝ) : Prop :=
  2 * q.1 - q.2 - lambda = 0 ∧
    2 * q.2 - q.1 - lambda = 0 ∧
    q.1 + q.2 = 1

def P₀ : ℝ × ℝ := (0, 0)
def P₁ : ℝ × ℝ := (1 / 2, 1 / 2)
def P₂ : ℝ × ℝ := (1 / 2, -1 / 2)
def P₃ : ℝ × ℝ := (-1 / 2, 1 / 2)
def P₄ : ℝ × ℝ := (-1 / 2, -1 / 2)
def P₅ : ℝ × ℝ := (1, 0)
def P₆ : ℝ × ℝ := (0, 1)
def P₇ : ℝ × ℝ := (-1, 0)
def P₈ : ℝ × ℝ := (0, -1)

theorem gap1 :
    {q | interiorCritical q} = ({P₀} : Set (ℝ × ℝ)) := by
  apply Set.ext
  intro q
  change interiorCritical q ↔ q = P₀
  constructor
  · intro h
    change 2 * q.1 - q.2 = 0 ∧ 2 * q.2 - q.1 = 0 ∧ |q.1| + |q.2| < 1 at h
    rcases h with ⟨h₁, h₂, h₃⟩
    have hx : q.1 = 0 := by linarith
    have hy : q.2 = 0 := by linarith
    apply Prod.ext
    · simpa [P₀] using hx
    · simpa [P₀] using hy
  · intro h
    subst q
    norm_num [interiorCritical, P₀]

theorem gap2 :
    interiorCritical P₀ := by
  norm_num [interiorCritical, P₀]

theorem gap3 :
    objective P₀ = 0 := by
  norm_num [objective, P₀]

theorem gap4 :
    {q | ∃ lambda, edgeCritical q lambda} =
      ({P₁} : Set (ℝ × ℝ)) := by
  apply Set.ext
  intro q
  change (∃ lambda, edgeCritical q lambda) ↔ q = P₁
  constructor
  · intro h
    rcases h with ⟨lambda, h⟩
    change 2 * q.1 - q.2 - lambda = 0 ∧
      2 * q.2 - q.1 - lambda = 0 ∧ q.1 + q.2 = 1 at h
    rcases h with ⟨h₁, h₂, h₃⟩
    have hx : q.1 = (1 / 2 : ℝ) := by linarith
    have hy : q.2 = (1 / 2 : ℝ) := by linarith
    apply Prod.ext
    · simpa [P₁] using hx
    · simpa [P₁] using hy
  · intro h
    subst q
    refine ⟨(1 / 2 : ℝ), ?_⟩
    norm_num [edgeCritical, P₁]

theorem gap5 :
    ∃ lambda, edgeCritical P₁ lambda := by
  refine ⟨(1 / 2 : ℝ), ?_⟩
  norm_num [edgeCritical, P₁]

theorem gap6 :
    objective P₁ = 1 / 4 := by
  norm_num [objective, P₁]

theorem gap7 :
    ∃ P : ℝ × ℝ, P = P₂ := by
  exact ⟨P₂, rfl⟩

theorem gap8 :
    ∃ P : ℝ × ℝ, P = P₃ := by
  exact ⟨P₃, rfl⟩

theorem gap9 :
    ∃ P : ℝ × ℝ, P = P₄ := by
  exact ⟨P₄, rfl⟩

theorem gap10 :
    objective P₂ = objective P₃ := by
  norm_num [objective, P₂, P₃]

theorem gap11 :
    objective P₃ = 3 / 4 := by
  norm_num [objective, P₃]

theorem gap12 :
    objective P₂ = 3 / 4 := by
  exact gap10.trans gap11

theorem gap13 :
    objective P₄ = 1 / 4 := by
  norm_num [objective, P₄]

theorem gap14 :
    ∃ P : ℝ × ℝ, P = P₅ := by
  exact ⟨P₅, rfl⟩

theorem gap15 :
    ∃ P : ℝ × ℝ, P = P₆ := by
  exact ⟨P₆, rfl⟩

theorem gap16 :
    ∃ P : ℝ × ℝ, P = P₇ := by
  exact ⟨P₇, rfl⟩

theorem gap17 :
    ∃ P : ℝ × ℝ, P = P₈ := by
  exact ⟨P₈, rfl⟩

theorem gap18 :
    objective P₅ = objective P₆ := by
  norm_num [objective, P₅, P₆]

theorem gap19 :
    objective P₆ = objective P₇ := by
  norm_num [objective, P₆, P₇]

theorem gap20 :
    objective P₇ = objective P₈ := by
  norm_num [objective, P₇, P₈]

theorem gap21 :
    objective P₈ = 1 := by
  norm_num [objective, P₈]

theorem gap22 :
    objective P₅ = 1 := by
  exact gap18.trans (gap19.trans (gap20.trans gap21))

theorem gap23 :
    sSup (objective '' diamond) = 1 := by
  have hub : ∀ z ∈ objective '' diamond, z ≤ (1 : ℝ) := by
    intro z hz
    rcases hz with ⟨q, hq, rfl⟩
    change |q.1| + |q.2| ≤ 1 at hq
    have hsum_nonneg : 0 ≤ |q.1| + |q.2| :=
      add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hplus : 0 ≤ 1 + (|q.1| + |q.2|) := by linarith
    have hmul :
        0 ≤ (1 - (|q.1| + |q.2|)) * (1 + (|q.1| + |q.2|)) :=
      mul_nonneg (sub_nonneg.mpr hq) hplus
    have hsum_sq : (|q.1| + |q.2|) ^ 2 ≤ 1 := by
      nlinarith
    have hxy : -(q.1 * q.2) ≤ |q.1| * |q.2| := by
      rw [← abs_mul]
      exact neg_le_abs _
    have hab : 0 ≤ |q.1| * |q.2| :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hx_sq : |q.1| ^ 2 = q.1 ^ 2 := sq_abs q.1
    have hy_sq : |q.2| ^ 2 = q.2 ^ 2 := sq_abs q.2
    unfold objective
    nlinarith
  have hmem : (1 : ℝ) ∈ objective '' diamond := by
    refine ⟨P₅, ?_, ?_⟩
    · norm_num [diamond, P₅]
    · exact gap22
  have hbdd : BddAbove (objective '' diamond) := ⟨1, hub⟩
  apply le_antisymm
  · exact csSup_le ⟨1, hmem⟩ hub
  · exact le_csSup hbdd hmem

theorem gap24 :
    sInf (objective '' diamond) = 0 := by
  have hlower : ∀ z ∈ objective '' diamond, (0 : ℝ) ≤ z := by
    intro z hz
    rcases hz with ⟨q, hq, rfl⟩
    unfold objective
    nlinarith [sq_nonneg (q.1 - q.2), sq_nonneg q.1, sq_nonneg q.2]
  have hmem : (0 : ℝ) ∈ objective '' diamond := by
    refine ⟨P₀, ?_, ?_⟩
    · norm_num [diamond, P₀]
    · exact gap3
  have hbdd : BddBelow (objective '' diamond) := ⟨0, hlower⟩
  apply le_antisymm
  · exact csInf_le hbdd hmem
  · exact le_csInf ⟨0, hmem⟩ hlower

end

end ProofGap.Exercise3677
