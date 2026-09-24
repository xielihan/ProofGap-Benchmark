import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3678

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ
  deriving DecidableEq

def objective (q : Point3) : ℝ :=
  q.x ^ 2 + 2 * q.y ^ 2 + 3 * q.z ^ 2

def ball : Set Point3 :=
  {q | q.x ^ 2 + q.y ^ 2 + q.z ^ 2 ≤ 100}

def P₀ : Point3 := ⟨0, 0, 0⟩
def P₁ : Point3 := ⟨10, 0, 0⟩
def P₂ : Point3 := ⟨-10, 0, 0⟩
def P₃ : Point3 := ⟨0, 10, 0⟩
def P₄ : Point3 := ⟨0, -10, 0⟩
def P₅ : Point3 := ⟨0, 0, 10⟩
def P₆ : Point3 := ⟨0, 0, -10⟩

private theorem objective_bounds_of_mem_ball {q : Point3} (hq : q ∈ ball) :
    0 ≤ objective q ∧ objective q ≤ 300 := by
  change q.x ^ 2 + q.y ^ 2 + q.z ^ 2 ≤ 100 at hq
  change 0 ≤ q.x ^ 2 + 2 * q.y ^ 2 + 3 * q.z ^ 2 ∧
    q.x ^ 2 + 2 * q.y ^ 2 + 3 * q.z ^ 2 ≤ 300
  have hx : 0 ≤ q.x ^ 2 := sq_nonneg q.x
  have hy : 0 ≤ q.y ^ 2 := sq_nonneg q.y
  have hz : 0 ≤ q.z ^ 2 := sq_nonneg q.z
  constructor <;> nlinarith

theorem gap1 :
    ∃ P : Point3, P = P₀ := by
  exact ⟨P₀, rfl⟩

theorem gap2 :
    ∃ P : Point3, P = P₁ := by
  exact ⟨P₁, rfl⟩

theorem gap3 :
    ∃ P : Point3, P = P₂ := by
  exact ⟨P₂, rfl⟩

theorem gap4 :
    ∃ P : Point3, P = P₃ := by
  exact ⟨P₃, rfl⟩

theorem gap5 :
    ∃ P : Point3, P = P₄ := by
  exact ⟨P₄, rfl⟩

theorem gap6 :
    ∃ P : Point3, P = P₅ := by
  exact ⟨P₅, rfl⟩

theorem gap7 :
    ∃ P : Point3, P = P₆ := by
  exact ⟨P₆, rfl⟩

theorem gap8 :
    objective P₀ = 0 := by
  norm_num [objective, P₀]

theorem gap9 :
    objective P₁ = objective P₂ := by
  norm_num [objective, P₁, P₂]

theorem gap10 :
    objective P₂ = 100 := by
  norm_num [objective, P₂]

theorem gap11 :
    objective P₁ = 100 := by
  calc
    objective P₁ = objective P₂ := gap9
    _ = 100 := gap10

theorem gap12 :
    objective P₃ = objective P₄ := by
  norm_num [objective, P₃, P₄]

theorem gap13 :
    objective P₄ = 200 := by
  norm_num [objective, P₄]

theorem gap14 :
    objective P₃ = 200 := by
  calc
    objective P₃ = objective P₄ := gap12
    _ = 200 := gap13

theorem gap15 :
    objective P₅ = objective P₆ := by
  norm_num [objective, P₅, P₆]

theorem gap16 :
    objective P₆ = 300 := by
  norm_num [objective, P₆]

theorem gap17 :
    objective P₅ = 300 := by
  calc
    objective P₅ = objective P₆ := gap15
    _ = 300 := gap16

theorem gap18 :
    sSup (objective '' ball) = 300 := by
  have hmem : 300 ∈ objective '' ball := by
    refine ⟨P₅, ?_, gap17⟩
    norm_num [ball, P₅]
  apply le_antisymm
  · refine csSup_le ⟨300, hmem⟩ ?_
    intro r hr
    rcases hr with ⟨q, hq, rfl⟩
    exact (objective_bounds_of_mem_ball hq).2
  · refine le_csSup ?_ hmem
    refine ⟨300, ?_⟩
    intro r hr
    rcases hr with ⟨q, hq, rfl⟩
    exact (objective_bounds_of_mem_ball hq).2

theorem gap19 :
    sInf (objective '' ball) = 0 := by
  have hmem : 0 ∈ objective '' ball := by
    refine ⟨P₀, ?_, gap8⟩
    norm_num [ball, P₀]
  apply le_antisymm
  · refine csInf_le ?_ hmem
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with ⟨q, hq, rfl⟩
    exact (objective_bounds_of_mem_ball hq).1
  · refine le_csInf ⟨0, hmem⟩ ?_
    intro r hr
    rcases hr with ⟨q, hq, rfl⟩
    exact (objective_bounds_of_mem_ball hq).1

end

end ProofGap.Exercise3678
