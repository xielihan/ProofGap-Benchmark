import ProofGapLean.Prelude.Sequences

open Filter Topology

noncomputable section

namespace ProofGap.Exercise120

def x (a b : ℝ) (n : ℕ) : ℝ :=
  (a + b + (-1 : ℝ) ^ n * (a - b)) / 2

private theorem x_mem (a b : ℝ) (n : ℕ) :
    x a b n ∈ ({a, b} : Set ℝ) := by
  rcases neg_one_pow_eq_or ℝ n with h | h
  · left
    simp [x, h]
  · right
    simp [x, h]
    ring

private theorem a_mem_cluster (a b : ℝ) :
    a ∈ ProofGap.ClusterSet (x a b) := by
  let p : ℕ → ℕ := fun k => 2 * k
  have hp : StrictMono p := by
    intro m n hmn
    dsimp [p]
    omega
  refine ⟨p, hp, ?_⟩
  apply tendsto_const_nhds.congr'
  filter_upwards with k
  dsimp [p, Function.comp_apply]
  simp [x, pow_mul]

private theorem b_mem_cluster (a b : ℝ) :
    b ∈ ProofGap.ClusterSet (x a b) := by
  let p : ℕ → ℕ := fun k => 2 * k + 1
  have hp : StrictMono p := by
    intro m n hmn
    dsimp [p]
    omega
  refine ⟨p, hp, ?_⟩
  apply tendsto_const_nhds.congr'
  filter_upwards with k
  dsimp [p, Function.comp_apply]
  simp [x, pow_add, pow_mul]
  ring

/-- Source: `proof_gap/exercise_120/1.txt`. -/
theorem gap1 (a b : ℝ) :
    ProofGap.ClusterSet (x a b) = ({a, b} : Set ℝ) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨p, hp, hlim⟩
    exact (isClosed_singleton.union isClosed_singleton).mem_of_tendsto hlim
      (Filter.Eventually.of_forall fun k => x_mem a b (p k))
  · intro hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hya | hyb
    · rw [hya]
      exact a_mem_cluster a b
    · rw [hyb]
      exact b_mem_cluster a b

end ProofGap.Exercise120
