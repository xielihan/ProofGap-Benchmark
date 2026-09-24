import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import Mathlib.Topology.Instances.Real.Lemmas

open Filter Topology

namespace ProofGap.Exercise79

noncomputable section

def x (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, (1 - 1 / (2 : ℝ) ^ i)

def Convergent (u : ℕ → ℝ) : Prop :=
  ∃ l : ℝ, Tendsto u atTop (𝓝 l)

private theorem x_pos (n : ℕ) : 0 < x n := by
  unfold x
  apply Finset.prod_pos
  intro i hi
  have hi1 : 0 < i := (Finset.mem_Icc.mp hi).1
  have hpow : 1 < (2 : ℝ) ^ i :=
    one_lt_pow₀ (by norm_num) (ne_of_gt hi1)
  have hinv : 1 / (2 : ℝ) ^ i < 1 :=
    (div_lt_one (by positivity)).mpr hpow
  linarith

/-- Source: `proof_gap/exercise_79/1.txt`; the product is explicit. -/
theorem gap1 :
    ∀ n : ℕ, x (n + 1) = x n * (1 - 1 / (2 : ℝ) ^ (n + 1)) := by
  intro n
  unfold x
  rw [Finset.prod_Icc_succ_top (by omega)]

/-- Source: `proof_gap/exercise_79/2.txt`. -/
theorem gap2 :
    ∀ n : ℕ, x n * (1 - 1 / (2 : ℝ) ^ (n + 1)) < x n := by
  intro n
  have hfac : 1 - 1 / (2 : ℝ) ^ (n + 1) < 1 := by
    have : 0 < 1 / (2 : ℝ) ^ (n + 1) := by positivity
    linarith
  simpa using mul_lt_mul_of_pos_left hfac (x_pos n)

/-- Source: `proof_gap/exercise_79/3.txt`. -/
theorem gap3 :
    ∀ n : ℕ, x (n + 1) < x n := by
  intro n
  rw [gap1]
  exact gap2 n

/-- Source: `proof_gap/exercise_79/4.txt`. -/
theorem gap4 :
    Antitone x := by
  exact antitone_nat_of_succ_le fun n => (gap3 n).le

/-- Source: `proof_gap/exercise_79/5.txt`. -/
theorem gap5 :
    ∀ n : ℕ, 0 < x n := by
  exact x_pos

/-- Source: `proof_gap/exercise_79/6.txt`; strictness starts at n=1. -/
theorem gap6 :
    ∀ n : ℕ, 0 < n → x n < 1 := by
  intro n hn
  have hx1 : x 1 < x 0 := gap3 0
  have hxn : x n ≤ x 1 := gap4 (by omega)
  have hchain := lt_of_le_of_lt hxn hx1
  simpa [x] using hchain

/-- Source: `proof_gap/exercise_79/7.txt`. -/
theorem gap7 :
    (0 : ℝ) < 1 := by
  norm_num

/-- Source: `proof_gap/exercise_79/8.txt`. -/
theorem gap8 :
    Bornology.IsBounded (Set.range x) := by
  apply isBounded_iff_bddBelow_bddAbove.mpr
  constructor
  · refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨n, rfl⟩
    exact (x_pos n).le
  · refine ⟨1, ?_⟩
    intro y hy
    rcases hy with ⟨n, rfl⟩
    have := gap4 (Nat.zero_le n)
    simpa [x] using this

/-- Source: `proof_gap/exercise_79/9.txt`. -/
theorem gap9
    (hmono : Antitone x)
    (hbelow : BddBelow (Set.range x)) :
    Convergent x := by
  have himage : x '' Set.Ici 0 = Set.range x := by
    ext y
    constructor
    · rintro ⟨n, _, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, Nat.zero_le n, rfl⟩
  have hbelow' : BddBelow (x '' Set.Ici 0) := by
    rwa [himage]
  refine ⟨sInf (Set.range x), ?_⟩
  have ht := Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici
    (k := 0) (hmono.antitoneOn (Set.Ici 0)) hbelow'
  rwa [himage] at ht

/-- Source: `proof_gap/exercise_79/10.txt`. -/
theorem gap10
    (hconv : Convergent x) :
    Convergent x := by
  exact hconv

end

end ProofGap.Exercise79
