import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import Mathlib.Topology.Instances.Real.Lemmas

open Filter Topology

namespace ProofGap.Exercise78

noncomputable section

def x (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, ((i : ℝ) + 9) / (2 * (i : ℝ) - 1)

def Convergent (u : ℕ → ℝ) : Prop :=
  ∃ l : ℝ, Tendsto u atTop (𝓝 l)

private theorem x_pos (n : ℕ) : 0 < x n := by
  unfold x
  apply Finset.prod_pos
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hden : 0 < 2 * (i : ℝ) - 1 := by
    have : (1 : ℝ) ≤ i := by exact_mod_cast hi1
    linarith
  exact div_pos (by positivity) hden

private theorem x_succ (n : ℕ) :
    x (n + 1) = x n * ((((n + 1 : ℕ) : ℝ) + 9) /
      (2 * ((n + 1 : ℕ) : ℝ) - 1)) := by
  unfold x
  rw [Finset.prod_Icc_succ_top (by omega)]

/-- Exercise 78, gap 1; the source cutoff 10 is false. -/
theorem gap1 :
    ∀ n : ℕ, n < 9 → x (n + 1) > x n := by
  intro n hn
  rw [x_succ]
  have hnR : (n : ℝ) < 9 := by exact_mod_cast hn
  have hn1R : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos n
  have hden : 0 < 2 * (((n + 1 : ℕ) : ℝ)) - 1 := by linarith
  have hfac :
      1 < ((((n + 1 : ℕ) : ℝ) + 9) /
        (2 * (((n + 1 : ℕ) : ℝ)) - 1)) := by
    rw [one_lt_div hden]
    push_cast
    linarith
  simpa using mul_lt_mul_of_pos_left hfac (x_pos n)

/-- Exercise 78, gap 2. -/
theorem gap2 :
    ∀ n : ℕ, 10 < n → ((n : ℝ) + 9) / (2 * (n : ℝ) - 1) < 1 := by
  intro n hn
  have hnR : (10 : ℝ) < n := by exact_mod_cast hn
  rw [div_lt_one]
  · linarith
  · linarith

/-- Exercise 78, gap 3. -/
theorem gap3 :
    ∀ n : ℕ, 10 < n → x (n + 1) < x n := by
  intro n hn
  rw [x_succ]
  have hfac := gap2 (n + 1) (by omega)
  have hn1R : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos n
  have hden : 0 < 2 * (((n + 1 : ℕ) : ℝ)) - 1 := by linarith
  have hfacpos :
      0 < ((((n + 1 : ℕ) : ℝ) + 9) /
        (2 * (((n + 1 : ℕ) : ℝ)) - 1)) := by positivity
  simpa using mul_lt_mul_of_pos_left hfac (x_pos n)

/-- Exercise 78, gap 4. -/
theorem gap4 :
    ∀ n : ℕ, 0 < n → 0 < x n := by
  intro n _
  exact x_pos n

/-- Exercise 78, gap 5. -/
theorem gap5 :
    BddBelow (Set.range x) := by
  refine ⟨0, ?_⟩
  intro y hy
  rcases hy with ⟨n, rfl⟩
  exact (x_pos n).le

/-- Exercise 78, gap 6. -/
theorem gap6
    (hdec : ∀ n : ℕ, 10 < n → x (n + 1) ≤ x n)
    (hbelow : BddBelow (Set.range x)) :
    Convergent x := by
  have hanti : AntitoneOn x (Set.Ici 11) := by
    apply antitoneOn_nat_Ici_of_succ_le
    intro n hn
    exact hdec n (by omega)
  have hbelow' : BddBelow (x '' Set.Ici 11) := by
    rcases hbelow with ⟨l, hl⟩
    refine ⟨l, ?_⟩
    intro y hy
    rcases hy with ⟨n, _, rfl⟩
    exact hl ⟨n, rfl⟩
  exact ⟨sInf (x '' Set.Ici 11),
    Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici hanti hbelow'⟩

/-- Exercise 78, gap 7. -/
theorem gap7
    (hconv : Convergent x) :
    Convergent x := by
  exact hconv

end

end ProofGap.Exercise78
