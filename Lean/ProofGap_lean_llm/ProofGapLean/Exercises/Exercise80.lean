import ProofGapLean.Prelude.Analysis
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Topology.Instances.Real.Lemmas

open Filter Topology

namespace ProofGap.Exercise80

noncomputable section

def x (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, (1 + 1 / (2 : ℝ) ^ i)

def expProduct (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, Real.exp (1 / (2 : ℝ) ^ i)

def exponentSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, 1 / (2 : ℝ) ^ i

def Convergent (u : ℕ → ℝ) : Prop :=
  ∃ l : ℝ, Tendsto u atTop (𝓝 l)

/-- Source: `proof_gap/exercise_80/1.txt`; the product is explicit. -/
theorem gap1 : ∀ n : ℕ, x (n + 1) = x n * (1 + 1 / (2 : ℝ) ^ (n + 1)) := by
  intro n
  unfold x
  rw [Finset.prod_Icc_succ_top (by omega)]

/-- Source: `proof_gap/exercise_80/2.txt`. -/
theorem gap2 : ∀ n : ℕ, x n * (1 + 1 / (2 : ℝ) ^ (n + 1)) > x n := by
  intro n
  have hx : 0 < x n := by
    unfold x
    positivity
  have hfac : 1 < 1 + 1 / (2 : ℝ) ^ (n + 1) := by
    have : 0 < 1 / (2 : ℝ) ^ (n + 1) := by positivity
    linarith
  simpa using mul_lt_mul_of_pos_left hfac hx

/-- Source: `proof_gap/exercise_80/3.txt`. -/
theorem gap3 : ∀ n : ℕ, x (n + 1) > x n := by
  intro n
  rw [gap1]
  exact gap2 n

/-- Source: `proof_gap/exercise_80/4.txt`. -/
theorem gap4 : Monotone x := by
  exact monotone_nat_of_le_succ fun n => (gap3 n).le

/-- Source: `proof_gap/exercise_80/5.txt`; equality at a=0 is excluded. -/
theorem gap5 : ∀ a : ℝ, a ≠ 0 → 1 + a < Real.exp a := by
  intro a ha
  simpa [add_comm] using Real.add_one_lt_exp ha

/-- Source: `proof_gap/exercise_80/6.txt`. -/
theorem gap6 : ∀ n : ℕ, 0 < x n := by
  intro n
  unfold x
  positivity

/-- Source: `proof_gap/exercise_80/7.txt`; the exponential product is explicit. -/
theorem gap7 : ∀ n : ℕ, 0 < n → x n < expProduct n := by
  intro n hn
  unfold x expProduct
  apply Finset.prod_lt_prod_of_nonempty
  · intro i hi
    positivity
  · intro i hi
    have hi1 : 0 < i := (Finset.mem_Icc.mp hi).1
    exact gap5 (1 / (2 : ℝ) ^ i) (by positivity)
  · exact ⟨1, Finset.mem_Icc.mpr ⟨by omega, hn⟩⟩

/-- Source: `proof_gap/exercise_80/8.txt`; both ellipses are finite. -/
theorem gap8 : ∀ n : ℕ, expProduct n = Real.exp (exponentSum n) := by
  intro n
  unfold expProduct exponentSum
  rw [Real.exp_sum]

/-- Source: `proof_gap/exercise_80/9.txt`. -/
theorem gap9 : ∀ n : ℕ, Real.exp (exponentSum n) < Real.exp 1 := by
  intro n
  rw [Real.exp_lt_exp]
  have hsum :
      exponentSum n =
        (((1 / 2 : ℝ) ^ 1 - (1 / 2 : ℝ) ^ (n + 1)) /
          (1 - (1 / 2 : ℝ))) := by
    unfold exponentSum
    rw [← Finset.Ico_add_one_right_eq_Icc]
    simpa only [one_div, inv_pow] using
      (geom_sum_Ico' (x := (1 / 2 : ℝ)) (m := 1) (n := n + 1)
        (by norm_num) (by omega))
  rw [hsum]
  have hpow : 0 < (1 / 2 : ℝ) ^ (n + 1) := by positivity
  norm_num
  linarith

/-- Source: `proof_gap/exercise_80/10.txt`. -/
theorem gap10 : 0 < Real.exp 1 := by
  positivity

/-- Source: `proof_gap/exercise_80/11.txt`. -/
theorem gap11 : Bornology.IsBounded (Set.range x) := by
  apply isBounded_iff_bddBelow_bddAbove.mpr
  constructor
  · refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨n, rfl⟩
    exact (gap6 n).le
  · refine ⟨Real.exp 1, ?_⟩
    intro y hy
    rcases hy with ⟨n, rfl⟩
    by_cases hn : n = 0
    · subst n
      norm_num [x]
    · exact le_of_lt <| lt_trans (gap7 n (Nat.pos_of_ne_zero hn))
        (by rw [gap8]; exact gap9 n)

/-- Source: `proof_gap/exercise_80/12.txt`. -/
theorem gap12
    (hmono : Monotone x)
    (hupper : BddAbove (Set.range x)) :
    Convergent x := by
  have himage : x '' Set.Ici 0 = Set.range x := by
    ext y
    constructor
    · rintro ⟨n, _, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, Nat.zero_le n, rfl⟩
  have hupper' : BddAbove (x '' Set.Ici 0) := by
    rwa [himage]
  refine ⟨sSup (Set.range x), ?_⟩
  have ht := Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici
    (k := 0) (hmono.monotoneOn (Set.Ici 0)) hupper'
  rwa [himage] at ht

/-- Source: `proof_gap/exercise_80/13.txt`. -/
theorem gap13 (hconv : Convergent x) : Convergent x := by
  exact hconv

end

end ProofGap.Exercise80
