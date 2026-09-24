import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace ProofGap.Exercise1241

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def Q (n : ℕ) (x : ℝ) : ℝ := (x + 1) ^ n * (x - 1) ^ n
def P (n : ℕ) (x : ℝ) : ℝ :=
  1 / ((2 : ℝ) ^ n * (Nat.factorial n : ℝ)) * iterDeriv n (Q n) x
def zeros (u : ℝ → ℝ) : Set ℝ := {x | u x = 0}

private theorem iteratedDeriv_add_pow (n k : ℕ) (a x : ℝ) :
    iteratedDeriv k (fun t : ℝ => (t + a) ^ n) x =
      (n.descFactorial k : ℝ) * (x + a) ^ (n - k) := by
  have h := congrFun
    (iteratedDeriv_comp_add_const k (fun z : ℝ => z ^ n) a) x
  simpa using h

private theorem iteratedDeriv_sub_pow (n k : ℕ) (a x : ℝ) :
    iteratedDeriv k (fun t : ℝ => (t - a) ^ n) x =
      (n.descFactorial k : ℝ) * (x - a) ^ (n - k) := by
  have h := congrFun
    (iteratedDeriv_comp_sub_const k (fun z : ℝ => z ^ n) a) x
  simpa using h

private theorem iterDeriv_Q_formula (n : ℕ) (x : ℝ) :
    iterDeriv n (Q n) x =
      ∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℝ) *
          ((n.descFactorial i : ℝ) * (x + 1) ^ (n - i)) *
          ((n.descFactorial (n - i) : ℝ) * (x - 1) ^ i) := by
  rw [iterDeriv, ← iteratedDeriv_eq_iterate]
  unfold Q
  rw [iteratedDeriv_fun_mul (n := n) (by fun_prop) (by fun_prop)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedDeriv_add_pow, iteratedDeriv_sub_pow]
  have hin : i ≤ n := by
    have := Finset.mem_range.mp hi
    omega
  rw [show n - (n - i) = i by omega]

private theorem iterDeriv_Q_pos_of_one_lt {n : ℕ} {x : ℝ} (hx : 1 < x) :
    0 < iterDeriv n (Q n) x := by
  rw [iterDeriv_Q_formula]
  have hp : 0 < x + 1 := by linarith
  have hm : 0 < x - 1 := by linarith
  apply Finset.sum_pos'
  · intro i hi
    positivity
  · refine ⟨0, by simp, ?_⟩
    simp
    positivity

private theorem Q_comp_neg (n : ℕ) :
    (fun x : ℝ => Q n (-x)) = Q n := by
  funext x
  unfold Q
  rw [show -x + 1 = -(x - 1) by ring,
    show -x - 1 = -(x + 1) by ring]
  have h1 : (-(x - 1)) ^ n = (-1 : ℝ) ^ n * (x - 1) ^ n := by
    rw [show -(x - 1) = (-1 : ℝ) * (x - 1) by ring, mul_pow]
  have h2 : (-(x + 1)) ^ n = (-1 : ℝ) ^ n * (x + 1) ^ n := by
    rw [show -(x + 1) = (-1 : ℝ) * (x + 1) by ring, mul_pow]
  rw [h1, h2]
  have hs : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← pow_add, ← two_mul n, pow_mul]
    norm_num
  rw [show
      ((-1 : ℝ) ^ n * (x - 1) ^ n) *
          ((-1 : ℝ) ^ n * (x + 1) ^ n) =
        ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
          ((x + 1) ^ n * (x - 1) ^ n) by ring,
    hs]
  ring

private theorem iterDeriv_Q_neg (n : ℕ) (x : ℝ) :
    iterDeriv n (Q n) (-x) =
      (-1 : ℝ) ^ n * iterDeriv n (Q n) x := by
  have h := iteratedDeriv_comp_neg n (Q n) (-x)
  rw [Q_comp_neg] at h
  simp only [neg_neg, smul_eq_mul] at h
  simpa only [iterDeriv, ← iteratedDeriv_eq_iterate] using h

private theorem iterDeriv_Q_ne_zero_of_lt_neg_one {n : ℕ} {x : ℝ}
    (hx : x < -1) :
    iterDeriv n (Q n) x ≠ 0 := by
  have hp : 0 < iterDeriv n (Q n) (-x) :=
    iterDeriv_Q_pos_of_one_lt (by linarith)
  have hsym := iterDeriv_Q_neg n (-x)
  simp only [neg_neg] at hsym
  rw [hsym]
  exact mul_ne_zero (by positivity) hp.ne'

private theorem iterDeriv_Q_one (n : ℕ) :
    iterDeriv n (Q n) 1 =
      (2 : ℝ) ^ n * (Nat.factorial n : ℝ) := by
  rw [iterDeriv_Q_formula, Finset.sum_eq_single 0]
  · norm_num [Nat.descFactorial_self]
  · intro i hi hi0
    simp [hi0]
  · simp

private theorem iterDeriv_Q_neg_one (n : ℕ) :
    iterDeriv n (Q n) (-1) =
      (-1 : ℝ) ^ n * ((2 : ℝ) ^ n * (Nat.factorial n : ℝ)) := by
  rw [iterDeriv_Q_neg, iterDeriv_Q_one]

private theorem P_one (n : ℕ) : P n 1 = 1 := by
  unfold P
  rw [iterDeriv_Q_one]
  field_simp

private theorem P_neg_one (n : ℕ) : P n (-1) = (-1 : ℝ) ^ n := by
  unfold P
  rw [iterDeriv_Q_neg_one]
  field_simp

private theorem iterDeriv_Q_zero_mem_Icc (n : ℕ) (x : ℝ)
    (hxzero : iterDeriv n (Q n) x = 0) :
    x ∈ Set.Icc (-1 : ℝ) 1 := by
  by_contra hxI
  simp only [Set.mem_Icc, not_and_or, not_le] at hxI
  rcases hxI with hleft | hright
  · exact iterDeriv_Q_ne_zero_of_lt_neg_one hleft hxzero
  · exact (iterDeriv_Q_pos_of_one_lt hright).ne' hxzero

theorem gap1 (n : ℕ) (x : ℝ) :
    Q n x = (x + 1) ^ n * (x - 1) ^ n := by
  rfl

theorem gap2 (n : ℕ) (hn : 1 ≤ n) :
    zeros (Q n) = ({(-1 : ℝ), (1 : ℝ)} : Set ℝ) := by
  have hn0 : n ≠ 0 := by omega
  ext x
  simp only [zeros, Set.mem_setOf_eq, Q, Set.mem_insert_iff,
    Set.mem_singleton_iff, mul_eq_zero, pow_eq_zero_iff hn0]
  constructor
  · rintro (h | h)
    · left
      linarith
    · right
      linarith
  · rintro (rfl | rfl) <;> norm_num [hn0]

theorem gap3 (n : ℕ) (hn : 1 ≤ n) :
    zeros (iterDeriv n (Q n)) ⊆ Set.Icc (-1 : ℝ) 1 := by
  intro x hxzero
  change iterDeriv n (Q n) x = 0 at hxzero
  exact iterDeriv_Q_zero_mem_Icc n x hxzero

theorem gap4 (n : ℕ) (x : ℝ) :
    P n x =
      1 / ((2 : ℝ) ^ n * (Nat.factorial n : ℝ)) *
        iterDeriv n (Q n) x := by
  rfl

theorem gap5 (n : ℕ) :
    (-1 : ℝ) ∉ zeros (P n) := by
  change P n (-1) ≠ 0
  rw [P_neg_one]
  positivity

theorem gap6 (n : ℕ) :
    (1 : ℝ) ∉ zeros (P n) := by
  change P n 1 ≠ 0
  rw [P_one]
  norm_num

theorem gap7 (n : ℕ) :
    zeros (P n) ⊆ Set.Ioo (-1 : ℝ) 1 := by
  intro x hx
  change P n x = 0 at hx
  have hiter : iterDeriv n (Q n) x = 0 := by
    unfold P at hx
    exact (mul_eq_zero.mp hx).resolve_left (by positivity)
  have hclosed := iterDeriv_Q_zero_mem_Icc n x hiter
  have hleft : x ≠ -1 := by
    intro heq
    subst x
    exact gap5 n hx
  have hright : x ≠ 1 := by
    intro heq
    subst x
    exact gap6 n hx
  exact ⟨lt_of_le_of_ne hclosed.1 hleft.symm,
    lt_of_le_of_ne hclosed.2 hright⟩

theorem gap8 :
    ∀ n, zeros (P n) ⊆ Set.Ioo (-1 : ℝ) 1 := by
  exact gap7

end

end ProofGap.Exercise1241
