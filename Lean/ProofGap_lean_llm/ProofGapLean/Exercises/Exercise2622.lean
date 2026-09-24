import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2622

noncomputable section

open scoped BigOperators
open Filter

def Positive (a : ℕ → ℝ) : Prop :=
  ∀ n ≥ 1, 0 < a n

def Nonincreasing (a : ℕ → ℝ) : Prop :=
  Antitone a

def partialSum (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, a k

def condensedPartial (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), (2 ^ j : ℝ) * a (2 ^ j)

def lowerBlockBound (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) * a 1 +
    ∑ j ∈ Finset.Icc 1 n, (2 ^ (j - 1) : ℝ) * a (2 ^ j)

def originalConverges (a : ℕ → ℝ) : Prop :=
  Summable (fun n : ℕ => a (n + 1))

def condensedConverges (a : ℕ → ℝ) : Prop :=
  Summable (fun n : ℕ => (2 ^ n : ℝ) * a (2 ^ n))

theorem gap1 (a : ℕ → ℝ) (hmono : Nonincreasing a) :
    a 2 ≤ a 1 := by
  exact hmono (by omega)

theorem gap2 (a : ℕ → ℝ) (hmono : Nonincreasing a) (k : ℕ) (hk : 2 ≤ k) :
    a k ≤ a 2 := by
  exact hmono hk

theorem gap3 (a : ℕ → ℝ) (hmono : Nonincreasing a)
    (n k : ℕ) (hk₀ : 2 ^ n ≤ k) (hk₁ : k ≤ 2 ^ (n + 1)) :
    a k ≤ a (2 ^ n) := by
  exact hmono hk₀

theorem gap4 (a : ℕ → ℝ) (hmono : Nonincreasing a) (n : ℕ) :
    a (2 ^ n + 1) ≤ a (2 ^ n) := by
  exact hmono (by omega)

theorem gap5 (a : ℕ → ℝ) (hmono : Nonincreasing a)
    (n k : ℕ) (hk₀ : 2 ^ n + 1 ≤ k) :
    a k ≤ a (2 ^ n + 1) := by
  exact hmono hk₀

theorem gap6 (a : ℕ → ℝ) (hpos : Positive a) (n : ℕ) :
    0 < a (2 ^ n) := by
  exact hpos (2 ^ n) (Nat.one_le_pow n 2 (by norm_num))

theorem gap7 (a : ℕ → ℝ) (hpos : Positive a) :
    0 < a 1 := by
  exact hpos 1 le_rfl

theorem gap8 (a : ℕ → ℝ) (hpos : Positive a) (n : ℕ) :
    0 < partialSum a (2 ^ n) := by
  unfold partialSum
  apply Finset.sum_pos'
  · intro k hk
    exact (hpos k (Finset.mem_Icc.mp hk).1).le
  · refine ⟨1, ?_, hpos 1 le_rfl⟩
    simp only [Finset.mem_Icc, le_refl, true_and]
    exact Nat.one_le_pow n 2 (by norm_num)

theorem gap9 (a : ℕ → ℝ) (hpos : Positive a) (n : ℕ) (hn : 1 ≤ n) :
    partialSum a (2 ^ n) < partialSum a (2 ^ (n + 1) - 1) := by
  have htwo : 2 ≤ 2 ^ n := by
    cases n with
    | zero => omega
    | succ m =>
        rw [pow_succ]
        have hm : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
        omega
  have hpow : 2 ^ (n + 1) = 2 ^ n * 2 := by
    rw [pow_succ]
  have hupper : 2 ^ n + 1 ≤ 2 ^ (n + 1) - 1 := by
    omega
  have hsubset : Finset.Icc 1 (2 ^ n) ⊆
      Finset.Icc 1 (2 ^ (n + 1) - 1) := by
    intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    exact ⟨hk.1, hk.2.trans (by omega)⟩
  unfold partialSum
  exact Finset.sum_lt_sum_of_subset hsubset
    (Finset.mem_Icc.mpr ⟨by omega, hupper⟩)
    (by simp) (hpos (2 ^ n + 1) (by omega))
    (fun k hk _ => (hpos k (Finset.mem_Icc.mp hk).1).le)

private theorem upper_block_bound (a : ℕ → ℝ)
    (hmono : Nonincreasing a) (j : ℕ) :
    (∑ k ∈ Finset.Icc (2 ^ j) (2 ^ (j + 1) - 1), a k) ≤
      (2 ^ j : ℝ) * a (2 ^ j) := by
  calc
    (∑ k ∈ Finset.Icc (2 ^ j) (2 ^ (j + 1) - 1), a k) ≤
        ∑ k ∈ Finset.Icc (2 ^ j) (2 ^ (j + 1) - 1), a (2 ^ j) := by
      gcongr with k hk
      exact hmono (Finset.mem_Icc.mp hk).1
    _ = ((Finset.Icc (2 ^ j) (2 ^ (j + 1) - 1)).card : ℝ) *
        a (2 ^ j) := by simp
    _ = (2 ^ j : ℝ) * a (2 ^ j) := by
      congr 1
      have hone : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by norm_num)
      norm_cast
      simp [pow_succ] <;> omega

theorem gap10 (a : ℕ → ℝ) (hmono : Nonincreasing a) (n : ℕ) :
    partialSum a (2 ^ (n + 1) - 1) ≤ condensedPartial a n := by
  induction n with
  | zero =>
      norm_num [partialSum, condensedPartial]
  | succ n ih =>
      have hone : 1 ≤ 2 ^ (n + 1) :=
        Nat.one_le_pow (n + 1) 2 (by norm_num)
      have hpow : 2 ^ ((n + 1) + 1) = 2 ^ (n + 1) * 2 := by
        rw [pow_succ]
      have hsplit : Finset.Icc 1 (2 ^ ((n + 1) + 1) - 1) =
          Finset.Icc 1 (2 ^ (n + 1) - 1) ∪
            Finset.Icc (2 ^ (n + 1)) (2 ^ ((n + 1) + 1) - 1) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_union]
        constructor
        · intro hk
          by_cases hkn : k ≤ 2 ^ (n + 1) - 1
          · exact Or.inl ⟨hk.1, hkn⟩
          · exact Or.inr ⟨by omega, hk.2⟩
        · rintro (hk | hk)
          · exact ⟨hk.1, by omega⟩
          · exact ⟨by omega, hk.2⟩
      have hdisj : Disjoint (Finset.Icc 1 (2 ^ (n + 1) - 1))
          (Finset.Icc (2 ^ (n + 1)) (2 ^ ((n + 1) + 1) - 1)) := by
        rw [Finset.disjoint_left]
        intro k hk₁ hk₂
        rw [Finset.mem_Icc] at hk₁ hk₂
        omega
      have hdecomp :
          partialSum a (2 ^ ((n + 1) + 1) - 1) =
            partialSum a (2 ^ (n + 1) - 1) +
              ∑ k ∈ Finset.Icc (2 ^ (n + 1))
                (2 ^ ((n + 1) + 1) - 1), a k := by
        unfold partialSum
        rw [hsplit, Finset.sum_union hdisj]
      have hcondensed : condensedPartial a (n + 1) =
          condensedPartial a n +
            (2 ^ (n + 1) : ℝ) * a (2 ^ (n + 1)) := by
        unfold condensedPartial
        rw [Finset.sum_range_succ]
      calc
        partialSum a (2 ^ (Nat.succ n + 1) - 1) =
            partialSum a (2 ^ (n + 1) - 1) +
              ∑ k ∈ Finset.Icc (2 ^ (n + 1))
                (2 ^ ((n + 1) + 1) - 1), a k := by
          simpa [Nat.succ_eq_add_one] using hdecomp
        _ ≤ condensedPartial a n +
              (2 ^ (n + 1) : ℝ) * a (2 ^ (n + 1)) :=
          add_le_add ih (upper_block_bound a hmono (n + 1))
        _ = condensedPartial a (Nat.succ n) := by
          simpa [Nat.succ_eq_add_one] using hcondensed.symm

theorem gap11 (a : ℕ → ℝ) (hpos : Positive a) (n : ℕ) :
    0 < condensedPartial a n := by
  unfold condensedPartial
  apply Finset.sum_pos'
  · intro j hj
    exact mul_nonneg (by positivity) (gap6 a hpos j).le
  · refine ⟨0, by simp, ?_⟩
    norm_num [gap7 a hpos]

theorem gap12 (a : ℕ → ℝ) (n : ℕ) :
    partialSum a (2 ^ n) =
      a 1 +
        ∑ j ∈ Finset.range n,
          ∑ k ∈ Finset.Icc (2 ^ j + 1) (2 ^ (j + 1)), a k := by
  induction n with
  | zero =>
      norm_num [partialSum]
  | succ n ih =>
      have hone : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
      have hpow : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
      have hsplit : Finset.Icc 1 (2 ^ (n + 1)) =
          Finset.Icc 1 (2 ^ n) ∪
            Finset.Icc (2 ^ n + 1) (2 ^ (n + 1)) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_union]
        constructor
        · intro hk
          by_cases hkn : k ≤ 2 ^ n
          · exact Or.inl ⟨hk.1, hkn⟩
          · exact Or.inr ⟨by omega, hk.2⟩
        · rintro (hk | hk)
          · exact ⟨hk.1, by omega⟩
          · exact ⟨by omega, hk.2⟩
      have hdisj : Disjoint (Finset.Icc 1 (2 ^ n))
          (Finset.Icc (2 ^ n + 1) (2 ^ (n + 1))) := by
        rw [Finset.disjoint_left]
        intro k hk₁ hk₂
        rw [Finset.mem_Icc] at hk₁ hk₂
        omega
      rw [partialSum, hsplit, Finset.sum_union hdisj,
        ← partialSum, ih, Finset.sum_range_succ]
      ring

private theorem lower_block_term_bound (a : ℕ → ℝ)
    (hmono : Nonincreasing a) (j : ℕ) :
    (2 ^ j : ℝ) * a (2 ^ (j + 1)) ≤
      ∑ k ∈ Finset.Icc (2 ^ j + 1) (2 ^ (j + 1)), a k := by
  have hone : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by norm_num)
  have hcard : (Finset.Icc (2 ^ j + 1) (2 ^ (j + 1))).card = 2 ^ j := by
    simp [pow_succ] <;> omega
  calc
    (2 ^ j : ℝ) * a (2 ^ (j + 1)) =
        ∑ k ∈ Finset.Icc (2 ^ j + 1) (2 ^ (j + 1)), a (2 ^ (j + 1)) := by
      simp [hcard]
    _ ≤ ∑ k ∈ Finset.Icc (2 ^ j + 1) (2 ^ (j + 1)), a k := by
      gcongr with k hk
      exact hmono (Finset.mem_Icc.mp hk).2

theorem gap13 (a : ℕ → ℝ) (hpos : Positive a)
    (hmono : Nonincreasing a) (n : ℕ) :
    lowerBlockBound a n < partialSum a (2 ^ n) := by
  induction n with
  | zero =>
      have ha1 := gap7 a hpos
      norm_num [lowerBlockBound, partialSum]
      linarith
  | succ n ih =>
      have hlower : lowerBlockBound a (n + 1) =
          lowerBlockBound a n + (2 ^ n : ℝ) * a (2 ^ (n + 1)) := by
        simp only [lowerBlockBound]
        rw [Finset.sum_Icc_succ_top (by omega)]
        have hsub : n + 1 - 1 = n := by omega
        rw [hsub]
        ring
      have hpartial : partialSum a (2 ^ (n + 1)) =
          partialSum a (2 ^ n) +
            ∑ k ∈ Finset.Icc (2 ^ n + 1) (2 ^ (n + 1)), a k := by
        rw [gap12 a (n + 1), gap12 a n, Finset.sum_range_succ]
        ring
      calc
        lowerBlockBound a (Nat.succ n) =
            lowerBlockBound a n + (2 ^ n : ℝ) * a (2 ^ (n + 1)) := by
          simpa [Nat.succ_eq_add_one] using hlower
        _ < partialSum a (2 ^ n) +
              ∑ k ∈ Finset.Icc (2 ^ n + 1) (2 ^ (n + 1)), a k :=
          add_lt_add_of_lt_of_le ih (lower_block_term_bound a hmono n)
        _ = partialSum a (2 ^ (Nat.succ n)) := by
          simpa [Nat.succ_eq_add_one] using hpartial.symm

theorem gap14 (a : ℕ → ℝ) (n : ℕ) :
    lowerBlockBound a n = (1 / 2 : ℝ) * condensedPartial a n := by
  induction n with
  | zero =>
      norm_num [lowerBlockBound, condensedPartial]
  | succ n ih =>
      unfold lowerBlockBound condensedPartial at ih
      rw [lowerBlockBound, Finset.sum_Icc_succ_top (by omega),
        condensedPartial, Finset.sum_range_succ]
      push_cast
      rw [pow_succ]
      linear_combination ih

theorem gap15 (a : ℕ → ℝ) (hpos : Positive a) (n : ℕ) :
    0 < (1 / 2 : ℝ) * condensedPartial a n := by
  exact mul_pos (by norm_num) (gap11 a hpos n)

theorem gap16 (a : ℕ → ℝ) (hpos : Positive a) (n : ℕ) :
    0 < partialSum a (2 ^ n) := by
  exact gap8 a hpos n

private theorem convergence_iff (a : ℕ → ℝ) (hpos : Positive a)
    (hmono : Nonincreasing a) :
    originalConverges a ↔ condensedConverges a := by
  have hnonneg : 0 ≤ᶠ[atTop] a := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (hpos n hn).le
  have hanti : ∀ᶠ n : ℕ in atTop, a (n + 1) ≤ a n :=
    Filter.Eventually.of_forall (fun n => hmono (Nat.le_succ n))
  have hcondiff := summable_condensed_iff_of_eventually_nonneg hnonneg hanti
  unfold originalConverges condensedConverges
  constructor
  · intro horiginal
    have hall : Summable a := (summable_nat_add_iff 1).mp horiginal
    exact hcondiff.mpr hall
  · intro hcondensed
    have hall : Summable a := hcondiff.mp hcondensed
    exact (summable_nat_add_iff 1).mpr hall

theorem gap17 (a : ℕ → ℝ) (hpos : Positive a)
    (hmono : Nonincreasing a) :
    condensedConverges a → originalConverges a := by
  exact (convergence_iff a hpos hmono).mpr

theorem gap18 (a : ℕ → ℝ) (hpos : Positive a)
    (hmono : Nonincreasing a) :
    (¬ condensedConverges a) → ¬ originalConverges a := by
  intro hcondensed horiginal
  exact hcondensed ((convergence_iff a hpos hmono).mp horiginal)

theorem gap19 (a : ℕ → ℝ) (hpos : Positive a)
    (hmono : Nonincreasing a) :
    originalConverges a ↔ condensedConverges a := by
  exact convergence_iff a hpos hmono

theorem gap20 (a : ℕ → ℝ) (hpos : Positive a)
    (hmono : Nonincreasing a) :
    originalConverges a ↔ condensedConverges a := by
  exact gap19 a hpos hmono

end

end ProofGap.Exercise2622
