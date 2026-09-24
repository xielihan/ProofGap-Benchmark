import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

open scoped BigOperators

namespace ProofGap.Exercise2571

noncomputable section

def blockSum (a : ℕ → ℝ) (m n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n - m), a (m + 1 + j)

def tailMass (a : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑' k : ℕ, a (k + m + 1)

def ratio (m n : ℕ) : ℝ :=
  (n : ℝ) / ((n : ℝ) - (m : ℝ))

def scaled (a : ℕ → ℝ) (n : ℕ) : ℝ := (n : ℝ) * a n

theorem gap1
    (a : ℕ → ℝ)
    (hpos : ∀ n, 0 < a n)
    (hmono : Antitone a)
    (hsum : Summable a) :
    ∀ m n, n > m → (n - m : ℕ) * a n ≤ blockSum a m n := by
  intro m n hmn
  unfold blockSum
  calc
    (n - m : ℕ) * a n = ∑ j ∈ Finset.range (n - m), a n := by simp
    _ ≤ ∑ j ∈ Finset.range (n - m), a (m + 1 + j) := by
      apply Finset.sum_le_sum
      intro j hj
      simp only [Finset.mem_range] at hj
      exact hmono (by omega)

theorem gap2
    (a : ℕ → ℝ)
    (hpos : ∀ n, 0 < a n)
    (hmono : Antitone a)
    (hsum : Summable a)
    (hblock : ∀ m n, n > m →
      (n - m : ℕ) * a n ≤ blockSum a m n) :
    ∀ m n, n > m → blockSum a m n < tailMass a m := by
  intro m n hmn
  have hb : Summable (fun k : ℕ => a (k + m + 1)) := by
    apply hsum.comp_injective
    intro x y hxy
    exact Nat.add_right_cancel (Nat.add_right_cancel hxy)
  calc
    blockSum a m n = ∑ j ∈ Finset.range (n - m), a (j + m + 1) := by
      unfold blockSum
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      omega
    _ < ∑ j ∈ Finset.range (n - m + 1), a (j + m + 1) := by
      rw [Finset.sum_range_succ]
      exact lt_add_of_pos_right _ (hpos (n - m + m + 1))
    _ ≤ tailMass a m := by
      unfold tailMass
      exact hb.sum_le_tsum (Finset.range (n - m + 1))
        (fun k hk => (hpos (k + m + 1)).le)

theorem gap3
    (a : ℕ → ℝ)
    (hblock : ∀ m n, n > m →
      (n - m : ℕ) * a n ≤ blockSum a m n)
    (htail : ∀ m n, n > m → blockSum a m n < tailMass a m) :
    ∀ m n, n > m →
      (n - m : ℕ) * a n < tailMass a m := by
  intro m n hmn
  exact lt_of_le_of_lt (hblock m n hmn) (htail m n hmn)

theorem gap4
    (a : ℕ → ℝ)
    (hbound : ∀ m n, n > m →
      (n - m : ℕ) * a n < tailMass a m) :
    ∀ m n, n > m →
      scaled a n < ratio m n * tailMass a m := by
  intro m n hmn
  have hden : 0 < (n : ℝ) - (m : ℝ) :=
    sub_pos.mpr (Nat.cast_lt.mpr hmn)
  have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
    rw [Nat.cast_sub (Nat.le_of_lt hmn)]
  have hnpos : 0 < (n : ℝ) :=
    Nat.cast_pos.mpr (by omega)
  have hrpos : 0 < ratio m n := by
    unfold ratio
    exact div_pos hnpos hden
  have hmul := mul_lt_mul_of_pos_left (hbound m n hmn) hrpos
  calc
    scaled a n = ratio m n * ((n - m : ℕ) * a n) := by
      unfold scaled ratio
      rw [hcast]
      field_simp [ne_of_gt hden]
      <;> ring
    _ < ratio m n * tailMass a m := hmul

theorem gap5
    (a : ℕ → ℝ)
    (hpos : ∀ n, 0 < a n)
    (hsum : Summable a) :
    ∀ ε : ℝ, ε > 0 → ∃ m₀ : ℕ, 1 ≤ m₀ ∧ tailMass a m₀ < ε := by
  intro ε hε
  have hseries :
      Tendsto (fun s : Finset ℕ => ∑ k ∈ s, a k)
        atTop (nhds (∑' k : ℕ, a k)) :=
    hsum.hasSum
  rcases (Metric.tendsto_atTop.1 hseries ε hε) with ⟨s, hs⟩
  have hcover : ∃ N : ℕ, s ⊆ Finset.range N := by
    clear hs
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨0, by simp⟩
    | @insert x s hx ih =>
        rcases ih with ⟨N, hN⟩
        refine ⟨max (x + 1) N, ?_⟩
        intro y hy
        simp only [Finset.mem_insert] at hy
        simp only [Finset.mem_range]
        rcases hy with rfl | hy
        · omega
        · have hyN : y < N := Finset.mem_range.mp (hN hy)
          omega
  rcases hcover with ⟨N, hN⟩
  let m := max 1 N
  refine ⟨m, ?_, ?_⟩
  · dsimp [m]
    omega
  · have hsub : s ⊆ Finset.range (m + 1) := by
      intro k hk
      have hkN : k < N := Finset.mem_range.mp (hN hk)
      apply Finset.mem_range.mpr
      dsimp [m]
      omega
    have hclose := hs (Finset.range (m + 1)) hsub
    rw [Real.dist_eq] at hclose
    have hlower : -ε <
        (∑ k ∈ Finset.range (m + 1), a k) - (∑' k : ℕ, a k) :=
      (abs_lt.mp hclose).1
    have hdecomp :
        (∑ k ∈ Finset.range (m + 1), a k) + tailMass a m =
          ∑' k : ℕ, a k := by
      simpa [tailMass, add_assoc, add_comm, add_left_comm] using
        (hsum.sum_add_tsum_nat_add (m + 1))
    linarith

theorem gap6 :
    ∀ m₀ : ℕ, Tendsto (ratio m₀) atTop (nhds 1) := by
  intro m
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N : ℕ, hN⟩ :=
    exists_nat_gt ((m : ℝ) + (m : ℝ) / ε)
  refine ⟨max (m + 1) N, ?_⟩
  intro n hn
  have hNn : N ≤ n := (le_max_right (m + 1) N).trans hn
  have hmn : m < n := by
    have hm1 : m + 1 ≤ n := (le_max_left (m + 1) N).trans hn
    omega
  have hden : 0 < (n : ℝ) - (m : ℝ) :=
    sub_pos.mpr (Nat.cast_lt.mpr hmn)
  have hlarge :
      (m : ℝ) + (m : ℝ) / ε < (n : ℝ) :=
    lt_of_lt_of_le hN (Nat.cast_le.mpr hNn)
  have hfrac : (m : ℝ) / ε < (n : ℝ) - (m : ℝ) := by
    linarith
  have hmul :
      (m : ℝ) < ε * ((n : ℝ) - (m : ℝ)) := by
    calc
      (m : ℝ) = ε * ((m : ℝ) / ε) := by
        field_simp [ne_of_gt hε]
      _ < ε * ((n : ℝ) - (m : ℝ)) :=
        mul_lt_mul_of_pos_left hfrac hε
  have hquot :
      (m : ℝ) / ((n : ℝ) - (m : ℝ)) < ε :=
    (div_lt_iff₀ hden).2 hmul
  have heq :
      ratio m n - 1 = (m : ℝ) / ((n : ℝ) - (m : ℝ)) := by
    unfold ratio
    field_simp [ne_of_gt hden]
    <;> ring
  rw [Real.dist_eq, heq,
    abs_of_nonneg (div_nonneg (Nat.cast_nonneg m) hden.le)]
  exact hquot

theorem gap7
    (hratio : ∀ m₀ : ℕ, Tendsto (ratio m₀) atTop (nhds 1)) :
    ∀ m₀ : ℕ, ∃ n₀ : ℕ, n₀ > m₀ ∧
      ∀ n ≥ n₀, ratio m₀ n < 2 := by
  intro m
  rcases (Metric.tendsto_atTop.1 (hratio m) 1 (by norm_num)) with
    ⟨N, hN⟩
  refine ⟨max N (m + 1), ?_, ?_⟩
  · omega
  · intro n hn
    have hNn : N ≤ n := (le_max_left N (m + 1)).trans hn
    have hd := hN n hNn
    rw [Real.dist_eq] at hd
    have hu := (abs_lt.mp hd).2
    linarith

theorem gap8
    (a : ℕ → ℝ)
    (hpos : ∀ n, 0 < a n)
    (hscaled : ∀ m n, n > m →
      scaled a n < ratio m n * tailMass a m)
    (htailSmall : ∀ ε : ℝ, ε > 0 →
      ∃ m₀ : ℕ, 1 ≤ m₀ ∧ tailMass a m₀ < ε)
    (hratioSmall : ∀ m₀ : ℕ, ∃ n₀ : ℕ, n₀ > m₀ ∧
      ∀ n ≥ n₀, ratio m₀ n < 2) :
    ∀ ε : ℝ, ε > 0 → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      0 < scaled a n ∧ scaled a n < 2 * ε := by
  intro ε hε
  rcases htailSmall ε hε with ⟨m, hm1, htail⟩
  rcases hratioSmall m with ⟨n₀, hn₀m, hratio⟩
  refine ⟨n₀, ?_⟩
  intro n hn
  have hnm : n > m := lt_of_lt_of_le hn₀m hn
  have hnpos : 0 < (n : ℝ) :=
    Nat.cast_pos.mpr (by omega)
  have hscaledpos : 0 < scaled a n := by
    unfold scaled
    exact mul_pos hnpos (hpos n)
  have hs := hscaled m n hnm
  have hdenpos : 0 < (n : ℝ) - (m : ℝ) :=
    sub_pos.mpr (Nat.cast_lt.mpr hnm)
  have hratiopos : 0 < ratio m n := by
    unfold ratio
    exact div_pos hnpos hdenpos
  have hprodpos : 0 < ratio m n * tailMass a m :=
    lt_trans hscaledpos hs
  have htailpos : 0 < tailMass a m := by
    rcases (mul_pos_iff.mp hprodpos) with hpp | hnn
    · exact hpp.2
    · linarith [hratiopos, hnn.1]
  constructor
  · exact hscaledpos
  · calc
      scaled a n < ratio m n * tailMass a m := hs
      _ < 2 * tailMass a m :=
        mul_lt_mul_of_pos_right (hratio n hn) htailpos
      _ < 2 * ε := mul_lt_mul_of_pos_left htail (by norm_num)

theorem gap9
    (a : ℕ → ℝ)
    (hepsilon : ∀ ε : ℝ, ε > 0 → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      0 < scaled a n ∧ scaled a n < 2 * ε) :
    Tendsto (scaled a) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  rcases hepsilon (ε / 2) (half_pos hε) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have h := hN n hn
  have hu : scaled a n < ε := by
    linarith [h.2]
  simpa [Real.dist_eq, abs_of_pos h.1] using hu

theorem gap10
    (a : ℕ → ℝ)
    (hlim : Tendsto (scaled a) atTop (nhds 0)) :
    Tendsto (scaled a) atTop (nhds 0) := by
  exact hlim

end

end ProofGap.Exercise2571
