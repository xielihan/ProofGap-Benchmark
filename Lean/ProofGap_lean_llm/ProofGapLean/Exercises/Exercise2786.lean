import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2786

noncomputable section

open Filter
open scoped BigOperators

def cutoff (n : ℕ) : ℝ :=
  1 / (2 : ℝ) ^ n

def f (n : ℕ) (x : ℝ) : ℝ :=
  if cutoff (n + 1) < x ∧ x < cutoff n then
    (1 / (n : ℝ)) * Real.sin ((2 : ℝ) ^ (n + 1) * Real.pi * x) ^ 2
  else
    0

def tail (N p : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range p, f (N + j + 1) x

def peakPoint (n : ℕ) : ℝ :=
  (3 / 2 : ℝ) * cutoff (n + 1)

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (n + 1), u k x) - g x| < ε

def HasSummableMajorant : Prop :=
  ∃ a : ℕ → ℝ,
    (∀ n, 0 ≤ a n) ∧
    Summable (fun n : ℕ => a (n + 1)) ∧
    ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Set.Icc (0 : ℝ) 1, |f n x| ≤ a n

private theorem cutoff_pos (n : ℕ) : 0 < cutoff n := by
  unfold cutoff
  positivity

private theorem cutoff_succ_lt (n : ℕ) : cutoff (n + 1) < cutoff n := by
  unfold cutoff
  rw [pow_succ]
  have hp : 0 < (2 : ℝ) ^ n := by positivity
  exact one_div_lt_one_div_of_lt hp (by nlinarith)

private theorem cutoff_strictAnti : StrictAnti cutoff :=
  strictAnti_nat_of_succ_lt cutoff_succ_lt

private def InSupport (n : ℕ) (x : ℝ) : Prop :=
  cutoff (n + 1) < x ∧ x < cutoff n

private theorem support_index_unique {n m : ℕ} {x : ℝ}
    (hn : InSupport n x) (hm : InSupport m x) : n = m := by
  rcases lt_trichotomy n m with hnm | hnm | hmn
  · have hc : cutoff m ≤ cutoff (n + 1) := cutoff_strictAnti.antitone (by omega)
    exfalso
    exact (not_lt_of_ge hc) (lt_trans hn.1 hm.2)
  · exact hnm
  · have hc : cutoff n ≤ cutoff (m + 1) := cutoff_strictAnti.antitone (by omega)
    exfalso
    exact (not_lt_of_ge hc) (lt_trans hm.1 hn.2)

private theorem support_of_f_ne_zero {n : ℕ} {x : ℝ} (h : f n x ≠ 0) :
    InSupport n x := by
  unfold f at h
  split_ifs at h with hs
  · exact hs
  · exact (h rfl).elim

private theorem f_nonneg (n : ℕ) (x : ℝ) : 0 ≤ f n x := by
  unfold f
  split_ifs
  · positivity
  · rfl

private theorem f_le_inv (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    f n x ≤ 1 / (n : ℝ) := by
  unfold f
  split_ifs with hsupp
  · have hs := Real.sin_mem_Icc ((2 : ℝ) ^ (n + 1) * Real.pi * x)
    have hsq : Real.sin ((2 : ℝ) ^ (n + 1) * Real.pi * x) ^ 2 ≤ 1 := by
      have habs : |Real.sin ((2 : ℝ) ^ (n + 1) * Real.pi * x)| ≤ 1 := (abs_le).2 hs
      have habs' : |Real.sin ((2 : ℝ) ^ (n + 1) * Real.pi * x)| ≤ |(1 : ℝ)| := by
        simpa using habs
      simpa using (sq_le_sq).2 habs'
    exact mul_le_of_le_one_right (by positivity) hsq
  · positivity

theorem gap1 (N p : ℕ) (x : ℝ) :
    tail N p x =
      ∑ j ∈ Finset.range p,
        if cutoff (N + j + 2) < x ∧ x < cutoff (N + j + 1) then
          (1 / ((N + j + 1 : ℕ) : ℝ)) *
            Real.sin
              ((2 : ℝ) ^ (N + j + 2) * Real.pi * x) ^ 2
        else 0 := by
  simp [tail, f, Nat.add_assoc]

theorem gap2 (N p : ℕ) (x : ℝ)
    (hN : 1 ≤ N) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |tail N p x| < 1 / (N : ℝ) := by
  classical
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  by_cases hex : ∃ j ∈ Finset.range p, InSupport (N + j + 1) x
  · obtain ⟨j, hj, hjsupp⟩ := hex
    have hsum : tail N p x = f (N + j + 1) x := by
      unfold tail
      apply Finset.sum_eq_single j
      · intro b hb hbj
        have hzero : f (N + b + 1) x = 0 := by
          by_contra hne
          have heq := support_index_unique hjsupp (support_of_f_ne_zero hne)
          omega
        exact hzero
      · intro hjnot
        exact (hjnot hj).elim
    rw [hsum, abs_of_nonneg (f_nonneg _ _)]
    calc
      f (N + j + 1) x ≤ 1 / ((N + j + 1 : ℕ) : ℝ) := f_le_inv _ _ (by omega)
      _ < 1 / (N : ℝ) := by
        apply one_div_lt_one_div_of_lt hN_pos
        exact_mod_cast (by omega : N < N + j + 1)
  · have hzero : ∀ j ∈ Finset.range p, f (N + j + 1) x = 0 := by
      intro j hj
      unfold f
      split_ifs with hsupp
      · exact (hex ⟨j, hj, hsupp⟩).elim
      · rfl
    rw [tail, Finset.sum_eq_zero hzero, abs_zero]
    positivity

theorem gap3 :
    ∀ ε > 0, ∃ N : ℕ, ∀ p : ℕ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |tail N p x| < ε := by
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hevent : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) < ε :=
    (tendsto_order.1 hlim).2 ε hε
  obtain ⟨K, hK⟩ := eventually_atTop.1 hevent
  refine ⟨max 1 K, fun p x hx => ?_⟩
  exact lt_trans (gap2 (max 1 K) p x (le_max_left _ _) hx)
    (hK _ (le_max_right _ _))

theorem gap4 (x : ℝ) :
    Summable (fun n : ℕ => |f (n + 1) x|) := by
  classical
  by_cases hex : ∃ n : ℕ, f (n + 1) x ≠ 0
  · obtain ⟨n, hn⟩ := hex
    apply summable_of_ne_finset_zero (s := {n})
    intro m hm
    have hmn : m ≠ n := by simpa using hm
    have hzero : f (m + 1) x = 0 := by
      by_contra hmne
      have heq := support_index_unique (support_of_f_ne_zero hmne) (support_of_f_ne_zero hn)
      omega
    simp [hzero]
  · have hzero : ∀ n : ℕ, f (n + 1) x = 0 := by
      intro n
      exact not_ne_iff.mp (not_exists.mp hex n)
    simpa [hzero] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))

private theorem series_remainder_bound (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |(∑ k ∈ Finset.range (n + 1), f (k + 1) x) -
      ∑' k : ℕ, f (k + 1) x| ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
  have hsummable : Summable (fun k : ℕ => f (k + 1) x) := (gap4 x).of_abs
  have hseries := hsummable.hasSum
  have htotal :
      Tendsto (fun m => ∑ k ∈ Finset.range (n + 1 + m), f (k + 1) x)
        atTop (nhds (∑' k : ℕ, f (k + 1) x)) := by
    simpa [Nat.add_comm] using hseries.tendsto_sum_nat.comp (tendsto_add_atTop_nat (n + 1))
  have hlim :
      Tendsto
        (fun m => |(∑ k ∈ Finset.range (n + 1), f (k + 1) x) -
          ∑ k ∈ Finset.range (n + 1 + m), f (k + 1) x|)
        atTop
        (nhds |(∑ k ∈ Finset.range (n + 1), f (k + 1) x) -
          ∑' k : ℕ, f (k + 1) x|) := by
    exact (tendsto_const_nhds.sub htotal).abs
  apply le_of_tendsto' hlim
  intro m
  have htail := (gap2 (n + 1) m x (by omega) hx).le
  have hsplit :
      (∑ k ∈ Finset.range (n + 1 + m), f (k + 1) x) =
        (∑ k ∈ Finset.range (n + 1), f (k + 1) x) +
          ∑ k ∈ Finset.range m, f (n + 1 + k + 1) x := by
    simpa using Finset.sum_range_add (f := fun k => f (k + 1) x) (n + 1) m
  rw [hsplit]
  simpa [tail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

theorem gap5 :
    SeriesUniformlyConvergesOn
      (fun n x => f (n + 1) x)
      (Set.Icc (0 : ℝ) 1)
      (fun x => ∑' n : ℕ, f (n + 1) x) := by
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (nhds 0) :=
    by simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hevent : ∀ᶠ n : ℕ in atTop, 1 / ((n + 1 : ℕ) : ℝ) < ε :=
    (tendsto_order.1 hlim).2 ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨N, fun n hn x hx => ?_⟩
  change |(∑ k ∈ Finset.range (n + 1), f (k + 1) x) -
    ∑' k : ℕ, f (k + 1) x| < ε
  exact lt_of_le_of_lt (series_remainder_bound n x hx) (hN n hn)

theorem gap6 (n : ℕ) (hn : 1 ≤ n) :
    cutoff (n + 1) < peakPoint n := by
  unfold peakPoint
  nlinarith [cutoff_pos (n + 1)]

private theorem cutoff_eq_two_mul_succ (n : ℕ) :
    cutoff n = 2 * cutoff (n + 1) := by
  unfold cutoff
  rw [pow_succ]
  have hp : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hp]

theorem gap7 (n : ℕ) (hn : 1 ≤ n) :
    peakPoint n < cutoff n := by
  rw [cutoff_eq_two_mul_succ]
  unfold peakPoint
  nlinarith [cutoff_pos (n + 1)]

theorem gap8 (n : ℕ) (hn : 1 ≤ n) :
    cutoff (n + 1) < cutoff n := by
  exact cutoff_succ_lt n

private theorem peakPoint_mem_Icc (n : ℕ) (hn : 1 ≤ n) :
    peakPoint n ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · unfold peakPoint
    exact mul_nonneg (by norm_num) (cutoff_pos (n + 1)).le
  · have hp_lt := gap7 n hn
    have hc_le : cutoff n ≤ cutoff 0 := cutoff_strictAnti.antitone (Nat.zero_le n)
    simpa [cutoff] using hp_lt.le.trans hc_le

theorem gap9 (a : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hmaj : ∀ m : ℕ, 1 ≤ m →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |f m x| ≤ a m) :
    a n ≥ |f n (peakPoint n)| := by
  exact hmaj n hn (peakPoint n) (peakPoint_mem_Icc n hn)

theorem gap10 (n : ℕ) (hn : 1 ≤ n) :
    |f n (peakPoint n)| =
      (1 / (n : ℝ)) *
        Real.sin ((2 : ℝ) ^ (n + 1) * Real.pi * peakPoint n) ^ 2 := by
  unfold f
  rw [if_pos ⟨gap6 n hn, gap7 n hn⟩]
  rw [abs_of_nonneg]
  positivity

private theorem peakPoint_angle (n : ℕ) :
    (2 : ℝ) ^ (n + 1) * Real.pi * peakPoint n = 3 * Real.pi / 2 := by
  unfold peakPoint cutoff
  have hp : (2 : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hp]

private theorem sin_three_pi_div_two : Real.sin (3 * Real.pi / 2) = -1 := by
  rw [show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring, Real.sin_add]
  simp

theorem gap11 (n : ℕ) (hn : 1 ≤ n) :
    (1 / (n : ℝ)) *
        Real.sin ((2 : ℝ) ^ (n + 1) * Real.pi * peakPoint n) ^ 2 =
      1 / (n : ℝ) := by
  rw [peakPoint_angle, sin_three_pi_div_two]
  ring

theorem gap12 (n : ℕ) (hn : 1 ≤ n) :
    1 / (n : ℝ) > 0 := by
  positivity

theorem gap13 (a : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hmaj : ∀ m : ℕ, 1 ≤ m →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |f m x| ≤ a m) :
    a n > 0 := by
  calc
    a n ≥ |f n (peakPoint n)| := gap9 a n hn hmaj
    _ = (1 / (n : ℝ)) *
        Real.sin ((2 : ℝ) ^ (n + 1) * Real.pi * peakPoint n) ^ 2 := gap10 n hn
    _ = 1 / (n : ℝ) := gap11 n hn
    _ > 0 := gap12 n hn

theorem gap14 :
    HasSummableMajorant →
      Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ))) := by
  rintro ⟨a, ha, hsummable, hmaj⟩
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsummable
  have hn : 1 ≤ n + 1 := by omega
  calc
    1 / (((n + 1 : ℕ) : ℝ)) = |f (n + 1) (peakPoint (n + 1))| := by
      rw [gap10 (n + 1) hn, gap11 (n + 1) hn]
    _ ≤ a (n + 1) := gap9 a (n + 1) hn hmaj

theorem gap15 :
    HasSummableMajorant → False := by
  intro hmajorant
  have hs := gap14 hmajorant
  have hnot : ¬Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ))) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (mt (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).mp
        Real.not_summable_one_div_natCast)
  exact hnot hs

theorem gap16 :
    ¬ HasSummableMajorant := by
  exact gap15

theorem gap17 :
    (∀ x : ℝ, Summable (fun n : ℕ => |f (n + 1) x|)) ∧
    SeriesUniformlyConvergesOn
      (fun n x => f (n + 1) x)
      (Set.Icc (0 : ℝ) 1)
      (fun x => ∑' n : ℕ, f (n + 1) x) ∧
    ¬ HasSummableMajorant := by
  exact ⟨gap4, gap5, gap16⟩

end

end ProofGap.Exercise2786
