import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise2771

noncomputable section

open Filter
open scoped BigOperators

def term (k : ℕ) (x : ℝ) : ℝ :=
  x / ((((k : ℝ) - 1) * x + 1) * ((k : ℝ) * x + 1))

def telescopingTerm (k : ℕ) (x : ℝ) : ℝ :=
  1 / (((k : ℝ) - 1) * x + 1) - 1 / ((k : ℝ) * x + 1)

def partialSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, term k x

def telescopingSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, telescopingTerm k x

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (n + 1), u k x) - f x| < ε

private theorem rangeShiftSum_eq_partialSum (n : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range n, term (k + 1) x) = partialSum n x := by
  induction n with
  | zero =>
      simp [partialSum]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hmem : Nat.succ n ∉ Finset.Icc 1 n := by
        simp
      have hset :
          Finset.Icc 1 (Nat.succ n) =
            insert (Nat.succ n) (Finset.Icc 1 n) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      change partialSum n x + term (Nat.succ n) x =
        ∑ k ∈ Finset.Icc 1 (Nat.succ n), term k x
      rw [hset, Finset.sum_insert hmem]
      simpa only [partialSum] using
        (add_comm (partialSum n x) (term (Nat.succ n) x))

private theorem hasSum_iff_tendsto_nat
    (x : ℝ) (hx : 0 < x) :
    HasSum (fun n => term (n + 1) x) 1 ↔
      Tendsto
        (fun n => ∑ k ∈ Finset.range n, term (k + 1) x)
        atTop (nhds 1) := by
  have hnonneg : ∀ m : ℕ, 0 ≤ term (m + 1) x := by
    intro m
    unfold term
    have hm : 1 ≤ m + 1 := by omega
    have hmR : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
      have hcast : ((1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) :=
        (Nat.cast_le).2 hm
      simpa only [Nat.cast_one] using hcast
    have hAprod :
        0 ≤ (((m + 1 : ℕ) : ℝ) - 1) * x :=
      mul_nonneg (sub_nonneg.mpr hmR) (le_of_lt hx)
    have hApos :
        0 < (((m + 1 : ℕ) : ℝ) - 1) * x + 1 :=
      add_pos_of_nonneg_of_pos hAprod zero_lt_one
    have hmRpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) :=
      lt_of_lt_of_le zero_lt_one hmR
    have hBprod : 0 < ((m + 1 : ℕ) : ℝ) * x :=
      mul_pos hmRpos hx
    have hBpos : 0 < ((m + 1 : ℕ) : ℝ) * x + 1 :=
      add_pos hBprod zero_lt_one
    exact div_nonneg (le_of_lt hx) (le_of_lt (mul_pos hApos hBpos))
  exact (hasSum_iff_tendsto_nat_of_nonneg hnonneg) (1 : ℝ)

theorem gap1 (n : ℕ) (x : ℝ) (hx : 0 < x) :
    partialSum n x = telescopingSum n x := by
  unfold partialSum telescopingSum
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_Icc] at hk
  unfold term telescopingTerm
  let A : ℝ := ((k : ℝ) - 1) * x + 1
  let B : ℝ := (k : ℝ) * x + 1
  change x / (A * B) = 1 / A - 1 / B
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by
    have hcast : ((1 : ℕ) : ℝ) ≤ ((k : ℕ) : ℝ) :=
      (Nat.cast_le).2 hk.1
    simpa only [Nat.cast_one] using hcast
  have hAprod :
      0 ≤ (((k : ℝ) - 1) * x) :=
    mul_nonneg (sub_nonneg.mpr hk') (le_of_lt hx)
  have hApos : 0 < A := by
    dsimp [A]
    exact add_pos_of_nonneg_of_pos hAprod zero_lt_one
  have hkpos : (0 : ℝ) < (k : ℝ) :=
    lt_of_lt_of_le zero_lt_one hk'
  have hBprod : 0 < (k : ℝ) * x := mul_pos hkpos hx
  have hBpos : 0 < B := by
    dsimp [B]
    exact add_pos hBprod zero_lt_one
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hBne : B ≠ 0 := ne_of_gt hBpos
  have hBA : B - A = x := by
    dsimp [A, B]
    ring
  have hleft : (1 / A) * (A * B) = B := by
    rw [one_div, ← mul_assoc, inv_mul_cancel₀ hAne, one_mul]
  have hright : (1 / B) * (A * B) = A := by
    calc
      (1 / B) * (A * B) = (1 / B) * (B * A) := by
        rw [mul_comm A B]
      _ = A := by
        rw [one_div, ← mul_assoc, inv_mul_cancel₀ hBne, one_mul]
  apply (div_eq_iff (mul_ne_zero hAne hBne)).2
  rw [sub_mul, hleft, hright, hBA]

theorem gap2 (n : ℕ) (x : ℝ) :
    telescopingSum n x = 1 - 1 / ((n : ℝ) * x + 1) := by
  induction n with
  | zero =>
      norm_num [telescopingSum]
  | succ n ih =>
      have hmem : Nat.succ n ∉ Finset.Icc 1 n := by
        simp
      have hset :
          Finset.Icc 1 (Nat.succ n) =
            insert (Nat.succ n) (Finset.Icc 1 n) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      change (∑ k ∈ Finset.Icc 1 (Nat.succ n), telescopingTerm k x) = _
      rw [hset, Finset.sum_insert hmem]
      change telescopingTerm (Nat.succ n) x + telescopingSum n x = _
      rw [ih]
      simp only [telescopingTerm, Nat.cast_succ, add_sub_cancel_right]
      ring

theorem gap3 (n : ℕ) (x : ℝ) (hx : 0 < x) :
    partialSum n x = 1 - 1 / ((n : ℝ) * x + 1) := by
  calc
    partialSum n x = telescopingSum n x := gap1 n x hx
    _ = 1 - 1 / ((n : ℝ) * x + 1) := gap2 n x

theorem gap4 (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n => partialSum n x) atTop (nhds 1) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (ε * x))
  refine ⟨N, ?_⟩
  intro n hn
  have hεx : 0 < ε * x := mul_pos hε hx
  have hNprod : 1 < (N : ℝ) * (ε * x) :=
    (div_lt_iff₀ hεx).mp hN
  have hnR : (N : ℝ) ≤ (n : ℝ) := by
    exact (Nat.cast_le).2 hn
  have hmul : (N : ℝ) * (ε * x) ≤ (n : ℝ) * (ε * x) :=
    mul_le_mul_of_nonneg_right hnR (le_of_lt hεx)
  have hlarge : 1 < ε * ((n : ℝ) * x + 1) := by
    nlinarith
  have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : 0 < (n : ℝ) * x + 1 := by
    nlinarith [mul_nonneg hnnonneg (le_of_lt hx)]
  have hbound : 1 / ((n : ℝ) * x + 1) < ε :=
    (div_lt_iff₀ hden).2 hlarge
  rw [gap3 n x hx, Real.dist_eq]
  calc
    |(1 - 1 / ((n : ℝ) * x + 1)) - 1| =
        |-(1 / ((n : ℝ) * x + 1))| := by ring
    _ = 1 / ((n : ℝ) * x + 1) := by
      rw [abs_neg, abs_of_pos (one_div_pos.mpr hden)]
    _ < ε := hbound

theorem gap5 (n : ℕ) (hn : 1 ≤ n) :
    |partialSum n (1 / (n : ℝ)) - 1| = 1 / 2 := by
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnR : 0 < (n : ℝ) := by
    exact (Nat.cast_pos).2 hnpos
  have hx : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnR
  rw [gap3 n (1 / (n : ℝ)) hx]
  have hmul : (n : ℝ) * (1 / (n : ℝ)) = 1 := by
    field_simp [ne_of_gt hnR]
  rw [hmul]
  norm_num

theorem gap6 (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    (1 / 2 : ℝ) > ε := by
  exact hεhalf

theorem gap7 (n : ℕ) (hn : 1 ≤ n) (ε : ℝ)
    (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    |partialSum n (1 / (n : ℝ)) - 1| > ε := by
  rw [gap5 n hn]
  exact gap6 ε hε hεhalf

theorem gap8 :
    ¬ SeriesUniformlyConvergesOn
      (fun n x => term (n + 1) x)
      (Set.Ioi (0 : ℝ))
      (fun _ => 1) := by
  intro huniform
  unfold SeriesUniformlyConvergesOn at huniform
  obtain ⟨N, hN⟩ := huniform (1 / 4) (by norm_num)
  let m : ℕ := N + 1
  have hm : 1 ≤ m := by
    dsimp [m]
    omega
  have hmpos : 0 < (m : ℝ) := by
    exact (Nat.cast_pos).2 (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hxmem : 1 / (m : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    change 0 < 1 / (m : ℝ)
    exact one_div_pos.mpr hmpos
  have hu := hN N (le_refl N) (1 / (m : ℝ)) hxmem
  change
    |(∑ k ∈ Finset.range (N + 1), term (k + 1) (1 / (m : ℝ))) - 1| <
      1 / 4 at hu
  rw [rangeShiftSum_eq_partialSum] at hu
  have hlower := gap7 m hm (1 / 4) (by norm_num) (by norm_num)
  dsimp [m] at hu hlower
  exact (not_lt_of_ge (le_of_lt hlower)) hu

theorem gap9 :
    (∀ x ∈ Set.Ioi (0 : ℝ),
      HasSum (fun n => term (n + 1) x) 1) ∧
    ¬ SeriesUniformlyConvergesOn
      (fun n x => term (n + 1) x)
      (Set.Ioi (0 : ℝ))
      (fun _ => 1) := by
  constructor
  · intro x hx
    have hxpos : 0 < x := by
      simpa only [Set.mem_Ioi] using hx
    apply (hasSum_iff_tendsto_nat x hxpos).2
    simpa only [rangeShiftSum_eq_partialSum] using gap4 x hxpos
  · exact gap8

end

end ProofGap.Exercise2771
