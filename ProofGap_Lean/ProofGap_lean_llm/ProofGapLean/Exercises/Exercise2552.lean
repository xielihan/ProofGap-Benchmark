import ProofGapLean.Prelude.Analysis
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2552

noncomputable section

def term (k : ℕ) : ℝ :=
  Real.sqrt (k + 2) - 2 * Real.sqrt (k + 1) + Real.sqrt k
def partialSum (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, term k

theorem gap1 (n : ℕ) :
    partialSum n = ∑ k ∈ Finset.Icc 1 n, term k := by
  rfl
theorem gap2 (n : ℕ) (hn : 1 ≤ n) :
    partialSum n =
      1 - Real.sqrt 2 + Real.sqrt (n + 2) - Real.sqrt (n + 1) := by
  induction n, hn using Nat.le_induction with
  | base =>
      norm_num [partialSum, term] <;> ring
  | succ n hn ih =>
      have hnot : n + 1 ∉ Finset.Icc 1 n := by
        simp
      have hIcc :
          Finset.Icc 1 (n + 1) =
            insert (n + 1) (Finset.Icc 1 n) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      calc
        partialSum (n + 1) = partialSum n + term (n + 1) := by
          unfold partialSum
          rw [hIcc, Finset.sum_insert hnot]
          exact add_comm _ _
        _ = 1 - Real.sqrt 2 +
              Real.sqrt (((n + 1 : ℕ) : ℝ) + 2) -
              Real.sqrt (((n + 1 : ℕ) : ℝ) + 1) := by
          have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by
            norm_num
          have hadd : (n : ℝ) + 2 = (n : ℝ) + 1 + 1 := by
            ring
          rw [ih]
          unfold term
          rw [hcast, hadd]
          ring
theorem gap3 (n : ℕ) :
    1 - Real.sqrt 2 + Real.sqrt (n + 2) - Real.sqrt (n + 1) =
      1 - Real.sqrt 2 +
        1 / (Real.sqrt (n + 2) + Real.sqrt (n + 1)) := by
  have hspos : 0 < Real.sqrt ((n : ℝ) + 1) :=
    Real.sqrt_pos.2 (show 0 < (n : ℝ) + 1 by positivity)
  have hdenpos :
      0 < Real.sqrt ((n : ℝ) + 2) + Real.sqrt ((n : ℝ) + 1) :=
    add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hspos
  have hden :
      Real.sqrt ((n : ℝ) + 2) + Real.sqrt ((n : ℝ) + 1) ≠ 0 :=
    ne_of_gt hdenpos
  have ha :
      (Real.sqrt ((n : ℝ) + 2)) ^ 2 = (n : ℝ) + 2 :=
    Real.sq_sqrt (show 0 ≤ (n : ℝ) + 2 by positivity)
  have hb :
      (Real.sqrt ((n : ℝ) + 1)) ^ 2 = (n : ℝ) + 1 :=
    Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity)
  have hdiff :
      Real.sqrt ((n : ℝ) + 2) - Real.sqrt ((n : ℝ) + 1) =
        1 / (Real.sqrt ((n : ℝ) + 2) + Real.sqrt ((n : ℝ) + 1)) := by
    apply (eq_div_iff hden).2
    calc
      (Real.sqrt ((n : ℝ) + 2) - Real.sqrt ((n : ℝ) + 1)) *
          (Real.sqrt ((n : ℝ) + 2) + Real.sqrt ((n : ℝ) + 1)) =
          (Real.sqrt ((n : ℝ) + 2)) ^ 2 -
            (Real.sqrt ((n : ℝ) + 1)) ^ 2 := by
            ring
      _ = 1 := by
        rw [ha, hb]
        ring
  calc
    1 - Real.sqrt 2 + Real.sqrt ((n : ℝ) + 2) -
          Real.sqrt ((n : ℝ) + 1) =
        1 - Real.sqrt 2 +
          (Real.sqrt ((n : ℝ) + 2) - Real.sqrt ((n : ℝ) + 1)) := by
            ring
    _ = 1 - Real.sqrt 2 +
          1 / (Real.sqrt ((n : ℝ) + 2) + Real.sqrt ((n : ℝ) + 1)) := by
            rw [hdiff]
theorem gap4 (n : ℕ) (hn : 1 ≤ n) :
    partialSum n =
      1 - Real.sqrt 2 +
        1 / (Real.sqrt (n + 2) + Real.sqrt (n + 1)) := by
  rw [gap2 n hn, gap3 n]
theorem gap5 :
    HasSum (fun k : ℕ => term (k + 1)) (1 - Real.sqrt 2) ↔
      Filter.Tendsto partialSum Filter.atTop (nhds (1 - Real.sqrt 2)) := by
  have hpartial : ∀ n : ℕ,
      (∑ k ∈ Finset.range n, term (k + 1)) = partialSum n := by
    intro n
    induction n with
    | zero =>
        simp [partialSum]
    | succ n ih =>
        have hnot : n + 1 ∉ Finset.Icc 1 n := by
          simp
        have hIcc :
            Finset.Icc 1 (n + 1) =
              insert (n + 1) (Finset.Icc 1 n) := by
          ext k
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        rw [Finset.sum_range_succ, ih]
        change
          (∑ k ∈ Finset.Icc 1 n, term k) + term (n + 1) =
            ∑ k ∈ Finset.Icc 1 (n + 1), term k
        rw [hIcc, Finset.sum_insert hnot]
        exact add_comm _ _
  have hnonneg : ∀ k : ℕ, 0 ≤ -term (k + 1) := by
    intro k
    let a : ℝ := Real.sqrt (((k + 3 : ℕ) : ℝ))
    let b : ℝ := Real.sqrt (((k + 2 : ℕ) : ℝ))
    let c : ℝ := Real.sqrt (((k + 1 : ℕ) : ℝ))
    have ha0 : 0 ≤ a := by
      dsimp [a]
      exact Real.sqrt_nonneg _
    have hb0 : 0 ≤ b := by
      dsimp [b]
      exact Real.sqrt_nonneg _
    have hc0 : 0 ≤ c := by
      dsimp [c]
      exact Real.sqrt_nonneg _
    have ha2 : a ^ 2 = ((k + 3 : ℕ) : ℝ) := by
      dsimp [a]
      exact Real.sq_sqrt (by positivity)
    have hb2 : b ^ 2 = ((k + 2 : ℕ) : ℝ) := by
      dsimp [b]
      exact Real.sq_sqrt (by positivity)
    have hc2 : c ^ 2 = ((k + 1 : ℕ) : ℝ) := by
      dsimp [c]
      exact Real.sq_sqrt (by positivity)
    have hprod2 :
        (a * c) ^ 2 = ((k + 3 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) := by
      calc
        (a * c) ^ 2 = a ^ 2 * c ^ 2 := by ring
        _ = ((k + 3 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) := by
          rw [ha2, hc2]
    have hb4 :
        (b ^ 2) ^ 2 = (((k + 2 : ℕ) : ℝ)) ^ 2 := by
      rw [hb2]
    have hnum :
        ((k + 3 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ≤
          (((k + 2 : ℕ) : ℝ)) ^ 2 := by
      norm_num [Nat.cast_add, Nat.cast_one]
      nlinarith
    have hsq : (a * c) ^ 2 ≤ (b ^ 2) ^ 2 := by
      rw [hprod2, hb4]
      exact hnum
    have hac : a * c ≤ b ^ 2 := by
      by_contra h
      have hlt : b ^ 2 < a * c := lt_of_not_ge h
      have hp : 0 < a * c - b ^ 2 := sub_pos.mpr hlt
      have hs : 0 < a * c + b ^ 2 := by
        nlinarith [mul_nonneg ha0 hc0, sq_nonneg b]
      have hm : 0 < (a * c - b ^ 2) * (a * c + b ^ 2) :=
        mul_pos hp hs
      nlinarith
    have hsumSq : (a + c) ^ 2 ≤ (2 * b) ^ 2 := by
      norm_num [Nat.cast_add, Nat.cast_one] at ha2 hb2 hc2
      nlinarith
    have hsum : a + c ≤ 2 * b := by
      by_contra h
      have hlt : 2 * b < a + c := lt_of_not_ge h
      have hp : 0 < a + c - 2 * b := sub_pos.mpr hlt
      have hs : 0 < a + c + 2 * b := by
        nlinarith
      have hm : 0 < (a + c - 2 * b) * (a + c + 2 * b) :=
        mul_pos hp hs
      nlinarith
    dsimp [a, b, c] at hsum
    norm_num [Nat.cast_add, Nat.cast_one] at hsum
    have hkcast : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by
      norm_num
    have hk2 : (k : ℝ) + 1 + 1 = (k : ℝ) + 2 := by
      ring
    have hk3 : (k : ℝ) + 1 + 2 = (k : ℝ) + 3 := by
      ring
    unfold term
    rw [hkcast, hk2, hk3]
    linarith [hsum]
  constructor
  · intro hs
    have ht := hs.tendsto_sum_nat
    simpa only [hpartial] using ht
  · intro ht
    have hrange :
        Filter.Tendsto
          (fun n : ℕ => ∑ k ∈ Finset.range n, term (k + 1))
          Filter.atTop (nhds (1 - Real.sqrt 2)) := by
      simpa only [hpartial] using ht
    have hnegRange :
        Filter.Tendsto
          (fun n : ℕ => ∑ k ∈ Finset.range n, -term (k + 1))
          Filter.atTop (nhds (-(1 - Real.sqrt 2))) := by
      simpa only [Finset.sum_neg_distrib] using hrange.neg
    have hnegSum :
        HasSum (fun k : ℕ => -term (k + 1)) (-(1 - Real.sqrt 2)) :=
      (hasSum_iff_tendsto_nat_of_nonneg hnonneg
        (-(1 - Real.sqrt 2))).2 hnegRange
    simpa only [neg_neg] using hnegSum.neg
theorem gap6 :
    Filter.Tendsto partialSum Filter.atTop (nhds (1 - Real.sqrt 2)) := by
  have hshift :
      Filter.Tendsto (fun n : ℕ => n + 1) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with n hn
    exact hn.trans (Nat.le_add_right n 1)
  have hcast :
      Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hsqrtCast :
      Filter.Tendsto
        (fun n : ℕ => Real.sqrt (((n + 1 : ℕ) : ℝ)))
        Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp (hcast.comp hshift)
  have hsqrt :
      Filter.Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) + 1))
        Filter.atTop Filter.atTop := by
    simpa only [Nat.cast_add, Nat.cast_one] using hsqrtCast
  have hden :
      Filter.Tendsto
        (fun n : ℕ => Real.sqrt (n + 2) + Real.sqrt (n + 1))
        Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [(Filter.tendsto_atTop.1 hsqrt) b] with n hn
    exact hn.trans (le_add_of_nonneg_left (Real.sqrt_nonneg _))
  have hinv :
      Filter.Tendsto
        (fun n : ℕ =>
          1 / (Real.sqrt (n + 2) + Real.sqrt (n + 1)))
        Filter.atTop (nhds 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hden
  have hconst :
      Filter.Tendsto (fun _ : ℕ => 1 - Real.sqrt 2)
        Filter.atTop (nhds (1 - Real.sqrt 2)) :=
    tendsto_const_nhds
  have hlim :
      Filter.Tendsto
        (fun n : ℕ =>
          1 - Real.sqrt 2 +
            1 / (Real.sqrt (n + 2) + Real.sqrt (n + 1)))
        Filter.atTop (nhds (1 - Real.sqrt 2)) := by
    simpa using hconst.add hinv
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact (gap4 n hn).symm
theorem gap7 :
    HasSum (fun k : ℕ => term (k + 1)) (1 - Real.sqrt 2) := by
  exact gap5.mpr gap6

end

end ProofGap.Exercise2552
