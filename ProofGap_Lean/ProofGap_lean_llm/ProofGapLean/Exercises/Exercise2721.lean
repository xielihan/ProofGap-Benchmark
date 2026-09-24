import ProofGapLean.Prelude.Analysis
import ProofGapLean.Prelude.Discrete
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Positivity
import Mathlib.Order.Filter.AtTopBot.Defs

namespace ProofGap.Exercise2721

noncomputable section

open Filter

def comparison (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n / (n : ℝ) ^ 2

def term (x : ℝ) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * Real.sin x ^ n / (n : ℝ) ^ 2

def nearIntegerMultiple (x : ℝ) (strict : Bool) : Prop :=
  ∃ k : ℤ,
    if strict then |x - (k : ℝ) * Real.pi| < Real.pi / 6
    else |x - (k : ℝ) * Real.pi| ≤ Real.pi / 6

private theorem comparison_ratio_eq (n : ℕ) :
    comparison (n + 1) / comparison (n + 2) =
      (1 / 2 : ℝ) * (1 + 1 / (((n + 1 : ℕ) : ℝ))) ^ 2 := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  simp only [comparison, Nat.cast_add, Nat.cast_one]
  simp [pow_succ]
  field_simp [ne_of_gt hn1, ne_of_gt hn2, pow_ne_zero]
  ring

private theorem half_shifted_tendsto :
    Tendsto
      (fun n : ℕ => (1 / 2 : ℝ) *
        (1 + 1 / (((n + 1 : ℕ) : ℝ))) ^ 2)
      atTop (nhds (1 / 2 : ℝ)) := by
  have hone :
      Tendsto (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)))
        atTop (nhds (0 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat
  have h :
      Tendsto
        (fun n : ℕ => (1 / 2 : ℝ) *
          (1 + 1 / (((n + 1 : ℕ) : ℝ))) ^ 2)
        atTop (nhds ((1 / 2 : ℝ) * (1 + 0) ^ 2)) :=
    tendsto_const_nhds.mul ((tendsto_const_nhds.add hone).pow 2)
  simpa using h

private theorem abs_sin_sub_int_mul_pi (x : ℝ) (k : ℤ) :
    |Real.sin x| = |Real.sin (x - (k : ℝ) * Real.pi)| := by
  have hx : x = (x - (k : ℝ) * Real.pi) + (k : ℝ) * Real.pi := by ring
  rw [hx, Real.sin_add_int_mul_pi]
  simp [abs_mul]

private theorem abs_sin_centered (y : ℝ)
    (hy : |y| ≤ Real.pi / 2) :
    (|Real.sin y| < 1 / 2 ↔ |y| < Real.pi / 6) ∧
    (|Real.sin y| ≤ 1 / 2 ↔ |y| ≤ Real.pi / 6) ∧
    (|Real.sin y| = 1 / 2 ↔ |y| = Real.pi / 6) := by
  have habs : |Real.sin y| = Real.sin |y| := by
    rcases le_total 0 y with h0 | h0
    · have hypi : y ≤ Real.pi := by
        have := hy
        rw [abs_of_nonneg h0] at this
        nlinarith [Real.pi_pos]
      have hsin : 0 ≤ Real.sin y :=
        Real.sin_nonneg_of_nonneg_of_le_pi h0 hypi
      simp [abs_of_nonneg h0, abs_of_nonneg hsin]
    · have hny0 : 0 ≤ -y := neg_nonneg.mpr h0
      have hnypi : -y ≤ Real.pi := by
        have := hy
        rw [abs_of_nonpos h0] at this
        nlinarith [Real.pi_pos]
      have hsin : 0 ≤ Real.sin (-y) :=
        Real.sin_nonneg_of_nonneg_of_le_pi hny0 hnypi
      rw [abs_of_nonpos h0]
      rw [← abs_neg (Real.sin y), ← Real.sin_neg]
      exact abs_of_nonneg hsin
  have ha : |y| ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · nlinarith [abs_nonneg y, Real.pi_pos]
    · exact hy
  have hb : Real.pi / 6 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  constructor
  · rw [habs, ← Real.sin_pi_div_six]
    exact Real.strictMonoOn_sin.lt_iff_lt ha hb
  constructor
  · rw [habs, ← Real.sin_pi_div_six]
    exact Real.strictMonoOn_sin.le_iff_le ha hb
  · rw [habs, ← Real.sin_pi_div_six]
    exact Real.strictMonoOn_sin.eq_iff_eq ha hb

private theorem exists_centered_int (x : ℝ) :
    ∃ k : ℤ,
      |x - (k : ℝ) * Real.pi| ≤ Real.pi / 2 ∧
      |Real.sin x| = |Real.sin (x - (k : ℝ) * Real.pi)| := by
  let k : ℤ := ⌊x / Real.pi + (1 / 2 : ℝ)⌋
  have hk : (k : ℝ) ≤ x / Real.pi + (1 / 2 : ℝ) := by
    exact Int.floor_le _
  have hxk : x / Real.pi + (1 / 2 : ℝ) < (k : ℝ) + 1 := by
    exact Int.lt_floor_add_one _
  have hk' := mul_le_mul_of_nonneg_right hk (le_of_lt Real.pi_pos)
  have hxk' := mul_lt_mul_of_pos_right hxk Real.pi_pos
  have hpine : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  simp only [add_mul] at hk' hxk'
  rw [div_mul_cancel₀ x hpine] at hk' hxk'
  refine ⟨k, ?_, abs_sin_sub_int_mul_pi x k⟩
  rw [abs_le]
  constructor <;> nlinarith

private theorem abs_sin_global_iff (x : ℝ) :
    (|Real.sin x| < 1 / 2 ↔
      ∃ k : ℤ, |x - (k : ℝ) * Real.pi| < Real.pi / 6) ∧
    (|Real.sin x| ≤ 1 / 2 ↔
      ∃ k : ℤ, |x - (k : ℝ) * Real.pi| ≤ Real.pi / 6) := by
  constructor
  · constructor
    · intro hx
      rcases exists_centered_int x with ⟨k, hk, hper⟩
      refine ⟨k, ?_⟩
      exact (abs_sin_centered (x - (k : ℝ) * Real.pi) hk).1.mp (by simpa [hper] using hx)
    · rintro ⟨k, hk⟩
      have hhalf : |x - (k : ℝ) * Real.pi| ≤ Real.pi / 2 := by
        exact le_trans (le_of_lt hk) (by nlinarith [Real.pi_pos])
      have hlocal :=
        (abs_sin_centered (x - (k : ℝ) * Real.pi) hhalf).1.mpr hk
      rw [abs_sin_sub_int_mul_pi x k]
      exact hlocal
  · constructor
    · intro hx
      rcases exists_centered_int x with ⟨k, hk, hper⟩
      refine ⟨k, ?_⟩
      exact (abs_sin_centered (x - (k : ℝ) * Real.pi) hk).2.1.mp (by simpa [hper] using hx)
    · rintro ⟨k, hk⟩
      have hhalf : |x - (k : ℝ) * Real.pi| ≤ Real.pi / 2 := by
        exact le_trans hk (by nlinarith [Real.pi_pos])
      have hlocal :=
        (abs_sin_centered (x - (k : ℝ) * Real.pi) hhalf).2.1.mpr hk
      rw [abs_sin_sub_int_mul_pi x k]
      exact hlocal

private theorem abs_term_eq (x : ℝ) (n : ℕ) :
    |term x n| = comparison n * |Real.sin x| ^ n := by
  simp only [term, comparison, abs_div, abs_mul, abs_pow]
  have htwo : |(2 : ℝ)| = 2 := abs_of_nonneg (by norm_num)
  have hn : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
  rw [htwo, hn]
  ring

theorem gap1 :
    Tendsto
      (fun n : ℕ => comparison (n + 1) / comparison (n + 2))
      atTop (nhds (1 / 2 : ℝ)) := by
  exact half_shifted_tendsto.congr'
    (Filter.Eventually.of_forall (fun n => (comparison_ratio_eq n).symm))

theorem gap2 :
    Tendsto
      (fun n : ℕ => (1 / 2 : ℝ) * (1 + 1 / ((n + 1 : ℕ) : ℝ)) ^ 2)
      atTop (nhds (1 / 2 : ℝ)) := by
  exact half_shifted_tendsto

theorem gap3 :
    Tendsto
      (fun n : ℕ => comparison (n + 1) / comparison (n + 2))
      atTop (nhds (1 / 2 : ℝ)) := by
  exact gap1

theorem gap4 (x : ℝ) (hx : |Real.sin x| < 1 / 2) :
    Summable (fun n : ℕ => |term x (n + 1)|) := by
  let r : ℝ := 2 * |Real.sin x|
  have hr0 : 0 ≤ r := by
    exact mul_nonneg (by norm_num) (abs_nonneg _)
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    dsimp [r]
    nlinarith
  have hs0 : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_norm_lt_one hr
  have hs : Summable (fun n : ℕ => r ^ (n + 1)) :=
    (summable_nat_add_iff 1).2 hs0
  refine hs.of_norm_bounded ?_
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _), abs_term_eq]
  have hm : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one]
    exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hm2 : (1 : ℝ) ≤ (((n + 1 : ℕ) : ℝ) ^ 2) := by
    nlinarith [sq_nonneg ((((n + 1 : ℕ) : ℝ) - 1))]
  have heq :
      comparison (n + 1) * |Real.sin x| ^ (n + 1) =
        r ^ (n + 1) / (((n + 1 : ℕ) : ℝ) ^ 2) := by
    dsimp [comparison, r]
    rw [mul_pow]
    ring
  rw [heq]
  have hdenpos : (0 : ℝ) < (((n + 1 : ℕ) : ℝ) ^ 2) :=
    lt_of_lt_of_le (by norm_num) hm2
  apply (div_le_iff₀ hdenpos).2
  have hrpow : 0 ≤ r ^ (n + 1) := pow_nonneg hr0 _
  nlinarith

theorem gap5 (x : ℝ) :
    |Real.sin x| < 1 / 2 ↔
      ∃ k : ℤ, |x - (k : ℝ) * Real.pi| < Real.pi / 6 := by
  exact (abs_sin_global_iff x).1

theorem gap6 (x : ℝ)
    (hx : ∃ k : ℤ, |x - (k : ℝ) * Real.pi| = Real.pi / 6) :
    ∀ n : ℕ, 1 ≤ n → |term x n| = 1 / (n : ℝ) ^ 2 := by
  rcases hx with ⟨k, hk⟩
  let y : ℝ := x - (k : ℝ) * Real.pi
  have hy : |y| ≤ Real.pi / 2 := by
    dsimp [y]
    rw [hk]
    nlinarith [Real.pi_pos]
  have hsy : |Real.sin y| = 1 / 2 :=
    (abs_sin_centered y hy).2.2.mpr (by simpa [y] using hk)
  have hsper := abs_sin_sub_int_mul_pi x k
  have hs : |Real.sin x| = 1 / 2 := by
    rw [hsper]
    exact hsy
  intro n hn
  rw [abs_term_eq, comparison, hs]
  rw [div_mul_eq_mul_div, ← mul_pow]
  norm_num

theorem gap7 :
    Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
  let a : ℕ → ℝ := fun n => 2 / ((n : ℝ) + 1)
  let g : ℕ → ℝ := fun n => a n - a (n + 1)
  have hsum : ∀ N : ℕ,
      Finset.sum (Finset.range N) g = a 0 - a N := by
    intro N
    induction N with
    | zero =>
        simp
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        change (a 0 - a N) + (a N - a (N + 1)) =
          a 0 - a (N + 1)
        ring
  have ha : Tendsto a atTop (nhds (0 : ℝ)) := by
    have h :
        Tendsto
          (fun n : ℕ => (2 : ℝ) * (1 / ((n : ℝ) + 1)))
          atTop (nhds ((2 : ℝ) * 0)) :=
      (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2)).mul
        tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [a, div_eq_mul_inv] using h
  have hgeq (n : ℕ) :
      g n = 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    dsimp [g, a]
    simp only [Nat.cast_add, Nat.cast_one]
    have hadd : (n : ℝ) + 1 + 1 = (n : ℝ) + 2 := by ring
    rw [hadd]
    have hn1 : 0 < (n : ℝ) + 1 := by positivity
    have hn2 : 0 < (n : ℝ) + 2 := by positivity
    field_simp [ne_of_gt hn1, ne_of_gt hn2] <;> ring
  have hgnonneg (n : ℕ) : 0 ≤ g n := by
    rw [hgeq n]
    positivity
  have finite_subset_range (s : Finset ℕ) :
      ∃ N : ℕ, s ⊆ Finset.range N := by
    classical
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨0, by simp⟩
    | @insert n s hn ih =>
        rcases ih with ⟨N, hN⟩
        refine ⟨max (n + 1) N, ?_⟩
        intro m hm
        simp only [Finset.mem_insert, Finset.mem_range] at hm ⊢
        rcases hm with rfl | hm
        · exact lt_of_lt_of_le (Nat.lt_succ_self m) (le_max_left _ _)
        · exact lt_of_lt_of_le (Finset.mem_range.mp (hN hm))
            (le_max_right _ _)
  have hpartial :
      Tendsto (fun N : ℕ => a 0 - a N) atTop (nhds (2 : ℝ)) := by
    have hlim :
        Tendsto (fun N : ℕ => a 0 - a N) atTop
          (nhds (a 0 - 0)) :=
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => a 0) atTop (nhds (a 0))).sub ha
    have ha0 : a 0 = (2 : ℝ) := by
      norm_num [a]
    simpa [ha0] using hlim
  have hg : Summable g := by
    have hhas : HasSum g (2 : ℝ) := by
      change Tendsto (fun s : Finset ℕ => Finset.sum s g)
        atTop (nhds (2 : ℝ))
      apply tendsto_order.2
      constructor
      · intro b hb
        have hev : ∀ᶠ N : ℕ in atTop, b < a 0 - a N :=
          (tendsto_order.1 hpartial).1 b hb
        rcases eventually_atTop.1 hev with ⟨N, hN⟩
        refine (eventually_ge_atTop (Finset.range N)).mono ?_
        intro s hs
        have hbase : b < Finset.sum (Finset.range N) g := by
          rw [hsum N]
          exact hN N le_rfl
        have hle :
            Finset.sum (Finset.range N) g ≤ Finset.sum s g :=
          Finset.sum_le_sum_of_subset_of_nonneg hs
            (fun n _ _ => hgnonneg n)
        exact lt_of_lt_of_le hbase hle
      · intro b hb
        refine Filter.Eventually.of_forall ?_
        intro s
        rcases finite_subset_range s with ⟨N, hs⟩
        have hle :
            Finset.sum s g ≤ Finset.sum (Finset.range N) g :=
          Finset.sum_le_sum_of_subset_of_nonneg hs
            (fun n _ _ => hgnonneg n)
        have haN : 0 < a N := by
          dsimp [a]
          positivity
        have ha0 : a 0 = (2 : ℝ) := by
          norm_num [a]
        have hlt : a 0 - a N < (2 : ℝ) := by
          rw [ha0]
          linarith
        calc
          Finset.sum s g ≤ Finset.sum (Finset.range N) g := hle
          _ = a 0 - a N := hsum N
          _ < (2 : ℝ) := hlt
          _ < b := hb
    exact hhas.summable
  refine hg.of_norm_bounded ?_
  intro n
  have hn1 : 0 < (n : ℝ) + 1 := by positivity
  have hn2 : 0 < (n : ℝ) + 2 := by positivity
  have htarget :
      0 ≤ 1 / (((n + 1 : ℕ) : ℝ) ^ 2) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg htarget, hgeq n]
  simp only [Nat.cast_add, Nat.cast_one]
  apply (div_le_div_iff₀ (pow_pos hn1 2) (mul_pos hn1 hn2)).2
  nlinarith [mul_nonneg (Nat.cast_nonneg n) (le_of_lt hn1)]

theorem gap8 (x : ℝ)
    (hx : ∃ k : ℤ, |x - (k : ℝ) * Real.pi| = Real.pi / 6) :
    Summable (fun n : ℕ => |term x (n + 1)|) := by
  have hfun :
      (fun n : ℕ => |term x (n + 1)|) =
        (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    funext n
    exact gap6 x hx (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  rw [hfun]
  exact gap7

theorem gap9 (x : ℝ)
    (hx : ∃ k : ℤ, |x - (k : ℝ) * Real.pi| ≤ Real.pi / 6) :
    Summable (fun n : ℕ => |term x (n + 1)|) := by
  rcases hx with ⟨k, hk⟩
  rcases lt_or_eq_of_le hk with hlt | heq
  · exact gap4 x ((gap5 x).2 ⟨k, hlt⟩)
  · exact gap8 x ⟨k, heq⟩

theorem gap10 (x : ℝ) :
    Summable (fun n : ℕ => |term x (n + 1)|) ↔
      ∃ k : ℤ, |x - (k : ℝ) * Real.pi| ≤ Real.pi / 6 := by
  constructor
  · intro hsum
    by_contra hne
    have hsnot : ¬ |Real.sin x| ≤ 1 / 2 := by
      intro hs
      exact hne ((abs_sin_global_iff x).2.mp hs)
    have hs : 1 / 2 < |Real.sin x| := lt_of_not_ge hsnot
    have hs0 : 0 < |Real.sin x| := by nlinarith
    have hev :
        ∀ᶠ n : ℕ in atTop,
          comparison (n + 1) / comparison (n + 2) < |Real.sin x| :=
      (tendsto_order.1 gap1).2 _ hs
    rcases eventually_atTop.1 hev with ⟨N, hN⟩
    have hinc : ∀ n : ℕ, N ≤ n →
        |term x (n + 1)| < |term x ((n + 1) + 1)| := by
      intro n hn
      have hcpos : 0 < comparison (n + 2) := by
        unfold comparison
        positivity
      have hc :
          comparison (n + 1) <
            |Real.sin x| * comparison (n + 2) :=
        (div_lt_iff₀ hcpos).mp (hN n hn)
      calc
        |term x (n + 1)| =
            comparison (n + 1) * |Real.sin x| ^ (n + 1) :=
              abs_term_eq x (n + 1)
        _ < (|Real.sin x| * comparison (n + 2)) *
              |Real.sin x| ^ (n + 1) :=
              mul_lt_mul_of_pos_right hc (pow_pos hs0 _)
        _ = comparison (n + 2) * |Real.sin x| ^ ((n + 1) + 1) := by
              rw [pow_succ]
              ring
        _ = |term x ((n + 1) + 1)| := by
              simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                (abs_term_eq x ((n + 1) + 1)).symm
    have hmono : Monotone (fun m : ℕ => |term x (N + m + 1)|) := by
      apply monotone_nat_of_le_succ
      intro m
      have hi := hinc (N + m) (Nat.le_add_right N m)
      simpa only [Nat.add_assoc] using le_of_lt hi
    have hfN : 0 < |term x (N + 1)| := by
      rw [abs_term_eq]
      exact mul_pos (by unfold comparison; positivity) (pow_pos hs0 _)
    have hzero : Tendsto (fun n : ℕ => |term x (n + 1)|) atTop (nhds 0) :=
      hsum.tendsto_atTop_zero
    have hevsmall : ∀ᶠ n : ℕ in atTop, |term x (n + 1)| < |term x (N + 1)| :=
      (tendsto_order.1 hzero).2 _ hfN
    rcases eventually_atTop.1 hevsmall with ⟨M, hM⟩
    let n := max N M
    have hNn : N ≤ n := le_max_left N M
    have hMn : M ≤ n := le_max_right N M
    have hle := hmono (Nat.zero_le (n - N))
    have hle' : |term x (N + 1)| ≤ |term x (n + 1)| := by
      simpa [Nat.add_sub_of_le hNn, Nat.add_assoc] using hle
    exact (not_lt_of_ge hle') (hM n hMn)
  · intro hx
    exact gap9 x hx

end

end ProofGap.Exercise2721
