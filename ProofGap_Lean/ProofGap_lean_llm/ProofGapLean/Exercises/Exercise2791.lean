import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace ProofGap.Exercise2791

noncomputable section

open scoped BigOperators

def weight (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-((n : ℝ) * x))

def term (a : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  a n * weight n x

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (n + 1), u k x) - g x| < ε

private theorem abel_sum_identity (b w : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), b i * w i) =
      (∑ i ∈ Finset.range (n + 1), b i) * w n +
        ∑ i ∈ Finset.range n,
          (∑ j ∈ Finset.range (i + 1), b j) * (w i - w (i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hleft :
          (∑ i ∈ Finset.range (n + 2), b i * w i) =
            (∑ i ∈ Finset.range (n + 1), b i * w i) + b (n + 1) * w (n + 1) := by
        simpa [Nat.succ_eq_add_one, add_assoc] using
          (Finset.sum_range_succ (fun i => b i * w i) (n + 1))
      have hprefix :
          (∑ i ∈ Finset.range (n + 2), b i) =
            (∑ i ∈ Finset.range (n + 1), b i) + b (n + 1) := by
        simpa [Nat.succ_eq_add_one, add_assoc] using
          (Finset.sum_range_succ b (n + 1))
      have hcorr :
          (∑ i ∈ Finset.range (n + 1),
              (∑ j ∈ Finset.range (i + 1), b j) * (w i - w (i + 1))) =
            (∑ i ∈ Finset.range n,
              (∑ j ∈ Finset.range (i + 1), b j) * (w i - w (i + 1))) +
              (∑ j ∈ Finset.range (n + 1), b j) * (w n - w (n + 1)) := by
        simpa [Nat.succ_eq_add_one] using
          (Finset.sum_range_succ
            (fun i => (∑ j ∈ Finset.range (i + 1), b j) *
              (w i - w (i + 1))) n)
      rw [hleft, ih, hprefix, hcorr]
      ring

private theorem weighted_telescoping (w : ℕ → ℝ) (δ : ℝ) (n : ℕ) :
    δ * w n + ∑ i ∈ Finset.range n, δ * (w i - w (i + 1)) =
      δ * w 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        δ * w (n + 1) +
              ((∑ i ∈ Finset.range n, δ * (w i - w (i + 1))) +
                δ * (w n - w (n + 1))) =
            δ * w n + ∑ i ∈ Finset.range n, δ * (w i - w (i + 1)) := by
          ring
        _ = δ * w 0 := ih

private theorem weighted_sum_bound
    (b w : ℕ → ℝ) (L : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hb : ∀ j < L, |∑ i ∈ Finset.range (j + 1), b i| < δ)
    (hwpos : ∀ i, 0 < w i)
    (hwmono : ∀ i, w (i + 1) ≤ w i)
    (hw0 : w 0 ≤ 1) :
    |∑ i ∈ Finset.range L, b i * w i| < δ := by
  cases L with
  | zero => simpa using hδ
  | succ n =>
      rw [abel_sum_identity]
      have hend :
          |(∑ i ∈ Finset.range (n + 1), b i) * w n| < δ * w n := by
        rw [abs_mul, abs_of_pos (hwpos n)]
        exact mul_lt_mul_of_pos_right (hb n (Nat.lt_succ_self n)) (hwpos n)
      have hcorr :
          |∑ i ∈ Finset.range n,
              (∑ j ∈ Finset.range (i + 1), b j) * (w i - w (i + 1))| ≤
            ∑ i ∈ Finset.range n, δ * (w i - w (i + 1)) := by
        calc
          |∑ i ∈ Finset.range n,
              (∑ j ∈ Finset.range (i + 1), b j) * (w i - w (i + 1))| ≤
              ∑ i ∈ Finset.range n,
                |(∑ j ∈ Finset.range (i + 1), b j) *
                  (w i - w (i + 1))| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i ∈ Finset.range n, δ * (w i - w (i + 1)) := by
            apply Finset.sum_le_sum
            intro i hi
            have hi' : i < n := Finset.mem_range.mp hi
            have hd : 0 ≤ w i - w (i + 1) := sub_nonneg.mpr (hwmono i)
            rw [abs_mul, abs_of_nonneg hd]
            exact mul_le_mul_of_nonneg_right
              (le_of_lt (hb i (Nat.lt_succ_of_lt hi'))) hd
      have htel :
          δ * w n + ∑ i ∈ Finset.range n, δ * (w i - w (i + 1)) =
            δ * w 0 := weighted_telescoping w δ n
      calc
        |(∑ i ∈ Finset.range (n + 1), b i) * w n +
            ∑ i ∈ Finset.range n,
              (∑ j ∈ Finset.range (i + 1), b j) * (w i - w (i + 1))| ≤
            |(∑ i ∈ Finset.range (n + 1), b i) * w n| +
              |∑ i ∈ Finset.range n,
                (∑ j ∈ Finset.range (i + 1), b j) *
                  (w i - w (i + 1))| := abs_add_le _ _
        _ < δ * w n +
              ∑ i ∈ Finset.range n, δ * (w i - w (i + 1)) :=
          add_lt_add_of_lt_of_le hend hcorr
        _ = δ * w 0 := htel
        _ ≤ δ := by nlinarith

theorem gap1 (n : ℕ) (x : ℝ) :
    0 < weight n x := by
  exact Real.exp_pos _

theorem gap2 (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    weight n x ≤ 1 := by
  unfold weight
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg n) hx)

theorem gap3 :
    (0 : ℝ) < 1 := by
  norm_num

theorem gap4 (n : ℕ) (x : ℝ) (hx : 0 < x) :
    weight n x > weight (n + 1) x := by
  unfold weight
  apply Real.exp_lt_exp.mpr
  simp only [Nat.cast_add, Nat.cast_one]
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

theorem gap5 (a : ℕ → ℝ)
    (hsum : Summable (fun n : ℕ => a (n + 1))) :
    SeriesUniformlyConvergesOn
      (fun n (_x : ℝ) => a (n + 1))
      (Set.Ici (0 : ℝ))
      (fun _ => ∑' n : ℕ, a (n + 1)) := by
  unfold SeriesUniformlyConvergesOn
  intro ε hε
  have hconv :
      Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, a (k + 1)) atTop
        (nhds (∑' n : ℕ, a (n + 1))) :=
    hsum.hasSum.tendsto_sum_nat
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hconv) ε hε
  refine ⟨N, ?_⟩
  intro n hn x hx
  have hn' : N ≤ n + 1 := le_trans hn (Nat.le_succ n)
  simpa [Real.dist_eq] using hN (n + 1) hn'

theorem gap6 (a : ℕ → ℝ)
    (hsum : Summable (fun n : ℕ => a (n + 1))) :
    SeriesUniformlyConvergesOn
      (fun n x => term a (n + 1) x)
      (Set.Ici (0 : ℝ))
      (fun x => ∑' n : ℕ, term a (n + 1) x) := by
  have hconv :
      Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, a (k + 1)) atTop
        (nhds (∑' n : ℕ, a (n + 1))) :=
    hsum.hasSum.tendsto_sum_nat
  have hsource :
      ∀ η > 0, ∃ N : ℕ, ∀ K ≥ N, ∀ L : ℕ,
        |∑ i ∈ Finset.range L, a (K + i + 1)| < η := by
    intro η hη
    obtain ⟨N, hN⟩ :=
      (Metric.tendsto_atTop.mp hconv) (η / 2) (by linarith)
    refine ⟨N, ?_⟩
    intro K hK L
    have hKL : N ≤ K + L := le_trans hK (Nat.le_add_right K L)
    have hK' :
        |(∑ k ∈ Finset.range K, a (k + 1)) -
            (∑' n : ℕ, a (n + 1))| < η / 2 := by
      simpa [Real.dist_eq] using hN K hK
    have hKL' :
        |(∑ k ∈ Finset.range (K + L), a (k + 1)) -
            (∑' n : ℕ, a (n + 1))| < η / 2 := by
      simpa [Real.dist_eq] using hN (K + L) hKL
    have hsplit :
        (∑ k ∈ Finset.range (K + L), a (k + 1)) =
          (∑ k ∈ Finset.range K, a (k + 1)) +
            ∑ i ∈ Finset.range L, a (K + i + 1) := by
      rw [Finset.sum_range_add]
    have htail :
        (∑ i ∈ Finset.range L, a (K + i + 1)) =
          ((∑ k ∈ Finset.range (K + L), a (k + 1)) -
              (∑' n : ℕ, a (n + 1))) -
            ((∑ k ∈ Finset.range K, a (k + 1)) -
              (∑' n : ℕ, a (n + 1))) := by
      rw [hsplit]
      ring
    rw [htail]
    calc
      |((∑ k ∈ Finset.range (K + L), a (k + 1)) -
            (∑' n : ℕ, a (n + 1))) -
          ((∑ k ∈ Finset.range K, a (k + 1)) -
            (∑' n : ℕ, a (n + 1)))| ≤
          |(∑ k ∈ Finset.range (K + L), a (k + 1)) -
            (∑' n : ℕ, a (n + 1))| +
          |(∑ k ∈ Finset.range K, a (k + 1)) -
            (∑' n : ℕ, a (n + 1))| := abs_sub _ _
      _ < η := by linarith
  have hweighted :
      ∀ η > 0, ∃ N : ℕ, ∀ K ≥ N, ∀ L : ℕ, ∀ x ∈ Set.Ici (0 : ℝ),
        |∑ i ∈ Finset.range L, term a (K + i + 1) x| < η := by
    intro η hη
    obtain ⟨N, hN⟩ := hsource η hη
    refine ⟨N, ?_⟩
    intro K hK L x hx
    have hx0 : 0 ≤ x := hx
    have hb : ∀ j < L,
        |∑ i ∈ Finset.range (j + 1), a (K + i + 1)| < η := by
      intro j hj
      exact hN K hK (j + 1)
    have hwpos : ∀ i : ℕ, 0 < weight (K + i + 1) x := by
      intro i
      exact gap1 _ _
    have hwmono : ∀ i : ℕ,
        weight (K + (i + 1) + 1) x ≤ weight (K + i + 1) x := by
      intro i
      unfold weight
      apply Real.exp_le_exp.mpr
      simp only [Nat.cast_add, Nat.cast_one]
      have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
      have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      nlinarith
    have hw0 : weight (K + 0 + 1) x ≤ 1 := gap2 _ _ hx0
    simpa [term, add_assoc] using
      weighted_sum_bound
        (b := fun i : ℕ => a (K + i + 1))
        (w := fun i : ℕ => weight (K + i + 1) x)
        (L := L) (δ := η) hη hb hwpos hwmono hw0
  have habs : Summable (fun k : ℕ => |a (k + 1)|) := hsum.abs
  have hsummable :
      ∀ x ∈ Set.Ici (0 : ℝ), Summable (fun k : ℕ => term a (k + 1) x) := by
    intro x hx
    refine habs.of_norm_bounded ?_
    intro k
    have hwpos : 0 < weight (k + 1) x := gap1 _ _
    have hwle : weight (k + 1) x ≤ 1 := gap2 _ _ hx
    calc
      ‖term a (k + 1) x‖ = |a (k + 1)| * weight (k + 1) x := by
        rw [term, norm_mul]
        simp only [Real.norm_eq_abs, abs_of_pos hwpos]
      _ ≤ |a (k + 1)| * 1 :=
        mul_le_mul_of_nonneg_left hwle (abs_nonneg _)
      _ = |a (k + 1)| := mul_one _
  unfold SeriesUniformlyConvergesOn
  intro ε hε
  obtain ⟨N, hN⟩ := hweighted (ε / 2) (by linarith)
  refine ⟨N, ?_⟩
  intro n hn x hx
  let q : ℕ → ℝ := fun m => ∑ k ∈ Finset.range m, term a (k + 1) x
  have hsx := hsummable x hx
  have hlim : Tendsto q atTop
      (nhds (∑' k : ℕ, term a (k + 1) x)) := by
    exact hsx.hasSum.tendsto_sum_nat
  have habslim :
      Tendsto (fun m => |q m - q (n + 1)|) atTop
        (nhds |(∑' k : ℕ, term a (k + 1) x) - q (n + 1)|) :=
    (hlim.sub_const (q (n + 1))).abs
  have hev : ∀ᶠ m : ℕ in atTop, |q m - q (n + 1)| ≤ ε / 2 := by
    refine Filter.eventually_atTop.2 ⟨n + 1, ?_⟩
    intro m hm
    have hadd : (n + 1) + (m - (n + 1)) = m := Nat.add_sub_of_le hm
    have hsplit :
        q m = q (n + 1) +
          ∑ i ∈ Finset.range (m - (n + 1)), term a (n + 1 + i + 1) x := by
      dsimp [q]
      conv_lhs => rw [← hadd]
      rw [Finset.sum_range_add]
    rw [hsplit]
    simp only [add_sub_cancel_left]
    exact le_of_lt (hN (n + 1) (le_trans hn (Nat.le_succ n))
      (m - (n + 1)) x hx)
  have hle :
      |(∑' k : ℕ, term a (k + 1) x) - q (n + 1)| ≤ ε / 2 :=
    le_of_tendsto habslim hev
  change |q (n + 1) - (∑' k : ℕ, term a (k + 1) x)| < ε
  rw [abs_sub_comm]
  linarith

theorem gap7 (a : ℕ → ℝ)
    (hsum : Summable (fun n : ℕ => a (n + 1))) :
    SeriesUniformlyConvergesOn
      (fun n x => term a (n + 1) x)
      (Set.Ici (0 : ℝ))
      (fun x => ∑' n : ℕ, term a (n + 1) x) := by
  exact gap6 a hsum

end

end ProofGap.Exercise2791
