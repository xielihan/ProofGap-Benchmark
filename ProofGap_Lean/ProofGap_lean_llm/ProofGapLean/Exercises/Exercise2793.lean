import ProofGapLean.Prelude.Analysis
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise2793

noncomputable section

open Filter
open scoped BigOperators

def integers : Set ℝ :=
  Set.range (fun z : ℤ => (z : ℝ))

def term (z : ℤ) (x : ℝ) : ℝ :=
  1 / ((z : ℝ) - x) ^ 2

def f (x : ℝ) : ℝ :=
  ∑' z : ℤ, term z x

def symmetricPartialSum (N : ℕ) (x : ℝ) : ℝ :=
  ∑ z ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), term z x

def SymmetricUniformlyConvergesOn (s : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |symmetricPartialSum n x - f x| < ε

def LocalInterval (x₀ a b : ℝ) : Prop :=
  (Int.floor x₀ : ℝ) < a ∧ a < x₀ ∧
    x₀ < b ∧ b < (Int.floor x₀ : ℝ) + 1

private theorem abs_le_endpoint_max {a b x : ℝ} (hx : x ∈ Set.Icc a b) :
    |x| ≤ max |a| |b| := by
  rw [abs_le]
  constructor
  · calc
      -max |a| |b| ≤ -|a| := neg_le_neg (le_max_left |a| |b|)
      _ ≤ a := neg_abs_le a
      _ ≤ x := hx.1
  · calc
      x ≤ b := hx.2
      _ ≤ |b| := le_abs_self b
      _ ≤ max |a| |b| := le_max_right |a| |b|

private theorem shifted_reciprocal_square (p : ℝ) :
    ∃ n₀ : ℕ, Summable (fun n : ℕ => 1 / (((n + n₀ : ℕ) : ℝ) - p) ^ 2) := by
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (|p| + 1)
  refine ⟨n₀, ?_⟩
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := by
    simpa only [one_div, inv_pow] using
      (Real.summable_nat_pow_inv (p := 2)).2 (by norm_num)
  have ht : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)) ^ 2) := by
    exact (summable_nat_add_iff 1).2 hs
  apply ht.of_norm_bounded
  intro n
  have hn₀cast : |p| + 1 < (n₀ : ℝ) := hn₀
  have hp : p ≤ |p| := le_abs_self p
  have hden : ((n + 1 : ℕ) : ℝ) ≤ ((n + n₀ : ℕ) : ℝ) - p := by
    push_cast
    linarith
  have hbase : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have htarget : 0 < ((n + n₀ : ℕ) : ℝ) - p := lt_of_lt_of_le hbase hden
  have hsquares : (((n + 1 : ℕ) : ℝ)) ^ 2 ≤
      (((n + n₀ : ℕ) : ℝ) - p) ^ 2 := by
    nlinarith [sq_nonneg (((n + n₀ : ℕ) : ℝ) - p)]
  rw [Real.norm_eq_abs, abs_of_nonneg (one_div_nonneg.mpr (sq_nonneg _))]
  exact one_div_le_one_div_of_le (sq_pos_of_pos hbase) hsquares

private theorem summable_reciprocal_square (p : ℝ) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) - p) ^ 2) := by
  obtain ⟨n₀, hs⟩ := shifted_reciprocal_square p
  rw [← summable_nat_add_iff n₀]
  simpa [Nat.cast_add] using hs

private theorem localInterval_avoids_integers {x₀ a b : ℝ}
    (hab : LocalInterval x₀ a b) :
    ∀ x ∈ Set.Icc a b, x ∉ integers := by
  intro x hx
  rintro ⟨z, hzx⟩
  change (z : ℝ) = x at hzx
  have hzloR : (Int.floor x₀ : ℝ) < (z : ℝ) := by
    calc
      (Int.floor x₀ : ℝ) < a := hab.1
      _ ≤ x := hx.1
      _ = (z : ℝ) := hzx.symm
  have hzhiR : (z : ℝ) < (Int.floor x₀ : ℝ) + 1 := by
    calc
      (z : ℝ) = x := hzx
      _ ≤ b := hx.2
      _ < (Int.floor x₀ : ℝ) + 1 := hab.2.2.2
  have hzlo : Int.floor x₀ < z := by exact_mod_cast hzloR
  have hzhi : z < Int.floor x₀ + 1 := by exact_mod_cast hzhiR
  omega

private def sumNatEquivInt : ℕ ⊕ ℕ ≃ ℤ where
  toFun
    | Sum.inl n => Int.ofNat n
    | Sum.inr n => Int.negSucc n
  invFun z :=
    match z with
    | Int.ofNat n => Sum.inl n
    | Int.negSucc n => Sum.inr n
  left_inv q := by cases q <;> rfl
  right_inv z := by cases z <;> rfl

private theorem integer_series_parts (g : ℤ → ℝ)
    (hpos : Summable (fun n : ℕ => g (n : ℤ)))
    (hneg : Summable (fun n : ℕ => g (Int.negSucc n))) :
    Summable g ∧
      (∑' z : ℤ, g z) =
        (∑' n : ℕ, g (n : ℤ)) + ∑' n : ℕ, g (Int.negSucc n) := by
  have hsSum :
      HasSum
        (Sum.elim (fun n : ℕ => g (n : ℤ))
          (fun n : ℕ => g (Int.negSucc n)))
        ((∑' n : ℕ, g (n : ℤ)) + ∑' n : ℕ, g (Int.negSucc n)) :=
    hpos.hasSum.sum hneg.hasSum
  have hfun :
      (fun q : ℕ ⊕ ℕ => g (sumNatEquivInt q)) =
        Sum.elim (fun n : ℕ => g (n : ℤ))
          (fun n : ℕ => g (Int.negSucc n)) := by
    funext q
    cases q <;> rfl
  constructor
  · rw [← sumNatEquivInt.summable_iff]
    change Summable (fun q : ℕ ⊕ ℕ => g (sumNatEquivInt q))
    rw [hfun]
    exact hsSum.summable
  · calc
      (∑' z : ℤ, g z) = ∑' q : ℕ ⊕ ℕ, g (sumNatEquivInt q) := by
        symm
        exact sumNatEquivInt.tsum_eq g
      _ = (∑' n : ℕ, g (n : ℤ)) + ∑' n : ℕ, g (Int.negSucc n) := by
        rw [hfun]
        exact hsSum.tsum_eq

private theorem symmetricPartialSum_split (N : ℕ) (x : ℝ) :
    symmetricPartialSum N x =
      (∑ n ∈ Finset.range (N + 1), term (n : ℤ) x) +
        ∑ n ∈ Finset.range N, term (Int.negSucc n) x := by
  classical
  induction N with
  | zero => simp [symmetricPartialSum]
  | succ N ih =>
      have hfin :
          Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
            insert (-((N + 1 : ℕ) : ℤ))
              (insert ((N + 1 : ℕ) : ℤ)
                (Finset.Icc (-(N : ℤ)) (N : ℤ))) := by
        ext z
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hleft :
          -((N + 1 : ℕ) : ℤ) ∉
            insert ((N + 1 : ℕ) : ℤ)
              (Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
        simp
        omega
      have hright :
          ((N + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
        simp
      have hneg : -((N + 1 : ℕ) : ℤ) = Int.negSucc N := by omega
      unfold symmetricPartialSum at ih ⊢
      rw [hfin, Finset.sum_insert hleft, Finset.sum_insert hright, ih, hneg]
      simp only [Finset.sum_range_succ]
      ring

private theorem uniform_nat_partial_tails
    (u : ℕ → ℝ → ℝ) (v : ℕ → ℝ) (s : Set ℝ)
    (hv : Summable v)
    (hv0 : ∀ n : ℕ, 0 ≤ v n)
    (hu0 : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ u n x)
    (hu : ∀ x : ℝ, x ∈ s → Summable (fun n => u n x))
    (hbound : ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
      ∀ x : ℝ, x ∈ s → |u n x| ≤ v n) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x ∈ s,
      |(∑ k ∈ Finset.range n, u k x) - ∑' k, u k x| < ε := by
  intro ε hε
  have hpartial :
      Tendsto (fun n => ∑ k ∈ Finset.range n, v k) atTop
        (nhds (∑' k, v k)) :=
    hv.hasSum.tendsto_sum_nat
  have hconst :
      Tendsto (fun _ : ℕ => (∑' k : ℕ, v k)) atTop
        (nhds (∑' k : ℕ, v k)) :=
    tendsto_const_nhds
  have hd :
      Tendsto
        (fun n : ℕ =>
          (∑' k : ℕ, v k) - ∑ k ∈ Finset.range n, v k)
        atTop
        (nhds ((∑' k : ℕ, v k) - (∑' k : ℕ, v k))) :=
    hconst.sub hpartial
  have htail :
      Tendsto (fun n => ∑' k, v (k + n)) atTop (nhds 0) := by
    have heq : ∀ n,
        (∑' k, v (k + n)) =
          (∑' k, v k) - ∑ k ∈ Finset.range n, v k := by
      intro n
      have h := hv.sum_add_tsum_nat_add n
      linarith
    simpa only [sub_self] using
      hd.congr' (Filter.Eventually.of_forall (fun n => (heq n).symm))
  have hball : Metric.ball (0 : ℝ) ε ∈ nhds 0 :=
    Metric.ball_mem_nhds 0 hε
  have hev : ∀ᶠ n in atTop, (∑' k, v (k + n)) ∈ Metric.ball (0 : ℝ) ε :=
    htail hball
  obtain ⟨Nt, hNt⟩ := eventually_atTop.1 hev
  obtain ⟨Kb, hKb⟩ := hbound
  refine ⟨max Nt Kb, ?_⟩
  intro n hn x hx
  have hnNt : Nt ≤ n := le_trans (le_max_left Nt Kb) hn
  have hnKb : Kb ≤ n := le_trans (le_max_right Nt Kb) hn
  have htailvAbs : |∑' k, v (k + n)| < ε := by
    simpa [Metric.mem_ball, Real.dist_eq] using hNt n hnNt
  have htailv0 : 0 ≤ ∑' k, v (k + n) :=
    tsum_nonneg (fun k => hv0 (k + n))
  have htailv : (∑' k, v (k + n)) < ε := by
    simpa [abs_of_nonneg htailv0] using htailvAbs
  have hux := hu x hx
  have hutail : Summable (fun k => u (k + n) x) :=
    (summable_nat_add_iff n).2 hux
  have hvtail : Summable (fun k => v (k + n)) :=
    (summable_nat_add_iff n).2 hv
  have htaille : (∑' k, u (k + n) x) ≤ ∑' k, v (k + n) := by
    have hdiff0 :
        0 ≤ ∑' k : ℕ, (v (k + n) - u (k + n) x) :=
      tsum_nonneg (fun k => by
        have hb := hKb (k + n)
          (le_trans hnKb (Nat.le_add_left n k)) x hx
        exact sub_nonneg.mpr
          (le_trans (le_abs_self (u (k + n) x)) hb))
    have hdiffEq :
        (∑' k : ℕ, (v (k + n) - u (k + n) x)) =
          (∑' k : ℕ, v (k + n)) - (∑' k : ℕ, u (k + n) x) :=
      (hvtail.hasSum.sub hutail.hasSum).tsum_eq
    rw [hdiffEq] at hdiff0
    linarith
  have hutail0 : 0 ≤ ∑' k, u (k + n) x :=
    tsum_nonneg (fun k => hu0 (k + n) x)
  have hdecomp := hux.sum_add_tsum_nat_add n
  have herr :
      |(∑ k ∈ Finset.range n, u k x) - ∑' k, u k x| =
        ∑' k, u (k + n) x := by
    have heq :
        (∑ k ∈ Finset.range n, u k x) - ∑' k, u k x =
          -(∑' k, u (k + n) x) := by
      linarith
    rw [heq, abs_neg, abs_of_nonneg hutail0]
  rw [herr]
  exact lt_of_le_of_lt htaille htailv

theorem gap1 (x : ℝ) (hx : x ∉ integers) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) - x) ^ 2) := by
  exact summable_reciprocal_square x

theorem gap2 (x : ℝ) (hx : x ∉ integers) :
    Summable
      (fun n : ℕ => 1 / ((-((n + 1 : ℕ) : ℤ) : ℝ) - x) ^ 2) := by
  have hs := summable_reciprocal_square (-x)
  have ht : Summable
      (fun n : ℕ => 1 / ((((n + 1 : ℕ) : ℝ)) - (-x)) ^ 2) := by
    exact (summable_nat_add_iff 1).2 hs
  refine ht.congr (fun n => ?_)
  have hsq :
      ((-((n + 1 : ℕ) : ℤ) : ℝ) - x) ^ 2 =
        (((n + 1 : ℕ) : ℝ) - (-x)) ^ 2 := by
    push_cast
    ring
  rw [hsq]

theorem gap3 (x : ℝ) (hx : x ∉ integers) :
    Summable (fun z : ℤ => term z x) := by
  have hp : Summable (fun n : ℕ => term (n : ℤ) x) := by
    simpa [term] using gap1 x hx
  have hn : Summable (fun n : ℕ => term (Int.negSucc n) x) := by
    simpa [term] using gap2 x hx
  exact (integer_series_parts (fun z : ℤ => term z x) hp hn).1

theorem gap4 (x₀ : ℝ) (hx₀ : x₀ ∉ integers) :
    ∃ a : ℝ, (Int.floor x₀ : ℝ) < a ∧ a < x₀ := by
  have hle : (Int.floor x₀ : ℝ) ≤ x₀ := Int.floor_le x₀
  have hne : (Int.floor x₀ : ℝ) ≠ x₀ := by
    intro h
    apply hx₀
    exact ⟨Int.floor x₀, h⟩
  have hlt : (Int.floor x₀ : ℝ) < x₀ := lt_of_le_of_ne hle hne
  refine ⟨((Int.floor x₀ : ℝ) + x₀) / 2, ?_, ?_⟩ <;> linarith

theorem gap5 (x₀ : ℝ) (hx₀ : x₀ ∉ integers) :
    ∃ a : ℝ, (Int.floor x₀ : ℝ) < a ∧ a < x₀ := by
  exact gap4 x₀ hx₀

theorem gap6 (x₀ : ℝ) (hx₀ : x₀ ∉ integers) :
    ∃ b : ℝ, x₀ < b ∧ b < (Int.floor x₀ : ℝ) + 1 := by
  have hlt : x₀ < (Int.floor x₀ : ℝ) + 1 := Int.lt_floor_add_one x₀
  refine ⟨(x₀ + ((Int.floor x₀ : ℝ) + 1)) / 2, ?_, ?_⟩ <;> linarith

theorem gap7 (x₀ : ℝ) (hx₀ : x₀ ∉ integers) :
    ∃ b : ℝ, x₀ < b ∧ b < (Int.floor x₀ : ℝ) + 1 := by
  exact gap6 x₀ hx₀

theorem gap8 (x₀ : ℝ) (hx₀ : x₀ ∉ integers) :
    (Int.floor x₀ : ℝ) < (Int.floor x₀ : ℝ) + 1 := by
  linarith

theorem gap9 (x₀ a b : ℝ) (hx₀ : x₀ ∉ integers)
    (hab : LocalInterval x₀ a b) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ x ∈ Set.Icc a b,
      |1 / ((n : ℝ) - x) ^ 2| ≤
        1 / ((n : ℝ) - |x|) ^ 2 := by
  let M : ℝ := max |a| |b|
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt M
  refine ⟨n₀, ?_⟩
  intro n hn x hx
  have hxM : |x| ≤ M := abs_le_endpoint_max hx
  have hncast : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnM : M < (n : ℝ) := lt_of_lt_of_le hn₀ hncast
  have hd : 0 < (n : ℝ) - |x| := by linarith
  have hde : (n : ℝ) - |x| ≤ (n : ℝ) - x := by
    have := le_abs_self x
    linarith
  have hsquares : ((n : ℝ) - |x|) ^ 2 ≤ ((n : ℝ) - x) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - x)]
  rw [abs_of_nonneg (one_div_nonneg.mpr (sq_nonneg _))]
  exact one_div_le_one_div_of_le (sq_pos_of_pos hd) hsquares

theorem gap10 (x₀ a b : ℝ) (hx₀ : x₀ ∉ integers)
    (hab : LocalInterval x₀ a b) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ x ∈ Set.Icc a b,
      1 / ((n : ℝ) - |x|) ^ 2 ≤
        1 / ((n : ℝ) - max |a| |b|) ^ 2 := by
  let M : ℝ := max |a| |b|
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt M
  refine ⟨n₀, ?_⟩
  intro n hn x hx
  have hxM : |x| ≤ M := abs_le_endpoint_max hx
  have hncast : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnM : M < (n : ℝ) := lt_of_lt_of_le hn₀ hncast
  have hdM : 0 < (n : ℝ) - M := by linarith
  have hden : (n : ℝ) - M ≤ (n : ℝ) - |x| := by linarith
  have hsquares : ((n : ℝ) - M) ^ 2 ≤ ((n : ℝ) - |x|) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - |x|)]
  exact one_div_le_one_div_of_le (sq_pos_of_pos hdM) hsquares

theorem gap11 (x₀ a b : ℝ) (hx₀ : x₀ ∉ integers)
    (hab : LocalInterval x₀ a b) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ x ∈ Set.Icc a b,
      |1 / ((n : ℝ) - x) ^ 2| ≤
        1 / ((n : ℝ) - max |a| |b|) ^ 2 := by
  obtain ⟨n₁, hn₁⟩ := gap9 x₀ a b hx₀ hab
  obtain ⟨n₂, hn₂⟩ := gap10 x₀ a b hx₀ hab
  refine ⟨max n₁ n₂, ?_⟩
  intro n hn x hx
  have h1 := hn₁ n (le_trans (le_max_left n₁ n₂) hn) x hx
  have h2 := hn₂ n (le_trans (le_max_right n₁ n₂) hn) x hx
  exact h1.trans h2

theorem gap12 (x₀ a b : ℝ) (hx₀ : x₀ ∉ integers)
    (hab : LocalInterval x₀ a b) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ x ∈ Set.Icc a b,
      |1 / ((-(n : ℝ)) - x) ^ 2| ≤
        1 / ((n : ℝ) - |x|) ^ 2 := by
  let M : ℝ := max |a| |b|
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt M
  refine ⟨n₀, ?_⟩
  intro n hn x hx
  have hxM : |x| ≤ M := abs_le_endpoint_max hx
  have hncast : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnM : M < (n : ℝ) := lt_of_lt_of_le hn₀ hncast
  have hd : 0 < (n : ℝ) - |x| := by linarith
  have hde : (n : ℝ) - |x| ≤ (n : ℝ) + x := by
    have := neg_abs_le x
    linarith
  have hsquares : ((n : ℝ) - |x|) ^ 2 ≤ ((n : ℝ) + x) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) + x)]
  rw [abs_of_nonneg (one_div_nonneg.mpr (sq_nonneg _))]
  have heq : ((-(n : ℝ)) - x) ^ 2 = ((n : ℝ) + x) ^ 2 := by ring
  rw [heq]
  exact one_div_le_one_div_of_le (sq_pos_of_pos hd) hsquares

theorem gap13 (x₀ a b : ℝ) (hx₀ : x₀ ∉ integers)
    (hab : LocalInterval x₀ a b) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ x ∈ Set.Icc a b,
      1 / ((n : ℝ) - |x|) ^ 2 ≤
        1 / ((n : ℝ) - max |a| |b|) ^ 2 := by
  exact gap10 x₀ a b hx₀ hab

theorem gap14 (x₀ a b : ℝ) (hx₀ : x₀ ∉ integers)
    (hab : LocalInterval x₀ a b) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ x ∈ Set.Icc a b,
      |1 / ((-(n : ℝ)) - x) ^ 2| ≤
        1 / ((n : ℝ) - max |a| |b|) ^ 2 := by
  obtain ⟨n₁, hn₁⟩ := gap12 x₀ a b hx₀ hab
  obtain ⟨n₂, hn₂⟩ := gap13 x₀ a b hx₀ hab
  refine ⟨max n₁ n₂, ?_⟩
  intro n hn x hx
  have h1 := hn₁ n (le_trans (le_max_left n₁ n₂) hn) x hx
  have h2 := hn₂ n (le_trans (le_max_right n₁ n₂) hn) x hx
  exact h1.trans h2

theorem gap15 (p : ℝ) :
    ∃ n₀ : ℕ,
      Summable
        (fun n : ℕ =>
          1 / ((((n + n₀ : ℕ) : ℝ)) - p) ^ 2) := by
  exact shifted_reciprocal_square p

theorem gap16 (x₀ : ℝ) (hx₀ : x₀ ∉ integers) :
    ∃ a b : ℝ,
      LocalInterval x₀ a b ∧
      SymmetricUniformlyConvergesOn (Set.Icc a b) := by
  classical
  obtain ⟨a, ha₁, ha₂⟩ := gap5 x₀ hx₀
  obtain ⟨b, hb₁, hb₂⟩ := gap7 x₀ hx₀
  have hab : LocalInterval x₀ a b := ⟨ha₁, ha₂, hb₁, hb₂⟩
  refine ⟨a, b, hab, ?_⟩
  let v : ℕ → ℝ := fun n => 1 / ((n : ℝ) - max |a| |b|) ^ 2
  obtain ⟨r, hr⟩ := gap15 (max |a| |b|)
  have hv : Summable v := by
    rw [← summable_nat_add_iff r]
    simpa [v, Nat.cast_add] using hr
  have hv0 : ∀ n : ℕ, 0 ≤ v n := by
    intro n
    exact one_div_nonneg.mpr (sq_nonneg _)
  have havoid : ∀ x ∈ Set.Icc a b, x ∉ integers :=
    localInterval_avoids_integers hab
  obtain ⟨kp, hkp⟩ := gap11 x₀ a b hx₀ hab
  have hposBound :
      ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
        ∀ x : ℝ, x ∈ Set.Icc a b →
          |term (n : ℤ) x| ≤ v n := by
    refine ⟨kp, ?_⟩
    intro n hn x hx
    simpa [term, v] using hkp n hn x hx
  have hposSum : ∀ x : ℝ, x ∈ Set.Icc a b →
      Summable (fun n : ℕ => term (n : ℤ) x) := by
    intro x hx
    simpa [term] using gap1 x (havoid x hx)
  have hpos0 : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ term (n : ℤ) x := by
    intro n x
    exact one_div_nonneg.mpr (sq_nonneg _)
  let w : ℕ → ℝ := fun n => v (n + 1)
  have hw : Summable w := by
    exact (summable_nat_add_iff 1).2 hv
  have hw0 : ∀ n : ℕ, 0 ≤ w n := by
    intro n
    exact hv0 (n + 1)
  obtain ⟨kn, hkn⟩ := gap14 x₀ a b hx₀ hab
  have hnegBound :
      ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
        ∀ x : ℝ, x ∈ Set.Icc a b →
          |term (Int.negSucc n) x| ≤ w n := by
    refine ⟨kn, ?_⟩
    intro n hn x hx
    have hn' : kn ≤ n + 1 := le_trans hn (Nat.le_succ n)
    have h := hkn (n + 1) hn' x hx
    simpa [term, w, v] using h
  have hnegSum : ∀ x : ℝ, x ∈ Set.Icc a b →
      Summable (fun n : ℕ => term (Int.negSucc n) x) := by
    intro x hx
    simpa [term] using gap2 x (havoid x hx)
  have hneg0 : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ term (Int.negSucc n) x := by
    intro n x
    exact one_div_nonneg.mpr (sq_nonneg _)
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨Np, hNp⟩ := uniform_nat_partial_tails
    (fun n x => term (n : ℤ) x) v (Set.Icc a b)
    hv hv0 hpos0 hposSum hposBound (ε / 2) hhalf
  obtain ⟨Nn, hNn⟩ := uniform_nat_partial_tails
    (fun n x => term (Int.negSucc n) x) w (Set.Icc a b)
    hw hw0 hneg0 hnegSum hnegBound (ε / 2) hhalf
  refine ⟨max Np Nn, ?_⟩
  intro n hn x hx
  have hp := hNp (n + 1)
    (le_trans (le_max_left Np Nn) (le_trans hn (Nat.le_succ n))) x hx
  have hn' := hNn n (le_trans (le_max_right Np Nn) hn) x hx
  have hf_split :
      f x = (∑' k : ℕ, term (k : ℤ) x) +
        ∑' k : ℕ, term (Int.negSucc k) x := by
    unfold f
    exact (integer_series_parts (fun z : ℤ => term z x)
      (hposSum x hx) (hnegSum x hx)).2
  rw [symmetricPartialSum_split, hf_split]
  calc
    |((∑ k ∈ Finset.range (n + 1), term (k : ℤ) x) +
          ∑ k ∈ Finset.range n, term (Int.negSucc k) x) -
        ((∑' k : ℕ, term (k : ℤ) x) +
          ∑' k : ℕ, term (Int.negSucc k) x)| =
        |((∑ k ∈ Finset.range (n + 1), term (k : ℤ) x) -
            ∑' k : ℕ, term (k : ℤ) x) +
          ((∑ k ∈ Finset.range n, term (Int.negSucc k) x) -
            ∑' k : ℕ, term (Int.negSucc k) x)| := by
      congr 1
      ring
    _ ≤ |(∑ k ∈ Finset.range (n + 1), term (k : ℤ) x) -
            ∑' k : ℕ, term (k : ℤ) x| +
          |(∑ k ∈ Finset.range n, term (Int.negSucc k) x) -
            ∑' k : ℕ, term (Int.negSucc k) x| := abs_add_le _ _
    _ < ε := by linarith

theorem gap17 (x₀ : ℝ) (hx₀ : x₀ ∉ integers) :
    ∃ a b : ℝ,
      LocalInterval x₀ a b ∧ ContinuousOn f (Set.Icc a b) := by
  classical
  obtain ⟨a, b, hab, hconv⟩ := gap16 x₀ hx₀
  refine ⟨a, b, hab, ?_⟩
  have hnonzero : ∀ z : ℤ, ∀ x ∈ Set.Icc a b, (z : ℝ) - x ≠ 0 := by
    intro z x hx hzero
    apply localInterval_avoids_integers hab x hx
    refine ⟨z, ?_⟩
    exact sub_eq_zero.mp hzero
  have hpartial : ∀ n : ℕ, ContinuousOn (symmetricPartialSum n) (Set.Icc a b) := by
    intro n
    unfold symmetricPartialSum
    refine continuousOn_finset_sum _ (fun z hz => ?_)
    unfold term
    exact continuousOn_const.div
      ((continuousOn_const.sub continuousOn_id).pow 2)
      (fun x hx => pow_ne_zero 2 (hnonzero z x hx))
  have hu : TendstoUniformlyOn (fun n : ℕ => symmetricPartialSum n) f atTop (Set.Icc a b) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hconv ε hε
    filter_upwards [eventually_ge_atTop N] with n hn
    intro x hx
    simpa [Real.dist_eq, abs_sub_comm] using hN n hn x hx
  exact hu.continuousOn ((Filter.Eventually.of_forall hpartial).frequently)

theorem gap18 (x₀ : ℝ) (hx₀ : x₀ ∉ integers) :
    ContinuousAt f x₀ := by
  obtain ⟨a, b, hab, hcont⟩ := gap17 x₀ hx₀
  apply hcont.continuousAt
  exact Icc_mem_nhds hab.2.1 hab.2.2.1

theorem gap19 (x : ℝ) (hx : x ∉ integers) :
    f (x + 1) = ∑' z : ℤ, 1 / ((z : ℝ) - (x + 1)) ^ 2 := by
  rfl

theorem gap20 (x : ℝ) (hx : x ∉ integers) :
    (∑' z : ℤ, 1 / ((z : ℝ) - (x + 1)) ^ 2) =
      ∑' z : ℤ, 1 / (((z : ℝ) - 1) - x) ^ 2 := by
  apply tsum_congr
  intro z
  congr 2
  ring

theorem gap21 (x : ℝ) (hx : x ∉ integers) :
    f (x + 1) =
      ∑' z : ℤ, 1 / (((z : ℝ) - 1) - x) ^ 2 := by
  exact (gap19 x hx).trans (gap20 x hx)

theorem gap22 (x : ℝ) (hx : x ∉ integers) :
    f (x + 1) = ∑' m : ℤ, term m x := by
  calc
    f (x + 1) = ∑' z : ℤ, 1 / (((z : ℝ) - 1) - x) ^ 2 := gap21 x hx
    _ = ∑' z : ℤ, term (z - 1) x := by
      apply tsum_congr
      intro z
      simp only [term, Int.cast_sub, Int.cast_one]
    _ = ∑' m : ℤ, term m x := by
      simpa [sub_eq_add_neg] using
        ((Equiv.addRight (-1 : ℤ)).tsum_eq (fun m : ℤ => term m x))

theorem gap23 (x : ℝ) (hx : x ∉ integers) :
    (∑' m : ℤ, term m x) = f x := by
  rfl

theorem gap24 (x : ℝ) (hx : x ∉ integers) :
    f (x + 1) = f x := by
  exact (gap22 x hx).trans (gap23 x hx)

theorem gap25 :
    ContinuousOn f (integersᶜ) := by
  intro x hx
  apply (gap18 x hx).continuousWithinAt

theorem gap26 :
    Function.Periodic f 1 := by
  intro x
  unfold f
  calc
    (∑' z : ℤ, term z (x + 1)) = ∑' z : ℤ, term (z - 1) x := by
      apply tsum_congr
      intro z
      unfold term
      congr 2
      push_cast
      ring
    _ = ∑' m : ℤ, term m x := by
      simpa [sub_eq_add_neg] using
        ((Equiv.addRight (-1 : ℤ)).tsum_eq (fun m : ℤ => term m x))

theorem gap27 :
    ContinuousOn f (integersᶜ) ∧ Function.Periodic f 1 := by
  exact ⟨gap25, gap26⟩

end

end ProofGap.Exercise2793
