import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace ProofGap.Exercise3031

noncomputable section

open Filter
open scoped BigOperators Topology

def Admissible (a : ℕ → ℝ) (x : ℝ) : Prop :=
  0 < x ∧
    (∀ n : ℕ, 1 ≤ n → 0 < a n) ∧
    ¬Summable (fun n : ℕ => 1 / a (n + 1))

def term (a : ℕ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.Icc 1 n, a k / (a (k + 1) + x)

def partialSum (a : ℕ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, term a x k

def remainder (a : ℕ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  a (n + 1) / x * term a x n

def alpha (a : ℕ → ℝ) (x : ℝ) (k : ℕ) : ℝ :=
  -x / (a k + x)

def u (a : ℕ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.Icc 2 (n + 1), (1 + alpha a x k)

private theorem partialSum_succ (a : ℕ → ℝ) (x : ℝ) (n : ℕ) :
    partialSum a x (n + 1) = partialSum a x n + term a x (n + 1) := by
  have hs : Finset.Icc 1 (n + 1) =
      insert (n + 1) (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [partialSum, partialSum, hs, Finset.sum_insert]
  · ring
  · simp

private theorem term_succ (a : ℕ → ℝ) (x : ℝ) (n : ℕ) :
    term a x (n + 1) =
      term a x n * (a (n + 1) / (a (n + 2) + x)) := by
  have hs : Finset.Icc 1 (n + 1) =
      insert (n + 1) (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [term, term, hs, Finset.prod_insert]
  · ring
  · simp

private theorem remainder_step (a : ℕ → ℝ) (x : ℝ)
    (h : Admissible a x) (n : ℕ) :
    term a x (n + 1) + remainder a x (n + 1) = remainder a x n := by
  rw [remainder, remainder, term_succ]
  have hx0 : x ≠ 0 := ne_of_gt h.1
  have hd0 : a (n + 2) + x ≠ 0 :=
    ne_of_gt (add_pos (h.2.1 (n + 2) (by omega)) h.1)
  field_simp [hx0, hd0]
  ring

private theorem partialSum_eq_sum_range (a : ℕ → ℝ) (x : ℝ) (n : ℕ) :
    partialSum a x n =
      ∑ k ∈ Finset.range n, term a x (k + 1) := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
      rw [partialSum_succ, Finset.sum_range_succ, ih]

private theorem tailSum_eq_sum_range (a : ℕ → ℝ) (x : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.Icc 2 (N + 1), 1 / (a k + x)) =
      ∑ n ∈ Finset.range N, 1 / (a (n + 2) + x) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hs : Finset.Icc 2 (N + 2) =
          insert (N + 2) (Finset.Icc 2 (N + 1)) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hs, Finset.sum_insert, Finset.sum_range_succ, ih]
      · ring
      · simp

private theorem u_pos (a : ℕ → ℝ) (x : ℝ) (h : Admissible a x)
    (n : ℕ) : 0 < u a x n := by
  unfold u
  apply Finset.prod_pos
  intro k hk
  have hk1 : 1 ≤ k := by
    simp only [Finset.mem_Icc] at hk
    omega
  have ha : 0 < a k := h.2.1 k hk1
  have hd : 0 < a k + x := add_pos ha h.1
  have heq : 1 + alpha a x k = a k / (a k + x) := by
    simp only [alpha]
    field_simp [ne_of_gt hd]
    ring
  rw [heq]
  exact div_pos ha hd

private theorem hasSum_iff_tendsto_nat
    {a : ℕ → ℝ} {x s : ℝ}
    (h : Admissible a x := by assumption) :
    HasSum (fun n : ℕ => term a x (n + 1)) s ↔
      Tendsto
        (fun n : ℕ => ∑ k ∈ Finset.range n, term a x (k + 1))
        atTop (𝓝 s) := by
  let f : ℕ → ℝ := fun n => term a x (n + 1)
  have hf : ∀ n : ℕ, 0 ≤ f n := by
    intro n
    apply le_of_lt
    unfold f term
    apply Finset.prod_pos
    intro k hk
    have hk1 : 1 ≤ k := by
      simp only [Finset.mem_Icc] at hk
      omega
    have hak : 0 < a k := h.2.1 k hk1
    have hak1 : 0 < a (k + 1) := h.2.1 (k + 1) (by omega)
    exact div_pos hak (add_pos hak1 h.1)
  constructor
  · intro hs
    simpa [f] using hs.tendsto_sum_nat
  · intro ht
    have ht' : Tendsto
        (fun n : ℕ => ∑ k ∈ Finset.range n, f k)
        atTop (𝓝 s) := by
      simpa [f] using ht
    have hsum : Summable f := by
      by_contra hns
      have htop : Tendsto
          (fun n : ℕ => ∑ k ∈ Finset.range n, f k)
          atTop atTop :=
        (not_summable_iff_tendsto_nat_atTop_of_nonneg hf).1 hns
      have hlarge : ∀ᶠ n : ℕ in atTop,
          s + 1 ≤ ∑ k ∈ Finset.range n, f k :=
        (tendsto_atTop.1 htop) (s + 1)
      have hsmall : ∀ᶠ n : ℕ in atTop,
          (∑ k ∈ Finset.range n, f k) < s + 1 :=
        (tendsto_order.1 ht').2 _ (by linarith)
      rcases (hlarge.and hsmall).exists with ⟨n, hnlarge, hnsmall⟩
      exact (not_lt_of_ge hnlarge) hnsmall
    have hcanon : Tendsto
        (fun n : ℕ => ∑ k ∈ Finset.range n, f k)
        atTop (𝓝 (∑' n : ℕ, f n)) :=
      hsum.hasSum.tendsto_sum_nat
    have heq : (∑' n : ℕ, f n) = s :=
      tendsto_nhds_unique hcanon ht'
    have hs : HasSum f s := by
      rw [← heq]
      exact hsum.hasSum
    simpa [f] using hs

theorem gap1 (a : ℕ → ℝ) (x : ℝ) (h : Admissible a x)
    (n : ℕ) (hn : 1 ≤ n) :
    a 1 / x = partialSum a x n + remainder a x n := by
  induction n, hn using Nat.le_induction with
  | base =>
      have hx0 : x ≠ 0 := ne_of_gt h.1
      have hd0 : a 2 + x ≠ 0 := ne_of_gt (add_pos (h.2.1 2 (by omega)) h.1)
      simp [partialSum, remainder, term]
      field_simp [hx0, hd0]
      <;> ring
  | succ n hn ih =>
      rw [partialSum_succ]
      have hr := remainder_step a x h n
      linarith

theorem gap2 (a : ℕ → ℝ) (x : ℝ) (h : Admissible a x) :
    ∀ n : ℕ, remainder a x n = a (n + 1) / x * term a x n := by
  intro n
  rfl

theorem gap3 (a : ℕ → ℝ) (x : ℝ) (h : Admissible a x)
    (n : ℕ) :
    a (n + 1) / x * term a x n =
      a 1 / x *
        (∏ k ∈ Finset.Icc 2 (n + 1), a k / (a k + x)) := by
  induction n with
  | zero => simp [term]
  | succ n ih =>
      rw [term_succ a x n]
      have hp :
          (∏ k ∈ Finset.Icc 2 (n + 2), a k / (a k + x)) =
            (∏ k ∈ Finset.Icc 2 (n + 1), a k / (a k + x)) *
              (a (n + 2) / (a (n + 2) + x)) := by
        have hs : Finset.Icc 2 (n + 2) =
            insert (n + 2) (Finset.Icc 2 (n + 1)) := by
          ext k
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        rw [hs, Finset.prod_insert]
        · ring
        · simp
      rw [hp]
      calc
        a (n + 2) / x *
              (term a x n * (a (n + 1) / (a (n + 2) + x))) =
            (a (n + 1) / x * term a x n) *
              (a (n + 2) / (a (n + 2) + x)) := by ring
        _ = (a 1 / x *
              (∏ k ∈ Finset.Icc 2 (n + 1), a k / (a k + x))) *
              (a (n + 2) / (a (n + 2) + x)) := by rw [ih]
        _ = a 1 / x *
              ((∏ k ∈ Finset.Icc 2 (n + 1), a k / (a k + x)) *
                (a (n + 2) / (a (n + 2) + x))) := by ring

theorem gap4 (a : ℕ → ℝ) (x : ℝ) (h : Admissible a x) :
    ∀ n : ℕ, remainder a x n =
      a 1 / x *
        (∏ k ∈ Finset.Icc 2 (n + 1), a k / (a k + x)) := by
  intro n
  rw [gap2 a x h n]
  exact gap3 a x h n

theorem gap5 (a : ℕ → ℝ) (x : ℝ) (h : Admissible a x) :
    ∀ n : ℕ, remainder a x n = a 1 / x * u a x n := by
  intro n
  rw [gap4 a x h n]
  apply congrArg (fun z : ℝ => a 1 / x * z)
  unfold u
  apply Finset.prod_congr rfl
  intro k hk
  have hk1 : 1 ≤ k := by
    simp only [Finset.mem_Icc] at hk
    omega
  have hd0 : a k + x ≠ 0 :=
    ne_of_gt (add_pos (h.2.1 k hk1) h.1)
  simp only [alpha]
  field_simp [hd0]
  ring

theorem gap6 (a : ℕ → ℝ) (x : ℝ) :
    ∀ k : ℕ, alpha a x k = -x / (a k + x) := by
  intro k
  rfl

theorem gap7 (a : ℕ → ℝ) (x τ : ℝ) (h : Admissible a x)
    (hlim : Tendsto (remainder a x) atTop (𝓝 τ)) :
    Tendsto (partialSum a x) atTop
      (𝓝 (∑' n : ℕ, term a x (n + 1))) := by
  have hraw : Tendsto (fun n : ℕ => a 1 / x - remainder a x n)
      atTop (𝓝 (a 1 / x - τ)) := tendsto_const_nhds.sub hlim
  have hps : Tendsto (partialSum a x) atTop (𝓝 (a 1 / x - τ)) := by
    apply hraw.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hi := gap1 a x h n hn
    linarith
  have hrange : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n, term a x (k + 1))
      atTop (𝓝 (a 1 / x - τ)) := by
    apply hps.congr'
    exact Filter.Eventually.of_forall
      (fun n => partialSum_eq_sum_range a x n)
  have hs : HasSum (fun n : ℕ => term a x (n + 1)) (a 1 / x - τ) :=
    (hasSum_iff_tendsto_nat).2 hrange
  have hcanon : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n, term a x (k + 1))
      atTop (𝓝 (∑' n : ℕ, term a x (n + 1))) :=
    (hasSum_iff_tendsto_nat).1 hs.summable.hasSum
  apply hcanon.congr'
  exact Filter.Eventually.of_forall
    (fun n => (partialSum_eq_sum_range a x n).symm)

theorem gap8 (a : ℕ → ℝ) (x τ : ℝ) (h : Admissible a x)
    (hlim : Tendsto (remainder a x) atTop (𝓝 τ)) :
    Tendsto (partialSum a x) atTop (𝓝 (a 1 / x - τ)) := by
  have ht : Tendsto (fun n : ℕ => a 1 / x - remainder a x n)
      atTop (𝓝 (a 1 / x - τ)) := tendsto_const_nhds.sub hlim
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hi := gap1 a x h n hn
  linarith

theorem gap9 (a : ℕ → ℝ) (x τ : ℝ) (h : Admissible a x)
    (hlim : Tendsto (remainder a x) atTop (𝓝 τ)) :
    Tendsto (fun n : ℕ => a 1 / x - remainder a x n)
      atTop (𝓝 (a 1 / x - τ)) := by
  exact tendsto_const_nhds.sub hlim

theorem gap10 (a : ℕ → ℝ) (x τ : ℝ) (h : Admissible a x)
    (hlim : Tendsto (remainder a x) atTop (𝓝 τ)) :
    (∑' n : ℕ, term a x (n + 1)) = a 1 / x - τ := by
  exact tendsto_nhds_unique (gap7 a x τ h hlim) (gap8 a x τ h hlim)

theorem gap11 (a : ℕ → ℝ) (x : ℝ) (h : Admissible a x)
    (k : ℕ) (hk : 1 ≤ k) :
    -1 < alpha a x k := by
  have hd : 0 < a k + x := add_pos (h.2.1 k hk) h.1
  have hq : x / (a k + x) < 1 :=
    (div_lt_one hd).2 (by linarith [h.2.1 k hk])
  unfold alpha
  rw [neg_div]
  exact neg_lt_neg hq

theorem gap12 (a : ℕ → ℝ) (x : ℝ) (h : Admissible a x)
    (k : ℕ) (hk : 1 ≤ k) :
    alpha a x k < 0 := by
  have hd : 0 < a k + x := add_pos (h.2.1 k hk) h.1
  have hq : 0 < x / (a k + x) := div_pos h.1 hd
  unfold alpha
  rw [neg_div]
  exact neg_lt_zero.mpr hq

theorem gap13 (a : ℕ → ℝ) (x : ℝ) (h : Admissible a x)
    (k : ℕ) (hk : 1 ≤ k) :
    0 < 1 + alpha a x k := by
  linarith [gap11 a x h k hk]

theorem gap14 (a : ℕ → ℝ) (x : ℝ) (h : Admissible a x)
    (k : ℕ) (hk : 1 ≤ k) :
    1 + alpha a x k < 1 := by
  linarith [gap12 a x h k hk]

theorem gap15 (a : ℕ → ℝ) (x : ℝ) (h : Admissible a x)
    (n : ℕ) :
    Real.log (u a x n) =
      ∑ k ∈ Finset.Icc 2 (n + 1), Real.log (1 + alpha a x k) := by
  unfold u
  rw [Real.log_prod]
  intro k hk
  have hk1 : 1 ≤ k := by
    simp only [Finset.mem_Icc] at hk
    omega
  exact ne_of_gt (gap13 a x h k hk1)

theorem gap16 (a : ℕ → ℝ) (x : ℝ) (h : Admissible a x) :
    ¬Summable (fun n : ℕ => 1 / (a (n + 2) + x)) := by
  intro hs
  have ht : Tendsto (fun n : ℕ => 1 / (a (n + 2) + x)) atTop (𝓝 0) :=
    hs.tendsto_atTop_zero
  have heps : 0 < 1 / (2 * x) :=
    one_div_pos.mpr (mul_pos (by norm_num) h.1)
  have hevsmall : ∀ᶠ n : ℕ in atTop,
      1 / (a (n + 2) + x) < 1 / (2 * x) :=
    (tendsto_order.1 ht).2 _ heps
  have hevax : ∀ᶠ n : ℕ in atTop, x ≤ a (n + 2) := by
    filter_upwards [hevsmall] with n hn
    have ha : 0 < a (n + 2) := h.2.1 (n + 2) (by omega)
    by_contra hnx
    have halt : a (n + 2) < x := lt_of_not_ge hnx
    have hden : 0 < a (n + 2) + x := add_pos ha h.1
    have hlt : a (n + 2) + x < 2 * x := by linarith
    have hrecip : 1 / (2 * x) < 1 / (a (n + 2) + x) :=
      one_div_lt_one_div_of_lt hden hlt
    linarith
  have hcompTop : ∀ᶠ n : ℕ in atTop,
      ‖1 / a (n + 2)‖ ≤ 2 * (1 / (a (n + 2) + x)) := by
    filter_upwards [hevax] with n hn
    have ha : 0 < a (n + 2) := h.2.1 (n + 2) (by omega)
    have hden : 0 < a (n + 2) + x := add_pos ha h.1
    have hle : a (n + 2) + x ≤ 2 * a (n + 2) := by linarith
    have hr : 1 / (2 * a (n + 2)) ≤ 1 / (a (n + 2) + x) :=
      one_div_le_one_div_of_le hden hle
    have hid : 1 / a (n + 2) = 2 * (1 / (2 * a (n + 2))) := by
      field_simp [ne_of_gt ha]
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr ha), hid]
    exact mul_le_mul_of_nonneg_left hr (by norm_num)
  have hcomp : ∀ᶠ n : ℕ in cofinite,
      ‖1 / a (n + 2)‖ ≤ 2 * (1 / (a (n + 2) + x)) := by
    simpa only [Nat.cofinite_eq_atTop] using hcompTop
  have hs2 : Summable (fun n : ℕ => 1 / a (n + 2)) :=
    Summable.of_norm_bounded_eventually (hs.mul_left 2) hcomp
  have hs1 : Summable (fun n : ℕ => 1 / a (n + 1)) := by
    apply (summable_nat_add_iff 1).1
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs2
  exact h.2.2 hs1

theorem gap17 (a : ℕ → ℝ) (x : ℝ) (h : Admissible a x) :
    Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.Icc 2 (N + 1), 1 / (a k + x))
      atTop atTop := by
  let f : ℕ → ℝ := fun n => 1 / (a (n + 2) + x)
  have hf : ∀ n : ℕ, 0 ≤ f n := by
    intro n
    exact le_of_lt (one_div_pos.mpr
      (add_pos (h.2.1 (n + 2) (by omega)) h.1))
  have hns : ¬Summable f := by
    simpa [f] using gap16 a x h
  have ht : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, f n) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hf).1 hns
  apply ht.congr'
  exact Filter.Eventually.of_forall
    (fun N => (tailSum_eq_sum_range a x N).symm)

theorem gap18 (a : ℕ → ℝ) (x : ℝ) (h : Admissible a x) :
    Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.Icc 2 (N + 1), alpha a x k)
      atTop atBot := by
  rw [tendsto_atBot]
  intro b
  have he := (tendsto_atTop.1 (gap17 a x h)) (-b / x)
  filter_upwards [he] with N hN
  have heq :
      (∑ k ∈ Finset.Icc 2 (N + 1), alpha a x k) =
        -x * (∑ k ∈ Finset.Icc 2 (N + 1), 1 / (a k + x)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [alpha]
    ring
  rw [heq]
  have hx0 : x ≠ 0 := ne_of_gt h.1
  have hid : x * (-b / x) = -b := by field_simp [hx0]
  have hmul := mul_le_mul_of_nonneg_left hN (le_of_lt h.1)
  calc
    -x * (∑ k ∈ Finset.Icc 2 (N + 1), 1 / (a k + x)) ≤
        -(x * (-b / x)) := by
          simpa only [neg_mul] using neg_le_neg hmul
    _ = b := by rw [hid]; ring

theorem gap19 (a : ℕ → ℝ) (x : ℝ) (h : Admissible a x)
    (k : ℕ) (hk : 1 ≤ k) :
    Real.log (1 + alpha a x k) < alpha a x k := by
  have hp : 0 < 1 + alpha a x k := gap13 a x h k hk
  have hne : 1 + alpha a x k ≠ 1 := by
    linarith [gap12 a x h k hk]
  have hl := Real.log_lt_sub_one_of_pos hp hne
  simpa using hl

theorem gap20 (a : ℕ → ℝ) (x : ℝ) (h : Admissible a x)
    (k : ℕ) (hk : 1 ≤ k) :
    alpha a x k < 0 := by
  exact gap12 a x h k hk

theorem gap21 (a : ℕ → ℝ) (x : ℝ) (h : Admissible a x)
    (k : ℕ) (hk : 1 ≤ k) :
    Real.log (1 + alpha a x k) < 0 := by
  linarith [gap19 a x h k hk, gap20 a x h k hk]

theorem gap22 (a : ℕ → ℝ) (x : ℝ) (h : Admissible a x) :
    Tendsto
      (fun N : ℕ =>
        ∑ k ∈ Finset.Icc 2 (N + 1), Real.log (1 + alpha a x k))
      atTop atBot := by
  rw [tendsto_atBot]
  intro b
  have he := (tendsto_atBot.1 (gap18 a x h)) b
  filter_upwards [he] with N hN
  calc
    (∑ k ∈ Finset.Icc 2 (N + 1), Real.log (1 + alpha a x k)) ≤
        ∑ k ∈ Finset.Icc 2 (N + 1), alpha a x k := by
      apply Finset.sum_le_sum
      intro k hk
      apply le_of_lt
      apply gap19 a x h k
      simp only [Finset.mem_Icc] at hk
      omega
    _ ≤ b := hN

theorem gap23 (a : ℕ → ℝ) (x : ℝ) (h : Admissible a x) :
    Tendsto (fun n : ℕ => Real.log (u a x n)) atTop atBot := by
  have ht := gap22 a x h
  apply ht.congr'
  exact Filter.Eventually.of_forall
    (fun n => (gap15 a x h n).symm)

theorem gap24 (a : ℕ → ℝ) (x : ℝ) (h : Admissible a x) :
    Tendsto (u a x) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => Real.exp (Real.log (u a x n)))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp (gap23 a x h)
  apply ht.congr'
  exact Filter.Eventually.of_forall (fun n =>
    Real.exp_log (u_pos a x h n))

theorem gap25 (a : ℕ → ℝ) (x : ℝ) (h : Admissible a x) :
    Tendsto (remainder a x) atTop (𝓝 0) := by
  have hc : Tendsto (fun _ : ℕ => a 1 / x) atTop (𝓝 (a 1 / x)) :=
    tendsto_const_nhds
  have hm := hc.mul (gap24 a x h)
  have heq : (fun n : ℕ => a 1 / x * u a x n) =ᶠ[atTop]
      remainder a x :=
    Filter.Eventually.of_forall (fun n => (gap5 a x h n).symm)
  have hr := hm.congr' heq
  simpa using hr

theorem gap26 (a : ℕ → ℝ) (x : ℝ) (h : Admissible a x) :
    ∃ τ : ℝ, τ = 0 ∧
      Tendsto (remainder a x) atTop (𝓝 τ) := by
  refine ⟨0, rfl, ?_⟩
  exact gap25 a x h

theorem gap27 (a : ℕ → ℝ) (x : ℝ) (h : Admissible a x) :
    (∑' n : ℕ, term a x (n + 1)) = a 1 / x := by
  have ht := gap10 a x 0 h (gap25 a x h)
  simpa using ht

end

end ProofGap.Exercise3031
