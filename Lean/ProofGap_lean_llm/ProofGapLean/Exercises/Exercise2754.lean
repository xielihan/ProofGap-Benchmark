import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2754

noncomputable section

open Filter
open scoped Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  n * (Real.sqrt (x + 1 / n) - Real.sqrt x)

def limitFunction (x : ℝ) : ℝ :=
  1 / (2 * Real.sqrt x)

def witnessError (n : ℕ) : ℝ :=
  |term n (1 / n) - limitFunction (1 / n)|

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < ε

theorem gap1 :
    ∀ x : ℝ, 0 < x →
      (fun n : ℕ => term n x) =
        (fun n : ℕ =>
          (n * (x + 1 / n - x)) /
            (Real.sqrt (x + 1 / n) + Real.sqrt x)) := by
  intro x hx
  funext n
  by_cases hn : n = 0
  · subst n
    simp [term]
  · simp only [term]
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have hx0 : 0 ≤ x := le_of_lt hx
    have hxn : 0 ≤ x + 1 / (n : ℝ) := by positivity
    have hsq1 : (Real.sqrt (x + 1 / (n : ℝ))) ^ 2 = x + 1 / (n : ℝ) :=
      Real.sq_sqrt hxn
    have hsqx : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0
    have hden : Real.sqrt (x + 1 / (n : ℝ)) + Real.sqrt x ≠ 0 := by
      have : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
      positivity
    apply (eq_div_iff hden).2
    calc
      (n : ℝ) * (Real.sqrt (x + 1 / (n : ℝ)) - Real.sqrt x) *
          (Real.sqrt (x + 1 / (n : ℝ)) + Real.sqrt x) =
          (n : ℝ) * ((Real.sqrt (x + 1 / (n : ℝ))) ^ 2 - (Real.sqrt x) ^ 2) := by ring
      _ = (n : ℝ) * (x + 1 / (n : ℝ) - x) := by rw [hsq1, hsqx]

theorem gap2 :
    ∀ x : ℝ, 0 < x →
      Tendsto
        (fun n : ℕ =>
          (n * (x + 1 / n - x)) /
            (Real.sqrt (x + 1 / n) + Real.sqrt x))
        atTop (𝓝 (limitFunction x)) := by
  intro x hx
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have harg : Tendsto (fun n : ℕ => x + 1 / (n : ℝ)) atTop (𝓝 x) := by
    simpa using (tendsto_const_nhds.add hinv)
  have hsqrt :
      Tendsto (fun n : ℕ => Real.sqrt (x + 1 / (n : ℝ))) atTop
        (𝓝 (Real.sqrt x)) := by
    exact (show Tendsto Real.sqrt (𝓝 x) (𝓝 (Real.sqrt x)) from
      Real.continuous_sqrt.continuousAt).comp harg
  have hnum :
      Tendsto
        (fun n : ℕ => (n : ℝ) * (x + 1 / (n : ℝ) - x))
        atTop (𝓝 1) := by
    refine (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hn
    field_simp [hn0] <;> ring
  have hden :
      Tendsto
        (fun n : ℕ => Real.sqrt (x + 1 / (n : ℝ)) + Real.sqrt x)
        atTop (𝓝 (Real.sqrt x + Real.sqrt x)) :=
    hsqrt.add tendsto_const_nhds
  have hden0 : Real.sqrt x + Real.sqrt x ≠ 0 := by
    have : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
    positivity
  have hquot := hnum.div hden hden0
  simpa [limitFunction, two_mul] using hquot

theorem gap3 :
    ∀ x : ℝ, 0 < x → limitFunction x = 1 / (2 * Real.sqrt x) := by
  intro x hx
  rfl

theorem gap4 :
    ∀ x : ℝ, 0 < x →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 (limitFunction x)) := by
  intro x hx
  rw [gap1 x hx]
  exact gap2 x hx

theorem gap5 :
    ∀ n : ℕ, 1 ≤ n →
      witnessError n =
        |n * (Real.sqrt (2 / n) - Real.sqrt (1 / n)) -
          1 / (2 * Real.sqrt (1 / n))| := by
  intro n hn
  unfold witnessError term limitFunction
  rw [show (1 / (n : ℝ) + 1 / (n : ℝ)) = 2 / (n : ℝ) by ring]

theorem gap6 :
    ∀ n : ℕ, 1 ≤ n →
      witnessError n =
        Real.sqrt n * |Real.sqrt 2 - 1 - 1 / 2| := by
  intro n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsqrtn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hsq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (le_of_lt hnpos)
  have hsqrt_one :
      Real.sqrt (1 / (n : ℝ)) = 1 / Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
  have hsqrt_two :
      Real.sqrt (2 / (n : ℝ)) = Real.sqrt 2 / Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
  have hinside :
      (n : ℝ) * (Real.sqrt 2 / Real.sqrt (n : ℝ) -
          1 / Real.sqrt (n : ℝ)) -
          1 / (2 * (1 / Real.sqrt (n : ℝ))) =
        Real.sqrt (n : ℝ) * (Real.sqrt 2 - 1 - 1 / 2) := by
    calc
      (n : ℝ) * (Real.sqrt 2 / Real.sqrt (n : ℝ) -
          1 / Real.sqrt (n : ℝ)) -
          1 / (2 * (1 / Real.sqrt (n : ℝ))) =
        (Real.sqrt (n : ℝ)) ^ 2 *
            (Real.sqrt 2 / Real.sqrt (n : ℝ) -
              1 / Real.sqrt (n : ℝ)) -
            1 / (2 * (1 / Real.sqrt (n : ℝ))) := by rw [hsq]
      _ = Real.sqrt (n : ℝ) * (Real.sqrt 2 - 1 - 1 / 2) := by
        field_simp [ne_of_gt hsqrtn] <;> ring
  rw [gap5 n hn, hsqrt_two, hsqrt_one, hinside, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg (n : ℝ))]

theorem gap7 :
    ∀ n : ℕ, 1 ≤ n →
      Real.sqrt n * |Real.sqrt 2 - 1 - 1 / 2| =
        Real.sqrt n * ((Real.sqrt 2 - 1) / (2 * (Real.sqrt 2 + 1))) := by
  intro n hn
  have hs2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hslt : Real.sqrt 2 < (3 / 2 : ℝ) := by
    nlinarith [hs2, Real.sqrt_nonneg 2]
  have hneg : Real.sqrt 2 - 1 - 1 / 2 < 0 := by linarith
  have hc :
      |Real.sqrt 2 - 1 - 1 / 2| =
        (Real.sqrt 2 - 1) / (2 * (Real.sqrt 2 + 1)) := by
    rw [abs_of_neg hneg]
    have hden : Real.sqrt 2 + 1 ≠ 0 := by positivity
    field_simp [hden]
    nlinarith [hs2]
  exact congrArg (fun y : ℝ => Real.sqrt n * y) hc

theorem gap8 :
    ∀ n : ℕ, 1 ≤ n →
      Real.sqrt n * ((Real.sqrt 2 - 1) / (2 * (Real.sqrt 2 + 1))) =
        Real.sqrt n / (2 * (Real.sqrt 2 + 1) ^ 2) := by
  intro n hn
  have hs2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hden : Real.sqrt 2 + 1 ≠ 0 := by positivity
  have hprod : (Real.sqrt 2 - 1) * (Real.sqrt 2 + 1) = (1 : ℝ) := by
    nlinarith [hs2]
  have hc :
      (Real.sqrt 2 - 1) / (2 * (Real.sqrt 2 + 1)) =
        1 / (2 * (Real.sqrt 2 + 1) ^ 2) := by
    calc
      (Real.sqrt 2 - 1) / (2 * (Real.sqrt 2 + 1)) =
          ((Real.sqrt 2 - 1) * (Real.sqrt 2 + 1)) /
            (2 * (Real.sqrt 2 + 1) ^ 2) := by
              field_simp [hden] <;> ring
      _ = 1 / (2 * (Real.sqrt 2 + 1) ^ 2) := by rw [hprod]
  calc
    Real.sqrt n * ((Real.sqrt 2 - 1) / (2 * (Real.sqrt 2 + 1))) =
        Real.sqrt n * (1 / (2 * (Real.sqrt 2 + 1) ^ 2)) := by rw [hc]
    _ = Real.sqrt n / (2 * (Real.sqrt 2 + 1) ^ 2) := by ring

theorem gap9 :
    ∀ n : ℕ, 1 ≤ n →
      Real.sqrt n / (2 * (Real.sqrt 2 + 1) ^ 2) >
        (1 / 18 : ℝ) * Real.sqrt n := by
  intro n hn
  have hs2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hslt3 : Real.sqrt 2 < (3 : ℝ) := by
    nlinarith [hs2, Real.sqrt_nonneg 2]
  have hdenpos : 0 < 2 * (Real.sqrt 2 + 1) ^ 2 := by positivity
  have hdenlt : 2 * (Real.sqrt 2 + 1) ^ 2 < (18 : ℝ) := by
    nlinarith [hs2]
  have hcoeff :
      (1 / 18 : ℝ) < 1 / (2 * (Real.sqrt 2 + 1) ^ 2) := by
    apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 18) hdenpos).2
    nlinarith [hdenlt]
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsqrtnpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hmul := mul_lt_mul_of_pos_right hcoeff hsqrtnpos
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul

theorem gap10 :
    ∀ n : ℕ, 1 ≤ n →
      witnessError n > (1 / 18 : ℝ) * Real.sqrt n := by
  intro n hn
  calc
    witnessError n =
        Real.sqrt n * |Real.sqrt 2 - 1 - 1 / 2| := gap6 n hn
    _ = Real.sqrt n *
        ((Real.sqrt 2 - 1) / (2 * (Real.sqrt 2 + 1))) := gap7 n hn
    _ = Real.sqrt n / (2 * (Real.sqrt 2 + 1) ^ 2) := gap8 n hn
    _ > (1 / 18 : ℝ) * Real.sqrt n := gap9 n hn

theorem gap11 :
    ∀ ε₀ : ℝ, 0 < ε₀ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → witnessError n > ε₀ := by
  intro ε₀ hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((18 * ε₀) ^ 2)
  have hNpos : 0 < N := by
    by_contra hpos
    have hzero : N = 0 := Nat.eq_zero_of_not_pos hpos
    have hbad : ((18 * ε₀) ^ 2 : ℝ) < 0 := by simpa [hzero] using hN
    nlinarith [sq_nonneg (18 * ε₀)]
  refine ⟨N, ?_⟩
  intro n hNn
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hNpos)
  have hn1 : 1 ≤ n := le_trans hN1 hNn
  have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
  have hsq_lt : (18 * ε₀) ^ 2 < (n : ℝ) := lt_of_lt_of_le hN hcast
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hsqn : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt hnnonneg
  have hsqrtnnonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have heighteen : 0 < 18 * ε₀ := mul_pos (by norm_num) hε
  have hroot : 18 * ε₀ < Real.sqrt (n : ℝ) := by
    nlinarith
  have hw := gap10 n hn1
  nlinarith

theorem gap12 :
    ¬ UniformlyConvergesOn term limitFunction (Set.Ioi (0 : ℝ)) := by
  intro hU
  obtain ⟨N, hsmall⟩ := hU (1 : ℝ) zero_lt_one
  obtain ⟨M, hlarge⟩ := gap11 (1 : ℝ) zero_lt_one
  let n : ℕ := max (N + 1) M
  have hnN1 : N + 1 ≤ n := by
    exact le_max_left (N + 1) M
  have hnN : N < n := lt_of_lt_of_le (Nat.lt_succ_self N) hnN1
  have hnM : M ≤ n := by
    exact le_max_right (N + 1) M
  have hnpos : 0 < n :=
    lt_of_lt_of_le (Nat.zero_lt_succ N) hnN1
  have hnposR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hx : (1 / (n : ℝ)) ∈ Set.Ioi (0 : ℝ) := by
    change 0 < 1 / (n : ℝ)
    exact one_div_pos.mpr hnposR
  have hs := hsmall n hnN (1 / (n : ℝ)) hx
  change witnessError n < 1 at hs
  have hl := hlarge n hnM
  linarith

theorem gap13 :
    (∀ x : ℝ, 0 < x →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 (limitFunction x))) ∧
      ¬ UniformlyConvergesOn term limitFunction (Set.Ioi (0 : ℝ)) := by
  exact ⟨gap4, gap12⟩

end

end ProofGap.Exercise2754
