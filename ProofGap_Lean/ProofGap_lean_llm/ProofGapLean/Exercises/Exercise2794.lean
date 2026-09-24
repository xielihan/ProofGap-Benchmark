import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace ProofGap.Exercise2794

noncomputable section

open Filter
open scoped BigOperators

def term (k : ℕ) (x : ℝ) : ℝ :=
  (k : ℝ) * x * Real.exp (-((k : ℝ) * x)) -
    ((k : ℝ) - 1) * x * Real.exp (-(((k : ℝ) - 1) * x))

def partialSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, term k x

def limit (_x : ℝ) : ℝ :=
  0

def badPoint (n : ℕ) : ℝ :=
  1 / (n : ℝ)

def UniformlyConvergesOn
    (s : ℕ → ℝ → ℝ) (E : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ E, |s n x - g x| < ε

theorem gap1 (n : ℕ) (x : ℝ) :
    partialSum n x = (n : ℝ) * x * Real.exp (-((n : ℝ) * x)) := by
  induction n with
  | zero =>
      simp [partialSum]
  | succ n ih =>
      rw [partialSum]
      have hset :
          Finset.Icc 1 (Nat.succ n) =
            insert (Nat.succ n) (Finset.Icc 1 n) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : Nat.succ n ∉ Finset.Icc 1 n := by
        simp
      rw [hset, Finset.sum_insert hnot]
      change term (Nat.succ n) x + partialSum n x =
        (Nat.succ n : ℝ) * x * Real.exp (-((Nat.succ n : ℝ) * x))
      rw [ih]
      simp only [term, Nat.cast_succ, add_sub_cancel_right]
      ring

theorem gap2 (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n => partialSum n x) atTop (nhds (limit x)) := by
  by_cases hx0 : x = 0
  · subst x
    simp [gap1, limit]
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    have hnx : Tendsto (fun n : ℕ => (n : ℝ) * x) atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro b
      obtain ⟨N, hN⟩ := exists_nat_gt (b / x)
      filter_upwards [eventually_ge_atTop N] with n hn
      have hNx : b < (N : ℝ) * x := (div_lt_iff₀ hxpos).1 hN
      have hcast : (N : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hn
      exact le_trans (le_of_lt hNx)
        (mul_le_mul_of_nonneg_right hcast (le_of_lt hxpos))
    have hdecay :=
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hnx
    simpa [gap1, limit, pow_one] using hdecay

theorem gap3 (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n => partialSum n x) atTop (nhds 0) := by
  simpa [limit] using gap2 x hx

theorem gap4 (x : ℝ) :
    limit x = 0 := by
  rfl

theorem gap5 :
    ContinuousOn limit (Set.Icc (0 : ℝ) 1) := by
  simpa [limit] using
    (continuous_const.continuousOn :
      ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc (0 : ℝ) 1))

theorem gap6
    (huniform : UniformlyConvergesOn partialSum (Set.Icc (0 : ℝ) 1) limit) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |partialSum n x - limit x| < ε := by
  exact huniform

theorem gap7
    (huniform : UniformlyConvergesOn partialSum (Set.Icc (0 : ℝ) 1) limit) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |partialSum n x - limit x| < (1 / 2 : ℝ) * Real.exp (-1) := by
  exact huniform _ (mul_pos (by norm_num) (Real.exp_pos _))

theorem gap8 (N n : ℕ) (hnN : N ≤ n) (hn : 1 ≤ n)
    (huniform : UniformlyConvergesOn partialSum (Set.Icc (0 : ℝ) 1) limit)
    (hN : ∀ m ≥ N, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |partialSum m x - limit x| < (1 / 2 : ℝ) * Real.exp (-1)) :
    |partialSum n (badPoint n) - limit (badPoint n)| <
      (1 / 2 : ℝ) * Real.exp (-1) := by
  apply hN n hnN (badPoint n)
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  constructor
  · unfold badPoint
    exact le_of_lt (div_pos (by norm_num) hnpos)
  · unfold badPoint
    exact (div_le_iff₀ hnpos).2 (by simpa using hnreal)

theorem gap9 (n : ℕ) (hn : 1 ≤ n) :
    |partialSum n (badPoint n) - limit (badPoint n)| =
      partialSum n (badPoint n) := by
  have hbad : 0 ≤ badPoint n := by
    unfold badPoint
    exact div_nonneg (by norm_num) (Nat.cast_nonneg n)
  have hp : 0 ≤ partialSum n (badPoint n) := by
    rw [gap1]
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg n) hbad)
      (le_of_lt (Real.exp_pos _))
  simpa [gap4] using (abs_of_nonneg hp)

theorem gap10 (n : ℕ) (hn : 1 ≤ n) :
    partialSum n (badPoint n) = Real.exp (-1) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hn))
  rw [gap1]
  have hnb : (n : ℝ) * badPoint n = 1 := by
    unfold badPoint
    field_simp
  rw [hnb]
  simp

theorem gap11 :
    Real.exp (-1) > (1 / 2 : ℝ) * Real.exp (-1) := by
  have he : 0 < Real.exp (-1) := Real.exp_pos _
  nlinarith

theorem gap12 (n : ℕ) (hn : 1 ≤ n) :
    |partialSum n (badPoint n) - limit (badPoint n)| >
      (1 / 2 : ℝ) * Real.exp (-1) := by
  rw [gap9 n hn, gap10 n hn]
  exact gap11

theorem gap13 :
    UniformlyConvergesOn partialSum (Set.Icc (0 : ℝ) 1) limit → False := by
  intro huniform
  obtain ⟨N, hN⟩ := gap7 huniform
  let n := max N 1
  have hnN : N ≤ n := by
    exact le_max_left N 1
  have hn : 1 ≤ n := by
    exact le_max_right N 1
  have hlt := gap8 N n hnN hn huniform hN
  have hgt := gap12 n hn
  exact (not_lt_of_ge (le_of_lt hgt)) hlt

theorem gap14 :
    (∀ x ∈ Set.Icc (0 : ℝ) 1,
      Summable (fun n : ℕ => term (n + 1) x)) ∧
    ¬ UniformlyConvergesOn partialSum (Set.Icc (0 : ℝ) 1) limit ∧
    ContinuousOn limit (Set.Icc (0 : ℝ) 1) := by
  constructor
  · intro x hx
    by_cases hx0 : x = 0
    · subst x
      simp [term]
    · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
      let q : ℝ := Real.exp (-x)
      have hq : ‖q‖ < 1 := by
        dsimp [q]
        rw [abs_of_pos (Real.exp_pos _)]
        exact (Real.exp_lt_one_iff).2 (neg_lt_zero.mpr hxpos)
      have hqpow (n : ℕ) :
          q ^ n = Real.exp (-((n : ℝ) * x)) := by
        dsimp [q]
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      have hgeom : Summable (fun n : ℕ => (n : ℝ) * q ^ n) :=
        (hasSum_coe_mul_geometric_of_norm_lt_one hq).summable
      have ha : Summable
          (fun n : ℕ => (n : ℝ) * x * Real.exp (-((n : ℝ) * x))) := by
        simpa only [hqpow, mul_assoc, mul_comm, mul_left_comm] using
          hgeom.mul_right x
      have hsucc : Function.Injective (fun n : ℕ => n + 1) := by
        intro m n h
        exact Nat.add_right_cancel h
      have hshift : Summable
          (fun n : ℕ =>
            ((n + 1 : ℕ) : ℝ) * x *
              Real.exp (-(((n + 1 : ℕ) : ℝ) * x))) := by
        simpa only [Function.comp_apply] using ha.comp_injective hsucc
      simpa [term, Nat.cast_add, Nat.cast_one] using hshift.sub ha
  · constructor
    · exact gap13
    · exact gap5

end

end ProofGap.Exercise2794
