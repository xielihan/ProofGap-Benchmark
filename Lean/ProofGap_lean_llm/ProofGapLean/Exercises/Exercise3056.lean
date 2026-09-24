import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed

namespace ProofGap.Exercise3056

noncomputable section

open Filter
open scoped BigOperators Topology

def factor (x : ℝ) (n : ℕ) : ℝ :=
  Real.cos (x / (2 : ℝ) ^ n)

def partialProduct (x : ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, factor x i

def normalizedSinc (x : ℝ) : ℝ :=
  if x = 0 then 1 else Real.sin x / x

def HasProduct (x L : ℝ) : Prop :=
  Tendsto (partialProduct x) atTop (𝓝 L)

private theorem partialProduct_sine_identity (x : ℝ) (n : ℕ) :
    partialProduct x n *
        ((2 : ℝ) ^ n * Real.sin (x / (2 : ℝ) ^ n)) = Real.sin x := by
  induction n with
  | zero =>
      simp [partialProduct]
  | succ n ih =>
      have hset :
          Finset.Icc 1 (Nat.succ n) =
            insert (Nat.succ n) (Finset.Icc 1 n) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hprod :
          partialProduct x (Nat.succ n) =
            partialProduct x n * factor x (Nat.succ n) := by
        unfold partialProduct
        rw [hset]
        simp [mul_comm]
      have harg :
          x / (2 : ℝ) ^ n =
            2 * (x / (2 : ℝ) ^ (Nat.succ n)) := by
        rw [pow_succ]
        field_simp <;> ring
      rw [harg, Real.sin_two_mul] at ih
      rw [hprod, ← ih]
      simp only [factor, pow_succ]
      ring

theorem gap1 (x : ℝ) (n : ℕ) :
    partialProduct x n =
      ∏ i ∈ Finset.Icc 1 n, Real.cos (x / (2 : ℝ) ^ i) := by
  rfl

theorem gap2 (x : ℝ) (n : ℕ) (hx : x ≠ 0)
    (hden : Real.sin (x / (2 : ℝ) ^ n) ≠ 0) :
    partialProduct x n =
      Real.sin x / ((2 : ℝ) ^ n * Real.sin (x / (2 : ℝ) ^ n)) := by
  apply (eq_div_iff (mul_ne_zero (pow_ne_zero n (by norm_num)) hden)).2
  exact partialProduct_sine_identity x n

theorem gap3 (x : ℝ) (n : ℕ) (hx : x ≠ 0)
    (hden : Real.sin (x / (2 : ℝ) ^ n) ≠ 0) :
    Real.sin x / ((2 : ℝ) ^ n * Real.sin (x / (2 : ℝ) ^ n)) =
      ((x / (2 : ℝ) ^ n) / Real.sin (x / (2 : ℝ) ^ n)) *
        (Real.sin x / x) := by
  field_simp [hx, hden] <;> ring

theorem gap4 (x : ℝ) (n : ℕ) (hx : x ≠ 0)
    (hden : Real.sin (x / (2 : ℝ) ^ n) ≠ 0) :
    partialProduct x n =
      ((x / (2 : ℝ) ^ n) / Real.sin (x / (2 : ℝ) ^ n)) *
        (Real.sin x / x) := by
  calc
    partialProduct x n =
        Real.sin x / ((2 : ℝ) ^ n * Real.sin (x / (2 : ℝ) ^ n)) :=
      gap2 x n hx hden
    _ = ((x / (2 : ℝ) ^ n) / Real.sin (x / (2 : ℝ) ^ n)) *
          (Real.sin x / x) := gap3 x n hx hden

theorem gap5 (x : ℝ) (hx : x ≠ 0) :
    Tendsto (partialProduct x) atTop (𝓝 (Real.sin x / x)) := by
  let q : ℕ → ℝ := fun n => x / (2 : ℝ) ^ n
  have hbase :
      Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  have hq : Tendsto q atTop (𝓝 0) := by
    have heq : q = fun n : ℕ => x * (1 / 2 : ℝ) ^ n := by
      funext n
      simp [q, div_pow, div_eq_mul_inv]
    rw [heq]
    simpa using tendsto_const_nhds.mul hbase
  have hevent :
      ∀ᶠ n : ℕ in atTop, q n ∈ Set.Ioo (-Real.pi) Real.pi :=
    hq.eventually
      (Ioo_mem_nhds (neg_lt_zero.mpr Real.pi_pos) Real.pi_pos)
  have hsin : ∀ᶠ n : ℕ in atTop, Real.sin (q n) ≠ 0 := by
    filter_upwards [hevent] with n hn
    have hqn : q n ≠ 0 :=
      div_ne_zero hx (pow_ne_zero n (by norm_num))
    rcases lt_or_gt_of_ne hqn with hneg | hpos
    · have hspos : 0 < Real.sin (-q n) :=
        Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hneg) (by linarith [hn.1])
      intro hs
      rw [Real.sin_neg, hs] at hspos
      norm_num at hspos
    · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos hn.2)
  have hsinc_at_zero : Tendsto Real.sinc (𝓝 0) (𝓝 1) := by
    have h :=
      (Real.continuous_sinc.continuousAt : ContinuousAt Real.sinc 0)
    change Tendsto Real.sinc (𝓝 0) (𝓝 (Real.sinc 0)) at h
    simpa only [Real.sinc_zero] using h
  have hsinc :
      Tendsto (fun n : ℕ => Real.sinc (q n)) atTop (𝓝 1) :=
    hsinc_at_zero.comp hq
  have hinv :
      Tendsto (fun n : ℕ => (Real.sinc (q n))⁻¹) atTop (𝓝 1) := by
    simpa using hsinc.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hratio :
      Tendsto (fun n : ℕ => q n / Real.sin (q n)) atTop (𝓝 1) := by
    refine (tendsto_congr' ?_).2 hinv
    filter_upwards [hsin] with n hsn
    have hqn : q n ≠ 0 :=
      div_ne_zero hx (pow_ne_zero n (by norm_num))
    simp only [Real.sinc, if_neg hqn]
    field_simp [hqn, hsn]
  have hcombined :
      Tendsto
        (fun n : ℕ => q n / Real.sin (q n) * (Real.sin x / x))
        atTop (𝓝 (Real.sin x / x)) := by
    simpa using
      hratio.mul
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => Real.sin x / x) atTop
            (𝓝 (Real.sin x / x)))
  refine (tendsto_congr' ?_).2 hcombined
  filter_upwards [hsin] with n hn
  exact gap4 x n hx hn

theorem gap6 (x : ℝ) :
    HasProduct x (normalizedSinc x) := by
  unfold HasProduct
  by_cases hx : x = 0
  · subst x
    have hp : partialProduct 0 = fun _ : ℕ => (1 : ℝ) := by
      funext n
      simp [partialProduct, factor]
    rw [hp]
    simpa [normalizedSinc] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)))
  · simpa [normalizedSinc, hx] using gap5 x hx

theorem gap7 (x : ℝ) :
    HasProduct x (normalizedSinc x) := by
  exact gap6 x

end

end ProofGap.Exercise3056
