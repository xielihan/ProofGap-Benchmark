import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Stirling

namespace ProofGap.Exercise3118

open Nat Finset Filter Real
open scoped Topology

noncomputable section

private theorem stirling_log_diff_lt (m : ℕ) :
    Real.log (Stirling.stirlingSeq (m + 1)) -
        Real.log (Stirling.stirlingSeq (m + 2)) <
      1 / (12 * (m + 1 : ℝ) * (m + 2 : ℝ)) := by
  let q : ℝ := (1 / (2 * (m + 1 : ℝ) + 1)) ^ 2
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    calc
      (1 / (2 * (m + 1 : ℝ) + 1)) ^ 2 < 1 ^ 2 := by
        gcongr
        rw [div_lt_one (by positivity)]
        norm_num
        positivity
      _ = 1 := by norm_num
  have hgeom : HasSum (fun k : ℕ => q ^ (k + 1)) (q / (1 - q)) := by
    have h := (hasSum_geometric_of_lt_one hq0.le hq1).mul_left q
    simpa [pow_succ, div_eq_mul_inv, mul_comm] using h
  have hg : HasSum (fun k : ℕ => (1 / 3 : ℝ) * q ^ (k + 1))
      ((1 / 3 : ℝ) * (q / (1 - q))) :=
    hgeom.mul_left (1 / 3 : ℝ)
  have hf := Stirling.log_stirlingSeq_diff_hasSum m
  have hle : (fun k : ℕ =>
      (1 : ℝ) / (2 * (k + 1 : ℝ) + 1) * q ^ (k + 1)) ≤
      (fun k : ℕ => (1 / 3 : ℝ) * q ^ (k + 1)) := by
    intro k
    apply mul_le_mul_of_nonneg_right
    · rw [div_le_iff₀ (by positivity)]
      norm_num
      have hk : 0 ≤ (k : ℝ) := by positivity
      nlinarith
    · positivity
  have hstrict :
      (1 : ℝ) / (2 * ((1 : ℕ) + 1 : ℝ) + 1) * q ^ ((1 : ℕ) + 1) <
        (1 / 3 : ℝ) * q ^ ((1 : ℕ) + 1) := by
    apply mul_lt_mul_of_pos_right
    · norm_num
    · positivity
  have hsum :
      Real.log (Stirling.stirlingSeq (m + 1)) -
          Real.log (Stirling.stirlingSeq (m + 2)) <
        (1 / 3 : ℝ) * (q / (1 - q)) := by
    exact hasSum_lt hle hstrict (by simpa [q] using hf) hg
  calc
    _ < (1 / 3 : ℝ) * (q / (1 - q)) := hsum
    _ = 1 / (12 * (m + 1 : ℝ) * (m + 2 : ℝ)) := by
      dsimp [q]
      field_simp
      rw [show (2 * ((m : ℝ) + 1) + 1) ^ 2 - 1 =
        4 * ((m : ℝ) + 1) * ((m : ℝ) + 2) by ring]
      field_simp
      ring

private theorem stirling_log_diff_lt' (j : ℕ) (hj : 1 ≤ j) :
    Real.log (Stirling.stirlingSeq j) -
        Real.log (Stirling.stirlingSeq (j + 1)) <
      1 / (12 * (j : ℝ) * (j + 1 : ℝ)) := by
  have h := stirling_log_diff_lt (j - 1)
  have h1 : j - 1 + 1 = j := by omega
  have h2 : j - 1 + 2 = j + 1 := by omega
  rw [h1, h2] at h
  have hc1 : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by exact_mod_cast h1
  have hc2 : ((j - 1 : ℕ) : ℝ) + 2 = (j : ℝ) + 1 := by exact_mod_cast h2
  rw [hc1, hc2] at h
  exact h

private theorem finite_stirling_log_residual_bound
    (n N : ℕ) (hn : 1 ≤ n) :
    Real.log (Stirling.stirlingSeq n) -
        Real.log (Stirling.stirlingSeq (n + N)) ≤
      1 / (12 * (n : ℝ)) - 1 / (12 * (n + N : ℝ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hj : 1 ≤ n + N := by omega
      have hd := (stirling_log_diff_lt' (n + N) hj).le
      push_cast at hd ⊢
      rw [show n + (N + 1) = (n + N) + 1 by omega]
      calc
        Real.log (Stirling.stirlingSeq n) -
            Real.log (Stirling.stirlingSeq (n + N + 1)) =
          (Real.log (Stirling.stirlingSeq n) -
              Real.log (Stirling.stirlingSeq (n + N))) +
            (Real.log (Stirling.stirlingSeq (n + N)) -
              Real.log (Stirling.stirlingSeq (n + N + 1))) := by ring
        _ ≤ (1 / (12 * (n : ℝ)) - 1 / (12 * (n + N : ℝ))) +
            1 / (12 * (n + N : ℝ) * (n + N + 1 : ℝ)) :=
          by
            push_cast at ih hd ⊢
            linarith
        _ = 1 / (12 * (n : ℝ)) - 1 / (12 * (n + N + 1 : ℝ)) := by
          push_cast
          field_simp
          ring
        _ = 1 / (12 * (n : ℝ)) -
            1 / (12 * ((n : ℝ) + ((N : ℝ) + 1))) := by ring

private theorem stirling_log_residual_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi) ≤
      1 / (12 * (n : ℝ)) := by
  have hseq0 := Stirling.tendsto_stirlingSeq_sqrt_pi
  have hseq : Tendsto (fun N : ℕ => Stirling.stirlingSeq (n + N)) atTop
      (𝓝 (Real.sqrt Real.pi)) := by
    have h := hseq0.comp (tendsto_add_atTop_nat n)
    exact h.congr' (Filter.Eventually.of_forall fun N => by
      simp [Function.comp_def, Nat.add_comm])
  have hsqrt : Real.sqrt Real.pi ≠ 0 := by positivity
  have hlog : Tendsto (fun N : ℕ =>
      Real.log (Stirling.stirlingSeq (n + N))) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log hsqrt).tendsto.comp hseq
  apply le_of_tendsto (tendsto_const_nhds.sub hlog)
  exact Filter.Eventually.of_forall fun N => by
    calc
      Real.log (Stirling.stirlingSeq n) -
          Real.log (Stirling.stirlingSeq (n + N)) ≤
        1 / (12 * (n : ℝ)) - 1 / (12 * (n + N : ℝ)) :=
        finite_stirling_log_residual_bound n N hn
      _ ≤ 1 / (12 * (n : ℝ)) := by
        have hp : 0 ≤ 1 / (12 * (n + N : ℝ)) := by positivity
        linarith

private theorem stirling_log_diff_pos (m : ℕ) :
    0 < Real.log (Stirling.stirlingSeq (m + 1)) -
      Real.log (Stirling.stirlingSeq (m + 2)) := by
  let f : ℕ → ℝ := fun k =>
    (1 : ℝ) / (2 * (k + 1 : ℝ) + 1) *
      ((1 / (2 * (m + 1 : ℝ) + 1)) ^ 2) ^ (k + 1)
  have hf : HasSum f
      (Real.log (Stirling.stirlingSeq (m + 1)) -
        Real.log (Stirling.stirlingSeq (m + 2))) := by
    simpa [f] using Stirling.log_stirlingSeq_diff_hasSum m
  exact hasSum_lt (fun k => by dsimp [f]; positivity)
    (by dsimp [f]; positivity : (0 : ℝ) < f 0) hasSum_zero hf

private theorem stirling_log_residual_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi) := by
  have hd : 0 < Real.log (Stirling.stirlingSeq n) -
      Real.log (Stirling.stirlingSeq (n + 1)) := by
    have h := stirling_log_diff_pos (n - 1)
    have h1 : n - 1 + 1 = n := by omega
    have h2 : n - 1 + 2 = n + 1 := by omega
    rwa [h1, h2] at h
  have hseq : Real.sqrt Real.pi ≤ Stirling.stirlingSeq (n + 1) :=
    Stirling.sqrt_pi_le_stirlingSeq (by omega)
  have hsqrt : 0 < Real.sqrt Real.pi := by positivity
  have hnext : 0 < Stirling.stirlingSeq (n + 1) := by
    simpa [Nat.add_comm] using Stirling.stirlingSeq'_pos n
  have hlogle : Real.log (Real.sqrt Real.pi) ≤
      Real.log (Stirling.stirlingSeq (n + 1)) :=
    Real.log_le_log hsqrt hseq
  linarith

private theorem stirling_log_residual_lt (n : ℕ) (hn : 1 ≤ n) :
    Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi) <
      1 / (12 * (n : ℝ)) := by
  have hd := stirling_log_diff_lt' n hn
  have hr := stirling_log_residual_le (n + 1) (by omega)
  push_cast at hr
  have htel :
      1 / (12 * (n : ℝ) * (n + 1 : ℝ)) +
          1 / (12 * (n + 1 : ℝ)) =
        1 / (12 * (n : ℝ)) := by
    field_simp
    ring
  have hdecomp :
      Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi) =
        (Real.log (Stirling.stirlingSeq n) -
          Real.log (Stirling.stirlingSeq (n + 1))) +
        (Real.log (Stirling.stirlingSeq (n + 1)) -
          Real.log (Real.sqrt Real.pi)) := by ring
  rw [hdecomp]
  rw [← htel]
  exact add_lt_add_of_lt_of_le hd hr

private theorem factorial_stirling_with_remainder (n : ℕ) (hn : 1 ≤ n) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      (Nat.factorial n : ℝ) =
        Real.sqrt (2 * Real.pi * n) * (n : ℝ) ^ n *
          Real.exp (-(n : ℝ)) * Real.exp (θ / (12 * (n : ℝ))) := by
  let r : ℝ :=
    Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi)
  let θ : ℝ := 12 * (n : ℝ) * r
  have hr0 : 0 < r := by
    exact stirling_log_residual_pos n hn
  have hr1 : r < 1 / (12 * (n : ℝ)) := by
    exact stirling_log_residual_lt n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hθ0 : 0 < θ := by dsimp [θ]; positivity
  have hθ1 : θ < 1 := by
    dsimp [θ]
    have hm := mul_lt_mul_of_pos_left hr1 (by positivity : 0 < 12 * (n : ℝ))
    field_simp at hm
    exact hm
  refine ⟨θ, hθ0, hθ1, ?_⟩
  have hseqpos : 0 < Stirling.stirlingSeq n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
      exact ⟨n - 1, by omega⟩
    exact Stirling.stirlingSeq'_pos m
  have hsqrt : 0 < Real.sqrt Real.pi := by positivity
  have hexp : Real.exp r =
      Stirling.stirlingSeq n / Real.sqrt Real.pi := by
    dsimp [r]
    rw [Real.exp_sub, Real.exp_log hseqpos, Real.exp_log hsqrt]
  have hθr : θ / (12 * (n : ℝ)) = r := by
    dsimp [θ]
    field_simp
  have hseqeq : Stirling.stirlingSeq n =
      Real.sqrt Real.pi * Real.exp (θ / (12 * (n : ℝ))) := by
    rw [hθr, hexp]
    field_simp
  rw [Stirling.stirlingSeq] at hseqeq
  have hsqrt_mul :
      Real.sqrt Real.pi * Real.sqrt (2 * (n : ℝ)) =
        Real.sqrt (2 * Real.pi * (n : ℝ)) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ Real.pi)]
    congr 1
    ring
  have hpow :
      ((n : ℝ) / Real.exp 1) ^ n =
        (n : ℝ) ^ n * Real.exp (-(n : ℝ)) := by
    rw [div_pow, ← Real.exp_nat_mul]
    rw [show (n : ℝ) * 1 = (n : ℝ) by ring, Real.exp_neg]
    rfl
  rw [hpow] at hseqeq
  have hdenne :
      Real.sqrt (2 * (n : ℝ)) *
        ((n : ℝ) ^ n * Real.exp (-(n : ℝ))) ≠ 0 := by
    positivity
  rw [div_eq_iff hdenne] at hseqeq
  calc
    (Nat.factorial n : ℝ) =
        (Real.sqrt Real.pi * Real.exp (θ / (12 * (n : ℝ)))) *
          (Real.sqrt (2 * (n : ℝ)) *
            ((n : ℝ) ^ n * Real.exp (-(n : ℝ)))) := hseqeq
    _ = _ := by
      rw [← hsqrt_mul]
      ring

def oddProduct (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, (2 * i - 1 : ℕ)

private theorem oddProduct_succ (n : ℕ) :
    oddProduct (n + 1) = oddProduct n * ((2 * n + 1 : ℕ) : ℝ) := by
  rw [oddProduct, Finset.prod_Icc_succ_top (by omega)]
  congr 1

private theorem oddProduct_factorial :
    ∀ n : ℕ,
      oddProduct n =
        (Nat.factorial (2 * n) : ℝ) /
          ((2 : ℝ) ^ n * (Nat.factorial n : ℝ)) := by
  intro n
  induction n with
  | zero => simp [oddProduct]
  | succ n ih =>
      rw [oddProduct_succ, ih]
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        Nat.factorial_succ,
        show 2 * n + 1 = 2 * n + 1 by rfl,
        Nat.factorial_succ]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        pow_succ]
      have hnfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
      have htwofac : (Nat.factorial (2 * n) : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

def asymptoticFormula (n : ℕ) (θ : ℝ) : ℝ :=
  Real.sqrt 2 * (2 * (n : ℝ)) ^ n *
    Real.exp (-(n : ℝ) + θ / (12 * (n : ℝ)))

private theorem odd_ratio_remainders :
    ∀ n : ℕ, 1 ≤ n →
      ∃ θ₁ θ₂ : ℝ,
        0 < θ₁ ∧ θ₁ < 1 ∧ 0 < θ₂ ∧ θ₂ < 1 ∧
        (Nat.factorial (2 * n) : ℝ) /
            ((2 : ℝ) ^ n * (Nat.factorial n : ℝ)) =
          (Real.sqrt (2 * Real.pi * (2 * n)) * (2 * (n : ℝ)) ^ (2 * n) *
              Real.exp (-(2 * (n : ℝ))) * Real.exp (θ₁ / (24 * (n : ℝ)))) /
            ((2 : ℝ) ^ n * Real.sqrt (2 * Real.pi * n) *
              (n : ℝ) ^ n * Real.exp (-(n : ℝ)) *
              Real.exp (θ₂ / (12 * (n : ℝ))) ) := by
  intro n hn
  obtain ⟨θ₁, hθ₁0, hθ₁1, hfact2⟩ :=
    factorial_stirling_with_remainder (2 * n) (by omega)
  obtain ⟨θ₂, hθ₂0, hθ₂1, hfact1⟩ :=
    factorial_stirling_with_remainder n hn
  refine ⟨θ₁, θ₂, hθ₁0, hθ₁1, hθ₂0, hθ₂1, ?_⟩
  have hfact2' :
      (Nat.factorial (2 * n) : ℝ) =
        Real.sqrt (2 * Real.pi * (2 * n)) *
          (2 * (n : ℝ)) ^ (2 * n) * Real.exp (-(2 * (n : ℝ))) *
          Real.exp (θ₁ / (24 * (n : ℝ))) := by
    convert hfact2 using 1 <;> push_cast <;> ring
  rw [hfact2', hfact1]
  ring

private theorem odd_ratio_asymptotic
    (n : ℕ) (hn : 1 ≤ n) (θ₁ θ₂ : ℝ)
    (hratio :
      (Nat.factorial (2 * n) : ℝ) /
          ((2 : ℝ) ^ n * (Nat.factorial n : ℝ)) =
        (Real.sqrt (2 * Real.pi * (2 * n)) * (2 * (n : ℝ)) ^ (2 * n) *
            Real.exp (-(2 * (n : ℝ))) * Real.exp (θ₁ / (24 * (n : ℝ)))) /
          ((2 : ℝ) ^ n * Real.sqrt (2 * Real.pi * n) *
            (n : ℝ) ^ n * Real.exp (-(n : ℝ)) *
            Real.exp (θ₂ / (12 * (n : ℝ))))) :
    (Nat.factorial (2 * n) : ℝ) /
        ((2 : ℝ) ^ n * (Nat.factorial n : ℝ)) =
      asymptoticFormula n (θ₁ / 2 - θ₂) := by
  rw [hratio]
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have hsqrt :
      Real.sqrt (2 * Real.pi * (2 * (n : ℝ))) =
        Real.sqrt 2 * Real.sqrt (2 * Real.pi * (n : ℝ)) := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hsqrtne : Real.sqrt (2 * Real.pi * (n : ℝ)) ≠ 0 := by positivity
  have hexp1 : Real.exp (-(2 * (n : ℝ))) =
      Real.exp (-(n : ℝ)) * Real.exp (-(n : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hrem :
      Real.exp (θ₁ / (24 * (n : ℝ))) /
          Real.exp (θ₂ / (12 * (n : ℝ))) =
        Real.exp ((θ₁ / 2 - θ₂) / (12 * (n : ℝ))) := by
    rw [← Real.exp_sub]
    congr 1
    field_simp
    ring
  rw [hsqrt, hexp1]
  unfold asymptoticFormula
  rw [Real.exp_add]
  rw [← hrem]
  field_simp
  ring

private theorem odd_asymptotic :
    ∀ n : ℕ, 1 ≤ n →
      ∃ θ : ℝ, |θ| < 1 ∧
        oddProduct n = asymptoticFormula n θ := by
  intro n hn
  obtain ⟨θ₁, θ₂, hθ₁0, hθ₁1, hθ₂0, hθ₂1, hratio⟩ :=
    odd_ratio_remainders n hn
  refine ⟨θ₁ / 2 - θ₂, ?_, ?_⟩
  · rw [abs_lt]
    constructor <;> linarith
  · rw [oddProduct_factorial n]
    exact odd_ratio_asymptotic n hn θ₁ θ₂ hratio

theorem gap1 :
    ∀ n : ℕ,
      oddProduct n =
        (Nat.factorial (2 * n) : ℝ) /
          ((2 : ℝ) ^ n * (Nat.factorial n : ℝ)) := by
  exact oddProduct_factorial

theorem gap2 :
    ∀ n : ℕ, 1 ≤ n →
      ∃ θ₁ θ₂ : ℝ,
        0 < θ₁ ∧ θ₁ < 1 ∧ 0 < θ₂ ∧ θ₂ < 1 ∧
        (Nat.factorial (2 * n) : ℝ) /
            ((2 : ℝ) ^ n * (Nat.factorial n : ℝ)) =
          (Real.sqrt (2 * Real.pi * (2 * n)) * (2 * (n : ℝ)) ^ (2 * n) *
              Real.exp (-(2 * (n : ℝ))) * Real.exp (θ₁ / (24 * (n : ℝ)))) /
            ((2 : ℝ) ^ n * Real.sqrt (2 * Real.pi * n) *
              (n : ℝ) ^ n * Real.exp (-(n : ℝ)) *
              Real.exp (θ₂ / (12 * (n : ℝ))) ) := by
  exact odd_ratio_remainders

theorem gap3 :
    ∀ n : ℕ, 1 ≤ n →
      ∃ θ : ℝ, |θ| < 1 ∧
        oddProduct n = asymptoticFormula n θ := by
  exact odd_asymptotic

theorem gap4 :
    ∀ n : ℕ, 1 ≤ n →
      ∃ θ : ℝ, |θ| < 1 ∧
        oddProduct n = asymptoticFormula n θ := by
  exact gap3

end

end ProofGap.Exercise3118
