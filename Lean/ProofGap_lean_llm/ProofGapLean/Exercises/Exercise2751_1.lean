import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2751_1

noncomputable section

open Filter
open scoped Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  x ^ n / (1 + x ^ n)

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < η

theorem gap1 :
    ∀ (δ x : ℝ), 0 < δ → δ < 1 → x ∈ Set.Icc 0 (1 - δ) →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  intro δ x hδ hδ_lt hx
  have hx_lt_one : x < 1 := by
    linarith [hx.2]
  have hp : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hx.1 hx_lt_one
  simpa [term] using
    hp.div (tendsto_const_nhds.add hp) (by norm_num : (1 : ℝ) + 0 ≠ 0)

theorem gap2 :
    ∀ (δ x : ℝ), 0 < δ → δ < 1 → x ∈ Set.Icc 0 (1 - δ) →
      (0 : ℝ) = 0 := by
  intros
  rfl

theorem gap3 :
    ∀ (δ x : ℝ), 0 < δ → δ < 1 → x ∈ Set.Icc 0 (1 - δ) →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  intro δ x hδ hδ_lt hx
  exact gap1 δ x hδ hδ_lt hx

theorem gap4 :
    ∀ (δ x : ℝ) (n : ℕ), 0 < δ → δ < 1 →
      x ∈ Set.Icc 0 (1 - δ) → |term n x| = x ^ n / (1 + x ^ n) := by
  intro δ x n hδ hδ_lt hx
  unfold term
  apply abs_of_nonneg
  apply div_nonneg
  · exact pow_nonneg hx.1 n
  · linarith [pow_nonneg hx.1 n]

theorem gap5 :
    ∀ (δ x : ℝ) (n : ℕ), 0 < δ → δ < 1 →
      x ∈ Set.Icc 0 (1 - δ) →
        x ^ n / (1 + x ^ n) < (1 - δ) ^ n := by
  intro δ x n hδ hδ_lt hx
  have hx0 : 0 ≤ x := hx.1
  have hq0 : 0 ≤ 1 - δ := by linarith
  have hqpos : 0 < 1 - δ := by linarith
  have hpow_le : x ^ n ≤ (1 - δ) ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, pow_succ]
        exact mul_le_mul ih hx.2 hx0 (pow_nonneg hq0 n)
  have hxpow : 0 ≤ x ^ n := pow_nonneg hx0 n
  have hqpow : 0 < (1 - δ) ^ n := pow_pos hqpos n
  by_cases hzero : x ^ n = 0
  · simp [hzero, hqpow]
  · have hxpow_pos : 0 < x ^ n := lt_of_le_of_ne hxpow (Ne.symm hzero)
    apply (div_lt_iff₀ (by linarith : 0 < 1 + x ^ n)).2
    nlinarith [mul_pos hqpow hxpow_pos]

theorem gap6 :
    ∀ (δ x : ℝ) (n : ℕ), 0 < δ → δ < 1 →
      x ∈ Set.Icc 0 (1 - δ) → |term n x| < (1 - δ) ^ n := by
  intro δ x n hδ hδ_lt hx
  rw [gap4 δ x n hδ hδ_lt hx]
  exact gap5 δ x n hδ hδ_lt hx

theorem gap7 :
    ∀ (δ x η : ℝ) (n : ℕ), 0 < δ → δ < 1 →
      x ∈ Set.Icc 0 (1 - δ) → 0 < η →
      (1 - δ) ^ n < η → |term n x| < η := by
  intro δ x η n hδ hδ_lt hx hη hn
  exact (gap6 δ x n hδ hδ_lt hx).trans hn

theorem gap8 :
    ∀ (δ η : ℝ) (n : ℕ), 0 < δ → δ < 1 → 0 < η →
      Real.log η / Real.log (1 - δ) < (n : ℝ) →
        (1 - δ) ^ n < η := by
  intro δ η n hδ hδ_lt hη hn
  have hqpos : 0 < 1 - δ := by linarith
  have hq_lt_one : 1 - δ < 1 := by linarith
  have hlogq : Real.log (1 - δ) < 0 :=
    Real.log_neg hqpos hq_lt_one
  have hscaled : (n : ℝ) * Real.log (1 - δ) < Real.log η :=
    (div_lt_iff_of_neg hlogq).mp hn
  have hpowpos : 0 < (1 - δ) ^ n := pow_pos hqpos n
  have hlogpow :
      Real.log ((1 - δ) ^ n) = (n : ℝ) * Real.log (1 - δ) := by
    rw [Real.log_pow]
  by_contra hnot
  have hle : η ≤ (1 - δ) ^ n := le_of_not_gt hnot
  have hlogle : Real.log η ≤ Real.log ((1 - δ) ^ n) :=
    Real.strictMonoOn_log.monotoneOn hη hpowpos hle
  rw [hlogpow] at hlogle
  linarith

theorem gap9 :
    ∀ (δ x η : ℝ) (n : ℕ), 0 < δ → δ < 1 →
      x ∈ Set.Icc 0 (1 - δ) → 0 < η →
      Real.log η / Real.log (1 - δ) < (n : ℝ) →
        |term n x| < η := by
  intro δ x η n hδ hδ_lt hx hη hn
  apply gap7 δ x η n hδ hδ_lt hx hη
  exact gap8 δ η n hδ hδ_lt hη hn

theorem gap10 :
    ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∀ η : ℝ, 0 < η →
        ∃ N : ℕ, ∀ n : ℕ, N < n →
          ∀ x ∈ Set.Icc 0 (1 - δ), |term n x| < η := by
  intro δ hδ hδ_lt η hη
  obtain ⟨N, hN⟩ :=
    exists_nat_gt (Real.log η / Real.log (1 - δ))
  refine ⟨N, ?_⟩
  intro n hn x hx
  apply gap9 δ x η n hδ hδ_lt hx hη
  have hNn : (N : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  exact hN.trans hNn

theorem gap11 :
    ∀ δ : ℝ, 0 < δ → δ < 1 →
      UniformlyConvergesOn term (fun _ => 0) (Set.Icc 0 (1 - δ)) := by
  intro δ hδ hδ_lt
  unfold UniformlyConvergesOn
  intro η hη
  obtain ⟨N, hN⟩ := gap10 δ hδ hδ_lt η hη
  refine ⟨N, ?_⟩
  intro n hn x hx
  simpa using hN n hn x hx

theorem gap12 :
    ∀ δ : ℝ, 0 < δ → δ < 1 →
      UniformlyConvergesOn term (fun _ => 0) (Set.Icc 0 (1 - δ)) := by
  intro δ hδ hδ_lt
  exact gap11 δ hδ hδ_lt

end

end ProofGap.Exercise2751_1
