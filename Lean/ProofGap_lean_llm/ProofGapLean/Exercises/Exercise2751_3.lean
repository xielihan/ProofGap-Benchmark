import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2751_3

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
    ∀ (δ x : ℝ), 0 < δ → 1 + δ ≤ x →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 1) := by
  intro δ x hδ hx
  have hxone : 1 < x := by linarith
  have hxpos : 0 < x := lt_trans zero_lt_one hxone
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hq0 : 0 ≤ x⁻¹ := le_of_lt (inv_pos.mpr hxpos)
  have hq_lt : x⁻¹ < 1 := by
    have h : 1 / x < (1 : ℝ) := by
      rw [div_lt_iff₀ hxpos]
      simpa using hxone
    simpa [one_div] using h
  have hq : Tendsto (fun n : ℕ => (x⁻¹) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq_lt
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have ht : Tendsto (fun n : ℕ => 1 / (1 + (x⁻¹) ^ n)) atTop (𝓝 1) := by
    have hsum := hone.add hq
    have hinv := hsum.inv₀ (by norm_num : (1 : ℝ) + 0 ≠ 0)
    simpa [one_div] using hinv
  have hterm : ∀ n : ℕ, term n x = 1 / (1 + (x⁻¹) ^ n) := by
    intro n
    unfold term
    rw [inv_pow]
    field_simp [pow_ne_zero n hxne] <;> ring
  have hfun : (fun n : ℕ => term n x) =
      (fun n : ℕ => 1 / (1 + (x⁻¹) ^ n)) := by
    funext n
    exact hterm n
  rw [hfun]
  exact ht

theorem gap2 :
    ∀ (δ x : ℝ), 0 < δ → 1 + δ ≤ x → (1 : ℝ) = 1 := by
  intro δ x hδ hx
  rfl

theorem gap3 :
    ∀ (δ x : ℝ), 0 < δ → 1 + δ ≤ x →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 1) := by
  intro δ x hδ hx
  exact gap1 δ x hδ hx

theorem gap4 :
    ∀ (δ x : ℝ) (n : ℕ), 0 < δ → 1 + δ ≤ x →
      |term n x - 1| = 1 / (1 + x ^ n) := by
  intro δ x n hδ hx
  have hxpos : 0 < x := by linarith
  have hden : 0 < 1 + x ^ n := by
    have hpow : 0 ≤ x ^ n := pow_nonneg (le_of_lt hxpos) n
    linarith
  have hid : term n x - 1 = -(1 / (1 + x ^ n)) := by
    unfold term
    field_simp [ne_of_gt hden] <;> ring
  calc
    |term n x - 1| = |-(1 / (1 + x ^ n))| := congrArg abs hid
    _ = 1 / (1 + x ^ n) := by
      rw [abs_neg, abs_of_pos (one_div_pos.mpr hden)]

theorem gap5 :
    ∀ (δ x : ℝ) (n : ℕ), 0 < δ → 1 + δ ≤ x →
      1 / (1 + x ^ n) < 1 / (1 + δ) ^ n := by
  intro δ x n hδ hx
  have ha : 0 < 1 + δ := by linarith
  have hxnonneg : 0 ≤ x := le_trans (le_of_lt ha) hx
  have hpow : (1 + δ) ^ n ≤ x ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, pow_succ]
        exact mul_le_mul ih hx (le_of_lt ha) (pow_nonneg hxnonneg n)
  have hdenlt : (1 + δ) ^ n < 1 + x ^ n := by linarith
  have hden : 0 < 1 + x ^ n := by
    have : 0 ≤ x ^ n := pow_nonneg hxnonneg n
    linarith
  have hapow : 0 < (1 + δ) ^ n := pow_pos ha n
  rw [div_lt_div_iff₀ hden hapow]
  simpa using hdenlt

theorem gap6 :
    ∀ (δ x : ℝ) (n : ℕ), 0 < δ → 1 + δ ≤ x →
      |term n x - 1| < 1 / (1 + δ) ^ n := by
  intro δ x n hδ hx
  rw [gap4 δ x n hδ hx]
  exact gap5 δ x n hδ hx

theorem gap7 :
    ∀ (δ x η : ℝ) (n : ℕ), 0 < δ → 1 + δ ≤ x → 0 < η →
      1 / (1 + δ) ^ n < η → |term n x - 1| < η := by
  intro δ x η n hδ hx hη hn
  exact lt_trans (gap6 δ x n hδ hx) hn

theorem gap8 :
    ∀ (δ η : ℝ) (n : ℕ), 0 < δ → 0 < η →
      Real.log (1 / η) / Real.log (1 + δ) < (n : ℝ) →
        1 / (1 + δ) ^ n < η := by
  intro δ η n hδ hη hn
  have ha : 0 < 1 + δ := by linarith
  have haone : 1 < 1 + δ := by linarith
  have hloga : 0 < Real.log (1 + δ) := Real.log_pos haone
  have hlog : Real.log (1 / η) < (n : ℝ) * Real.log (1 + δ) :=
    (div_lt_iff₀ hloga).mp hn
  have hexp_nat_all : ∀ m : ℕ,
      Real.exp ((m : ℝ) * Real.log (1 + δ)) = (1 + δ) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Nat.cast_succ, add_mul, one_mul, Real.exp_add, ih,
          Real.exp_log ha, pow_succ]
  have hexp : 1 / η < (1 + δ) ^ n := by
    calc
      1 / η = Real.exp (Real.log (1 / η)) :=
        (Real.exp_log (one_div_pos.mpr hη)).symm
      _ < Real.exp ((n : ℝ) * Real.log (1 + δ)) :=
        Real.exp_lt_exp.mpr hlog
      _ = (1 + δ) ^ n := hexp_nat_all n
  have hcross : 1 < (1 + δ) ^ n * η :=
    (div_lt_iff₀ hη).mp hexp
  rw [div_lt_iff₀ (pow_pos ha n)]
  simpa [mul_comm] using hcross

theorem gap9 :
    ∀ (δ x η : ℝ) (n : ℕ), 0 < δ → 1 + δ ≤ x → 0 < η →
      Real.log (1 / η) / Real.log (1 + δ) < (n : ℝ) →
        |term n x - 1| < η := by
  intro δ x η n hδ hx hη hn
  apply gap7 δ x η n hδ hx hη
  exact gap8 δ η n hδ hη hn

theorem gap10 :
    ∀ δ : ℝ, 0 < δ →
      ∀ η : ℝ, 0 < η →
        ∃ N : ℕ, ∀ n : ℕ, N < n →
          ∀ x ∈ Set.Ici (1 + δ), |term n x - 1| < η := by
  intro δ hδ η hη
  obtain ⟨N, hN⟩ :=
    exists_nat_gt (Real.log (1 / η) / Real.log (1 + δ))
  refine ⟨N, ?_⟩
  intro n hn x hx
  have hcast : (N : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  apply gap9 δ x η n hδ hx hη
  exact lt_trans hN hcast

theorem gap11 :
    ∀ δ : ℝ, 0 < δ →
      UniformlyConvergesOn term (fun _ => 1) (Set.Ici (1 + δ)) := by
  intro δ hδ
  simpa [UniformlyConvergesOn] using (gap10 δ hδ)

theorem gap12 :
    ∀ δ : ℝ, 0 < δ →
      UniformlyConvergesOn term (fun _ => 1) (Set.Ici (1 + δ)) := by
  intro δ hδ
  exact gap11 δ hδ

end

end ProofGap.Exercise2751_3
