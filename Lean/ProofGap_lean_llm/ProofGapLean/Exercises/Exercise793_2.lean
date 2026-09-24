import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise793_2

noncomputable section

def f (x : ℝ) : ℝ := x ^ 2
def u (n : ℕ) : ℝ := n + 1 / (n + 1 : ℝ)
def v (n : ℕ) : ℝ := n

theorem gap1 : ∀ᶠ n in Filter.atTop, |u n - v n| = 1 / (n + 1 : ℝ) := by
  filter_upwards [] with n
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hq : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hn
  have hEq : u n - v n = 1 / ((n : ℝ) + 1) := by
    unfold u v
    ring
  rw [hEq, abs_of_pos hq]
theorem gap2 (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in Filter.atTop, 1 / (n + 1 : ℝ) < δ := by
  refine Filter.eventually_atTop.2 ⟨1 / δ, ?_⟩
  intro n hn
  have hnpos : 0 < n := lt_of_lt_of_le (one_div_pos.mpr hδ) hn
  have hden : 0 < n + 1 := by linarith
  have hone : 1 ≤ n * δ := (div_le_iff₀ hδ).1 hn
  apply (div_lt_iff₀ hden).2
  nlinarith
theorem gap3 (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in Filter.atTop, |u n - v n| < δ := by
  rcases Filter.eventually_atTop.1 (gap2 δ hδ) with ⟨a, ha⟩
  obtain ⟨N, hN⟩ := exists_nat_gt a
  have hrecip : ∀ᶠ n : ℕ in Filter.atTop, 1 / (n + 1 : ℝ) < δ := by
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact ha (n : ℝ) (le_trans (le_of_lt hN) hNn)
  filter_upwards [gap1, hrecip] with n hEq hLt
  rw [hEq]
  exact hLt
theorem gap4 : ∀ᶠ n in Filter.atTop, |f (u n) - f (v n)| =
    2 * (n : ℝ) / (n + 1) + (1 / (n + 1 : ℝ)) ^ 2 := by
  filter_upwards [] with n
  have hident : f (u n) - f (v n) =
      2 * (n : ℝ) / (n + 1) + (1 / (n + 1 : ℝ)) ^ 2 := by
    unfold f u v
    ring
  rw [hident, abs_of_nonneg]
  positivity
theorem gap5 : ∀ᶠ n in Filter.atTop,
    1 < 2 * (n : ℝ) / (n + 1) + (1 / (n + 1 : ℝ)) ^ 2 := by
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hmain : 1 ≤ 2 * (n : ℝ) / (n + 1) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  have hsq : 0 < (1 / ((n : ℝ) + 1)) ^ 2 := by positivity
  nlinarith
theorem gap6 : ∀ᶠ n in Filter.atTop, 1 < |f (u n) - f (v n)| := by
  rcases Filter.eventually_atTop.1 gap5 with ⟨a, ha⟩
  obtain ⟨N, hN⟩ := exists_nat_gt a
  have hbound : ∀ᶠ n : ℕ in Filter.atTop,
      1 < 2 * (n : ℝ) / (n + 1) + (1 / (n + 1 : ℝ)) ^ 2 := by
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact ha (n : ℝ) (le_trans (le_of_lt hN) hNn)
  filter_upwards [gap4, hbound] with n hEq hLt
  rw [hEq]
  exact hLt
theorem gap7 : ¬ UniformContinuous f := by
  intro hf
  rw [Metric.uniformContinuous_iff] at hf
  obtain ⟨δ, hδ, hcontrol⟩ := hf 1 (by norm_num)
  rcases (Filter.eventually_atTop.1 (gap3 δ hδ)) with ⟨N, hN⟩
  rcases (Filter.eventually_atTop.1 gap6) with ⟨M, hM⟩
  let n : ℕ := max N M
  have hclose : |u n - v n| < δ := hN n (by simp [n])
  have hfar : 1 < |f (u n) - f (v n)| := hM n (by simp [n])
  have hdist : dist (u n) (v n) < δ := by
    simpa only [Real.dist_eq] using hclose
  have hout : dist (f (u n)) (f (v n)) < 1 :=
    @hcontrol (u n) (v n) hdist
  have hout' : |f (u n) - f (v n)| < 1 := by
    simpa only [Real.dist_eq] using hout
  linarith
theorem gap8 : ¬ UniformContinuous f := by
  exact gap7

end
end ProofGap.Exercise793_2
