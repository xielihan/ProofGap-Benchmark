import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise788

noncomputable section

def f (x : ℝ) : ℝ := 1 / x
def u (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)
def v (n : ℕ) : ℝ := 1 / (n + 2 : ℝ)

theorem gap1 : ContinuousOn f (Set.Ioo 0 1) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  simpa [f] using
    (continuousAt_const.div continuousAt_id (ne_of_gt hx.1))
theorem gap2 : ∀ᶠ n in Filter.atTop, |u n - v n| = 1 / ((n + 1 : ℝ) * (n + 2)) := by
  apply Filter.Eventually.of_forall
  intro n
  have h1 : (n + 1 : ℝ) ≠ 0 := by positivity
  have h2 : (n + 2 : ℝ) ≠ 0 := by positivity
  have hEq : u n - v n = 1 / ((n + 1 : ℝ) * (n + 2)) := by
    dsimp [u, v]
    field_simp [h1, h2] <;> ring
  rw [hEq, abs_of_pos (by positivity)]
theorem gap3 (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in Filter.atTop, 1 / ((n + 1 : ℝ) * (n + 2)) < δ := by
  have hlarge : ∀ᶠ n : ℝ in Filter.atTop, 1 / δ + 1 ≤ n :=
    Filter.eventually_ge_atTop (1 / δ + 1)
  filter_upwards [hlarge] with n hn
  have hinv_pos : 0 < 1 / δ := by positivity
  have hn_bound : 1 / δ < n := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hprod_pos : 0 < (n + 1) * (n + 2) := by positivity
  have hprod_ge : n ≤ (n + 1) * (n + 2) := by
    nlinarith [sq_nonneg n]
  apply (div_lt_iff₀ hprod_pos).2
  have hδn : 1 < n * δ := (div_lt_iff₀ hδ).1 hn_bound
  have hmul := mul_le_mul_of_nonneg_left hprod_ge (le_of_lt hδ)
  nlinarith
theorem gap4 (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in Filter.atTop, |u n - v n| < δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hlarge : ∀ᶠ n : ℕ in Filter.atTop, N ≤ n :=
    Filter.eventually_ge_atTop N
  filter_upwards [gap2, hlarge] with n hEq hn
  rw [hEq]
  have hNn_cast : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  have hn_bound : 1 / δ < (n : ℝ) := lt_of_lt_of_le hN hNn_cast
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hprod_pos : 0 < ((n + 1 : ℝ) * (n + 2)) := by positivity
  have hprod_ge : (n : ℝ) ≤ (n + 1 : ℝ) * (n + 2) := by
    nlinarith [sq_nonneg (n : ℝ)]
  apply (div_lt_iff₀ hprod_pos).2
  have hδn : 1 < (n : ℝ) * δ := (div_lt_iff₀ hδ).1 hn_bound
  have hmul := mul_le_mul_of_nonneg_left hprod_ge (le_of_lt hδ)
  nlinarith
theorem gap5 : ∀ᶠ n in Filter.atTop, |f (u n) - f (v n)| = 1 := by
  apply Filter.Eventually.of_forall
  intro n
  have hu : f (u n) = (n + 1 : ℝ) := by
    simp [f, u]
  have hv : f (v n) = (n + 2 : ℝ) := by
    simp [f, v]
  rw [hu, hv]
  have hdiff : (n + 1 : ℝ) - (n + 2 : ℝ) = -1 := by ring
  rw [hdiff]
  norm_num
theorem gap6 (ε₀ : ℝ) (hε : 0 < ε₀) (hε' : ε₀ < 1) :
    ∀ᶠ _n : ℕ in Filter.atTop, ε₀ < 1 := by
  exact Filter.Eventually.of_forall (fun _ => hε')
theorem gap7 (ε₀ : ℝ) (hε : 0 < ε₀) (hε' : ε₀ < 1) :
    ∀ᶠ n in Filter.atTop, ε₀ < |f (u n) - f (v n)| := by
  filter_upwards [gap5, gap6 ε₀ hε hε'] with n hEq hlt
  rw [hEq]
  exact hlt
theorem gap8 : ¬ UniformContinuousOn f (Set.Ioo 0 1) := by
  intro h
  rcases (Metric.uniformContinuousOn_iff.mp h) (1 / 2 : ℝ) (by norm_num) with
    ⟨δ, hδ, hunif⟩
  have hlarge : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ n :=
    Filter.eventually_ge_atTop 1
  have hevent : ∀ᶠ n : ℕ in Filter.atTop,
      1 ≤ n ∧ |u n - v n| < δ ∧ |f (u n) - f (v n)| = 1 := by
    filter_upwards [hlarge, gap4 δ hδ, gap5] with n hn hclose hout
    exact ⟨hn, hclose, hout⟩
  rcases hevent.exists with ⟨n, hn, hclose, hout⟩
  have hnR_nat : ((1 : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by
    simpa using hnR_nat
  have hu : u n ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · dsimp [u]
      positivity
    · dsimp [u]
      have hd : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      apply (div_lt_iff₀ hd).2
      nlinarith
  have hv : v n ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · dsimp [v]
      positivity
    · dsimp [v]
      have hd : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      apply (div_lt_iff₀ hd).2
      nlinarith
  have hdist : dist (u n) (v n) < δ := by
    simpa only [Real.dist_eq] using hclose
  have hsmall := hunif (u n) hu (v n) hv hdist
  have houtdist : dist (f (u n)) (f (v n)) = 1 := by
    simpa only [Real.dist_eq] using hout
  rw [houtdist] at hsmall
  norm_num at hsmall
theorem gap9 : ContinuousOn f (Set.Ioo 0 1) ∧
    ¬ UniformContinuousOn f (Set.Ioo 0 1) := by
  exact ⟨gap1, gap8⟩

end
end ProofGap.Exercise788
