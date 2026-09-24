import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise789

noncomputable section

def f (x : ℝ) : ℝ := Real.sin (Real.pi / x)
def xseq (n : ℕ) : ℝ := 2 / n
def yseq (n : ℕ) : ℝ := 2 / (n + 1)

private theorem sin_nat_mul_pi_aux (n : ℕ) :
    Real.sin ((n : ℝ) * Real.pi) = 0 := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, Real.sin_add, ih, Real.sin_pi]
      ring

theorem gap1 : ContinuousOn f (Set.Ioo 0 1) := by
  intro x hx
  have hquot : ContinuousAt (fun y : ℝ => Real.pi / y) x :=
    continuousAt_const.div continuousAt_id (ne_of_gt hx.1)
  have hcomp : ContinuousAt (fun y : ℝ => Real.sin (Real.pi / y)) x := by
    simpa only [Function.comp_apply] using
      Real.continuous_sin.continuousAt.comp hquot
  simpa only [f] using hcomp.continuousWithinAt
theorem gap2 (x : ℝ) : |f x| ≤ 1 := by
  simp only [f]
  rw [abs_le]
  constructor <;>
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi / x),
      sq_nonneg (Real.sin (Real.pi / x)),
      sq_nonneg (Real.cos (Real.pi / x))]

/-- Spell out boundedness on the interval. -/
theorem gap3 : ∃ C : ℝ, ∀ x ∈ Set.Ioo (0 : ℝ) 1, |f x| ≤ C := by
  refine ⟨1, ?_⟩
  intro x hx
  exact gap2 x

theorem gap4 (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₁ : ε₀ < 1)
    (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      |xseq n - yseq n| = 2 / ((n : ℝ) * (n + 1)) := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hn_nat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn_nat
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
    nlinarith
  simp only [xseq, yseq, Nat.cast_add, Nat.cast_one]
  have hcalc :
      (2 : ℝ) / (n : ℝ) - 2 / ((n : ℝ) + 1) =
        2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    field_simp [ne_of_gt hn_pos, ne_of_gt hn1_pos]
    <;> ring
  rw [hcalc]
  exact abs_of_pos (div_pos (by norm_num) (mul_pos hn_pos hn1_pos))
theorem gap5 (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₁ : ε₀ < 1)
    (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, 2 / ((n : ℝ) * (n + 1)) < δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / δ)
  filter_upwards [Filter.eventually_ge_atTop (max 1 N)] with n hn
  have hn_one : 1 ≤ n := le_trans (Nat.le_max_left 1 N) hn
  have hNn : N ≤ n := le_trans (Nat.le_max_right 1 N) hn
  have hn_nat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn_one
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn_nat
  have hNn_real : (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hNn
  have hNδ : (2 : ℝ) < (N : ℝ) * δ :=
    (div_lt_iff₀ hδ).mp hN
  have hmul : (N : ℝ) * δ ≤ (n : ℝ) * δ :=
    mul_le_mul_of_nonneg_right hNn_real (le_of_lt hδ)
  have hbase : (2 : ℝ) < δ * (n : ℝ) := by
    have : (2 : ℝ) < (n : ℝ) * δ := lt_of_lt_of_le hNδ hmul
    simpa only [mul_comm] using this
  have hden_ge :
      (n : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) := by
    nlinarith [sq_nonneg (n : ℝ)]
  have hscaled :
      δ * (n : ℝ) ≤ δ * ((n : ℝ) * ((n : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left hden_ge (le_of_lt hδ)
  have htarget :
      (2 : ℝ) < δ * ((n : ℝ) * ((n : ℝ) + 1)) :=
    lt_of_lt_of_le hbase hscaled
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
    nlinarith
  apply (div_lt_iff₀ (mul_pos hn_pos hn1_pos)).2
  exact htarget
theorem gap6 (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₁ : ε₀ < 1)
    (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, |xseq n - yseq n| < δ := by
  filter_upwards [gap4 ε₀ δ hε₀ hε₁ hδ,
    gap5 ε₀ δ hε₀ hε₁ hδ] with n heq hlt
  rw [heq]
  exact hlt
theorem gap7 (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₁ : ε₀ < 1)
    (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, |f (xseq n) - f (yseq n)| = 1 := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hn_nat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn_nat
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
    nlinarith
  let a : ℝ := Real.pi * (n : ℝ) / 2
  have hxarg : Real.pi / (2 / (n : ℝ)) = a := by
    dsimp [a]
    field_simp [ne_of_gt hn_pos]
    <;> ring
  have hyarg :
      Real.pi / (2 / ((n : ℝ) + 1)) = a + Real.pi / 2 := by
    dsimp [a]
    field_simp [ne_of_gt hn1_pos]
    <;> ring
  simp only [f, xseq, yseq, Nat.cast_add, Nat.cast_one]
  rw [hxarg, hyarg, Real.sin_add, Real.sin_pi_div_two,
    Real.cos_pi_div_two]
  simp only [mul_zero, mul_one, zero_add]
  have hangle : 2 * a = (n : ℝ) * Real.pi := by
    dsimp [a]
    ring
  have hsin_double : Real.sin (2 * a) = 0 := by
    rw [hangle]
    exact sin_nat_mul_pi_aux n
  have hprod : Real.sin a * Real.cos a = 0 := by
    have htwo := Real.sin_two_mul a
    rw [hsin_double] at htwo
    nlinarith
  have hsq : (Real.sin a - Real.cos a) ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq a]
  have habssq : |Real.sin a - Real.cos a| ^ 2 = 1 := by
    simpa only [sq_abs] using hsq
  nlinarith [abs_nonneg (Real.sin a - Real.cos a)]
theorem gap8 (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₁ : ε₀ < 1)
    (hδ : 0 < δ) : ∀ᶠ _n : ℕ in Filter.atTop, ε₀ < 1 := by
  exact Filter.Eventually.of_forall (fun _ => hε₁)
theorem gap9 (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₁ : ε₀ < 1)
    (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, ε₀ < |f (xseq n) - f (yseq n)| := by
  filter_upwards [gap7 ε₀ δ hε₀ hε₁ hδ,
    gap8 ε₀ δ hε₀ hε₁ hδ] with n heq hlt
  simpa only [heq] using hlt
theorem gap10 : ¬ UniformContinuousOn f (Set.Ioo 0 1) := by
  intro huc
  rw [Metric.uniformContinuousOn_iff] at huc
  rcases huc (1 / 2 : ℝ) (by norm_num) with ⟨δ, hδ, hcontrol⟩
  have hmem :
      ∀ᶠ n : ℕ in Filter.atTop,
        xseq n ∈ Set.Ioo (0 : ℝ) 1 ∧ yseq n ∈ Set.Ioo (0 : ℝ) 1 := by
    filter_upwards [Filter.eventually_ge_atTop (3 : ℕ)] with n hn
    have hn_nat : 2 < n := lt_of_lt_of_le (by norm_num) hn
    have hn_real : (2 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn_nat
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      nlinarith
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
      nlinarith
    change
      (0 < xseq n ∧ xseq n < 1) ∧
        (0 < yseq n ∧ yseq n < 1)
    simp only [xseq, yseq, Nat.cast_add, Nat.cast_one]
    refine ⟨⟨div_pos (by norm_num) hn_pos, ?_⟩,
      ⟨div_pos (by norm_num) hn1_pos, ?_⟩⟩
    · exact (div_lt_iff₀ hn_pos).2 (by nlinarith)
    · exact (div_lt_iff₀ hn1_pos).2 (by nlinarith)
  have hclose :=
    gap6 (1 / 2 : ℝ) δ (by norm_num) (by norm_num) hδ
  have hfar :=
    gap9 (1 / 2 : ℝ) δ (by norm_num) (by norm_num) hδ
  have hevent :
      ∀ᶠ n : ℕ in Filter.atTop,
        (xseq n ∈ Set.Ioo (0 : ℝ) 1 ∧
          yseq n ∈ Set.Ioo (0 : ℝ) 1) ∧
        |xseq n - yseq n| < δ ∧
        (1 / 2 : ℝ) < |f (xseq n) - f (yseq n)| := by
    filter_upwards [hmem, hclose, hfar] with n hm hc hf
    exact ⟨hm, hc, hf⟩
  rcases hevent.exists with ⟨n, hm, hc, hf⟩
  have hout :
      dist (f (xseq n)) (f (yseq n)) < (1 / 2 : ℝ) :=
    hcontrol (xseq n) hm.1 (yseq n) hm.2 (by
      simpa only [Real.dist_eq] using hc)
  have hout_abs :
      |f (xseq n) - f (yseq n)| < (1 / 2 : ℝ) := by
    simpa only [Real.dist_eq] using hout
  linarith
theorem gap11 :
    ContinuousOn f (Set.Ioo 0 1) ∧
      (∃ C : ℝ, ∀ x ∈ Set.Ioo (0 : ℝ) 1, |f x| ≤ C) ∧
      ¬ UniformContinuousOn f (Set.Ioo 0 1) := by
  exact ⟨gap1, gap3, gap10⟩

end

end ProofGap.Exercise789
