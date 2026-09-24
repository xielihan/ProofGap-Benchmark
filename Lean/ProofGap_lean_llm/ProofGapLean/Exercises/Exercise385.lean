import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise385

noncomputable section

def f (x : ℝ) : ℝ := Real.log x * Real.sin (Real.pi / x) ^ 2

def BoundedAboveOn (g : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ M : ℝ, ∀ x ∈ s, g x ≤ M

def BoundedBelowOn (g : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ M : ℝ, ∀ x ∈ s, M ≤ g x

/-- Exercise 385, gap 1; restrict to `(0,ε)` and use a valid non-strict upper bound. -/
theorem gap1 : ∀ ε > 0, ∀ x ∈ Set.Ioo 0 ε,
    f x ≤ max 0 (Real.log ε) := by
  intro ε hε x hx
  unfold f
  have hx0 : 0 < x := hx.1
  have hxε : x < ε := hx.2
  have hsin_nonneg : 0 ≤ Real.sin (Real.pi / x) ^ 2 := sq_nonneg _
  have hsin_le : Real.sin (Real.pi / x) ^ 2 ≤ 1 := by
    nlinarith [Real.neg_one_le_sin (Real.pi / x), Real.sin_le_one (Real.pi / x)]
  by_cases hlog : Real.log x ≤ 0
  · have hprod : Real.log x * Real.sin (Real.pi / x) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hlog hsin_nonneg
    exact hprod.trans (le_max_left _ _)
  · have hlog0 : 0 ≤ Real.log x := le_of_not_ge hlog
    have hlog_le : Real.log x ≤ Real.log ε :=
      Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hx0) (Set.mem_Ioi.mpr hε) hxε.le
    have hprod : Real.log x * Real.sin (Real.pi / x) ^ 2 ≤ Real.log x := by
      nlinarith
    exact (hprod.trans hlog_le).trans (le_max_right _ _)

/-- Exercise 385, gap 2; require a nonempty positive interval. -/
theorem gap2 : ∀ ε > 0, BoundedAboveOn f (Set.Ioo 0 ε) := by
  intro ε hε
  refine ⟨max 0 (Real.log ε), ?_⟩
  intro x hx
  exact gap1 ε hε x hx

/-- Exercise 385, gap 3; require a nonempty positive interval. -/
theorem gap3 : ∀ ε > 0, ¬BoundedBelowOn f (Set.Ioo 0 ε) := by
  intro ε hε hbounded
  rcases hbounded with ⟨M, hM⟩
  obtain ⟨n : ℕ, hn : max (2 / ε) (2 / Real.exp M) < n⟩ := exists_nat_gt (max (2 / ε) (2 / Real.exp M))
  let x : ℝ := 2 / (4 * (n : ℝ) + 1)
  have hn0 : 0 < (n : ℝ) := by
    have : 0 < max (2 / ε) (2 / Real.exp M) := lt_max_of_lt_left (div_pos (by norm_num) hε)
    exact_mod_cast this.trans hn
  have hden : 0 < 4 * (n : ℝ) + 1 := by positivity
  have hx0 : 0 < x := by
    dsimp [x]
    positivity
  have hnε : 2 / ε < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hnexp : 2 / Real.exp M < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hxε : x < ε := by
    dsimp [x]
    rw [div_lt_iff₀ hden]
    have := (div_lt_iff₀ hε).mp hnε
    nlinarith
  have hxexp : x < Real.exp M := by
    dsimp [x]
    rw [div_lt_iff₀ hden]
    have hexp : 0 < Real.exp M := Real.exp_pos M
    have := (div_lt_iff₀ hexp).mp hnexp
    nlinarith
  have hlog : Real.log x < M := by
    rw [← Real.log_exp M]
    exact Real.strictMonoOn_log (Set.mem_Ioi.mpr hx0) (Set.mem_Ioi.mpr (Real.exp_pos M)) hxexp
  have harg : Real.pi / x = Real.pi / 2 + (n : ℝ) * (2 * Real.pi) := by
    dsimp [x]
    have htwo : (2 : ℝ) ≠ 0 := by norm_num
    field_simp
    ring
  have hperiod :
      Real.sin (Real.pi / 2 + (n : ℝ) * (2 * Real.pi)) =
        Real.sin (Real.pi / 2) := by
    simpa using
      (Real.sin_add_int_mul_two_pi (Real.pi / 2) (n : ℤ))
  have hsin : Real.sin (Real.pi / x) ^ 2 = 1 := by
    rw [harg, hperiod, Real.sin_pi_div_two]
    norm_num
  have := hM x ⟨hx0, hxε⟩
  unfold f at this
  rw [hsin, mul_one] at this
  exact (not_lt_of_ge this) hlog

/-- Exercise 385, gap 4; require `ε>0`. -/
theorem gap4 : ∀ ε > 0,
    BoundedAboveOn f (Set.Ioo 0 ε) ∧
      ¬BoundedBelowOn f (Set.Ioo 0 ε) := by
  intro ε hε
  exact ⟨gap2 ε hε, gap3 ε hε⟩

end

end ProofGap.Exercise385
