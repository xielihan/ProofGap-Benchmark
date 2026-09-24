import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise2718

noncomputable section

open Filter

def ratio (x : ℝ) : ℝ :=
  x / (2 * x + 1)

def term (x : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) / (n + 1 : ℕ) * ratio x ^ n

def ConditionallySummable (x : ℝ) : Prop :=
  Summable (fun n : ℕ => term x (n + 1)) ∧
    ¬ Summable (fun n : ℕ => |term x (n + 1)|)

private theorem not_tendsto_term_zero_of_one_le_abs_ratio
    (x : ℝ) (hr : 1 ≤ |ratio x|) :
    ¬ Tendsto (fun n : ℕ => term x (n + 1)) atTop (nhds 0) := by
  intro ht
  have he : ∀ᶠ n : ℕ in atTop,
      dist (term x (n + 1)) 0 < (1 / 2 : ℝ) :=
    (Metric.tendsto_nhds.1 ht) (1 / 2) (by norm_num)
  have hf : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [he] with n hn
    have hc0 :
        0 ≤ ((n + 1 : ℕ) : ℝ) / (((n + 1) + 1 : ℕ) : ℝ) := by
      positivity
    have hc :
        (1 / 2 : ℝ) ≤
          ((n + 1 : ℕ) : ℝ) / (((n + 1) + 1 : ℕ) : ℝ) := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      apply (le_div_iff₀ (by positivity)).2
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith
    have hp : 1 ≤ |ratio x| ^ (n + 1) := one_le_pow₀ hr
    have hlower : (1 / 2 : ℝ) ≤ |term x (n + 1)| := by
      rw [term, abs_mul, abs_pow, abs_of_nonneg hc0]
      calc
        (1 / 2 : ℝ) ≤
            (((n + 1 : ℕ) : ℝ) / (((n + 1) + 1 : ℕ) : ℝ)) * 1 := by
              simpa using hc
        _ ≤ (((n + 1 : ℕ) : ℝ) / (((n + 1) + 1 : ℕ) : ℝ)) *
            |ratio x| ^ (n + 1) :=
          mul_le_mul_of_nonneg_left hp hc0
    have hn' : |term x (n + 1)| < (1 / 2 : ℝ) := by
      simpa [Real.dist_eq] using hn
    exact (not_lt_of_ge hlower) hn'
  rcases hf.exists with ⟨n, hn⟩
  exact hn

theorem gap1 :
    Tendsto
      (fun n : ℕ =>
        (((n + 1 : ℕ) : ℝ) / (n + 2 : ℕ)) /
          (((n + 2 : ℕ) : ℝ) / (n + 3 : ℕ)))
      atTop (nhds 1) := by
  have hbase :
      Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop 1
  have hadd (k : ℕ) : Tendsto (fun n : ℕ => n + k) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have heq₁ :
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n + 2 : ℕ)) =
        (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) ∘
          (fun n : ℕ => n + 1) := by
    funext n
    norm_num [Function.comp_apply, Nat.cast_add, add_assoc]
  have heq₂ :
      (fun n : ℕ => ((n + 2 : ℕ) : ℝ) / (n + 3 : ℕ)) =
        (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) ∘
          (fun n : ℕ => n + 2) := by
    funext n
    norm_num [Function.comp_apply, Nat.cast_add, add_assoc]
  have h₁ :
      Tendsto
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n + 2 : ℕ))
        atTop (nhds 1) := by
    rw [heq₁]
    exact hbase.comp (hadd 1)
  have h₂ :
      Tendsto
        (fun n : ℕ => ((n + 2 : ℕ) : ℝ) / (n + 3 : ℕ))
        atTop (nhds 1) := by
    rw [heq₂]
    exact hbase.comp (hadd 2)
  simpa using h₁.div h₂ (by norm_num : (1 : ℝ) ≠ 0)

theorem gap2 (x : ℝ) (hx : x ≠ -1 / 2) :
    |ratio x| < 1 ↔ x ^ 2 < 4 * x ^ 2 + 4 * x + 1 := by
  unfold ratio
  have hd : 2 * x + 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  rw [abs_div, div_lt_one (abs_pos.mpr hd)]
  constructor <;> intro h
  · nlinarith [sq_abs x, sq_abs (2 * x + 1),
      abs_nonneg x, abs_nonneg (2 * x + 1)]
  · nlinarith [sq_abs x, sq_abs (2 * x + 1),
      abs_nonneg x, abs_nonneg (2 * x + 1)]

theorem gap3 (x : ℝ) :
    (3 * x + 1) * (x + 1) > 0 ↔ -1 / 3 < x ∨ x < -1 := by
  constructor
  · intro h
    by_contra hn
    have hx₁ : x ≤ -1 / 3 := by
      apply le_of_not_gt
      intro hx
      exact hn (Or.inl hx)
    have hx₂ : -1 ≤ x := by
      apply le_of_not_gt
      intro hx
      exact hn (Or.inr hx)
    have ha : 3 * x + 1 ≤ 0 := by linarith
    have hb : 0 ≤ x + 1 := by linarith
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg ha hb)) h
  · intro h
    rcases h with h | h
    · exact mul_pos (by linarith) (by linarith)
    · exact mul_pos_of_neg_of_neg (by linarith) (by linarith)

theorem gap4 (x : ℝ) (hx : -1 / 3 < x ∨ x < -1) :
    Summable (fun n : ℕ => |term x (n + 1)|) := by
  have hx0 : x ≠ -1 / 2 := by
    intro h
    rcases hx with hx | hx
    · rw [h] at hx
      norm_num at hx
    · rw [h] at hx
      norm_num at hx
  have hp : 0 < (3 * x + 1) * (x + 1) := (gap3 x).2 hx
  have hsq : x ^ 2 < 4 * x ^ 2 + 4 * x + 1 := by
    nlinarith [hp]
  have hr : |ratio x| < 1 := (gap2 x hx0).2 hsq
  have hs : Summable (fun n : ℕ => |ratio x| ^ n) := by
    apply summable_geometric_of_norm_lt_one
    simpa [Real.norm_eq_abs] using hr
  refine hs.of_norm_bounded ?_
  intro n
  have hc0 :
      0 ≤ ((n + 1 : ℕ) : ℝ) / (((n + 1) + 1 : ℕ) : ℝ) := by
    positivity
  have hc1 :
      ((n + 1 : ℕ) : ℝ) / (((n + 1) + 1 : ℕ) : ℝ) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    simp only [Nat.cast_add, Nat.cast_one]
    linarith
  have hr0 : 0 ≤ |ratio x| := abs_nonneg (ratio x)
  have hpow : |ratio x| ^ (n + 1) ≤ |ratio x| ^ n := by
    calc
      |ratio x| ^ (n + 1) = |ratio x| ^ n * |ratio x| := by
        rw [pow_succ]
      _ ≤ |ratio x| ^ n * 1 :=
        mul_le_mul_of_nonneg_left (le_of_lt hr) (pow_nonneg hr0 n)
      _ = |ratio x| ^ n := by rw [mul_one]
  have hterm : |term x (n + 1)| ≤ |ratio x| ^ n := by
    rw [term, abs_mul, abs_pow, abs_of_nonneg hc0]
    calc
      ((n + 1 : ℕ) : ℝ) / (((n + 1) + 1 : ℕ) : ℝ) *
          |ratio x| ^ (n + 1) ≤
          1 * |ratio x| ^ (n + 1) :=
        mul_le_mul_of_nonneg_right hc1 (pow_nonneg hr0 (n + 1))
      _ = |ratio x| ^ (n + 1) := by rw [one_mul]
      _ ≤ |ratio x| ^ n := hpow
  simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr0 n)] using hterm

theorem gap5 (x : ℝ) (hx : x = -1 / 3 ∨ x = -1) :
    ¬ Tendsto (fun n : ℕ => term x (n + 1)) atTop (nhds 0) := by
  apply not_tendsto_term_zero_of_one_le_abs_ratio x
  rcases hx with rfl | rfl <;> norm_num [ratio]

theorem gap6 (x : ℝ) (hx : x = -1 / 3 ∨ x = -1) :
    ¬ Summable (fun n : ℕ => term x (n + 1)) := by
  intro hs
  exact gap5 x hx hs.tendsto_atTop_zero

theorem gap7 (x : ℝ) (hx0 : x ≠ -1 / 2)
    (hx1 : -1 < x) (hx2 : x < -1 / 3) :
    ¬ Summable (fun n : ℕ => term x (n + 1)) := by
  have ha : 3 * x + 1 < 0 := by linarith
  have hb : 0 < x + 1 := by linarith
  have hp : (3 * x + 1) * (x + 1) < 0 :=
    mul_neg_of_neg_of_pos ha hb
  have hnq : ¬ x ^ 2 < 4 * x ^ 2 + 4 * x + 1 := by
    intro hq
    nlinarith [hp]
  have hr : 1 ≤ |ratio x| := by
    apply le_of_not_gt
    intro hratio
    exact hnq ((gap2 x hx0).1 hratio)
  intro hs
  exact not_tendsto_term_zero_of_one_le_abs_ratio x hr
    hs.tendsto_atTop_zero

theorem gap8 :
    ¬ ∃ x : ℝ, x ≠ -1 / 2 ∧ ConditionallySummable x := by
  rintro ⟨x, hx0, hs, hns⟩
  by_cases hout : -1 / 3 < x ∨ x < -1
  · exact hns (gap4 x hout)
  · have hl : -1 ≤ x := by
      apply le_of_not_gt
      intro h
      exact hout (Or.inr h)
    have hu : x ≤ -1 / 3 := by
      apply le_of_not_gt
      intro h
      exact hout (Or.inl h)
    by_cases hleft : x = -1
    · exact gap6 x (Or.inr hleft) hs
    by_cases hright : x = -1 / 3
    · exact gap6 x (Or.inl hright) hs
    have hl' : -1 < x := lt_of_le_of_ne hl (Ne.symm hleft)
    have hu' : x < -1 / 3 := lt_of_le_of_ne hu hright
    exact gap7 x hx0 hl' hu' hs

theorem gap9 (x : ℝ) (hx0 : x ≠ -1 / 2) :
    ((-1 / 3 < x ∨ x < -1) →
      Summable (fun n : ℕ => |term x (n + 1)|)) ∧
    (-1 ≤ x → x ≤ -1 / 3 →
      ¬ Summable (fun n : ℕ => term x (n + 1))) ∧
    ¬ ConditionallySummable x := by
  have habs :
      (-1 / 3 < x ∨ x < -1) →
        Summable (fun n : ℕ => |term x (n + 1)|) :=
    gap4 x
  have hmiddle :
      -1 ≤ x → x ≤ -1 / 3 →
        ¬ Summable (fun n : ℕ => term x (n + 1)) := by
    intro hl hu
    by_cases hleft : x = -1
    · exact gap6 x (Or.inr hleft)
    by_cases hright : x = -1 / 3
    · exact gap6 x (Or.inl hright)
    have hl' : -1 < x := lt_of_le_of_ne hl (Ne.symm hleft)
    have hu' : x < -1 / 3 := lt_of_le_of_ne hu hright
    exact gap7 x hx0 hl' hu'
  refine ⟨habs, hmiddle, ?_⟩
  intro hc
  by_cases hout : -1 / 3 < x ∨ x < -1
  · exact hc.2 (habs hout)
  · have hl : -1 ≤ x := by
      apply le_of_not_gt
      intro h
      exact hout (Or.inr h)
    have hu : x ≤ -1 / 3 := by
      apply le_of_not_gt
      intro h
      exact hout (Or.inl h)
    exact hmiddle hl hu hc.1

end

end ProofGap.Exercise2718
