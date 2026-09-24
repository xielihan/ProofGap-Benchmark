import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2733_3

noncomputable section

def term (y : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / (n + y ^ n)

def ConditionallySummable (y : ℝ) : Prop :=
  ProofGap.SeriesConverges (fun n : ℕ => term y (n + 1)) ∧
    ¬ Summable (fun n : ℕ => |term y (n + 1)|)

theorem gap1 (y : ℝ) (hy : 1 < y) :
    ∀ n : ℕ, 1 ≤ n → |term y n| = 1 / (n + y ^ n) := by
  intro n hn
  have hy0 : 0 < y := by linarith
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) + y ^ n := by positivity
  simp [term, abs_div, abs_of_pos hden]

theorem gap2 (y : ℝ) (hy : 1 < y) :
    ∀ n : ℕ, 1 ≤ n → 1 / (n + y ^ n) < (1 / y) ^ n := by
  intro n hn
  have hy0 : 0 < y := by linarith
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hypow : 0 < y ^ n := pow_pos hy0 n
  have hlt : y ^ n < (n : ℝ) + y ^ n := by linarith
  calc
    1 / ((n : ℝ) + y ^ n) < 1 / y ^ n := one_div_lt_one_div_of_lt hypow hlt
    _ = (1 / y) ^ n := by rw [div_pow]; simp

theorem gap3 (y : ℝ) (hy : 1 < y) :
    ∀ n : ℕ, 1 ≤ n → |term y n| < (1 / y) ^ n := by
  intro n hn
  rw [gap1 y hy n hn]
  exact gap2 y hy n hn

theorem gap4 (y : ℝ) (hy : 1 < y) :
    Summable (fun n : ℕ => |term y (n + 1)|) := by
  have hy0 : 0 < y := by linarith
  have hratio : ‖(1 / y : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (div_pos zero_lt_one hy0)]
    exact (div_lt_one hy0).2 hy
  have hgeom : Summable (fun n : ℕ => (1 / y) ^ (n + 1)) := by
    simpa [pow_succ'] using
      (summable_geometric_of_norm_lt_one hratio).mul_left (1 / y : ℝ)
  refine hgeom.of_norm_bounded (fun n => ?_)
  rw [Real.norm_eq_abs, abs_abs]
  exact (gap3 y hy (n + 1) (by omega)).le

theorem gap5 (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ∀ n : ℕ, 1 ≤ n → term y n = (-1 : ℝ) ^ n / (n + y ^ n) := by
  intro n _
  rfl

theorem gap6 (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ConditionallySummable y := by
  let a : ℕ → ℝ := fun n => 1 / (((n + 1 : ℕ) : ℝ) + y ^ (n + 1))
  have hden_pos (n : ℕ) : 0 < (((n + 1 : ℕ) : ℝ) + y ^ (n + 1)) := by
    have : 0 ≤ y ^ (n + 1) := pow_nonneg hy0 _
    positivity
  have hden_mono : Monotone (fun n : ℕ => (((n + 1 : ℕ) : ℝ) + y ^ (n + 1))) := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    have hp_le : y ^ (n + 1) ≤ 1 := pow_le_one₀ hy0 hy1
    have hp_next : 0 ≤ y ^ ((n + 1) + 1) := pow_nonneg hy0 _
    norm_num [Nat.cast_add, Nat.cast_one] at *
    linarith
  have ha_anti : Antitone a := by
    intro m n hmn
    dsimp [a]
    exact one_div_le_one_div_of_le (hden_pos m) (hden_mono hmn)
  have ha_zero : Tendsto a atTop (nhds 0) := by
    refine squeeze_zero (fun n => ?_) (fun n => ?_)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · dsimp [a]
      positivity
    · dsimp [a]
      apply one_div_le_one_div_of_le
      · positivity
      · norm_num [Nat.cast_add, Nat.cast_one]
        exact pow_nonneg hy0 _
  have hterm (n : ℕ) : term y (n + 1) = -((-1 : ℝ) ^ n * a n) := by
    dsimp [a]
    simp only [term, pow_succ, div_eq_mul_inv]
    ring
  constructor
  · rcases ha_anti.tendsto_alternating_series_of_tendsto_zero ha_zero with ⟨l, hl⟩
    have hpartial :
        (fun n : ℕ => ∑ i ∈ Finset.range n, term y (i + 1)) =
          fun n : ℕ => -(∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * a i) := by
      funext n
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    have htend : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, term y (i + 1))
        atTop (nhds (-l)) := by
      rw [hpartial]
      exact hl.neg
    rw [ProofGap.SeriesConverges]
    refine ⟨-l, ?_⟩
    simpa [HasSum, Function.comp_def] using htend
  · intro habs
    have habs_formula (n : ℕ) : |term y (n + 1)| = a n := by
      dsimp [a]
      rw [term, abs_div, abs_of_pos (hden_pos n)]
      simp
    have hshift : Summable (fun n : ℕ => 1 / (((n + 2 : ℕ) : ℝ))) := by
      refine habs.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      rw [habs_formula]
      dsimp [a]
      apply one_div_le_one_div_of_le (hden_pos n)
      have hp_le : y ^ (n + 1) ≤ 1 := pow_le_one₀ hy0 hy1
      norm_num [Nat.cast_add, Nat.cast_one] at *
      linarith
    exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 2).1 hshift)

theorem gap7 :
    {y : ℝ | 0 ≤ y ∧ Summable (fun n : ℕ => |term y (n + 1)|)} =
      {y : ℝ | 1 < y} := by
  ext y
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hy0, habs⟩
    by_contra hnot
    exact (gap6 y hy0 (le_of_not_gt hnot)).2 habs
  · intro hy
    exact ⟨(lt_trans zero_lt_one hy).le, gap4 y hy⟩

theorem gap8 :
    {y : ℝ | 0 ≤ y ∧ ConditionallySummable y} =
      {y : ℝ | 0 ≤ y ∧ y ≤ 1} := by
  ext y
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hy0, hcond⟩
    refine ⟨hy0, ?_⟩
    by_contra hnot
    exact hcond.2 (gap4 y (lt_of_not_ge hnot))
  · rintro ⟨hy0, hy1⟩
    exact ⟨hy0, gap6 y hy0 hy1⟩

end

end ProofGap.Exercise2733_3
