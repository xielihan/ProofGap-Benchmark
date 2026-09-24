import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Normed.Group.FunctionSeries

namespace ProofGap.Exercise2790

noncomputable section

open scoped BigOperators

def weight (n : ℕ) (x : ℝ) : ℝ :=
  1 / Real.rpow n x

def term (a : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  a n * weight n x

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (n + 1), u k x) - g x| < ε

private theorem seriesUniformlyConvergesOn_of_summable_bound
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (b : ℕ → ℝ)
    (hb : Summable b)
    (hub : ∀ n x, x ∈ s → ‖u n x‖ ≤ b n) :
    SeriesUniformlyConvergesOn u s (fun x => ∑' n, u n x) := by
  intro ε hε
  have h := tendstoUniformlyOn_tsum_nat hb hub
  rw [Metric.tendstoUniformlyOn_iff] at h
  have heventually := h ε hε
  rw [Filter.eventually_atTop] at heventually
  obtain ⟨N, hN⟩ := heventually
  refine ⟨N, ?_⟩
  intro n hn x hx
  have hdist := hN (n + 1) (hn.trans (Nat.le_succ n)) x hx
  simpa only [Real.dist_eq, abs_sub_comm] using hdist

theorem gap1 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    0 < weight n x := by
  unfold weight
  apply one_div_pos.mpr
  apply Real.rpow_pos_of_pos
  exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)

theorem gap2 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) (hx : 0 ≤ x) :
    weight n x ≤ 1 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hrpow : (1 : ℝ) ≤ Real.rpow n x := Real.one_le_rpow hn' hx
  simpa [weight] using
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hrpow

theorem gap3 :
    (0 : ℝ) < 1 := by norm_num

theorem gap4 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) (hx : 0 < x) :
    weight n x > weight (n + 1) x := by
  unfold weight
  apply one_div_lt_one_div_of_lt
  · apply Real.rpow_pos_of_pos
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  · apply Real.rpow_lt_rpow
    · positivity
    · exact_mod_cast Nat.lt_succ_self n
    · exact hx

theorem gap5 (a : ℕ → ℝ)
    (hsum : Summable (fun n : ℕ => a (n + 1))) :
    SeriesUniformlyConvergesOn
      (fun n (_x : ℝ) => a (n + 1))
      (Set.Ici (0 : ℝ))
      (fun _ => ∑' n : ℕ, a (n + 1)) := by
  apply seriesUniformlyConvergesOn_of_summable_bound
      (b := fun n => |a (n + 1)|) (hb := hsum.abs)
  intro n x hx
  simp only [Real.norm_eq_abs]
  exact le_rfl

theorem gap6 (a : ℕ → ℝ)
    (hsum : Summable (fun n : ℕ => a (n + 1))) :
    SeriesUniformlyConvergesOn
      (fun n x => term a (n + 1) x)
      (Set.Ici (0 : ℝ))
      (fun x => ∑' n : ℕ, term a (n + 1) x) := by
  apply seriesUniformlyConvergesOn_of_summable_bound
      (b := fun n => |a (n + 1)|) (hb := hsum.abs)
  intro n x hx
  calc
    ‖term a (n + 1) x‖ = ‖a (n + 1)‖ * weight (n + 1) x := by
      rw [term, norm_mul, show ‖weight (n + 1) x‖ = weight (n + 1) x by
        rw [Real.norm_eq_abs, abs_of_pos (gap1 (n + 1) x (Nat.le_add_left 1 n))]]
    _ ≤ |a (n + 1)| := by
      simpa only [Real.norm_eq_abs] using
        mul_le_of_le_one_right (norm_nonneg (a (n + 1)))
          (gap2 (n + 1) x (Nat.le_add_left 1 n) hx)

theorem gap7 (a : ℕ → ℝ)
    (hsum : Summable (fun n : ℕ => a (n + 1))) :
    SeriesUniformlyConvergesOn
      (fun n x => term a (n + 1) x)
      (Set.Ici (0 : ℝ))
      (fun x => ∑' n : ℕ, term a (n + 1) x) := by
  exact gap6 a hsum

end

end ProofGap.Exercise2790
