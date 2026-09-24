import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2726

noncomputable section

open Filter

def term (x : ℝ) (n : ℕ) : ℝ :=
  x ^ n / (1 + x ^ (2 * n))

private theorem reciprocal_fraction (a : ℝ) (ha : a ≠ 0) :
    a / (1 + a ^ 2) = a⁻¹ / (1 + (a⁻¹) ^ 2) := by
  have h1 : 1 + a ^ 2 ≠ 0 := by positivity
  have h2 : 1 + (a⁻¹) ^ 2 ≠ 0 := by positivity
  field_simp [ha, h1, h2] <;> ring

theorem gap1 (x : ℝ) (hx : |x| < 1) :
    ∀ n : ℕ, 1 ≤ n → |term x n| ≤ |x| ^ n := by
  intro n hn
  unfold term
  rw [abs_div, abs_pow]
  have hp : 0 ≤ x ^ (2 * n) := by
    rw [mul_comm 2 n, pow_mul]
    positivity
  have hden : 1 ≤ 1 + x ^ (2 * n) := le_add_of_nonneg_right hp
  have hden0 : 0 ≤ 1 + x ^ (2 * n) := le_trans zero_le_one hden
  rw [abs_of_nonneg hden0]
  exact div_le_self (by positivity) hden

theorem gap2 (x : ℝ) (hx : |x| < 1) :
    Summable (fun n : ℕ => |x| ^ (n + 1)) := by
  have hgeom : Summable (fun n : ℕ => |x| ^ n) :=
    summable_geometric_of_norm_lt_one (by
      simpa [Real.norm_eq_abs] using hx)
  simpa [pow_succ, mul_comm] using (hgeom.mul_left |x|)

theorem gap3 (x : ℝ) (hx : |x| < 1) :
    Summable (fun n : ℕ => |term x (n + 1)|) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => |x| ^ (n + 1))
  · exact gap2 x hx
  · intro n
    have hn : 1 ≤ n + 1 := by omega
    simpa only [Real.norm_eq_abs, abs_abs] using
      (gap1 x hx (n + 1) hn)

theorem gap4 (x : ℝ) (hx : |x| = 1) :
    ∀ n : ℕ, 1 ≤ n → |term x n| = 1 / 2 := by
  intro n hn
  have hx2 : x ^ 2 = 1 := by
    calc
      x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      _ = 1 := by rw [hx]; norm_num
  have hxeven : x ^ (2 * n) = 1 := by
    rw [pow_mul, hx2, one_pow]
  unfold term
  rw [abs_div, abs_pow, hx, one_pow, hxeven]
  norm_num

theorem gap5 (x : ℝ) (hx : |x| = 1) :
    ¬ Tendsto (fun n : ℕ => term x (n + 1)) atTop (nhds 0) := by
  intro h
  have habs : Tendsto (fun n : ℕ => |term x (n + 1)|) atTop (nhds 0) := by
    simpa using ((continuous_abs.tendsto (0 : ℝ)).comp h)
  have hfun :
      (fun n : ℕ => |term x (n + 1)|) =
        (fun _ : ℕ => (1 / 2 : ℝ)) := by
    funext n
    have hn : 1 ≤ n + 1 := by omega
    exact gap4 x hx (n + 1) hn
  rw [hfun] at habs
  have hhalf :
      Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2)) :=
    tendsto_const_nhds
  have heq : (1 / 2 : ℝ) = 0 := tendsto_nhds_unique hhalf habs
  norm_num at heq

theorem gap6 (x : ℝ) (hx : |x| = 1) :
    ¬ Summable (fun n : ℕ => term x (n + 1)) := by
  intro hs
  exact gap5 x hx hs.tendsto_atTop_zero

theorem gap7 (x : ℝ) (hx : 1 < |x|) :
    ∀ n : ℕ, 1 ≤ n →
      term x n = (1 / x) ^ n / (1 + (1 / x) ^ (2 * n)) := by
  intro n hn
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    norm_num at hx
  have hxn0 : x ^ n ≠ 0 := pow_ne_zero n hx0
  calc
    term x n = x ^ n / (1 + (x ^ n) ^ 2) := by
      unfold term
      rw [mul_comm 2 n, pow_mul]
    _ = (x ^ n)⁻¹ / (1 + ((x ^ n)⁻¹) ^ 2) :=
      reciprocal_fraction (x ^ n) hxn0
    _ = (1 / x) ^ n / (1 + (1 / x) ^ (2 * n)) := by
      simpa only [one_div, inv_pow, mul_comm 2 n, pow_mul]

theorem gap8 (x : ℝ) (hx : 1 < |x|) :
    |1 / x| < 1 := by
  rw [abs_div, abs_one]
  have hpos : 0 < |x| := lt_trans zero_lt_one hx
  exact (div_lt_one hpos).2 hx

theorem gap9 (x : ℝ) (hx : 1 < |x|) :
    Summable
      (fun n : ℕ =>
        |(1 / x) ^ (n + 1) / (1 + (1 / x) ^ (2 * (n + 1)))|) := by
  simpa [term] using gap3 (1 / x) (gap8 x hx)

theorem gap10 (x : ℝ) :
    |x| ≠ 1 ↔ Summable (fun n : ℕ => term x (n + 1)) := by
  constructor
  · intro hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · apply Summable.of_norm
      simpa only [Real.norm_eq_abs] using gap3 x hlt
    · have hs :
          Summable
            (fun n : ℕ =>
              (1 / x) ^ (n + 1) /
                (1 + (1 / x) ^ (2 * (n + 1)))) := by
        apply Summable.of_norm
        simpa only [Real.norm_eq_abs] using gap9 x hgt
      refine hs.congr ?_
      intro n
      have hn : 1 ≤ n + 1 := by omega
      exact (gap7 x hgt (n + 1) hn).symm
  · intro hs hx
    exact gap6 x hx hs

end

end ProofGap.Exercise2726
