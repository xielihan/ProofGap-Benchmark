import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise992_1

open Filter

noncomputable section

def f (n : ℕ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else x ^ n * Real.sin (1 / x)

private theorem sin_at_pi_div_two_add_nat_mul_two_pi (k : ℕ) :
    Real.sin (Real.pi / 2 + (k : ℝ) * (2 * Real.pi)) = 1 := by
  induction k with
  | zero =>
      simp [Real.sin_pi_div_two]
  | succ k ih =>
      rw [Nat.cast_succ]
      have h :
          Real.pi / 2 + ((k : ℝ) + 1) * (2 * Real.pi) =
            (Real.pi / 2 + (k : ℝ) * (2 * Real.pi)) + 2 * Real.pi := by
        ring
      rw [h, Real.sin_add, ih, Real.sin_two_pi, Real.cos_two_pi]
      norm_num

theorem gap1 (n : ℕ) (hn : 0 < n) :
    Tendsto (fun x : ℝ => x ^ n * Real.sin (1 / x)) (nhds 0) (nhds 0) := by
  have hp :
      Tendsto (fun x : ℝ => x ^ n) (nhds 0) (nhds 0) := by
    simpa [Nat.ne_of_gt hn] using
      ((tendsto_id : Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0)).pow n)
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.1 hp) ε hε] with x hx
  rw [Real.dist_eq, sub_zero] at hx ⊢
  calc
    |x ^ n * Real.sin (1 / x)| = |x ^ n| * |Real.sin (1 / x)| := abs_mul _ _
    _ ≤ |x ^ n| * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
    _ = |x ^ n| := mul_one _
    _ < ε := hx

theorem gap2 (n : ℕ) (hn : 0 < n) :
    Tendsto (f n) (nhds 0) (nhds (f n 0)) := by
  have hf :
      f n = fun x : ℝ => x ^ n * Real.sin (1 / x) := by
    funext x
    by_cases hx : x = 0
    · subst x
      simp [f, Nat.ne_of_gt hn]
    · simp [f, hx]
  rw [hf]
  simpa [Nat.ne_of_gt hn] using gap1 n hn

theorem gap3 (n : ℕ) (hn : 0 < n) :
    ContinuousAt (f n) 0 := by
  exact gap2 n hn

theorem gap4 (n : ℕ) :
    0 < n ↔ ContinuousAt (f n) 0 := by
  constructor
  · intro hn
    exact gap3 n hn
  · intro hcont
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have hevent :
        ∀ᶠ x in nhds (0 : ℝ),
          dist (f 0 x) (f 0 0) < (1 / 2 : ℝ) :=
      (Metric.tendsto_nhds.1 hcont) (1 / 2) (by norm_num)
    rcases Metric.eventually_nhds_iff.1 hevent with ⟨δ, hδ, hd⟩
    have hpihalf : 0 < Real.pi / 2 := div_pos Real.pi_pos (by norm_num)
    have htwo_pos : 0 < (2 : ℝ) * Real.pi :=
      mul_pos (by norm_num) Real.pi_pos
    have hdenom_pos : 0 < δ * (2 * Real.pi) :=
      mul_pos hδ htwo_pos
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / (δ * (2 * Real.pi)))
    let A : ℝ := Real.pi / 2 + (k : ℝ) * (2 * Real.pi)
    have hk_nonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hprod_nonneg : 0 ≤ (k : ℝ) * (2 * Real.pi) :=
      mul_nonneg hk_nonneg (le_of_lt htwo_pos)
    have hA : 0 < A := by
      dsimp [A]
      exact add_pos_of_pos_of_nonneg hpihalf hprod_nonneg
    have hkδ : 1 < (k : ℝ) * (δ * (2 * Real.pi)) :=
      (div_lt_iff₀ hdenom_pos).mp hk
    have hδprod : 1 < δ * ((k : ℝ) * (2 * Real.pi)) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hkδ
    have hprodA : (k : ℝ) * (2 * Real.pi) < A := by
      dsimp [A]
      linarith
    have hδmul :
        δ * ((k : ℝ) * (2 * Real.pi)) < δ * A :=
      mul_lt_mul_of_pos_left hprodA hδ
    have hδA : 1 < δ * A := lt_trans hδprod hδmul
    have hxlt : 1 / A < δ := (div_lt_iff₀ hA).2 hδA
    have hxpos : 0 < 1 / A := one_div_pos.mpr hA
    have hxdist : dist (1 / A) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hxpos]
      exact hxlt
    have hrecip : 1 / (1 / A) = A := by
      simp [one_div]
    have hfx : f 0 (1 / A) = 1 := by
      rw [f, if_neg (ne_of_gt hxpos), pow_zero, one_mul, hrecip]
      dsimp [A]
      exact sin_at_pi_div_two_add_nat_mul_two_pi k
    have hclose := hd hxdist
    rw [hfx] at hclose
    norm_num [f, Real.dist_eq] at hclose

end

end ProofGap.Exercise992_1
