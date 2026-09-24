import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1374_2

noncomputable section

open Filter

def quotient (x : ℝ) : ℝ := (x - Real.sin x) / (x + Real.sin x)
def derivativeRatio (x : ℝ) : ℝ := (1 - Real.cos x) / (1 + Real.cos x)
def normalized (x : ℝ) : ℝ := (1 - Real.sin x / x) / (1 + Real.sin x / x)

def SameLimitAtTop (u v : ℝ → ℝ) : Prop :=
  ∀ L : ℝ, Tendsto u atTop (nhds L) ↔ Tendsto v atTop (nhds L)

private theorem trig_nat_mul_two_pi (n : ℕ) :
    Real.sin ((n : ℝ) * (2 * Real.pi)) = 0 ∧
      Real.cos ((n : ℝ) * (2 * Real.pi)) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      constructor
      · calc
          Real.sin (((Nat.succ n : ℕ) : ℝ) * (2 * Real.pi)) =
              Real.sin ((n : ℝ) * (2 * Real.pi) + 2 * Real.pi) := by
                rw [Nat.cast_succ, add_mul]
                simp
          _ = Real.sin ((n : ℝ) * (2 * Real.pi)) :=
            Real.sin_add_two_pi _
          _ = 0 := ih.1
      · calc
          Real.cos (((Nat.succ n : ℕ) : ℝ) * (2 * Real.pi)) =
              Real.cos ((n : ℝ) * (2 * Real.pi) + 2 * Real.pi) := by
                rw [Nat.cast_succ, add_mul]
                simp
          _ = Real.cos ((n : ℝ) * (2 * Real.pi)) :=
            Real.cos_add_two_pi _
          _ = 1 := ih.2

theorem gap1 (x : ℝ) (hden : 1 + Real.cos x ≠ 0) :
    deriv (fun t : ℝ => t - Real.sin t) x /
        deriv (fun t : ℝ => t + Real.sin t) x =
      derivativeRatio x := by
  have hsub :
      HasDerivAt (fun t : ℝ => t - Real.sin t) (1 - Real.cos x) x :=
    (hasDerivAt_id x).sub (Real.hasDerivAt_sin x)
  have hadd :
      HasDerivAt (fun t : ℝ => t + Real.sin t) (1 + Real.cos x) x :=
    (hasDerivAt_id x).add (Real.hasDerivAt_sin x)
  change
    deriv (fun t : ℝ => t - Real.sin t) x /
        deriv (fun t : ℝ => t + Real.sin t) x =
      (1 - Real.cos x) / (1 + Real.cos x)
  rw [hsub.deriv, hadd.deriv]

theorem gap2 :
    ¬ ∃ L : ℝ, Tendsto derivativeRatio atTop (nhds L) := by
  rintro ⟨L, hL⟩
  have hevBall :
      ∀ᶠ x : ℝ in atTop,
        derivativeRatio x ∈ Metric.ball L (1 / 3 : ℝ) :=
    hL (Metric.ball_mem_nhds L (by norm_num))
  have hev :
      ∀ᶠ x : ℝ in atTop,
        dist (derivativeRatio x) L < (1 / 3 : ℝ) := by
    simpa only [Metric.mem_ball] using hevBall
  rcases eventually_atTop.1 hev with ⟨b, hb⟩
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (max b 0)
  have hnpos : 0 < (n : ℝ) :=
    lt_of_le_of_lt (le_max_right b 0) hn
  have hbn : b < (n : ℝ) :=
    lt_of_le_of_lt (le_max_left b 0) hn
  have hfactor : (1 : ℝ) ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hscale :
      (n : ℝ) ≤ (n : ℝ) * (2 * Real.pi) := by
    simpa using
      mul_le_mul_of_nonneg_left hfactor (Nat.cast_nonneg n)
  have hy0 : b < (n : ℝ) * (2 * Real.pi) :=
    lt_of_lt_of_le hbn hscale
  have hy1 :
      b < (n : ℝ) * (2 * Real.pi) + Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have htrig := trig_nat_mul_two_pi n
  have hval0 :
      derivativeRatio ((n : ℝ) * (2 * Real.pi)) = 0 := by
    simp [derivativeRatio, htrig.2]
  have hval1 :
      derivativeRatio
          ((n : ℝ) * (2 * Real.pi) + Real.pi / 2) = 1 := by
    simp [derivativeRatio, Real.cos_add, htrig.1, htrig.2]
  have hd0 := hb _ (le_of_lt hy0)
  have hd1 := hb _ (le_of_lt hy1)
  rw [hval0] at hd0
  rw [hval1] at hd1
  have htriangle :
      dist (0 : ℝ) 1 ≤ dist (0 : ℝ) L + dist (1 : ℝ) L := by
    calc
      dist (0 : ℝ) 1 ≤ dist (0 : ℝ) L + dist L 1 :=
        dist_triangle 0 L 1
      _ = dist (0 : ℝ) L + dist (1 : ℝ) L := by
        rw [dist_comm L 1]
  have hone : dist (0 : ℝ) 1 = 1 := by
    norm_num
  rw [hone] at htriangle
  linarith

theorem gap3 :
    SameLimitAtTop quotient normalized := by
  intro L
  have heq : quotient =ᶠ[atTop] normalized := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hnum :
        1 - Real.sin x / x = (x - Real.sin x) / x := by
      field_simp [hx0]
    have hden :
        1 + Real.sin x / x = (x + Real.sin x) / x := by
      field_simp [hx0]
    change
      (x - Real.sin x) / (x + Real.sin x) =
        (1 - Real.sin x / x) / (1 + Real.sin x / x)
    rw [hnum, hden]
    by_cases hs : x + Real.sin x = 0
    · simp [hs]
    · field_simp [hx0, hs]
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

theorem gap4 :
    Tendsto normalized atTop (nhds 1) := by
  have hs :
      Tendsto (fun x : ℝ => Real.sin x / x) atTop (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [eventually_gt_atTop (1 / ε)] with x hx
    have hinvpos : 0 < 1 / ε := one_div_pos.mpr hε
    have hxpos : 0 < x := lt_trans hinvpos hx
    have hratio : 1 / x < ε := by
      apply (div_lt_iff₀ hxpos).2
      simpa [mul_comm] using ((div_lt_iff₀ hε).1 hx)
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hxpos]
    exact lt_of_le_of_lt
      ((div_le_div_iff_of_pos_right hxpos).2
        (Real.abs_sin_le_one x))
      hratio
  simpa [normalized] using
    (tendsto_const_nhds.sub hs).div
      (tendsto_const_nhds.add hs)
      (by norm_num : (1 : ℝ) + 0 ≠ 0)

theorem gap5 :
    Tendsto quotient atTop (nhds 1) := by
  exact (gap3 1).2 gap4

end

end ProofGap.Exercise1374_2
