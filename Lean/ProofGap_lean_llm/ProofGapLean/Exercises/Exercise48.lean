import ProofGapLean.Prelude.Full
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open scoped Topology

/-!
# Exercise 48

Semantic formalization of Exercise 48, gaps 1,2,3.
-/

namespace ProofGap.Exercise48

noncomputable section

def scale (n : ℕ) : ℝ :=
  Real.cbrt ((n : ℝ) ^ 2) / ((n : ℝ) + 1)

def u (n : ℕ) : ℝ :=
  Real.cbrt ((n : ℝ) ^ 2) *
      Real.sin (Nat.factorial n : ℝ) / ((n : ℝ) + 1)

/-- Exercise 48, gap 1. -/
theorem gap1 :
    ∀ n : ℕ, |Real.sin (Nat.factorial n : ℝ)| ≤ 1 := by
  intro n
  exact Real.abs_sin_le_one _

/-- Exercise 48, gap 2. -/
theorem gap2
    (h1 : ∀ n : ℕ, |Real.sin (Nat.factorial n : ℝ)| ≤ 1) :
    Tendsto scale atTop (𝓝 0) := by
  have hpow :
      Tendsto (fun n : ℕ => Real.rpow (n : ℝ) (-(1 / 3 : ℝ)))
        atTop (𝓝 0) := by
    exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop
  have hinv :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hden :
      Tendsto (fun n : ℕ => 1 + (1 : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hinv
  have hnormalized :
      Tendsto
        (fun n : ℕ =>
          Real.rpow (n : ℝ) (-(1 / 3 : ℝ)) /
            (1 + (1 : ℝ) / (n : ℝ)))
        atTop (𝓝 0) := by
    simpa using hpow.div hden (by norm_num)
  apply Filter.Tendsto.congr' _ hnormalized
  filter_upwards [Filter.eventually_ne_atTop 0] with n hn
  have hnpos : 0 < (n : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hcbrt :
      Real.cbrt ((n : ℝ) ^ 2) =
        Real.rpow (n : ℝ) (2 / 3 : ℝ) := by
    unfold Real.cbrt
    rw [show (n : ℝ) ^ 2 = (n : ℝ) * (n : ℝ) by ring]
    calc
      Real.rpow ((n : ℝ) * (n : ℝ)) (1 / 3 : ℝ) =
          Real.rpow (n : ℝ) (1 / 3 : ℝ) *
            Real.rpow (n : ℝ) (1 / 3 : ℝ) :=
        Real.mul_rpow hnpos.le hnpos.le
      _ = Real.rpow (n : ℝ) ((1 / 3 : ℝ) + 1 / 3) :=
        (Real.rpow_add hnpos _ _).symm
      _ = Real.rpow (n : ℝ) (2 / 3 : ℝ) := by norm_num
  have hmul :
      Real.rpow (n : ℝ) (-(1 / 3 : ℝ)) * (n : ℝ) =
        Real.rpow (n : ℝ) (2 / 3 : ℝ) := by
    calc
      Real.rpow (n : ℝ) (-(1 / 3 : ℝ)) * (n : ℝ) =
          Real.rpow (n : ℝ) (-(1 / 3 : ℝ) + 1) :=
        (Real.rpow_add_one hnpos.ne' _).symm
      _ = Real.rpow (n : ℝ) (2 / 3 : ℝ) := by norm_num
  unfold scale
  rw [hcbrt]
  field_simp [hnpos.ne']
  nlinarith

/-- Exercise 48, gap 3. -/
theorem gap3
    (h1 : ∀ n : ℕ, |Real.sin (Nat.factorial n : ℝ)| ≤ 1)
    (h2 : Tendsto scale atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) := by
  apply squeeze_zero_norm (a := scale)
  · intro n
    have hu :
        u n = scale n * Real.sin (Nat.factorial n : ℝ) := by
      unfold u scale
      ring
    rw [hu, Real.norm_eq_abs, abs_mul]
    have hscale : 0 ≤ scale n := by
      unfold scale Real.cbrt
      exact div_nonneg (Real.rpow_nonneg (sq_nonneg _) _)
        (by positivity)
    rw [abs_of_nonneg hscale]
    nlinarith [h1 n, abs_nonneg (Real.sin (Nat.factorial n : ℝ))]
  · exact h2

end

end ProofGap.Exercise48
