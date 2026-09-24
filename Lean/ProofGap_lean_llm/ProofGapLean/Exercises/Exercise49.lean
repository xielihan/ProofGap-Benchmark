import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.SpecificLimits.Normed

open scoped Topology

/-!
# Exercise 49

Semantic formalization of `proof_gap/exercise_49/{1,2,3}.txt`.
-/

namespace ProofGap.Exercise49

noncomputable section

def u (n : ℕ) : ℝ :=
  ((-2 : ℝ) ^ n + 3 ^ n) / ((-2 : ℝ) ^ (n + 1) + 3 ^ (n + 1))

def normalized (n : ℕ) : ℝ :=
  ((-(2 / 3 : ℝ)) ^ n * (1 / 3 : ℝ) + (1 / 3 : ℝ)) /
    ((-(2 / 3 : ℝ)) ^ (n + 1) + 1)

def SameLimit (a b : ℕ → ℝ) : Prop :=
  ∀ l : ℝ, Tendsto a atTop (𝓝 l) ↔ Tendsto b atTop (𝓝 l)

/-- Source: `proof_gap/exercise_49/1.txt`. -/
theorem gap1 :
    SameLimit u normalized := by
  have hun : ∀ n, u n = normalized n := by
    intro n
    have hpow :
        |(-(2 / 3 : ℝ)) ^ (n + 1)| < 1 := by
      rw [abs_pow]
      norm_num
      exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    have hden :
        (-(2 / 3 : ℝ)) ^ (n + 1) + 1 ≠ 0 := by
      have := (abs_lt.mp hpow).1
      linarith
    unfold u normalized
    rw [show -(2 / 3 : ℝ) = (-2 : ℝ) / 3 by ring, div_pow, div_pow]
    field_simp [hden]
    ring
  intro l
  exact Filter.tendsto_congr hun

/-- Source: `proof_gap/exercise_49/2.txt`. -/
theorem gap2
    (h1 : SameLimit u normalized) :
    Tendsto normalized atTop (𝓝 (1 / 3 : ℝ)) := by
  have hpow :
      Tendsto (fun n : ℕ => (-(2 / 3 : ℝ)) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  have hpowsucc :
      Tendsto (fun n : ℕ => (-(2 / 3 : ℝ)) ^ (n + 1))
        atTop (𝓝 0) := by
    simpa [pow_succ] using hpow.mul_const (-(2 / 3 : ℝ))
  unfold normalized
  have hnum :
      Tendsto
        (fun n : ℕ =>
          (-(2 / 3 : ℝ)) ^ n * (1 / 3 : ℝ) + (1 / 3 : ℝ))
        atTop (𝓝 (1 / 3 : ℝ)) := by
    simpa using (hpow.mul_const (1 / 3 : ℝ)).add tendsto_const_nhds
  have hden :
      Tendsto (fun n : ℕ => (-(2 / 3 : ℝ)) ^ (n + 1) + 1)
        atTop (𝓝 1) := by
    simpa using hpowsucc.add tendsto_const_nhds
  simpa using hnum.div hden (by norm_num)

/-- Source: `proof_gap/exercise_49/3.txt`. -/
theorem gap3
    (h1 : SameLimit u normalized)
    (h2 : Tendsto normalized atTop (𝓝 (1 / 3 : ℝ))) :
    Tendsto u atTop (𝓝 (1 / 3 : ℝ)) := by
  exact (h1 (1 / 3)).mpr h2

end

end ProofGap.Exercise49
