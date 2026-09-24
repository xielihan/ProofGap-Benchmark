import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.SpecificLimits.Basic

open scoped Topology

/-!
# Exercise 46

Semantic formalization of Exercise 46, gaps 1,2,3.
-/

namespace ProofGap.Exercise46

noncomputable section

def u (n : ℕ) : ℝ :=
  (10000 * (n : ℝ)) / ((n : ℝ) ^ 2 + 1)

def v (n : ℕ) : ℝ :=
  10000 / ((n : ℝ) + 1 / (n : ℝ))

def SameLimit (a b : ℕ → ℝ) : Prop :=
  ∀ l : ℝ, Tendsto a atTop (𝓝 l) ↔ Tendsto b atTop (𝓝 l)

/-- Exercise 46, gap 1. -/
theorem gap1 :
    SameLimit u v := by
  have huv : u =ᶠ[atTop] v := by
    filter_upwards [Filter.eventually_ne_atTop 0] with n hn
    unfold u v
    have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp [hnreal]
  intro l
  exact Filter.tendsto_congr' huv

/-- Exercise 46, gap 2. -/
theorem gap2
    (h1 : SameLimit u v) :
    Tendsto v atTop (𝓝 0) := by
  have hnum :
      Tendsto (fun n : ℕ => (10000 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 10000
  have hinv :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hden :
      Tendsto (fun n : ℕ => 1 + ((1 : ℝ) / (n : ℝ)) ^ 2)
        atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (hinv.pow 2)
  have hquot :
      Tendsto
        (fun n : ℕ =>
          ((10000 : ℝ) / (n : ℝ)) /
            (1 + ((1 : ℝ) / (n : ℝ)) ^ 2))
        atTop (𝓝 0) := by
    simpa using hnum.div hden (by norm_num)
  apply Filter.Tendsto.congr' _ hquot
  filter_upwards [Filter.eventually_ne_atTop 0] with n hn
  unfold v
  have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp [hnreal]

/-- Exercise 46, gap 3. -/
theorem gap3
    (h1 : SameLimit u v)
    (h2 : Tendsto v atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) := by
  exact (h1 0).mpr h2

end

end ProofGap.Exercise46
