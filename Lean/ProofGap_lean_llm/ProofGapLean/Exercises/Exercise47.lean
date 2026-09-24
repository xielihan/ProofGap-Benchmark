import ProofGapLean.Prelude.Analysis

open scoped Topology

/-!
# Exercise 47

Semantic formalization of Exercise 47, gaps 1,...,4.
-/

namespace ProofGap.Exercise47

noncomputable section

def u (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) + 1) - Real.sqrt n

def rationalized (n : ℕ) : ℝ :=
  ((Real.sqrt ((n : ℝ) + 1) - Real.sqrt n) *
      (Real.sqrt ((n : ℝ) + 1) + Real.sqrt n)) /
    (Real.sqrt ((n : ℝ) + 1) + Real.sqrt n)

def reciprocal (n : ℕ) : ℝ :=
  1 / (Real.sqrt ((n : ℝ) + 1) + Real.sqrt n)

def SameLimit (a b : ℕ → ℝ) : Prop :=
  ∀ l : ℝ, Tendsto a atTop (𝓝 l) ↔ Tendsto b atTop (𝓝 l)

/-- Exercise 47, gap 1. -/
theorem gap1 :
    SameLimit u rationalized := by
  have hur : ∀ n, u n = rationalized n := by
    intro n
    unfold u rationalized
    have hden :
        0 < Real.sqrt ((n : ℝ) + 1) + Real.sqrt n := by
      have : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
      positivity
    field_simp [hden.ne']
  intro l
  exact Filter.tendsto_congr hur

/-- Exercise 47, gap 2. -/
theorem gap2
    (h1 : SameLimit u rationalized) :
    SameLimit rationalized reciprocal := by
  have hrr : ∀ n, rationalized n = reciprocal n := by
    intro n
    unfold rationalized reciprocal
    have hden :
        0 < Real.sqrt ((n : ℝ) + 1) + Real.sqrt n := by
      have : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
      positivity
    have hsuc :
        (Real.sqrt ((n : ℝ) + 1)) ^ 2 = (n : ℝ) + 1 :=
      Real.sq_sqrt (by positivity)
    have hn : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg n)
    field_simp [hden.ne']
    nlinarith
  intro l
  exact Filter.tendsto_congr hrr

/-- Exercise 47, gap 3. -/
theorem gap3
    (h2 : SameLimit rationalized reciprocal) :
    Tendsto reciprocal atTop (𝓝 0) := by
  have hsqrt :
      Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv :
      Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => by
      unfold reciprocal
      positivity
  · filter_upwards [Filter.eventually_ne_atTop 0] with n hn
    unfold reciprocal
    apply one_div_le_one_div_of_le
    · exact Real.sqrt_pos.2 (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
    · exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
  · simpa [one_div] using hinv

/-- Exercise 47, gap 4. -/
theorem gap4
    (h1 : SameLimit u rationalized)
    (h2 : SameLimit rationalized reciprocal)
    (h3 : Tendsto reciprocal atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) := by
  exact (h1 0).mpr ((h2 0).mpr h3)

end

end ProofGap.Exercise47
