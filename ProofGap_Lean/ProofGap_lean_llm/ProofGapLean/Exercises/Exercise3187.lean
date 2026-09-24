import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise3187

noncomputable section

open Filter
open scoped Topology

def xNonzeroFilter (a : ℝ) : Filter (ℝ × ℝ) :=
  𝓝[setOf fun p : ℝ × ℝ => p.1 ≠ 0] (0, a)

def original (p : ℝ × ℝ) : ℝ :=
  Real.sin (p.1 * p.2) / p.1

def factored (p : ℝ × ℝ) : ℝ :=
  (Real.sin (p.1 * p.2) / (p.1 * p.2)) * p.2

/--
Exercise 3187, gap 1; approach `(0,a)` through
the natural domain `x≠0`.
-/
theorem gap1 :
    ∀ a L : ℝ,
      Tendsto original (xNonzeroFilter a) (𝓝 L) ↔
        Tendsto factored (xNonzeroFilter a) (𝓝 L) := by
  intro a L
  have heq : original =ᶠ[xNonzeroFilter a] factored := by
    unfold xNonzeroFilter
    filter_upwards [self_mem_nhdsWithin] with p hp
    change p.1 ≠ 0 at hp
    by_cases hy : p.2 = 0
    · simp [original, factored, hy]
    · unfold original factored
      field_simp [hp, hy] <;> ring
  exact tendsto_congr' heq

/-- Exercise 3187, gap 2; sine-ratio limit on the same domain. -/
theorem gap2 :
    ∀ a : ℝ, Tendsto factored (xNonzeroFilter a) (𝓝 a) := by
  intro a
  let g : ℝ × ℝ → ℝ := fun p => Real.sinc (p.1 * p.2) * p.2
  have heq : factored =ᶠ[xNonzeroFilter a] g := by
    unfold xNonzeroFilter
    filter_upwards [self_mem_nhdsWithin] with p hp
    change p.1 ≠ 0 at hp
    by_cases hy : p.2 = 0
    · simp [g, factored, hy]
    · simp [g, factored, Real.sinc, hp, hy]
  have hcontinuous : Continuous g := by
    dsimp [g]
    exact
      (Real.continuous_sinc.comp
          (continuous_fst.mul continuous_snd)).mul continuous_snd
  have ht : Tendsto g (xNonzeroFilter a) (𝓝 a) := by
    unfold xNonzeroFilter
    have hga : g ((0, a) : ℝ × ℝ) = a := by
      simp [g, Real.sinc]
    have hc :
        Tendsto g (𝓝 ((0, a) : ℝ × ℝ))
          (𝓝 (g ((0, a) : ℝ × ℝ))) :=
      hcontinuous.continuousAt
    have hfull : Tendsto g (𝓝 ((0, a) : ℝ × ℝ)) (𝓝 a) := by
      simpa only [hga] using hc
    exact hfull.mono_left inf_le_left
  exact (tendsto_congr' heq).2 ht

/-- Exercise 3187, gap 3; final restricted-domain limit. -/
theorem gap3 :
    ∀ a : ℝ, Tendsto original (xNonzeroFilter a) (𝓝 a) := by
  intro a
  exact (gap1 a a).2 (gap2 a)

end

end ProofGap.Exercise3187
