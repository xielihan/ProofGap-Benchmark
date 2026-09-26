import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology intervalIntegral
open Filter MeasureTheory intervalIntegral

noncomputable abbrev shellSet : Set (ℝ × ℝ × ℝ) :=
  {w | w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 > 1}

noncomputable abbrev weightedKernel (φ : ℝ → ℝ → ℝ → ℝ) (p : ℝ) : ℝ × ℝ × ℝ → ℝ :=
  fun w => φ w.1 w.2.1 w.2.2 / Real.rpow (w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2) p

noncomputable abbrev modelKernel (p : ℝ) : ℝ × ℝ × ℝ → ℝ :=
  fun w => 1 / Real.rpow (w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2) p

noncomputable abbrev volumeIntegralOn (Ω : Set (ℝ × ℝ × ℝ)) (f : ℝ × ℝ × ℝ → ℝ) : ℝ :=
  ∫ w in Ω, f w ∂volume

def ImproperConverges (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ L : ℝ, Tendsto (fun b : ℝ => ∫ r in a..b, f r) atTop (𝓝 L)

def ImproperDivergesToInfinity (f : ℝ → ℝ) (a : ℝ) : Prop :=
  Tendsto (fun b : ℝ => ∫ r in a..b, f r) atTop atTop

theorem proof_gap_exercise_4191_1
    (φ : ℝ → ℝ → ℝ → ℝ) (p m M x y z : ℝ)
    (hmφ : x ^ 2 + y ^ 2 + z ^ 2 > 1 → 0 < m ∧ m ≤ |φ x y z| ∧ |φ x y z| ≤ M)
    (hxyz : x ^ 2 + y ^ 2 + z ^ 2 > 1) :
    m / Real.rpow (x ^ 2 + y ^ 2 + z ^ 2) p ≤ |φ x y z| / Real.rpow (x ^ 2 + y ^ 2 + z ^ 2) p := by
  sorry

theorem proof_gap_exercise_4191_2
    (φ : ℝ → ℝ → ℝ → ℝ) (p m M x y z : ℝ)
    (hmφ : x ^ 2 + y ^ 2 + z ^ 2 > 1 → 0 < m ∧ m ≤ |φ x y z| ∧ |φ x y z| ≤ M)
    (hxyz : x ^ 2 + y ^ 2 + z ^ 2 > 1)
    (hlower : m / Real.rpow (x ^ 2 + y ^ 2 + z ^ 2) p ≤ |φ x y z| / Real.rpow (x ^ 2 + y ^ 2 + z ^ 2) p) :
    |φ x y z| / Real.rpow (x ^ 2 + y ^ 2 + z ^ 2) p ≤ M / Real.rpow (x ^ 2 + y ^ 2 + z ^ 2) p := by
  sorry

theorem proof_gap_exercise_4191_3
    (φ : ℝ → ℝ → ℝ → ℝ) (p m M : ℝ) (Ω : Set (ℝ × ℝ × ℝ))
    (hΩ : Ω = shellSet)
    (hmφ : ∀ x y z, x ^ 2 + y ^ 2 + z ^ 2 > 1 → 0 < m ∧ m ≤ |φ x y z| ∧ |φ x y z| ≤ M) :
    IntegrableOn (weightedKernel φ p) Ω volume ↔ IntegrableOn (modelKernel p) Ω volume := by
  sorry

theorem proof_gap_exercise_4191_4
    (p : ℝ) (Ω : Set (ℝ × ℝ × ℝ)) (hΩ : Ω = shellSet) :
    Tendsto
      (fun R : ℝ =>
        (∫ θ in (0 : ℝ)..(2 * Real.pi), (1 : ℝ)) *
        (∫ ψ in (-(Real.pi / 2))..(Real.pi / 2), Real.cos ψ) *
        (∫ r in (1 : ℝ)..R, 1 / Real.rpow r (2 * p - 2)))
      atTop (𝓝 (volumeIntegralOn Ω (modelKernel p))) := by
  sorry

theorem proof_gap_exercise_4191_5
    (p : ℝ) (Ω : Set (ℝ × ℝ × ℝ)) (hΩ : Ω = shellSet)
    (hspherical : Tendsto
      (fun R : ℝ =>
        (∫ θ in (0 : ℝ)..(2 * Real.pi), (1 : ℝ)) *
        (∫ ψ in (-(Real.pi / 2))..(Real.pi / 2), Real.cos ψ) *
        (∫ r in (1 : ℝ)..R, 1 / Real.rpow r (2 * p - 2)))
      atTop (𝓝 (volumeIntegralOn Ω (modelKernel p)))) :
    Tendsto
      (fun R : ℝ => 4 * Real.pi * (∫ r in (1 : ℝ)..R, 1 / Real.rpow r (2 * p - 2)))
      atTop (𝓝 (volumeIntegralOn Ω (modelKernel p))) := by
  sorry

theorem proof_gap_exercise_4191_6 (p : ℝ) :
    p > (3 / 2 : ℝ) → ImproperConverges (fun r : ℝ => 1 / Real.rpow r (2 * p - 2)) 1 := by
  sorry

theorem proof_gap_exercise_4191_7 (p : ℝ) :
    p ≤ (3 / 2 : ℝ) → ImproperDivergesToInfinity (fun r : ℝ => 1 / Real.rpow r (2 * p - 2)) 1 := by
  sorry

theorem proof_gap_exercise_4191_8
    (φ : ℝ → ℝ → ℝ → ℝ) (p m M : ℝ) (Ω : Set (ℝ × ℝ × ℝ))
    (hΩ : Ω = shellSet)
    (hmφ : ∀ x y z, x ^ 2 + y ^ 2 + z ^ 2 > 1 → 0 < m ∧ m ≤ |φ x y z| ∧ |φ x y z| ≤ M) :
    p ∈ {p : ℝ | p > (3 / 2 : ℝ)} ↔ IntegrableOn (weightedKernel φ p) Ω volume := by
  sorry
