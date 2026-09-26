import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology intervalIntegral
open Filter MeasureTheory intervalIntegral

noncomputable abbrev octant4193 (p q r : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {w | 0 ≤ w.1 ∧ 0 ≤ w.2.1 ∧ 0 ≤ w.2.2 ∧ w.1 + w.2.1 + w.2.2 > 1}

noncomputable abbrev Ω1_4193 (p q r : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {w | 0 ≤ w.1 ∧ 0 ≤ w.2.1 ∧ 0 ≤ w.2.2 ∧ w.1 + w.2.1 + w.2.2 > 1 ∧ Real.rpow w.1 p + Real.rpow w.2.1 q + Real.rpow w.2.2 r ≤ 3}

noncomputable abbrev Ω2_4193 (p q r : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {w | 0 ≤ w.1 ∧ 0 ≤ w.2.1 ∧ 0 ≤ w.2.2 ∧ w.1 + w.2.1 + w.2.2 > 1 ∧ Real.rpow w.1 p + Real.rpow w.2.1 q + Real.rpow w.2.2 r > 3}

noncomputable abbrev Ω3_4193 (p q r : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {w | 0 ≤ w.1 ∧ 0 ≤ w.2.1 ∧ 0 ≤ w.2.2 ∧ Real.rpow w.1 p + Real.rpow w.2.1 q + Real.rpow w.2.2 r > 3}

noncomputable abbrev whole4193 : Set (ℝ × ℝ × ℝ) :=
  {w | |w.1| + |w.2.1| + |w.2.2| > 1}

noncomputable abbrev kernel4193 (p q r : ℝ) : ℝ × ℝ × ℝ → ℝ :=
  fun w => 1 / (Real.rpow |w.1| p + Real.rpow |w.2.1| q + Real.rpow |w.2.2| r)

noncomputable abbrev positiveKernel4193 (p q r : ℝ) : ℝ × ℝ × ℝ → ℝ :=
  fun w => 1 / (Real.rpow w.1 p + Real.rpow w.2.1 q + Real.rpow w.2.2 r)

def ImproperConverges (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ L : ℝ, Tendsto (fun b : ℝ => ∫ R in a..b, f R) atTop (𝓝 L)

def ImproperDivergesToInfinity (f : ℝ → ℝ) (a : ℝ) : Prop :=
  Tendsto (fun b : ℝ => ∫ R in a..b, f R) atTop atTop

theorem proof_gap_exercise_4193_1 (p q r : ℝ) :
    (∫ w in whole4193, kernel4193 p q r w ∂volume) =
      8 * (∫ w in octant4193 p q r, positiveKernel4193 p q r w ∂volume) := by
  sorry

theorem proof_gap_exercise_4193_2 (p q r : ℝ) :
    (∫ w in octant4193 p q r, positiveKernel4193 p q r w ∂volume) =
      (∫ w in Ω1_4193 p q r, positiveKernel4193 p q r w ∂volume) +
      (∫ w in Ω2_4193 p q r, positiveKernel4193 p q r w ∂volume) := by
  sorry

theorem proof_gap_exercise_4193_3 (p q r : ℝ) :
    Ω2_4193 p q r = Ω3_4193 p q r := by
  sorry

theorem proof_gap_exercise_4193_4 (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    IntegrableOn (positiveKernel4193 p q r) (Ω1_4193 p q r) volume := by
  sorry

theorem proof_gap_exercise_4193_5 (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    IntegrableOn (kernel4193 p q r) whole4193 volume ↔ IntegrableOn (positiveKernel4193 p q r) (Ω3_4193 p q r) volume := by
  sorry

theorem proof_gap_exercise_4193_6 (p q r R φ ψ x : ℝ) (hR : 0 < R) :
    x = Real.rpow R (2 / p) * Real.rpow (Real.cos φ) (2 / p) * Real.rpow (Real.cos ψ) (2 / p) := by
  sorry

theorem proof_gap_exercise_4193_7 (p q r R φ ψ y : ℝ) (hR : 0 < R) :
    y = Real.rpow R (2 / q) * Real.rpow (Real.sin φ) (2 / q) * Real.rpow (Real.cos ψ) (2 / q) := by
  sorry

theorem proof_gap_exercise_4193_8 (p q r R ψ z : ℝ) (hR : 0 < R) :
    z = Real.rpow R (2 / r) * Real.rpow (Real.sin ψ) (2 / r) := by
  sorry

theorem proof_gap_exercise_4193_9 (p q r : ℝ) (B : ℝ → ℝ → ℝ) :
    Tendsto
      (fun b : ℝ =>
        (2 / (p * q * r)) * B (1 / r) (1 / p + 1 / q) * B (1 / q) (1 / p) *
          (∫ R in Real.sqrt 3..b, Real.rpow R (2 / p + 2 / q + 2 / r - 3)))
      atTop (𝓝 (∫ w in Ω3_4193 p q r, positiveKernel4193 p q r w ∂volume)) := by
  sorry

theorem proof_gap_exercise_4193_10 (p q r : ℝ) :
    2 / p + 2 / q + 2 / r - 3 < -1 ↔ 1 / p + 1 / q + 1 / r < 1 := by
  sorry

theorem proof_gap_exercise_4193_11 (p q r : ℝ) :
    1 / p + 1 / q + 1 / r < 1 →
      ImproperConverges (fun R : ℝ => Real.rpow R (2 / p + 2 / q + 2 / r - 3)) (Real.sqrt 3) := by
  sorry

theorem proof_gap_exercise_4193_12 (p q r : ℝ) :
    1 / p + 1 / q + 1 / r ≥ 1 →
      ImproperDivergesToInfinity (fun R : ℝ => Real.rpow R (2 / p + 2 / q + 2 / r - 3)) (Real.sqrt 3) := by
  sorry

theorem proof_gap_exercise_4193_13 (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    (p, q, r) ∈ {t : ℝ × ℝ × ℝ | 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧ 1 / t.1 + 1 / t.2.1 + 1 / t.2.2 < 1} ↔
      IntegrableOn (kernel4193 p q r) whole4193 volume := by
  sorry
