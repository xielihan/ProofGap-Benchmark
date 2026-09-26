import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology ENNReal
open Filter MeasureTheory Set intervalIntegral

/-!
exercise: exercise_4185
Original problem: convergence of the improper double integral over the unit disk.
-/

noncomputable section

variable (p : ℝ) (φ : ℝ × ℝ → ℝ)

def disk4185 : Set (ℝ × ℝ) := {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1}
def openDisk4185 : Set (ℝ × ℝ) := {z | z.1 ^ 2 + z.2 ^ 2 < 1}
def kernel4185 (p : ℝ) (z : ℝ × ℝ) : ℝ := (1 - z.1 ^ 2 - z.2 ^ 2) ^ (-p)
def weighted4185 (p : ℝ) (φ : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ := φ z * kernel4185 p z
def radial4185 (p : ℝ) (r : ℝ) : ℝ := r / ((1 - r) ^ p * (1 + r) ^ p)

theorem proof_gap_exercise_4185_1
    (hcont : ContinuousOn φ (disk4185)) (hbdd : Bornology.IsBounded (φ '' disk4185)) :
    ∃ m M : ℝ, ∀ x y : ℝ, x ^ 2 + y ^ 2 < 1 →
      m / (1 - x ^ 2 - y ^ 2) ^ p ≤ |φ (x, y)| / (1 - x ^ 2 - y ^ 2) ^ p ∧
      |φ (x, y)| / (1 - x ^ 2 - y ^ 2) ^ p ≤ M / (1 - x ^ 2 - y ^ 2) ^ p := by sorry

theorem proof_gap_exercise_4185_2
    (hcomp : ∃ m M : ℝ, ∀ x y : ℝ, x ^ 2 + y ^ 2 < 1 →
      m / (1 - x ^ 2 - y ^ 2) ^ p ≤ |φ (x, y)| / (1 - x ^ 2 - y ^ 2) ^ p ∧
      |φ (x, y)| / (1 - x ^ 2 - y ^ 2) ^ p ≤ M / (1 - x ^ 2 - y ^ 2) ^ p) :
    IntegrableOn (weighted4185 p φ) openDisk4185 volume ↔
      IntegrableOn (kernel4185 p) openDisk4185 volume := by sorry

theorem proof_gap_exercise_4185_3 :
    ∫ z in openDisk4185, kernel4185 p z ∂volume =
      (∫ θ in (0)..(2 * Real.pi), (1 : ℝ)) *
        ∫ r in (0)..(1), r / (1 - r ^ 2) ^ p := by sorry

theorem proof_gap_exercise_4185_4 :
    (∫ θ in (0)..(2 * Real.pi), (1 : ℝ)) * (∫ r in (0)..(1), r / (1 - r ^ 2) ^ p) =
      2 * Real.pi * ∫ r in (0)..(1), radial4185 p r := by sorry

theorem proof_gap_exercise_4185_5 :
    Tendsto (fun r : ℝ => (1 - r) ^ p * radial4185 p r) (𝓝[<] (1 : ℝ)) (𝓝 (2 ^ (-p))) := by sorry

theorem proof_gap_exercise_4185_6 (hp : p < 1) :
    IntegrableOn (radial4185 p) (Ioo (0 : ℝ) 1) volume := by sorry

theorem proof_gap_exercise_4185_7 (hp : p < 1) :
    IntegrableOn (kernel4185 p) openDisk4185 volume := by sorry

theorem proof_gap_exercise_4185_8 (hp : 1 < p) :
    Tendsto (fun a : ℝ => ∫ r in (0)..a, radial4185 p r) (𝓝[<] (1 : ℝ)) atTop := by sorry

theorem proof_gap_exercise_4185_9 (hp : 1 < p) :
    Tendsto (fun a : ℝ => ∫ z in {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 < a}, kernel4185 p z ∂volume)
      (𝓝[<] (1 : ℝ)) atTop := by sorry

theorem proof_gap_exercise_4185_10 (hp : p = 1) :
    (fun a : ℝ => ∫ r in (0)..a, r / (1 - r ^ 2)) =ᶠ[𝓝[<] (1 : ℝ)]
      (fun a : ℝ => (-1 / 2) * Real.log (1 - a ^ 2)) := by sorry

theorem proof_gap_exercise_4185_11 (hp : p = 1) :
    Tendsto (fun a : ℝ => (-1 / 2) * Real.log (1 - a ^ 2)) (𝓝[<] (1 : ℝ)) atTop := by sorry

theorem proof_gap_exercise_4185_12 (hp : p = 1) :
    Tendsto (fun a : ℝ => ∫ z in {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 < a}, kernel4185 p z ∂volume)
      (𝓝[<] (1 : ℝ)) atTop := by sorry

theorem proof_gap_exercise_4185_13
    (hcont : ContinuousOn φ (disk4185)) (hbdd : Bornology.IsBounded (φ '' disk4185)) :
    IntegrableOn (weighted4185 p φ) openDisk4185 volume ↔ p < 1 := by sorry

theorem proof_gap_exercise_4185_14
    (hcont : ContinuousOn φ (disk4185)) (hbdd : Bornology.IsBounded (φ '' disk4185)) :
    p ∈ {q : ℝ | q < 1} ↔ IntegrableOn (weighted4185 p φ) openDisk4185 volume := by sorry
