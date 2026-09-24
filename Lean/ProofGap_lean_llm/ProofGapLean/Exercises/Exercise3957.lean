import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise3957

noncomputable section

open MeasureTheory
open scoped Interval

def sourceRegion (a b α β : ℝ) : Set (ℝ × ℝ) :=
  {p | a ≤ p.1 ∧ p.1 ≤ b ∧ α * p.1 ≤ p.2 ∧ p.2 ≤ β * p.1}

def parameterRegion (a b α β : ℝ) : Set (ℝ × ℝ) :=
  Set.Icc a b ×ˢ Set.Icc α β

def coordinateMap (u v : ℝ) : ℝ × ℝ :=
  (u, u * v)

def jacobianDet (u v : ℝ) : ℝ :=
  1 * u - 0 * v

theorem gap1 (a b α β : ℝ) :
    sourceRegion a b α β =
      {p | a ≤ p.1 ∧ p.1 ≤ b ∧
        α * p.1 ≤ p.2 ∧ p.2 ≤ β * p.1} := by
  rfl

theorem gap2 (a b α β : ℝ) :
    parameterRegion a b α β =
      {p | a ≤ p.1 ∧ p.1 ≤ b ∧ α ≤ p.2 ∧ p.2 ≤ β} := by
  ext p
  change
    ((a ≤ p.1 ∧ p.1 ≤ b) ∧ (α ≤ p.2 ∧ p.2 ≤ β)) ↔
      (a ≤ p.1 ∧ p.1 ≤ b ∧ α ≤ p.2 ∧ p.2 ≤ β)
  constructor
  · rintro ⟨⟨ha, hb⟩, hα, hβ⟩
    exact ⟨ha, hb, hα, hβ⟩
  · rintro ⟨ha, hb, hα, hβ⟩
    exact ⟨⟨ha, hb⟩, hα, hβ⟩

theorem gap3 (u v : ℝ) :
    jacobianDet u v = 1 * u - 0 * v := by
  rfl

theorem gap4 (u v : ℝ) :
    jacobianDet u v = u := by
  simp [jacobianDet]

theorem gap5 (a b α β u v : ℝ) (ha : 0 < a)
    (huv : (u, v) ∈ parameterRegion a b α β) :
    0 < u := by
  change (u ∈ Set.Icc a b) ∧ (v ∈ Set.Icc α β) at huv
  exact lt_of_lt_of_le ha huv.1.1

theorem gap6 (a b α β u v : ℝ) (ha : 0 < a)
    (huv : (u, v) ∈ parameterRegion a b α β) :
    0 < jacobianDet u v := by
  simpa [jacobianDet] using
    (gap5 a b α β u v ha huv)

theorem gap7 (a b α β : ℝ) (f : ℝ → ℝ → ℝ)
    (ha : 0 < a) (hab : a < b) (hαβ : α < β)
    (hf : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2)
      (sourceRegion a b α β)) :
    (∫ x in a..b, ∫ y in α * x..β * x, f x y) =
      ∫ u in a..b, ∫ v in α..β, u * f u (u * v) := by
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le hab.le] at hu
  have hu0 : u ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hu.1)
  have hscale :
      (∫ v in α..β, f u (u * v)) =
        u⁻¹ * (∫ y in α * u..β * u, f u y) := by
    simpa only [mul_comm u α, mul_comm u β] using
      (intervalIntegral.integral_comp_mul_left
        (f := fun y : ℝ => f u y) (a := α) (b := β) hu0)
  calc
    (∫ y in α * u..β * u, f u y) =
        (u * u⁻¹) * (∫ y in α * u..β * u, f u y) := by
          simp [hu0]
    _ = u * (u⁻¹ * (∫ y in α * u..β * u, f u y)) := by
          rw [mul_assoc]
    _ = u * (∫ v in α..β, f u (u * v)) := by
          rw [← hscale]
    _ = ∫ v in α..β, u * f u (u * v) := by
          rw [intervalIntegral.integral_const_mul]

end

end ProofGap.Exercise3957
