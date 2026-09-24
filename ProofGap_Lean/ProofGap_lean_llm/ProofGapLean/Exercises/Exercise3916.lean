import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod

namespace ProofGap.Exercise3916

noncomputable section

open MeasureTheory
open scoped Interval

def triangle : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ p.1}

def triangleIntegral (f : ℝ → ℝ → ℝ) : ℝ :=
  ∫ p in triangle, f p.1 p.2

private theorem measurableSet_triangle : MeasurableSet triangle := by
  unfold triangle
  change MeasurableSet
    ({p : ℝ × ℝ | (0 : ℝ) ≤ p.1} ∩
      ({p : ℝ × ℝ | p.1 ≤ 1} ∩
        ({p : ℝ × ℝ | (0 : ℝ) ≤ p.2} ∩
          {p : ℝ × ℝ | p.2 ≤ p.1})))
  exact
    (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_fst measurable_const).inter
        ((measurableSet_le measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd measurable_fst)))

private theorem ae_ne_real (a : ℝ) :
    ∀ᵐ x : ℝ ∂volume, x ≠ a := by
  refine ae_iff.2 ?_
  simp

private theorem triangle_left_formula (f : ℝ → ℝ → ℝ) :
    (∫ x : ℝ, ∫ y : ℝ,
      triangle.indicator (fun p : ℝ × ℝ => f p.1 p.2) (x, y)) =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..x, f x y := by
  rw [intervalIntegral.integral_of_le zero_le_one,
    ← MeasureTheory.integral_indicator measurableSet_Ioc]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [ae_ne_real (0 : ℝ)] with x hx
  by_cases h0x : 0 ≤ x
  · have hxpos : 0 < x := lt_of_le_of_ne h0x (Ne.symm hx)
    by_cases hx1 : x ≤ 1
    · have hmem : x ∈ Set.Ioc (0 : ℝ) 1 := ⟨hxpos, hx1⟩
      rw [Set.indicator_of_mem hmem,
        intervalIntegral.integral_of_le h0x,
        ← MeasureTheory.integral_indicator measurableSet_Ioc]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [ae_ne_real (0 : ℝ)] with y hy
      have hmem_iff :
          (x, y) ∈ triangle ↔ y ∈ Set.Ioc (0 : ℝ) x := by
        constructor
        · intro h
          exact
            ⟨lt_of_le_of_ne h.2.2.1 (Ne.symm hy), h.2.2.2⟩
        · intro h
          exact ⟨h0x, hx1, h.1.le, h.2⟩
      by_cases htri : (x, y) ∈ triangle
      · have hioc : y ∈ Set.Ioc (0 : ℝ) x := hmem_iff.mp htri
        simp [htri, hioc]
      · have hioc : y ∉ Set.Ioc (0 : ℝ) x :=
          fun h => htri (hmem_iff.mpr h)
        simp [htri, hioc]
    · have hmem : x ∉ Set.Ioc (0 : ℝ) 1 := fun h => hx1 h.2
      have htri (y : ℝ) : (x, y) ∉ triangle := by
        intro h
        exact hx1 h.2.1
      have hfun :
          (fun y : ℝ =>
            triangle.indicator (fun p : ℝ × ℝ => f p.1 p.2) (x, y)) = 0 := by
        funext y
        simp [htri y]
      rw [hfun]
      simp [hmem]
  · have hmem : x ∉ Set.Ioc (0 : ℝ) 1 := fun h => h0x h.1.le
    have htri (y : ℝ) : (x, y) ∉ triangle := by
      intro h
      exact h0x h.1
    have hfun :
        (fun y : ℝ =>
          triangle.indicator (fun p : ℝ × ℝ => f p.1 p.2) (x, y)) = 0 := by
      funext y
      simp [htri y]
    rw [hfun]
    simp [hmem]

private theorem triangle_right_formula (f : ℝ → ℝ → ℝ) :
    (∫ y : ℝ, ∫ x : ℝ,
      triangle.indicator (fun p : ℝ × ℝ => f p.1 p.2) (x, y)) =
      ∫ y in (0 : ℝ)..1, ∫ x in y..1, f x y := by
  rw [intervalIntegral.integral_of_le zero_le_one,
    ← MeasureTheory.integral_indicator measurableSet_Ioc]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [ae_ne_real (0 : ℝ)] with y hy
  by_cases hy0 : 0 ≤ y
  · have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy)
    by_cases hy1 : y ≤ 1
    · have hmem : y ∈ Set.Ioc (0 : ℝ) 1 := ⟨hypos, hy1⟩
      rw [Set.indicator_of_mem hmem,
        intervalIntegral.integral_of_le hy1,
        ← MeasureTheory.integral_indicator measurableSet_Ioc]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [ae_ne_real y] with x hx
      have hmem_iff :
          (x, y) ∈ triangle ↔ x ∈ Set.Ioc y 1 := by
        constructor
        · intro h
          exact
            ⟨lt_of_le_of_ne h.2.2.2 (Ne.symm hx), h.2.1⟩
        · intro h
          exact ⟨hy0.trans h.1.le, h.2, hy0, h.1.le⟩
      by_cases htri : (x, y) ∈ triangle
      · have hioc : x ∈ Set.Ioc y 1 := hmem_iff.mp htri
        simp [htri, hioc]
      · have hioc : x ∉ Set.Ioc y 1 :=
          fun h => htri (hmem_iff.mpr h)
        simp [htri, hioc]
    · have hmem : y ∉ Set.Ioc (0 : ℝ) 1 := fun h => hy1 h.2
      have htri (x : ℝ) : (x, y) ∉ triangle := by
        intro h
        exact hy1 (h.2.2.2.trans h.2.1)
      have hfun :
          (fun x : ℝ =>
            triangle.indicator (fun p : ℝ × ℝ => f p.1 p.2) (x, y)) = 0 := by
        funext x
        simp [htri x]
      rw [hfun]
      simp [hmem]
  · have hmem : y ∉ Set.Ioc (0 : ℝ) 1 := fun h => hy0 h.1.le
    have htri (x : ℝ) : (x, y) ∉ triangle := by
      intro h
      exact hy0 h.2.2.1
    have hfun :
        (fun x : ℝ =>
          triangle.indicator (fun p : ℝ × ℝ => f p.1 p.2) (x, y)) = 0 := by
      funext x
      simp [htri x]
    rw [hfun]
    simp [hmem]

theorem gap1 (f : ℝ → ℝ → ℝ)
    (hf : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) triangle) :
    triangleIntegral f =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..x, f x y := by
  have hfi :
      Integrable
        (triangle.indicator (fun p : ℝ × ℝ => f p.1 p.2)) :=
    (MeasureTheory.integrable_indicator_iff measurableSet_triangle).2 hf
  rw [triangleIntegral,
    ← MeasureTheory.integral_indicator measurableSet_triangle]
  calc
    (∫ p : ℝ × ℝ,
        triangle.indicator (fun p : ℝ × ℝ => f p.1 p.2) p) =
        ∫ x : ℝ, ∫ y : ℝ,
          triangle.indicator (fun p : ℝ × ℝ => f p.1 p.2) (x, y) :=
      MeasureTheory.integral_prod
        (f := triangle.indicator (fun p : ℝ × ℝ => f p.1 p.2)) hfi
    _ = ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..x, f x y :=
      triangle_left_formula f

theorem gap2 (f : ℝ → ℝ → ℝ)
    (hf : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) triangle) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..x, f x y) =
      ∫ y in (0 : ℝ)..1, ∫ x in y..1, f x y := by
  have hfi :
      Integrable
        (triangle.indicator (fun p : ℝ × ℝ => f p.1 p.2)) :=
    (MeasureTheory.integrable_indicator_iff measurableSet_triangle).2 hf
  calc
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..x, f x y) =
        ∫ x : ℝ, ∫ y : ℝ,
          triangle.indicator (fun p : ℝ × ℝ => f p.1 p.2) (x, y) :=
      (triangle_left_formula f).symm
    _ = ∫ p : ℝ × ℝ,
          triangle.indicator (fun p : ℝ × ℝ => f p.1 p.2) p :=
      (MeasureTheory.integral_prod
        (f := triangle.indicator (fun p : ℝ × ℝ => f p.1 p.2)) hfi).symm
    _ = ∫ y : ℝ, ∫ x : ℝ,
          triangle.indicator (fun p : ℝ × ℝ => f p.1 p.2) (x, y) :=
      MeasureTheory.integral_prod_symm
        (f := triangle.indicator (fun p : ℝ × ℝ => f p.1 p.2)) hfi
    _ = ∫ y in (0 : ℝ)..1, ∫ x in y..1, f x y :=
      triangle_right_formula f

theorem gap3 (f : ℝ → ℝ → ℝ)
    (hf : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) triangle) :
    triangleIntegral f =
      ∫ y in (0 : ℝ)..1, ∫ x in y..1, f x y := by
  exact (gap1 f hf).trans (gap2 f hf)

end

end ProofGap.Exercise3916
