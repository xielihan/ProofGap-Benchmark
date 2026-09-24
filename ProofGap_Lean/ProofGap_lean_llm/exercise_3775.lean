import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open Filter

noncomputable abbrev improperInt (a : ℝ) (f : ℝ -> ℝ) : ℝ := ∫ x in Set.Ioi a, f x
def AccumulationPointSet (D : Set ℝ) : Set ℝ := {y | ClusterPt y (𝓝ˢ D)}
def IntegrableFuncOn (f : ℝ -> ℝ) (S : Set ℝ) : Prop := MeasureTheory.IntegrableOn f S
def paramLimitAt (f : ℝ -> ℝ -> ℝ) (y0 : ℝ) : ℝ -> ℝ := fun x => f x y0

-- exercise: exercise_3775

theorem proof_gap_exercise_3775_1
  (a y0 : ℝ) (D : Set ℝ) (f : ℝ -> ℝ -> ℝ) (F : ℝ -> ℝ)
  (hy0 : y0 ∈ D) (hacc : y0 ∈ AccumulationPointSet D)
  (hlocal_int : ∀ b y : ℝ, b ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ b > a ∧ y ∈ D -> IntegrableFuncOn (fun x => f x y) (Set.Icc a b))
  (hpoint : ∀ y b x : ℝ, y ∈ (Set.univ : Set ℝ) ∧ b ∈ (Set.univ : Set ℝ) ∧ x ∈ (Set.univ : Set ℝ) ∧ y ∈ D ∧ b > a ∧ x ∈ Set.Icc a b ->
    Tendsto (fun y' : ℝ => f x y') (𝓝 y0) (𝓝 (f x y0)))
  (hdom : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Ici a ∧ y ∈ D -> |f x y| ≤ F x)
  (hF : MeasureTheory.HasFiniteIntegral F (MeasureTheory.volume.restrict (Set.Ici a)))
  : ∀ b : ℝ, b ∈ (Set.univ : Set ℝ) ∧ b > a ->
      Tendsto (fun y : ℝ => ∫ x in a..b, f x y) (𝓝 y0) (𝓝 (∫ x in a..b, f x y0)) := by
  sorry

theorem proof_gap_exercise_3775_2
  (a y0 : ℝ) (D : Set ℝ) (f : ℝ -> ℝ -> ℝ) (F : ℝ -> ℝ)
  (hy0 : y0 ∈ D) (hdom : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Ici a ∧ y ∈ D -> |f x y| ≤ F x)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Ici a -> |f x y0| ≤ F x := by
  sorry

theorem proof_gap_exercise_3775_3
  (a y0 : ℝ) (D : Set ℝ) (f : ℝ -> ℝ -> ℝ) (F : ℝ -> ℝ)
  (hlim_bound : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Ici a -> |f x y0| ≤ F x)
  (hF : MeasureTheory.HasFiniteIntegral F (MeasureTheory.volume.restrict (Set.Ici a)))
  : MeasureTheory.HasFiniteIntegral (fun x => f x y0) (MeasureTheory.volume.restrict (Set.Ici a)) := by
  sorry

theorem proof_gap_exercise_3775_4
  (a y0 : ℝ) (D : Set ℝ) (f : ℝ -> ℝ -> ℝ) (F : ℝ -> ℝ)
  (hF : MeasureTheory.HasFiniteIntegral F (MeasureTheory.volume.restrict (Set.Ici a)))
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ->
      ∃ b : ℝ, b ∈ (Set.univ : Set ℝ) ∧ b > a ∧ improperInt b F < ε / 3 := by
  sorry

theorem proof_gap_exercise_3775_5
  (a y0 : ℝ) (D : Set ℝ) (f : ℝ -> ℝ -> ℝ) (F : ℝ -> ℝ)
  (hfinite_lim : ∀ b : ℝ, b ∈ (Set.univ : Set ℝ) ∧ b > a ->
      Tendsto (fun y : ℝ => ∫ x in a..b, f x y) (𝓝 y0) (𝓝 (∫ x in a..b, f x y0)))
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ->
      ∃ b : ℝ, b ∈ (Set.univ : Set ℝ) ∧ b > a ∧
        ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧
          (∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ y ∈ D ∧ 0 < |y - y0| ∧ |y - y0| < δ ->
            |(∫ x in a..b, f x y) - (∫ x in a..b, f x y0)| < ε / 3) := by
  sorry

theorem proof_gap_exercise_3775_6
  (a y0 : ℝ) (D : Set ℝ) (f : ℝ -> ℝ -> ℝ) (F : ℝ -> ℝ)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ->
      ∃ b : ℝ, b ∈ (Set.univ : Set ℝ) ∧ b > a ∧
        ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧
          (∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ y ∈ D ∧ 0 < |y - y0| ∧ |y - y0| < δ ->
            |improperInt a (fun x => f x y) - improperInt a (fun x => f x y0)| ≤
              |(∫ x in a..b, f x y) - (∫ x in a..b, f x y0)| +
              improperInt b (fun x => |f x y|) + improperInt b (fun x => |f x y0|)) := by
  sorry

theorem proof_gap_exercise_3775_7
  (a y0 : ℝ) (D : Set ℝ) (f : ℝ -> ℝ -> ℝ) (F : ℝ -> ℝ)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ->
      ∃ b : ℝ, b ∈ (Set.univ : Set ℝ) ∧ b > a ∧
        ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧
          (∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ y ∈ D ∧ 0 < |y - y0| ∧ |y - y0| < δ ->
            |improperInt a (fun x => f x y) - improperInt a (fun x => f x y0)| <
              ε / 3 + improperInt b F + improperInt b F) := by
  sorry

theorem proof_gap_exercise_3775_8
  (a y0 : ℝ) (D : Set ℝ) (f : ℝ -> ℝ -> ℝ) (F : ℝ -> ℝ)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ->
      ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧
        (∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ y ∈ D ∧ 0 < |y - y0| ∧ |y - y0| < δ ->
          |improperInt a (fun x => f x y) - improperInt a (fun x => f x y0)| < ε) := by
  sorry

theorem proof_gap_exercise_3775_9
  (a y0 : ℝ) (D : Set ℝ) (f : ℝ -> ℝ -> ℝ) (F : ℝ -> ℝ)
  : Tendsto (fun y : ℝ => improperInt a (fun x => f x y)) (𝓝 y0) (𝓝 (improperInt a (fun x => f x y0))) := by
  sorry

theorem proof_gap_exercise_3775_10
  (a y0 : ℝ) (D : Set ℝ) (f : ℝ -> ℝ -> ℝ) (F : ℝ -> ℝ)
  : improperInt a (fun x => f x y0) =
      improperInt a (paramLimitAt f y0) := by
  sorry

theorem proof_gap_exercise_3775_11
  (a y0 : ℝ) (D : Set ℝ) (f : ℝ -> ℝ -> ℝ) (F : ℝ -> ℝ)
  (hleft : Tendsto (fun y : ℝ => improperInt a (fun x => f x y)) (𝓝 y0) (𝓝 (improperInt a (fun x => f x y0))))
  (hright : improperInt a (fun x => f x y0) =
      improperInt a (paramLimitAt f y0))
  : Tendsto (fun y : ℝ => improperInt a (fun x => f x y)) (𝓝 y0)
      (𝓝 (improperInt a (paramLimitAt f y0))) := by
  sorry

theorem proof_gap_exercise_3775_12
  (a y0 : ℝ) (D : Set ℝ) (f : ℝ -> ℝ -> ℝ) (F : ℝ -> ℝ)
  (hfinal : Tendsto (fun y : ℝ => improperInt a (fun x => f x y)) (𝓝 y0)
      (𝓝 (improperInt a (paramLimitAt f y0))))
  : Tendsto (fun y : ℝ => improperInt a (fun x => f x y)) (𝓝 y0)
      (𝓝 (improperInt a (paramLimitAt f y0))) := by
  sorry
