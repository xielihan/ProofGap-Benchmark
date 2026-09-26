import Mathlib

attribute [local instance] Classical.propDecidable
set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

def DefinedOnOpenClosed01 (f : ℝ -> ℝ) : Prop :=
  MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))
def UnboundedNearZeroOn01 (f : ℝ -> ℝ) : Prop := ¬ Bornology.IsBounded (f '' Set.Ioc (0 : ℝ) 1)
def IntegralExists01 (f : ℝ -> ℝ) : Prop := IntervalIntegrable f MeasureTheory.volume (0 : ℝ) 1
def TendsToPosInfAtZeroRight (f : ℝ -> ℝ) : Prop := Tendsto f (𝓝[>] (0 : ℝ)) atTop
def RiemannAverageLimit01 (f : ℝ -> ℝ) : Prop :=
  Tendsto (fun n : ℕ =>
    ((1 : ℝ) / n) * Finset.sum (Finset.Icc 1 n) (fun k => f ((k : ℝ) / n)))
    atTop (𝓝 (∫ x in (0 : ℝ)..1, f x))

-- exercise: exercise_2388

-- Source: proofgap/exercise_2388/1.txt
theorem proof_gap_exercise_2388_1
  (f : ℝ -> ℝ)
  (hdef : DefinedOnOpenClosed01 f)
  (hmono : AntitoneOn f (Set.Ioc (0 : ℝ) 1) ∨ MonotoneOn f (Set.Ioc (0 : ℝ) 1))
  (hunbdd : UnboundedNearZeroOn01 f)
  (hint : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 -> IntegralExists01 f)
  : AntitoneOn f (Set.Ioc (0 : ℝ) 1) -> TendsToPosInfAtZeroRight f := by
  sorry

-- Source: proofgap/exercise_2388/2.txt
theorem proof_gap_exercise_2388_2
  (f : ℝ -> ℝ)
  (h1 : AntitoneOn f (Set.Ioc (0 : ℝ) 1) -> TendsToPosInfAtZeroRight f)
  : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 ->
      AntitoneOn f (Set.Ioc (0 : ℝ) 1) ->
      (∀ y : ℝ, 0 < y -> y ≤ 1 -> f y ≥ 0) ->
      ∀ n : ℕ, 0 < n ->
        (∫ u in (0 : ℝ)..1, f u) =
          Finset.sum (Finset.Ico 0 n) (fun k =>
            ∫ u in ((k : ℝ) / n)..(((k + 1 : ℕ) : ℝ) / n), f u) := by
  sorry

-- Source: proofgap/exercise_2388/3.txt
theorem proof_gap_exercise_2388_3
  (f : ℝ -> ℝ)
  : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 ->
      AntitoneOn f (Set.Ioc (0 : ℝ) 1) ->
      (∀ y : ℝ, 0 < y -> y ≤ 1 -> f y ≥ 0) ->
      ∀ n : ℕ, 0 < n ->
        (∫ u in (0 : ℝ)..1, f u) <
          (∫ u in (0 : ℝ)..((1 : ℝ) / n), f u) +
          Finset.sum (Finset.Icc 1 (n - 1)) (fun k =>
            f ((k : ℝ) / n) * ((1 : ℝ) / n)) := by
  sorry

-- Source: proofgap/exercise_2388/4.txt
theorem proof_gap_exercise_2388_4
  (f : ℝ -> ℝ)
  : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 ->
      AntitoneOn f (Set.Ioc (0 : ℝ) 1) ->
      (∀ y : ℝ, 0 < y -> y ≤ 1 -> f y ≥ 0) ->
      ∀ n : ℕ, 0 < n ->
        (∫ u in (0 : ℝ)..((1 : ℝ) / n), f u) +
          Finset.sum (Finset.Icc 1 (n - 1)) (fun k =>
            f ((k : ℝ) / n) * ((1 : ℝ) / n)) <
        (∫ u in (0 : ℝ)..((1 : ℝ) / n), f u) +
          Finset.sum (Finset.Icc 1 n) (fun k =>
            f ((k : ℝ) / n) * ((1 : ℝ) / n)) := by
  sorry

-- Source: proofgap/exercise_2388/5.txt
theorem proof_gap_exercise_2388_5
  (f : ℝ -> ℝ)
  : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 ->
      AntitoneOn f (Set.Ioc (0 : ℝ) 1) ->
      (∀ y : ℝ, 0 < y -> y ≤ 1 -> f y ≥ 0) ->
      ∀ n : ℕ, 0 < n ->
        (∫ u in (0 : ℝ)..1, f u) >
          Finset.sum (Finset.Icc 1 n) (fun k =>
            f ((k : ℝ) / n) * ((1 : ℝ) / n)) := by
  sorry

-- Source: proofgap/exercise_2388/6.txt
theorem proof_gap_exercise_2388_6
  (f : ℝ -> ℝ)
  : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 ->
      AntitoneOn f (Set.Ioc (0 : ℝ) 1) ->
      (∀ y : ℝ, 0 < y -> y ≤ 1 -> f y ≥ 0) ->
      ∀ n : ℕ, 0 < n ->
        0 < (∫ u in (0 : ℝ)..1, f u) -
          ((1 : ℝ) / n) * Finset.sum (Finset.Icc 1 n) (fun k => f ((k : ℝ) / n)) := by
  sorry

-- Source: proofgap/exercise_2388/7.txt
theorem proof_gap_exercise_2388_7
  (f : ℝ -> ℝ)
  : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 ->
      AntitoneOn f (Set.Ioc (0 : ℝ) 1) ->
      (∀ y : ℝ, 0 < y -> y ≤ 1 -> f y ≥ 0) ->
      ∀ n : ℕ, 0 < n ->
        (∫ u in (0 : ℝ)..1, f u) -
          ((1 : ℝ) / n) * Finset.sum (Finset.Icc 1 n) (fun k => f ((k : ℝ) / n)) <
        ∫ u in (0 : ℝ)..((1 : ℝ) / n), f u := by
  sorry

-- Source: proofgap/exercise_2388/8.txt
theorem proof_gap_exercise_2388_8
  (f : ℝ -> ℝ)
  : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 ->
      AntitoneOn f (Set.Ioc (0 : ℝ) 1) ->
      (∀ y : ℝ, 0 < y -> y ≤ 1 -> f y ≥ 0) ->
      Tendsto (fun n : ℕ => ∫ u in (0 : ℝ)..((1 : ℝ) / n), f u) atTop (𝓝 0) := by
  sorry

-- Source: proofgap/exercise_2388/9.txt
theorem proof_gap_exercise_2388_9
  (f : ℝ -> ℝ)
  : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 ->
      AntitoneOn f (Set.Ioc (0 : ℝ) 1) ->
      (∀ y : ℝ, 0 < y -> y ≤ 1 -> f y ≥ 0) ->
      RiemannAverageLimit01 f := by
  sorry

-- Source: proofgap/exercise_2388/10.txt
theorem proof_gap_exercise_2388_10
  (f phi : ℝ -> ℝ)
  (hphi : phi = fun x => f x - f 1)
  : AntitoneOn f (Set.Ioc (0 : ℝ) 1) ->
      ¬ (∀ x : ℝ, 0 < x -> x ≤ 1 -> f x ≥ 0) ->
      ∀ x : ℝ, 0 < x -> x ≤ 1 -> phi x ≥ 0 := by
  sorry

-- Source: proofgap/exercise_2388/11.txt
theorem proof_gap_exercise_2388_11
  (f phi : ℝ -> ℝ)
  (hphi : phi = fun x => f x - f 1)
  : AntitoneOn f (Set.Ioc (0 : ℝ) 1) ->
      ¬ (∀ x : ℝ, 0 < x -> x ≤ 1 -> f x ≥ 0) ->
      AntitoneOn phi (Set.Ioc (0 : ℝ) 1) := by
  sorry

-- Source: proofgap/exercise_2388/12.txt
theorem proof_gap_exercise_2388_12
  (f phi : ℝ -> ℝ)
  (hphi : phi = fun x => f x - f 1)
  : AntitoneOn f (Set.Ioc (0 : ℝ) 1) ->
      ¬ (∀ x : ℝ, 0 < x -> x ≤ 1 -> f x ≥ 0) ->
      TendsToPosInfAtZeroRight phi := by
  sorry

-- Source: proofgap/exercise_2388/13.txt
theorem proof_gap_exercise_2388_13
  (f phi : ℝ -> ℝ)
  : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 ->
      AntitoneOn f (Set.Ioc (0 : ℝ) 1) ->
      ¬ (∀ y : ℝ, 0 < y -> y ≤ 1 -> f y ≥ 0) ->
      RiemannAverageLimit01 phi := by
  sorry

-- Source: proofgap/exercise_2388/14.txt
theorem proof_gap_exercise_2388_14
  (f : ℝ -> ℝ)
  : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 ->
      AntitoneOn f (Set.Ioc (0 : ℝ) 1) ->
      ¬ (∀ y : ℝ, 0 < y -> y ≤ 1 -> f y ≥ 0) ->
      Tendsto (fun n : ℕ => ((1 : ℝ) / n) *
        Finset.sum (Finset.Icc 1 n) (fun k => f ((k : ℝ) / n) - f 1))
        atTop (𝓝 (∫ u in (0 : ℝ)..1, (f u - f 1))) := by
  sorry

-- Source: proofgap/exercise_2388/15.txt
theorem proof_gap_exercise_2388_15
  (f : ℝ -> ℝ)
  : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 ->
      AntitoneOn f (Set.Ioc (0 : ℝ) 1) ->
      ¬ (∀ y : ℝ, 0 < y -> y ≤ 1 -> f y ≥ 0) ->
      RiemannAverageLimit01 f := by
  sorry

-- Source: proofgap/exercise_2388/16.txt
theorem proof_gap_exercise_2388_16
  (f : ℝ -> ℝ)
  (hposcase : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 ->
      AntitoneOn f (Set.Ioc (0 : ℝ) 1) ->
      (∀ y : ℝ, 0 < y -> y ≤ 1 -> f y ≥ 0) -> RiemannAverageLimit01 f)
  (hshiftcase : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 ->
      AntitoneOn f (Set.Ioc (0 : ℝ) 1) ->
      ¬ (∀ y : ℝ, 0 < y -> y ≤ 1 -> f y ≥ 0) -> RiemannAverageLimit01 f)
  : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 ->
      AntitoneOn f (Set.Ioc (0 : ℝ) 1) -> RiemannAverageLimit01 f := by
  sorry

-- Source: proofgap/exercise_2388/17.txt
theorem proof_gap_exercise_2388_17
  (f g : ℝ -> ℝ)
  (hg : g = fun x => - f x)
  : MonotoneOn f (Set.Ioc (0 : ℝ) 1) -> AntitoneOn g (Set.Ioc (0 : ℝ) 1) := by
  sorry

-- Source: proofgap/exercise_2388/18.txt
theorem proof_gap_exercise_2388_18
  (f g : ℝ -> ℝ)
  (hg : g = fun x => - f x)
  (hint : IntegralExists01 f)
  : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 ->
      MonotoneOn f (Set.Ioc (0 : ℝ) 1) -> IntegralExists01 g := by
  sorry

-- Source: proofgap/exercise_2388/19.txt
theorem proof_gap_exercise_2388_19
  (f g : ℝ -> ℝ)
  (hg : g = fun x => - f x)
  : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 ->
      MonotoneOn f (Set.Ioc (0 : ℝ) 1) -> RiemannAverageLimit01 g := by
  sorry

-- Source: proofgap/exercise_2388/20.txt
theorem proof_gap_exercise_2388_20
  (f g : ℝ -> ℝ)
  (hg : g = fun x => - f x)
  (h19 : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 ->
      MonotoneOn f (Set.Ioc (0 : ℝ) 1) -> RiemannAverageLimit01 g)
  : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 ->
      MonotoneOn f (Set.Ioc (0 : ℝ) 1) -> RiemannAverageLimit01 f := by
  sorry

-- Source: proofgap/exercise_2388/21.txt
theorem proof_gap_exercise_2388_21
  (f : ℝ -> ℝ)
  (hdec : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 ->
      AntitoneOn f (Set.Ioc (0 : ℝ) 1) -> RiemannAverageLimit01 f)
  (hinc : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 ->
      MonotoneOn f (Set.Ioc (0 : ℝ) 1) -> RiemannAverageLimit01 f)
  (hmono : AntitoneOn f (Set.Ioc (0 : ℝ) 1) ∨ MonotoneOn f (Set.Ioc (0 : ℝ) 1))
  : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 -> RiemannAverageLimit01 f := by
  sorry

-- Source: proofgap/exercise_2388/22.txt
theorem proof_gap_exercise_2388_22
  (f : ℝ -> ℝ)
  (hdef : DefinedOnOpenClosed01 f)
  (hmono : AntitoneOn f (Set.Ioc (0 : ℝ) 1) ∨ MonotoneOn f (Set.Ioc (0 : ℝ) 1))
  (hunbdd : UnboundedNearZeroOn01 f)
  (hint : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 -> IntegralExists01 f)
  (h21 : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 -> RiemannAverageLimit01 f)
  : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 -> RiemannAverageLimit01 f := by
  sorry
