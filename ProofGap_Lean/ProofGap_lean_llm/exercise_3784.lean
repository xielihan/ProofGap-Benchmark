import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable abbrev DefInt01 (g : ℝ -> ℝ) : ℝ := ∫ x in (0 : ℝ)..(1 : ℝ), g x
noncomputable abbrev FunDeri (g : ℝ -> ℝ) (_dir order : ℕ) (a : ℝ) : ℝ := iteratedDeriv order g a
def ex3784_uniformDerivativeIntegralOn (G : ℝ -> ℝ) (s : Set ℝ) (F : ℝ -> ℝ) : Prop :=
  TendstoUniformlyOn (fun _ : ℕ => G) F atTop s

-- exercise: exercise_3784

theorem proof_gap_exercise_3784_1
    (I n : ℝ) (m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hbase : ∀ n : ℝ, 0 < n -> DefInt01 (fun x => Real.rpow x (n - 1)) = 1 /. n)
    (hI : I = DefInt01 (fun x => Real.rpow x (n - 1) * (Real.log x) ^ m)) :
    ∀ x : ℝ, 0 < x -> x ≤ 1 ->
      FunDeri (fun n => Real.rpow x (n - 1)) 1 1 n = Real.rpow x (n - 1) * Real.log x := by
  sorry

theorem proof_gap_exercise_3784_2
    (I n : ℝ) (m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ∀ n0 : ℝ, 0 < n0 -> ∀ x : ℝ, 0 < x -> x ≤ 1 -> ∀ n' : ℝ, n0 ≤ n' ->
      |Real.rpow x (n' - 1) * Real.log x| ≤ -Real.rpow x (n0 - 1) * Real.log x := by
  sorry

theorem proof_gap_exercise_3784_3
    (I n : ℝ) (m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ∀ n0 : ℝ, 0 < n0 ->
      MeasureTheory.IntegrableOn (fun x => Real.rpow x (n0 - 1) * Real.log x) (Set.Ioc (0 : ℝ) 1) := by
  sorry

theorem proof_gap_exercise_3784_4
    (I n : ℝ) (m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ∀ n0 : ℝ, 0 < n0 ->
      ex3784_uniformDerivativeIntegralOn
        (fun n => DefInt01 (fun x => Real.rpow x (n - 1) * Real.log x))
        (Set.Ici n0)
        (fun n => DefInt01 (fun x => Real.rpow x (n - 1) * Real.log x)) := by
  sorry

theorem proof_gap_exercise_3784_5
    (I n : ℝ) (m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ∀ n0 : ℝ, 0 < n0 ->
      FunDeri (fun n => DefInt01 (fun x => Real.rpow x (n - 1))) 1 1 n =
        DefInt01 (fun x => FunDeri (fun n => Real.rpow x (n - 1)) 1 1 n) := by
  sorry

theorem proof_gap_exercise_3784_6
    (I n : ℝ) (m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ∀ n0 : ℝ, 0 < n0 ->
      DefInt01 (fun x => FunDeri (fun n => Real.rpow x (n - 1)) 1 1 n) =
        DefInt01 (fun x => Real.rpow x (n - 1) * Real.log x) := by
  sorry

theorem proof_gap_exercise_3784_7
    (I n : ℝ) (m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ∀ n0 : ℝ, 0 < n0 ->
      FunDeri (fun n => DefInt01 (fun x => Real.rpow x (n - 1))) 1 1 n =
        DefInt01 (fun x => Real.rpow x (n - 1) * Real.log x) := by
  sorry

theorem proof_gap_exercise_3784_8
    (I n : ℝ) (m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ∀ k : ℕ, 0 < k ->
      FunDeri (fun n => DefInt01 (fun x => Real.rpow x (n - 1))) 1 k n =
        DefInt01 (fun x => Real.rpow x (n - 1) * (Real.log x) ^ k) := by
  sorry

theorem proof_gap_exercise_3784_9
    (I n : ℝ) (m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    FunDeri (fun n => DefInt01 (fun x => Real.rpow x (n - 1))) 1 m n =
      DefInt01 (fun x => Real.rpow x (n - 1) * (Real.log x) ^ m) := by
  sorry

theorem proof_gap_exercise_3784_10
    (I n : ℝ) (m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    FunDeri (fun n => 1 /. n) 1 m n = ((-1 : ℝ) ^ m * (Nat.factorial m : ℝ)) /. (n ^ (m + 1)) := by
  sorry

theorem proof_gap_exercise_3784_11
    (I n : ℝ) (m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hI : I = DefInt01 (fun x => Real.rpow x (n - 1) * (Real.log x) ^ m)) :
    I = ((-1 : ℝ) ^ m * (Nat.factorial m : ℝ)) /. (n ^ (m + 1)) := by
  sorry
