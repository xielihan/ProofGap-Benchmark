import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def PosNat (n : ℕ) : Prop := 0 < n
noncomputable def seq3006 (x : ℝ) : ℕ → ℝ := fun n => if n = 0 then 0 else x ^ n /. n
noncomputable def derivSeries3006 (x : ℝ) : ℝ := ∑' n : ℕ, if 0 < n then x ^ (n - 1) else 0
noncomputable def sumSeries3006 (x : ℝ) : ℝ := ∑' n : ℕ, if 0 < n then x ^ n /. n else 0
def ConvSeries (u : ℕ → ℝ) : Prop := Summable u
def DivSeries (u : ℕ → ℝ) : Prop := ¬ Summable u
def RadiusOfConvergence (a : ℕ → ℝ) (r : ℝ) : Prop := ∀ x : ℝ, |x| < r → Summable fun n : ℕ => a n * x ^ n
noncomputable def FunDeri (f : ℝ → ℝ) (x : ℝ) : ℝ := deriv f x

-- Exercise 3006, gap 1
theorem proof_gap_exercise_3006_1 (x : ℝ) (f : ℝ → ℝ) (a : ℕ → ℝ)
  (hx : x ∈ (Set.univ : Set ℝ)) (ha : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ PosNat n → a n = 1 /. n) :
  Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop (𝓝 1) ↔ Tendsto (fun n : ℕ => ((n + 1 : ℝ) /. n)) atTop (𝓝 1) := by sorry

-- Exercise 3006, gap 2
theorem proof_gap_exercise_3006_2 (x : ℝ) (f : ℝ → ℝ) (a : ℕ → ℝ)
  (hx : x ∈ (Set.univ : Set ℝ)) (ha : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ PosNat n → a n = 1 /. n)
  (h5 : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop (𝓝 1) ↔ Tendsto (fun n : ℕ => ((n + 1 : ℝ) /. n)) atTop (𝓝 1)) :
  Tendsto (fun n : ℕ => ((n + 1 : ℝ) /. n)) atTop (𝓝 1) := by sorry

-- Exercise 3006, gap 3
theorem proof_gap_exercise_3006_3 (x : ℝ) (f : ℝ → ℝ) (a : ℕ → ℝ)
  (hx : x ∈ (Set.univ : Set ℝ)) (ha : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ PosNat n → a n = 1 /. n)
  (h5 : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop (𝓝 1) ↔ Tendsto (fun n : ℕ => ((n + 1 : ℝ) /. n)) atTop (𝓝 1))
  (h6 : Tendsto (fun n : ℕ => ((n + 1 : ℝ) /. n)) atTop (𝓝 1)) :
  Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop (𝓝 1) := by sorry

-- Exercise 3006, gap 4
theorem proof_gap_exercise_3006_4 (x : ℝ) (f : ℝ → ℝ) (a : ℕ → ℝ)
  (hx : x ∈ (Set.univ : Set ℝ)) (ha : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ PosNat n → a n = 1 /. n)
  (h5 : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop (𝓝 1) ↔ Tendsto (fun n : ℕ => ((n + 1 : ℝ) /. n)) atTop (𝓝 1))
  (h6 : Tendsto (fun n : ℕ => ((n + 1 : ℝ) /. n)) atTop (𝓝 1))
  (h7 : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop (𝓝 1)) :
  RadiusOfConvergence a 1 := by sorry

-- Exercise 3006, gap 5
theorem proof_gap_exercise_3006_5 (x : ℝ) (f : ℝ → ℝ) (a : ℕ → ℝ)
  (hx : x ∈ (Set.univ : Set ℝ)) (ha : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ PosNat n → a n = 1 /. n)
  (h5 : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop (𝓝 1) ↔ Tendsto (fun n : ℕ => ((n + 1 : ℝ) /. n)) atTop (𝓝 1))
  (h6 : Tendsto (fun n : ℕ => ((n + 1 : ℝ) /. n)) atTop (𝓝 1)) (h7 : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop (𝓝 1)) (h8 : RadiusOfConvergence a 1) :
  DivSeries (fun n : ℕ => if 0 < n then (1 : ℝ) ^ n /. n else 0) := by sorry

-- Exercise 3006, gap 6
theorem proof_gap_exercise_3006_6 (x : ℝ) (f : ℝ → ℝ) (a : ℕ → ℝ)
  (hx : x ∈ (Set.univ : Set ℝ)) (ha : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ PosNat n → a n = 1 /. n)
  (h5 : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop (𝓝 1) ↔ Tendsto (fun n : ℕ => ((n + 1 : ℝ) /. n)) atTop (𝓝 1))
  (h6 : Tendsto (fun n : ℕ => ((n + 1 : ℝ) /. n)) atTop (𝓝 1)) (h7 : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop (𝓝 1)) (h8 : RadiusOfConvergence a 1)
  (h9 : DivSeries (fun n : ℕ => if 0 < n then (1 : ℝ) ^ n /. n else 0)) :
  ConvSeries (fun n : ℕ => if 0 < n then (-1 : ℝ) ^ n /. n else 0) := by sorry

-- Exercise 3006, gap 7
theorem proof_gap_exercise_3006_7 (x : ℝ) (f : ℝ → ℝ) (a : ℕ → ℝ)
  (hx : x ∈ (Set.univ : Set ℝ)) (ha : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ PosNat n → a n = 1 /. n)
  (h5 : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop (𝓝 1) ↔ Tendsto (fun n : ℕ => ((n + 1 : ℝ) /. n)) atTop (𝓝 1)) (h6 : Tendsto (fun n : ℕ => ((n + 1 : ℝ) /. n)) atTop (𝓝 1)) (h7 : Tendsto (fun n : ℕ => |(a n /. a (n + 1))|) atTop (𝓝 1)) (h8 : RadiusOfConvergence a 1)
  (h9 : DivSeries (fun n : ℕ => if 0 < n then (1 : ℝ) ^ n /. n else 0)) (h10 : ConvSeries (fun n : ℕ => if 0 < n then (-1 : ℝ) ^ n /. n else 0)) :
  {x : ℝ | x ∈ (Set.univ : Set ℝ) ∧ ConvSeries (seq3006 x)} = Set.Ico (-1) 1 := by sorry

-- Exercise 3006, gap 8
theorem proof_gap_exercise_3006_8 (x : ℝ) (f : ℝ → ℝ) (a : ℕ → ℝ)
  (hx : x ∈ (Set.univ : Set ℝ)) (ha : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ PosNat n → a n = 1 /. n)
  (h11 : {x : ℝ | x ∈ (Set.univ : Set ℝ) ∧ ConvSeries (seq3006 x)} = Set.Ico (-1) 1) :
  x ∈ Set.Ico (-1) 1 → f = sumSeries3006 → |x| < 1 → FunDeri f x = derivSeries3006 x := by sorry

-- Exercise 3006, gap 9
theorem proof_gap_exercise_3006_9 (x : ℝ) (f : ℝ → ℝ) (a : ℕ → ℝ)
  (hx : x ∈ (Set.univ : Set ℝ)) (ha : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ PosNat n → a n = 1 /. n)
  (h11 : {x : ℝ | x ∈ (Set.univ : Set ℝ) ∧ ConvSeries (seq3006 x)} = Set.Ico (-1) 1)
  (h12 : x ∈ Set.Ico (-1) 1 → f = sumSeries3006 → |x| < 1 → FunDeri f x = derivSeries3006 x) :
  x ∈ Set.Ico (-1) 1 → f = sumSeries3006 → |x| < 1 → derivSeries3006 x = 1 /. (1 - x) := by sorry

-- Exercise 3006, gap 10
theorem proof_gap_exercise_3006_10 (x : ℝ) (f : ℝ → ℝ) (a : ℕ → ℝ)
  (hx : x ∈ (Set.univ : Set ℝ)) (ha : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ PosNat n → a n = 1 /. n)
  (h12 : x ∈ Set.Ico (-1) 1 → f = sumSeries3006 → |x| < 1 → FunDeri f x = derivSeries3006 x)
  (h13 : x ∈ Set.Ico (-1) 1 → f = sumSeries3006 → |x| < 1 → derivSeries3006 x = 1 /. (1 - x)) :
  x ∈ Set.Ico (-1) 1 → f = sumSeries3006 → |x| < 1 → FunDeri f x = 1 /. (1 - x) := by sorry

-- Exercise 3006, gap 11
theorem proof_gap_exercise_3006_11 (x : ℝ) (f : ℝ → ℝ) (a : ℕ → ℝ)
  (hx : x ∈ (Set.univ : Set ℝ)) (ha : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ PosNat n → a n = 1 /. n)
  (h14 : x ∈ Set.Ico (-1) 1 → f = sumSeries3006 → |x| < 1 → FunDeri f x = 1 /. (1 - x)) :
  x ∈ Set.Ico (-1) 1 → f = sumSeries3006 → |x| < 1 → f 0 = 0 := by sorry

-- Exercise 3006, gap 12
theorem proof_gap_exercise_3006_12 (x : ℝ) (f : ℝ → ℝ) (a : ℕ → ℝ)
  (hx : x ∈ (Set.univ : Set ℝ)) (ha : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ PosNat n → a n = 1 /. n)
  (h15 : x ∈ Set.Ico (-1) 1 → f = sumSeries3006 → |x| < 1 → f 0 = 0) :
  ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ∈ Set.Ioo (-1) 1 ∧ x ∈ Set.Ico (-1) 1 ∧ f = sumSeries3006 ∧ |x| < 1 → f x = ∫ u in (0)..x, FunDeri f u := by sorry

-- Exercise 3006, gap 13
theorem proof_gap_exercise_3006_13 (x : ℝ) (f : ℝ → ℝ) (a : ℕ → ℝ)
  (hx : x ∈ (Set.univ : Set ℝ)) (ha : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ PosNat n → a n = 1 /. n)
  (h16 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ∈ Set.Ioo (-1) 1 ∧ x ∈ Set.Ico (-1) 1 ∧ f = sumSeries3006 ∧ |x| < 1 → f x = ∫ u in (0)..x, FunDeri f u) :
  ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ∈ Set.Ioo (-1) 1 ∧ x ∈ Set.Ico (-1) 1 ∧ f = sumSeries3006 ∧ |x| < 1 → (∫ u in (0)..x, FunDeri f u) = ∫ u in (0)..x, 1 /. (1 - u) := by sorry

-- Exercise 3006, gap 14
theorem proof_gap_exercise_3006_14 (x : ℝ) (f : ℝ → ℝ) (a : ℕ → ℝ)
  (hx : x ∈ (Set.univ : Set ℝ)) (ha : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ PosNat n → a n = 1 /. n)
  (h17 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ∈ Set.Ioo (-1) 1 ∧ x ∈ Set.Ico (-1) 1 ∧ f = sumSeries3006 ∧ |x| < 1 → (∫ u in (0)..x, FunDeri f u) = ∫ u in (0)..x, 1 /. (1 - u)) :
  ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ∈ Set.Ioo (-1) 1 ∧ x ∈ Set.Ico (-1) 1 ∧ f = sumSeries3006 ∧ |x| < 1 → (∫ u in (0)..x, 1 /. (1 - u)) = Real.log (1 /. (1 - x)) := by sorry

-- Exercise 3006, gap 15
theorem proof_gap_exercise_3006_15 (x : ℝ) (f : ℝ → ℝ) (a : ℕ → ℝ)
  (hx : x ∈ (Set.univ : Set ℝ)) (ha : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ PosNat n → a n = 1 /. n)
  (h16 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ∈ Set.Ioo (-1) 1 ∧ x ∈ Set.Ico (-1) 1 ∧ f = sumSeries3006 ∧ |x| < 1 → f x = ∫ u in (0)..x, FunDeri f u)
  (h17 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ∈ Set.Ioo (-1) 1 ∧ x ∈ Set.Ico (-1) 1 ∧ f = sumSeries3006 ∧ |x| < 1 → (∫ u in (0)..x, FunDeri f u) = ∫ u in (0)..x, 1 /. (1 - u))
  (h18 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ∈ Set.Ioo (-1) 1 ∧ x ∈ Set.Ico (-1) 1 ∧ f = sumSeries3006 ∧ |x| < 1 → (∫ u in (0)..x, 1 /. (1 - u)) = Real.log (1 /. (1 - x))) :
  x ∈ Set.Ico (-1) 1 → f = sumSeries3006 → |x| < 1 → f x = Real.log (1 /. (1 - x)) := by sorry

-- Exercise 3006, gap 16
theorem proof_gap_exercise_3006_16 (x : ℝ) (f : ℝ → ℝ) (a : ℕ → ℝ)
  (hx : x ∈ (Set.univ : Set ℝ)) (ha : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ PosNat n → a n = 1 /. n)
  (h19 : x ∈ Set.Ico (-1) 1 → f = sumSeries3006 → |x| < 1 → f x = Real.log (1 /. (1 - x))) :
  x ∈ Set.Ico (-1) 1 → f = sumSeries3006 → x = -1 → sumSeries3006 (-1) = -Real.log 2 := by sorry

-- Exercise 3006, gap 17
theorem proof_gap_exercise_3006_17 (x : ℝ) (f : ℝ → ℝ) (a : ℕ → ℝ)
  (hx : x ∈ (Set.univ : Set ℝ)) (ha : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ PosNat n → a n = 1 /. n)
  (h20 : x ∈ Set.Ico (-1) 1 → f = sumSeries3006 → x = -1 → sumSeries3006 (-1) = -Real.log 2) :
  x ∈ Set.Ico (-1) 1 → f = sumSeries3006 → x = -1 → -Real.log 2 = Real.log (1 /. 2) := by sorry

-- Exercise 3006, gap 18
theorem proof_gap_exercise_3006_18 (x : ℝ) (f : ℝ → ℝ) (a : ℕ → ℝ)
  (hx : x ∈ (Set.univ : Set ℝ)) (ha : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ PosNat n → a n = 1 /. n)
  (h20 : x ∈ Set.Ico (-1) 1 → f = sumSeries3006 → x = -1 → sumSeries3006 (-1) = -Real.log 2)
  (h21 : x ∈ Set.Ico (-1) 1 → f = sumSeries3006 → x = -1 → -Real.log 2 = Real.log (1 /. 2)) :
  x ∈ Set.Ico (-1) 1 → f = sumSeries3006 → x = -1 → sumSeries3006 (-1) = Real.log (1 /. 2) := by sorry

-- Exercise 3006, gap 19
theorem proof_gap_exercise_3006_19 (x : ℝ) (f : ℝ → ℝ) (a : ℕ → ℝ)
  (hx : x ∈ (Set.univ : Set ℝ)) (ha : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ PosNat n → a n = 1 /. n)
  (h22 : x ∈ Set.Ico (-1) 1 → f = sumSeries3006 → x = -1 → sumSeries3006 (-1) = Real.log (1 /. 2)) :
  x ∈ Set.Ico (-1) 1 → f = sumSeries3006 → x = -1 → f x = Real.log (1 /. (1 - x)) := by sorry

-- Exercise 3006, gap 20
theorem proof_gap_exercise_3006_20 (x : ℝ) (f : ℝ → ℝ) (a : ℕ → ℝ)
  (hx : x ∈ (Set.univ : Set ℝ)) (ha : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ PosNat n → a n = 1 /. n)
  (h23 : x ∈ Set.Ico (-1) 1 → f = sumSeries3006 → x = -1 → f x = Real.log (1 /. (1 - x))) :
  x ∈ Set.Ico (-1) 1 → f = sumSeries3006 → sumSeries3006 x = Real.log (1 /. (1 - x)) := by sorry

-- Exercise 3006, gap 21
theorem proof_gap_exercise_3006_21 (x : ℝ) (f : ℝ → ℝ) (a : ℕ → ℝ)
  (hx : x ∈ (Set.univ : Set ℝ)) (ha : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ PosNat n → a n = 1 /. n)
  (h11 : {x : ℝ | x ∈ (Set.univ : Set ℝ) ∧ ConvSeries (seq3006 x)} = Set.Ico (-1) 1) :
  x ∉ Set.Ico (-1) 1 → DivSeries (seq3006 x) := by sorry

-- Exercise 3006, gap 22
theorem proof_gap_exercise_3006_22 (x : ℝ) (f : ℝ → ℝ) (a : ℕ → ℝ)
  (hx : x ∈ (Set.univ : Set ℝ)) (ha : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ PosNat n → a n = 1 /. n)
  (h25 : x ∉ Set.Ico (-1) 1 → DivSeries (seq3006 x)) :
  x ∈ Set.Ico (-1) 1 → sumSeries3006 x = Real.log (1 /. (1 - x)) := by sorry
