import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def infiniteProductFrom (a : ℕ -> ℝ) (start : ℕ) (L : ℝ) : Prop :=
  Tendsto (fun N : ℕ => Finset.prod (Finset.Icc start N) (fun k : ℕ => a k)) atTop (𝓝 L)

-- exercise: exercise_3054

-- GAP 1: substitute the definition of the partial product P_n into the left side.
theorem proof_gap_exercise_3054_1
  (P : ℕ -> ℝ)
  (hP : ∀ n : ℕ, P n = Finset.prod (Finset.Icc 0 n) (fun i : ℕ => 1 + (1 /. 2) ^ (2 ^ i : ℕ)))
  : ∀ n : ℕ, (1 - 1 /. 2) * P n =
      (1 - 1 /. 2) * (Finset.prod (Finset.Icc 0 n) (fun i : ℕ => 1 + (1 /. 2) ^ (2 ^ i : ℕ))) := by
  sorry

-- GAP 2: telescoping identity after multiplying by 1 - 1/2.
theorem proof_gap_exercise_3054_2
  (P : ℕ -> ℝ)
  (hP : ∀ n : ℕ, P n = Finset.prod (Finset.Icc 0 n) (fun i : ℕ => 1 + (1 /. 2) ^ (2 ^ i : ℕ)))
  (h1 : ∀ n : ℕ, (1 - 1 /. 2) * P n =
      (1 - 1 /. 2) * (Finset.prod (Finset.Icc 0 n) (fun i : ℕ => 1 + (1 /. 2) ^ (2 ^ i : ℕ))))
  : ∀ n : ℕ, (1 - 1 /. 2) * P n = 1 - (1 /. 2) ^ (2 ^ (n + 1) : ℕ) := by
  sorry

-- GAP 3: divide the telescoping identity by 1 - 1/2.
theorem proof_gap_exercise_3054_3
  (P : ℕ -> ℝ)
  (hP : ∀ n : ℕ, P n = Finset.prod (Finset.Icc 0 n) (fun i : ℕ => 1 + (1 /. 2) ^ (2 ^ i : ℕ)))
  (h1 : ∀ n : ℕ, (1 - 1 /. 2) * P n =
      (1 - 1 /. 2) * (Finset.prod (Finset.Icc 0 n) (fun i : ℕ => 1 + (1 /. 2) ^ (2 ^ i : ℕ))))
  (h2 : ∀ n : ℕ, (1 - 1 /. 2) * P n = 1 - (1 /. 2) ^ (2 ^ (n + 1) : ℕ))
  : ∀ n : ℕ, P n = (1 - (1 /. 2) ^ (2 ^ (n + 1) : ℕ)) /. (1 - 1 /. 2) := by
  sorry

-- GAP 4: limit of the explicit partial-product formula.
theorem proof_gap_exercise_3054_4
  (P : ℕ -> ℝ)
  (hP : ∀ n : ℕ, P n = Finset.prod (Finset.Icc 0 n) (fun i : ℕ => 1 + (1 /. 2) ^ (2 ^ i : ℕ)))
  (h1 : ∀ n : ℕ, (1 - 1 /. 2) * P n =
      (1 - 1 /. 2) * (Finset.prod (Finset.Icc 0 n) (fun i : ℕ => 1 + (1 /. 2) ^ (2 ^ i : ℕ))))
  (h2 : ∀ n : ℕ, (1 - 1 /. 2) * P n = 1 - (1 /. 2) ^ (2 ^ (n + 1) : ℕ))
  (h3 : ∀ n : ℕ, P n = (1 - (1 /. 2) ^ (2 ^ (n + 1) : ℕ)) /. (1 - 1 /. 2))
  : Tendsto P atTop (𝓝 (1 /. (1 - 1 /. 2))) := by
  sorry

-- GAP 5: arithmetic simplification of the limiting value.
theorem proof_gap_exercise_3054_5
  (P : ℕ -> ℝ)
  (hP : ∀ n : ℕ, P n = Finset.prod (Finset.Icc 0 n) (fun i : ℕ => 1 + (1 /. 2) ^ (2 ^ i : ℕ)))
  (h1 : ∀ n : ℕ, (1 - 1 /. 2) * P n =
      (1 - 1 /. 2) * (Finset.prod (Finset.Icc 0 n) (fun i : ℕ => 1 + (1 /. 2) ^ (2 ^ i : ℕ))))
  (h2 : ∀ n : ℕ, (1 - 1 /. 2) * P n = 1 - (1 /. 2) ^ (2 ^ (n + 1) : ℕ))
  (h3 : ∀ n : ℕ, P n = (1 - (1 /. 2) ^ (2 ^ (n + 1) : ℕ)) /. (1 - 1 /. 2))
  (h4 : Tendsto P atTop (𝓝 (1 /. (1 - 1 /. 2))))
  : (1 /. (1 - 1 /. 2)) = 2 := by
  sorry

-- GAP 6: rewrite the partial-product limit using the simplified value.
theorem proof_gap_exercise_3054_6
  (P : ℕ -> ℝ)
  (hP : ∀ n : ℕ, P n = Finset.prod (Finset.Icc 0 n) (fun i : ℕ => 1 + (1 /. 2) ^ (2 ^ i : ℕ)))
  (h1 : ∀ n : ℕ, (1 - 1 /. 2) * P n =
      (1 - 1 /. 2) * (Finset.prod (Finset.Icc 0 n) (fun i : ℕ => 1 + (1 /. 2) ^ (2 ^ i : ℕ))))
  (h2 : ∀ n : ℕ, (1 - 1 /. 2) * P n = 1 - (1 /. 2) ^ (2 ^ (n + 1) : ℕ))
  (h3 : ∀ n : ℕ, P n = (1 - (1 /. 2) ^ (2 ^ (n + 1) : ℕ)) /. (1 - 1 /. 2))
  (h4 : Tendsto P atTop (𝓝 (1 /. (1 - 1 /. 2))))
  (h5 : (1 /. (1 - 1 /. 2)) = 2)
  : Tendsto P atTop (𝓝 2) := by
  sorry

-- GAP 7: identify the infinite product with the limit of its partial products.
theorem proof_gap_exercise_3054_7
  (P : ℕ -> ℝ)
  (hP : ∀ n : ℕ, P n = Finset.prod (Finset.Icc 0 n) (fun i : ℕ => 1 + (1 /. 2) ^ (2 ^ i : ℕ)))
  (h1 : ∀ n : ℕ, (1 - 1 /. 2) * P n =
      (1 - 1 /. 2) * (Finset.prod (Finset.Icc 0 n) (fun i : ℕ => 1 + (1 /. 2) ^ (2 ^ i : ℕ))))
  (h2 : ∀ n : ℕ, (1 - 1 /. 2) * P n = 1 - (1 /. 2) ^ (2 ^ (n + 1) : ℕ))
  (h3 : ∀ n : ℕ, P n = (1 - (1 /. 2) ^ (2 ^ (n + 1) : ℕ)) /. (1 - 1 /. 2))
  (h4 : Tendsto P atTop (𝓝 (1 /. (1 - 1 /. 2))))
  (h5 : (1 /. (1 - 1 /. 2)) = 2)
  (h6 : Tendsto P atTop (𝓝 2))
  : infiniteProductFrom (fun n : ℕ => 1 + (1 /. 2) ^ (2 ^ n : ℕ)) 0 2 := by
  sorry

-- GAP 8: final restatement of the product value.
theorem proof_gap_exercise_3054_8
  (P : ℕ -> ℝ)
  (hP : ∀ n : ℕ, P n = Finset.prod (Finset.Icc 0 n) (fun i : ℕ => 1 + (1 /. 2) ^ (2 ^ i : ℕ)))
  (h1 : ∀ n : ℕ, (1 - 1 /. 2) * P n =
      (1 - 1 /. 2) * (Finset.prod (Finset.Icc 0 n) (fun i : ℕ => 1 + (1 /. 2) ^ (2 ^ i : ℕ))))
  (h2 : ∀ n : ℕ, (1 - 1 /. 2) * P n = 1 - (1 /. 2) ^ (2 ^ (n + 1) : ℕ))
  (h3 : ∀ n : ℕ, P n = (1 - (1 /. 2) ^ (2 ^ (n + 1) : ℕ)) /. (1 - 1 /. 2))
  (h4 : Tendsto P atTop (𝓝 (1 /. (1 - 1 /. 2))))
  (h5 : (1 /. (1 - 1 /. 2)) = 2)
  (h6 : Tendsto P atTop (𝓝 2))
  (h7 : infiniteProductFrom (fun n : ℕ => 1 + (1 /. 2) ^ (2 ^ n : ℕ)) 0 2)
  : infiniteProductFrom (fun n : ℕ => 1 + (1 /. 2) ^ (2 ^ n : ℕ)) 0 2 := by
  sorry
