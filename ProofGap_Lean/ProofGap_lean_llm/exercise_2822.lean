import Mathlib

attribute [local instance] Classical.propDecidable
set_option linter.style.longLine false

open Filter
open scoped Topology BigOperators

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def lpRadiusOfConvergence (a : ℕ → ℝ) : ℝ :=
  sSup {r : ℝ | 0 ≤ r ∧ ∀ x : ℝ, |x| < r → Summable (fun n : ℕ => a n * x ^ n)}

def lpDivergentSeries (u : ℕ → ℝ) : Prop := ¬ Summable u

-- exercise: exercise_2822
-- Exercise 2822

theorem proof_gap_exercise_2822_1
  (x a b θ : ℝ) (c : ℕ → ℝ)
  (ha : a > 0) (hb : b > 0)
  (hc : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} → c n = 1 /. (a ^ n + b ^ n))
  (hθ : θ = min a b /. max a b) (hθpos : 0 < θ) (hθle : θ ≤ 1) :
  Tendsto (fun n : ℕ => |(c n /. c (n + 1))|) atTop
      (𝓝 (atTop.limUnder (fun n : ℕ => max a b * ((1 + θ ^ (n + 1)) /. (1 + θ ^ n))))) := by
  sorry

theorem proof_gap_exercise_2822_2
  (x a b θ : ℝ) (c : ℕ → ℝ)
  (ha : a > 0) (hb : b > 0)
  (hc : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} → c n = 1 /. (a ^ n + b ^ n))
  (hθ : θ = min a b /. max a b) (hθpos : 0 < θ) (hθle : θ ≤ 1)
  (h12 : Tendsto (fun n : ℕ => |(c n /. c (n + 1))|) atTop
      (𝓝 (atTop.limUnder (fun n : ℕ => max a b * ((1 + θ ^ (n + 1)) /. (1 + θ ^ n)))))) :
  Tendsto (fun n : ℕ => max a b * ((1 + θ ^ (n + 1)) /. (1 + θ ^ n))) atTop (𝓝 (max a b)) := by
  sorry

theorem proof_gap_exercise_2822_3
  (x a b θ : ℝ) (c : ℕ → ℝ)
  (ha : a > 0) (hb : b > 0)
  (hc : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} → c n = 1 /. (a ^ n + b ^ n))
  (hθ : θ = min a b /. max a b) (hθpos : 0 < θ) (hθle : θ ≤ 1)
  (h12 : Tendsto (fun n : ℕ => |(c n /. c (n + 1))|) atTop
      (𝓝 (atTop.limUnder (fun n : ℕ => max a b * ((1 + θ ^ (n + 1)) /. (1 + θ ^ n))))))
  (h13 : Tendsto (fun n : ℕ => max a b * ((1 + θ ^ (n + 1)) /. (1 + θ ^ n))) atTop (𝓝 (max a b))) :
  Tendsto (fun n : ℕ => |(c n /. c (n + 1))|) atTop (𝓝 (max a b)) := by
  sorry

theorem proof_gap_exercise_2822_4
  (x a b θ : ℝ) (c : ℕ → ℝ)
  (ha : a > 0) (hb : b > 0)
  (hc : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} → c n = 1 /. (a ^ n + b ^ n))
  (hθ : θ = min a b /. max a b) (hθpos : 0 < θ) (hθle : θ ≤ 1)
  (h14 : Tendsto (fun n : ℕ => |(c n /. c (n + 1))|) atTop (𝓝 (max a b))) :
  lpRadiusOfConvergence c = max a b := by
  sorry

theorem proof_gap_exercise_2822_5
  (x a b θ : ℝ) (c : ℕ → ℝ)
  (ha : a > 0) (hb : b > 0)
  (hc : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} → c n = 1 /. (a ^ n + b ^ n))
  (hR : lpRadiusOfConvergence c = max a b) :
  ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ |y| < max a b → Summable (fun n : ℕ => if 1 ≤ n then c n * y ^ n else 0) := by
  sorry

theorem proof_gap_exercise_2822_6
  (x a b θ : ℝ) (c : ℕ → ℝ)
  (ha : a > 0) (hb : b > 0)
  (hc : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} → c n = 1 /. (a ^ n + b ^ n)) :
  ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} ∧ |x| = max a b →
    |(c n * x ^ n)| = (max a b) ^ n /. (a ^ n + b ^ n) := by
  sorry

theorem proof_gap_exercise_2822_7
  (x a b θ : ℝ) (c : ℕ → ℝ)
  (ha : a > 0) (hb : b > 0)
  (hc : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} → c n = 1 /. (a ^ n + b ^ n)) :
  |x| = max a b → Tendsto (fun n : ℕ => (max a b) ^ n /. (a ^ n + b ^ n)) atTop (𝓝 1) := by
  sorry

theorem proof_gap_exercise_2822_8
  (x a b θ : ℝ) (c : ℕ → ℝ)
  (ha : a > 0) (hb : b > 0)
  (hc : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} → c n = 1 /. (a ^ n + b ^ n))
  (h18 : |x| = max a b → Tendsto (fun n : ℕ => (max a b) ^ n /. (a ^ n + b ^ n)) atTop (𝓝 1)) :
  |x| = max a b → ¬ Tendsto (fun n : ℕ => c n * x ^ n) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2822_9
  (x a b θ : ℝ) (c : ℕ → ℝ)
  (ha : a > 0) (hb : b > 0)
  (hc : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} → c n = 1 /. (a ^ n + b ^ n))
  (h19 : |x| = max a b → ¬ Tendsto (fun n : ℕ => c n * x ^ n) atTop (𝓝 0)) :
  |x| = max a b → lpDivergentSeries (fun n : ℕ => if 1 ≤ n then c n * x ^ n else 0) := by
  sorry

theorem proof_gap_exercise_2822_10
  (x a b θ : ℝ) (c : ℕ → ℝ)
  (ha : a > 0) (hb : b > 0)
  (hc : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {m : ℕ | 0 < m} → c n = 1 /. (a ^ n + b ^ n))
  (h16 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ |y| < max a b → Summable (fun n : ℕ => if 1 ≤ n then c n * y ^ n else 0))
  (h20 : |x| = max a b → lpDivergentSeries (fun n : ℕ => if 1 ≤ n then c n * x ^ n else 0)) :
  x ∈ Set.Ioo (-(max a b)) (max a b) ↔ Summable (fun n : ℕ => if 1 ≤ n then c n * x ^ n else 0) := by
  sorry
