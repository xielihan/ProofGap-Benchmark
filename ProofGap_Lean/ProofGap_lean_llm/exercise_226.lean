import Mathlib

/- The source declares y on all of ℝ. This is deliberately retained.
   Inverse values use Mathlib's preimage selector; on the image of an
   injective function this is the unique inverse value.
   Function equality is encoded by graph equality, including domains.
   the theorem library, Thm 263 defines InverseFunc by reversing the graph.
   WARNING: gap 4 has a source domain error; see the semantic review.
-/
namespace Exercise226

def inverseGraph (y : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | y p.2 = p.1}

def restrictedFractionGraph : Set (ℝ × ℝ) :=
  {p | p.1 ≠ -1 ∧ p.2 = (1 - p.1) / (1 + p.1)}

end Exercise226

-- Exercise 226, gap 1
theorem proof_gap_exercise_226_1
  (y : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ≠ -1 → y x = (1 - x) / (1 + x))
  : ∀ x : ℝ, x ≠ -1 → y x + x * y x = 1 - x := by
  sorry

-- Exercise 226, gap 2
theorem proof_gap_exercise_226_2
  (y : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ≠ -1 → y x = (1 - x) / (1 + x))
  (h2 : ∀ x : ℝ, x ≠ -1 → y x + x * y x = 1 - x)
  : ∀ x : ℝ, x ≠ -1 → x = (1 - y x) / (1 + y x) := by
  sorry

-- Exercise 226, gap 3
theorem proof_gap_exercise_226_3
  (y : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ≠ -1 → y x = (1 - x) / (1 + x))
  (h2 : ∀ x : ℝ, x ≠ -1 → y x + x * y x = 1 - x)
  (h3 : ∀ x : ℝ, x ≠ -1 → x = (1 - y x) / (1 + y x))
  (h4 : Function.Injective y)
  : ∀ t : ℝ, t ≠ -1 → Function.invFun y t = (1 - t) / (1 + t) := by
  sorry

-- Exercise 226, gap 4
theorem proof_gap_exercise_226_4
  (y : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ≠ -1 → y x = (1 - x) / (1 + x))
  (h2 : ∀ x : ℝ, x ≠ -1 → y x + x * y x = 1 - x)
  (h3 : ∀ x : ℝ, x ≠ -1 → x = (1 - y x) / (1 + y x))
  (h4 : ∀ t : ℝ, t ≠ -1 → Function.invFun y t = (1 - t) / (1 + t))
  : Exercise226.inverseGraph y = Exercise226.restrictedFractionGraph := by
  sorry

