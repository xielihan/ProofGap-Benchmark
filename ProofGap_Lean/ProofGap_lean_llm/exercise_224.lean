import Mathlib

namespace Exercise224

-- A function with an explicit real domain. Values outside the domain are unused.
structure RealFunction where
  domain : Set ℝ
  value : ℝ → ℝ

-- The inverse domain is the original range, not automatically all reals.
-- Under each gap's affine hypothesis, every real has a unique preimage;
-- hence invFun is the actual inverse everywhere on this domain.
noncomputable def inverse (y : ℝ → ℝ) : RealFunction :=
  ⟨Set.range y, Function.invFun y⟩

noncomputable def answer : RealFunction :=
  ⟨Set.univ, fun z => (z - 3) / 2⟩

end Exercise224

-- Exercise 224, gap 1 (PROOF GAP @1).
-- RealSet membership is represented by the binder type ℝ.
theorem proof_gap_exercise_224_1
    (y : ℝ → ℝ)
    (h1 : ∀ x : ℝ, y x = 2 * x + 3) :
    ∀ z : ℝ, (Exercise224.inverse y).value z = (z - 3) / 2 := by
  sorry

-- Exercise 224, gap 2 (PROOF GAP @2).
theorem proof_gap_exercise_224_2
    (y : ℝ → ℝ)
    (h1 : ∀ x : ℝ, y x = 2 * x + 3)
    (h2 : ∀ z : ℝ, (Exercise224.inverse y).value z = (z - 3) / 2) :
    (Exercise224.inverse y).domain = Set.univ := by
  sorry

-- Exercise 224, gap 3 (PROOF GAP @3).
-- Equality includes both the domain and the values of the restricted lambda.
theorem proof_gap_exercise_224_3
    (y : ℝ → ℝ)
    (h1 : ∀ x : ℝ, y x = 2 * x + 3)
    (h2 : ∀ z : ℝ, (Exercise224.inverse y).value z = (z - 3) / 2)
    (h3 : (Exercise224.inverse y).domain = Set.univ) :
    Exercise224.inverse y = Exercise224.answer := by
  sorry
