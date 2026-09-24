import Mathlib

open Filter
open scoped Topology

namespace Exercise541

-- Inverse on the image: total representatives impose no values outside the image.
def InverseOnImage (x y : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, x (y t) = t) ∧
  (∀ u : ℝ, u ∈ Set.range y → y (x u) = u)

-- Equality to the source's restricted lambda, only for 1 + u > 0.
def LogInverse (a : ℝ) (x : ℝ → ℝ) : Prop :=
  ∀ u : ℝ, 1 + u > 0 → x u = Real.logb a (1 + u)

noncomputable def quotientA (a : ℝ) (t : ℝ) : ℝ :=
  (Real.rpow a t - 1) / t

noncomputable def quotientB (a : ℝ) (u : ℝ) : ℝ :=
  u / Real.logb a (1 + u)

noncomputable def quotientC (a : ℝ) (u : ℝ) : ℝ :=
  1 / Real.logb a (Real.rpow (1 + u) (1 / u))

-- Both finite punctured limits exist and have the same value.
def SameLimit (f g : ℝ → ℝ) : Prop :=
  ∃ L : ℝ, Tendsto f (𝓝[≠] (0 : ℝ)) (𝓝 L) ∧
    Tendsto g (𝓝[≠] (0 : ℝ)) (𝓝 L)

end Exercise541

open Exercise541

-- Exercise 541, gap 1
theorem proof_gap_exercise_541_1
  (a : ℝ) (x y : ℝ → ℝ)
  (ha : a > 0 ∧ a ≠ 1)
  (hy : y = fun t : ℝ => Real.rpow a t - 1)
  (hx : InverseOnImage x y)
  : LogInverse a x := by
  sorry

-- Exercise 541, gap 2
theorem proof_gap_exercise_541_2
  (a : ℝ) (x y : ℝ → ℝ)
  (ha : a > 0 ∧ a ≠ 1)
  (hy : y = fun t : ℝ => Real.rpow a t - 1)
  (hx : LogInverse a x)
  : SameLimit (quotientA a) (quotientB a) := by
  sorry

-- Exercise 541, gap 3
theorem proof_gap_exercise_541_3
  (a : ℝ) (x y : ℝ → ℝ)
  (ha : a > 0 ∧ a ≠ 1)
  (hy : y = fun t : ℝ => Real.rpow a t - 1)
  (hx : LogInverse a x)
  (hAB : SameLimit (quotientA a) (quotientB a))
  : SameLimit (quotientB a) (quotientC a) := by
  sorry

-- Exercise 541, gap 4
theorem proof_gap_exercise_541_4
  (a : ℝ) (x y : ℝ → ℝ)
  (ha : a > 0 ∧ a ≠ 1)
  (hy : y = fun t : ℝ => Real.rpow a t - 1)
  (hx : LogInverse a x)
  (hAB : SameLimit (quotientA a) (quotientB a))
  (hBC : SameLimit (quotientB a) (quotientC a))
  : Tendsto (quotientC a) (𝓝[≠] (0 : ℝ)) (𝓝 (1 / Real.logb a (Real.exp 1))) := by
  sorry

-- Exercise 541, gap 5
theorem proof_gap_exercise_541_5
  (a : ℝ) (x y : ℝ → ℝ)
  (ha : a > 0 ∧ a ≠ 1)
  (hy : y = fun t : ℝ => Real.rpow a t - 1)
  (hx : LogInverse a x)
  (hAB : SameLimit (quotientA a) (quotientB a))
  (hBC : SameLimit (quotientB a) (quotientC a))
  (hC : Tendsto (quotientC a) (𝓝[≠] (0 : ℝ))
    (𝓝 (1 / Real.logb a (Real.exp 1))))
  : 1 / Real.logb a (Real.exp 1) = Real.log a := by
  sorry

-- Exercise 541, gap 6
theorem proof_gap_exercise_541_6
  (a : ℝ) (x y : ℝ → ℝ)
  (ha : a > 0 ∧ a ≠ 1)
  (hy : y = fun t : ℝ => Real.rpow a t - 1)
  (hx : LogInverse a x)
  (hAB : SameLimit (quotientA a) (quotientB a))
  (hBC : SameLimit (quotientB a) (quotientC a))
  (hC : Tendsto (quotientC a) (𝓝[≠] (0 : ℝ))
    (𝓝 (1 / Real.logb a (Real.exp 1))))
  (hlog : 1 / Real.logb a (Real.exp 1) = Real.log a)
  : Tendsto (quotientA a) (𝓝[≠] (0 : ℝ)) (𝓝 (Real.log a)) := by
  sorry

