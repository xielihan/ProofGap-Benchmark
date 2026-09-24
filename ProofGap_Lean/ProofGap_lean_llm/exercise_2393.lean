import Mathlib

attribute [local instance] Classical.propDecidable
set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def limValue (l : Filter ℝ) (u : ℝ -> ℝ) : ℝ :=
  if h : ∃ L : ℝ, Tendsto u l (𝓝 L) then Classical.choose h else 0

noncomputable def pv2393Integrand (x : ℝ) : ℝ := 1 /. (x * Real.log x)

-- exercise: exercise_2393

-- Exercise 2393, gap 1
theorem proof_gap_exercise_2393_1
  (VPInt : Set ℝ -> (ℝ -> ℝ) -> ℝ)
  (eps : ℝ)
  : VPInt (Set.Icc ((1 : ℝ) /. 2) 2) pv2393Integrand =
      limValue (𝓝[>] (0 : ℝ)) (fun eps =>
        (∫ x in ((1 : ℝ) /. 2)..(1 - eps), pv2393Integrand x) +
        (∫ x in (1 + eps)..2, pv2393Integrand x)) := by
  sorry

-- Exercise 2393, gap 2
theorem proof_gap_exercise_2393_2
  (VPInt : Set ℝ -> (ℝ -> ℝ) -> ℝ)
  (eps : ℝ)
  (h1 : VPInt (Set.Icc ((1 : ℝ) /. 2) 2) pv2393Integrand =
      limValue (𝓝[>] (0 : ℝ)) (fun eps =>
        (∫ x in ((1 : ℝ) /. 2)..(1 - eps), pv2393Integrand x) +
        (∫ x in (1 + eps)..2, pv2393Integrand x)))
  : ∀ eps : ℝ, 0 < eps -> eps < 1 ->
      (∫ x in ((1 : ℝ) /. 2)..(1 - eps), pv2393Integrand x) +
      (∫ x in (1 + eps)..2, pv2393Integrand x) =
        Real.log |Real.log (1 - eps)| - Real.log (Real.log 2) +
        Real.log (Real.log 2) - Real.log |Real.log (1 + eps)| := by
  sorry

-- Exercise 2393, gap 3
theorem proof_gap_exercise_2393_3
  (VPInt : Set ℝ -> (ℝ -> ℝ) -> ℝ)
  (h1 : VPInt (Set.Icc ((1 : ℝ) /. 2) 2) pv2393Integrand =
      limValue (𝓝[>] (0 : ℝ)) (fun eps =>
        (∫ x in ((1 : ℝ) /. 2)..(1 - eps), pv2393Integrand x) +
        (∫ x in (1 + eps)..2, pv2393Integrand x)))
  (h2 : ∀ eps : ℝ, 0 < eps -> eps < 1 ->
      (∫ x in ((1 : ℝ) /. 2)..(1 - eps), pv2393Integrand x) +
      (∫ x in (1 + eps)..2, pv2393Integrand x) =
        Real.log |Real.log (1 - eps)| - Real.log (Real.log 2) +
        Real.log (Real.log 2) - Real.log |Real.log (1 + eps)|)
  : VPInt (Set.Icc ((1 : ℝ) /. 2) 2) pv2393Integrand =
      limValue (𝓝[>] (0 : ℝ)) (fun eps =>
        Real.log |((Real.log (1 - eps)) /. (Real.log (1 + eps)))|) := by
  sorry

-- Exercise 2393, gap 4
theorem proof_gap_exercise_2393_4
  (VPInt : Set ℝ -> (ℝ -> ℝ) -> ℝ)
  : limValue (𝓝[>] (0 : ℝ)) (fun eps =>
      (Real.log (1 - eps)) /. (Real.log (1 + eps))) =
    limValue (𝓝[>] (0 : ℝ)) (fun eps =>
      ((-1 : ℝ) /. (1 - eps)) /. ((1 : ℝ) /. (1 + eps))) := by
  sorry

-- Exercise 2393, gap 5
theorem proof_gap_exercise_2393_5
  (VPInt : Set ℝ -> (ℝ -> ℝ) -> ℝ)
  (h4 : limValue (𝓝[>] (0 : ℝ)) (fun eps =>
      (Real.log (1 - eps)) /. (Real.log (1 + eps))) =
    limValue (𝓝[>] (0 : ℝ)) (fun eps =>
      ((-1 : ℝ) /. (1 - eps)) /. ((1 : ℝ) /. (1 + eps))))
  : limValue (𝓝[>] (0 : ℝ)) (fun eps =>
      ((-1 : ℝ) /. (1 - eps)) /. ((1 : ℝ) /. (1 + eps))) = -1 := by
  sorry

-- Exercise 2393, gap 6
theorem proof_gap_exercise_2393_6
  (VPInt : Set ℝ -> (ℝ -> ℝ) -> ℝ)
  (h4 : limValue (𝓝[>] (0 : ℝ)) (fun eps =>
      (Real.log (1 - eps)) /. (Real.log (1 + eps))) =
    limValue (𝓝[>] (0 : ℝ)) (fun eps =>
      ((-1 : ℝ) /. (1 - eps)) /. ((1 : ℝ) /. (1 + eps))))
  (h5 : limValue (𝓝[>] (0 : ℝ)) (fun eps =>
      ((-1 : ℝ) /. (1 - eps)) /. ((1 : ℝ) /. (1 + eps))) = -1)
  : limValue (𝓝[>] (0 : ℝ)) (fun eps =>
      (Real.log (1 - eps)) /. (Real.log (1 + eps))) = -1 := by
  sorry

-- Exercise 2393, gap 7
theorem proof_gap_exercise_2393_7
  (VPInt : Set ℝ -> (ℝ -> ℝ) -> ℝ)
  (h3 : VPInt (Set.Icc ((1 : ℝ) /. 2) 2) pv2393Integrand =
      limValue (𝓝[>] (0 : ℝ)) (fun eps =>
        Real.log |((Real.log (1 - eps)) /. (Real.log (1 + eps)))|))
  (h6 : limValue (𝓝[>] (0 : ℝ)) (fun eps =>
      (Real.log (1 - eps)) /. (Real.log (1 + eps))) = -1)
  : VPInt (Set.Icc ((1 : ℝ) /. 2) 2) pv2393Integrand = Real.log 1 := by
  sorry

-- Exercise 2393, gap 8
theorem proof_gap_exercise_2393_8
  (VPInt : Set ℝ -> (ℝ -> ℝ) -> ℝ)
  (h7 : VPInt (Set.Icc ((1 : ℝ) /. 2) 2) pv2393Integrand = Real.log 1)
  : Real.log 1 = (0 : ℝ) := by
  sorry

-- Exercise 2393, gap 9
theorem proof_gap_exercise_2393_9
  (VPInt : Set ℝ -> (ℝ -> ℝ) -> ℝ)
  (h7 : VPInt (Set.Icc ((1 : ℝ) /. 2) 2) pv2393Integrand = Real.log 1)
  (h8 : Real.log 1 = (0 : ℝ))
  : VPInt (Set.Icc ((1 : ℝ) /. 2) 2) pv2393Integrand = 0 := by
  sorry
