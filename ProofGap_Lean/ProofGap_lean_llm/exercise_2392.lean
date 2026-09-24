import Mathlib

attribute [local instance] Classical.propDecidable
set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def limValue (l : Filter ℝ) (u : ℝ -> ℝ) : ℝ :=
  if h : ∃ L : ℝ, Tendsto u l (𝓝 L) then Classical.choose h else 0

noncomputable def pv2392Integrand (x : ℝ) : ℝ := 1 /. (x ^ (2 : ℕ) - 3 * x + 2)

-- exercise: exercise_2392

-- Exercise 2392, gap 1
theorem proof_gap_exercise_2392_1
  (VPInt : Set ℝ -> (ℝ -> ℝ) -> ℝ)
  (eps eta b : ℝ)
  : VPInt (Set.Ici (0 : ℝ)) pv2392Integrand =
      limValue (𝓝[>] (0 : ℝ)) (fun eps =>
        limValue (𝓝[>] (0 : ℝ)) (fun eta =>
          limValue atTop (fun b =>
            (∫ x in (0 : ℝ)..(1 - eps), pv2392Integrand x) +
            (∫ x in (1 + eps)..(2 - eta), pv2392Integrand x) +
            (∫ x in (2 + eta)..b, pv2392Integrand x)))) := by
  sorry

-- Exercise 2392, gap 2
theorem proof_gap_exercise_2392_2
  (VPInt : Set ℝ -> (ℝ -> ℝ) -> ℝ)
  (eps eta b : ℝ)
  (h1 : VPInt (Set.Ici (0 : ℝ)) pv2392Integrand =
      limValue (𝓝[>] (0 : ℝ)) (fun eps =>
        limValue (𝓝[>] (0 : ℝ)) (fun eta =>
          limValue atTop (fun b =>
            (∫ x in (0 : ℝ)..(1 - eps), pv2392Integrand x) +
            (∫ x in (1 + eps)..(2 - eta), pv2392Integrand x) +
            (∫ x in (2 + eta)..b, pv2392Integrand x)))))
  : ∀ eps : ℝ, 0 < eps -> eps < 1 ->
      ∀ eta : ℝ, 0 < eta -> eta < 1 ->
        ∀ b : ℝ, b > 2 ->
          (∫ x in (0 : ℝ)..(1 - eps), pv2392Integrand x) +
          (∫ x in (1 + eps)..(2 - eta), pv2392Integrand x) +
          (∫ x in (2 + eta)..b, pv2392Integrand x) =
            Real.log ((eps + 1) /. eps) - Real.log 2 +
            Real.log (eta /. (1 - eta)) - Real.log ((1 - eps) /. eps) +
            Real.log |((b - 2) /. (b - 1))| - Real.log (eta /. (1 + eta)) := by
  sorry

-- Exercise 2392, gap 3
theorem proof_gap_exercise_2392_3
  (VPInt : Set ℝ -> (ℝ -> ℝ) -> ℝ)
  (h1 : VPInt (Set.Ici (0 : ℝ)) pv2392Integrand =
      limValue (𝓝[>] (0 : ℝ)) (fun eps =>
        limValue (𝓝[>] (0 : ℝ)) (fun eta =>
          limValue atTop (fun b =>
            (∫ x in (0 : ℝ)..(1 - eps), pv2392Integrand x) +
            (∫ x in (1 + eps)..(2 - eta), pv2392Integrand x) +
            (∫ x in (2 + eta)..b, pv2392Integrand x)))))
  (h2 : ∀ eps : ℝ, 0 < eps -> eps < 1 ->
      ∀ eta : ℝ, 0 < eta -> eta < 1 ->
        ∀ b : ℝ, b > 2 ->
          (∫ x in (0 : ℝ)..(1 - eps), pv2392Integrand x) +
          (∫ x in (1 + eps)..(2 - eta), pv2392Integrand x) +
          (∫ x in (2 + eta)..b, pv2392Integrand x) =
            Real.log ((eps + 1) /. eps) - Real.log 2 +
            Real.log (eta /. (1 - eta)) - Real.log ((1 - eps) /. eps) +
            Real.log |((b - 2) /. (b - 1))| - Real.log (eta /. (1 + eta)))
  : VPInt (Set.Ici (0 : ℝ)) pv2392Integrand =
      limValue (𝓝[>] (0 : ℝ)) (fun eps =>
        limValue (𝓝[>] (0 : ℝ)) (fun eta =>
          Real.log ((eps + 1) /. (1 - eps)) - Real.log 2 +
          Real.log ((1 + eta) /. (1 - eta)))) := by
  sorry

-- Exercise 2392, gap 4
theorem proof_gap_exercise_2392_4
  (VPInt : Set ℝ -> (ℝ -> ℝ) -> ℝ)
  (h3 : VPInt (Set.Ici (0 : ℝ)) pv2392Integrand =
      limValue (𝓝[>] (0 : ℝ)) (fun eps =>
        limValue (𝓝[>] (0 : ℝ)) (fun eta =>
          Real.log ((eps + 1) /. (1 - eps)) - Real.log 2 +
          Real.log ((1 + eta) /. (1 - eta)))))
  : VPInt (Set.Ici (0 : ℝ)) pv2392Integrand = - Real.log 2 := by
  sorry

-- Exercise 2392, gap 5
theorem proof_gap_exercise_2392_5
  (VPInt : Set ℝ -> (ℝ -> ℝ) -> ℝ)
  (h4 : VPInt (Set.Ici (0 : ℝ)) pv2392Integrand = - Real.log 2)
  : - Real.log 2 = Real.log ((1 : ℝ) /. 2) := by
  sorry

-- Exercise 2392, gap 6
theorem proof_gap_exercise_2392_6
  (VPInt : Set ℝ -> (ℝ -> ℝ) -> ℝ)
  (h4 : VPInt (Set.Ici (0 : ℝ)) pv2392Integrand = - Real.log 2)
  (h5 : - Real.log 2 = Real.log ((1 : ℝ) /. 2))
  : VPInt (Set.Ici (0 : ℝ)) pv2392Integrand = Real.log ((1 : ℝ) /. 2) := by
  sorry
