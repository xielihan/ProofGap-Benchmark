import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open Filter

namespace Exercise3105_1

noncomputable def eulerGammaApprox (x : ℂ) (n : ℕ) : ℂ :=
  (Nat.factorial n : ℂ) * (n : ℂ) ^ x /
    ((Finset.range (n + 1)).prod (fun k => x + (k : ℂ)))

noncomputable def gammaEulerProductTerm (x : ℂ) (n : ℕ) : ℂ :=
  (1 + (1 / (n + 1 : ℂ))) ^ x / (1 + x / (n + 1 : ℂ))

-- exercise: exercise_3105_1

theorem proof_gap_exercise_3105_1_1
    (Gamma : ℂ -> ℂ) (x : ℂ) (n k : ℕ)
    (hx_small : x ∉ ({0, -1, -2, -3, -4, -5, -6, -7, -8, -9, -10} : Finset ℂ))
    (hx_tail : ∀ m : ℤ, 11 ≤ m -> x + (m : ℂ) ≠ 0)
    (hGamma : Gamma x = limUnder atTop (fun n : ℕ => eulerGammaApprox x n)) :
    ∀ n : ℕ, 0 < n ->
      eulerGammaApprox x n =
        ((n : ℂ) ^ x / x) * (1 / ((Finset.range n).prod (fun j => 1 + x / (j + 1 : ℂ)))) := by
  sorry

theorem proof_gap_exercise_3105_1_2
    (Gamma : ℂ -> ℂ) (x : ℂ) (n k : ℕ)
    (hx_small : x ∉ ({0, -1, -2, -3, -4, -5, -6, -7, -8, -9, -10} : Finset ℂ))
    (hx_tail : ∀ m : ℤ, 11 ≤ m -> x + (m : ℂ) ≠ 0)
    (hGamma : Gamma x = limUnder atTop (fun n : ℕ => eulerGammaApprox x n))
    (h1 : ∀ n : ℕ, 0 < n ->
      eulerGammaApprox x n =
        ((n : ℂ) ^ x / x) * (1 / ((Finset.range n).prod (fun j => 1 + x / (j + 1 : ℂ))))) :
    ∀ n : ℕ, 0 < n ->
      eulerGammaApprox x n =
        (1 / x) *
          (((Finset.range n).prod (fun j => (1 + 1 / (j + 1 : ℂ)) ^ x)) /
            ((Finset.range n).prod (fun j => 1 + x / (j + 1 : ℂ)))) *
          (1 / (1 + 1 / (n : ℂ)) ^ x) := by
  sorry

theorem proof_gap_exercise_3105_1_3
    (Gamma : ℂ -> ℂ) (x : ℂ) (n k : ℕ)
    (hx_small : x ∉ ({0, -1, -2, -3, -4, -5, -6, -7, -8, -9, -10} : Finset ℂ))
    (hx_tail : ∀ m : ℤ, 11 ≤ m -> x + (m : ℂ) ≠ 0)
    (hGamma : Gamma x = limUnder atTop (fun n : ℕ => eulerGammaApprox x n))
    (h1 : ∀ n : ℕ, 0 < n ->
      eulerGammaApprox x n =
        ((n : ℂ) ^ x / x) * (1 / ((Finset.range n).prod (fun j => 1 + x / (j + 1 : ℂ)))))
    (h2 : ∀ n : ℕ, 0 < n ->
      eulerGammaApprox x n =
        (1 / x) *
          (((Finset.range n).prod (fun j => (1 + 1 / (j + 1 : ℂ)) ^ x)) /
            ((Finset.range n).prod (fun j => 1 + x / (j + 1 : ℂ)))) *
          (1 / (1 + 1 / (n : ℂ)) ^ x)) :
    Gamma x = (1 / x) * tprod (gammaEulerProductTerm x) := by
  sorry

theorem proof_gap_exercise_3105_1_4
    (Gamma : ℂ -> ℂ) (x : ℂ) (n k : ℕ)
    (hx_small : x ∉ ({0, -1, -2, -3, -4, -5, -6, -7, -8, -9, -10} : Finset ℂ))
    (hx_tail : ∀ m : ℤ, 11 ≤ m -> x + (m : ℂ) ≠ 0)
    (hGamma : Gamma x = limUnder atTop (fun n : ℕ => eulerGammaApprox x n))
    (h1 : ∀ n : ℕ, 0 < n ->
      eulerGammaApprox x n =
        ((n : ℂ) ^ x / x) * (1 / ((Finset.range n).prod (fun j => 1 + x / (j + 1 : ℂ)))))
    (h2 : ∀ n : ℕ, 0 < n ->
      eulerGammaApprox x n =
        (1 / x) *
          (((Finset.range n).prod (fun j => (1 + 1 / (j + 1 : ℂ)) ^ x)) /
            ((Finset.range n).prod (fun j => 1 + x / (j + 1 : ℂ)))) *
          (1 / (1 + 1 / (n : ℂ)) ^ x))
    (h3 : Gamma x = (1 / x) * tprod (gammaEulerProductTerm x)) :
    Gamma x = (1 / x) * tprod (gammaEulerProductTerm x) := by
  sorry

end Exercise3105_1

