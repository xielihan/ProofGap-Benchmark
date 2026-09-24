import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def DefInt (a b : ℝ) (f : ℝ → ℝ) : ℝ := ∫ x in a..b, f x
noncomputable def sqrtn (_n : ℕ) (x : ℝ) : ℝ := Real.sqrt x
def approx (eps x y : ℝ) : Prop := |x - y| ≤ eps

noncomputable def ex2932_8_integrand : ℝ → ℝ := fun x => 1 /. sqrtn 2 (1 + x ^ 4)
noncomputable def ex2932_8_powerIntegrand : ℝ → ℝ := fun x => (1 + x ^ 4) ^ (-(1 /. 2))
noncomputable def ex2932_8_binomTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * ((Nat.centralBinom n : ℝ) /. (4 ^ n)) /. (4 * n + 1)
noncomputable def ex2932_8_binomSeries : ℝ := ∑' n : ℕ, ex2932_8_binomTerm n
noncomputable def ex2932_8_writtenDecimalSeries : ℝ :=
  (1.0000 + 0.0417 + 0.0160 + 0.0090 + 0.0060 + 0.0043 + 0.0033 + 0.0026 + 0.0022 + 0.0018 +
    0.0014 + 0.0012) -
  (0.1000 + 0.0240 + 0.0117 + 0.0072 + 0.0050 + 0.0037 + 0.0029 + 0.0024 +
    0.0020 + 0.0016 + 0.0013 + 0.0010)
noncomputable def ex2932_8_remainderBound : ℝ :=
  ((Finset.range 24).prod (fun k => ((2 * k + 1 : ℕ) : ℝ)) /. (97 * 2 ^ 24 * (Nat.factorial 24 : ℝ)))

-- exercise: exercise_2932_8

theorem proof_gap_exercise_2932_8_1 :
    ContinuousOn ex2932_8_integrand (Set.Icc 0 1) := by
  sorry

theorem proof_gap_exercise_2932_8_2
    (h1 : ContinuousOn ex2932_8_integrand (Set.Icc 0 1)) :
    ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_integrand x = ex2932_8_powerIntegrand x := by
  sorry

theorem proof_gap_exercise_2932_8_3
    (h1 : ContinuousOn ex2932_8_integrand (Set.Icc 0 1))
    (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_integrand x = ex2932_8_powerIntegrand x) :
    ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_powerIntegrand x =
        (∑' n : ℕ, (-1 : ℝ) ^ n * ((Nat.centralBinom n : ℝ) /. (4 ^ n)) * x ^ (4 * n)) := by
  sorry

theorem proof_gap_exercise_2932_8_4
    (h1 : ContinuousOn ex2932_8_integrand (Set.Icc 0 1))
    (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_integrand x = ex2932_8_powerIntegrand x)
    (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_powerIntegrand x =
        (∑' n : ℕ, (-1 : ℝ) ^ n * ((Nat.centralBinom n : ℝ) /. (4 ^ n)) * x ^ (4 * n))) :
    ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_integrand x =
        (∑' n : ℕ, (-1 : ℝ) ^ n * ((Nat.centralBinom n : ℝ) /. (4 ^ n)) * x ^ (4 * n)) := by
  sorry

theorem proof_gap_exercise_2932_8_5
    (h1 : ContinuousOn ex2932_8_integrand (Set.Icc 0 1))
    (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_integrand x = ex2932_8_powerIntegrand x)
    (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_powerIntegrand x =
        (∑' n : ℕ, (-1 : ℝ) ^ n * ((Nat.centralBinom n : ℝ) /. (4 ^ n)) * x ^ (4 * n)))
    (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_integrand x =
        (∑' n : ℕ, (-1 : ℝ) ^ n * ((Nat.centralBinom n : ℝ) /. (4 ^ n)) * x ^ (4 * n))) :
    DefInt 0 1 ex2932_8_integrand = DefInt 0 1 ex2932_8_powerIntegrand := by
  sorry

theorem proof_gap_exercise_2932_8_6
    (h1 : ContinuousOn ex2932_8_integrand (Set.Icc 0 1))
    (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_integrand x = ex2932_8_powerIntegrand x)
    (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_powerIntegrand x =
        (∑' n : ℕ, (-1 : ℝ) ^ n * ((Nat.centralBinom n : ℝ) /. (4 ^ n)) * x ^ (4 * n)))
    (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_integrand x =
        (∑' n : ℕ, (-1 : ℝ) ^ n * ((Nat.centralBinom n : ℝ) /. (4 ^ n)) * x ^ (4 * n)))
    (h5 : DefInt 0 1 ex2932_8_integrand = DefInt 0 1 ex2932_8_powerIntegrand) :
    DefInt 0 1 ex2932_8_integrand = ex2932_8_binomSeries := by
  sorry

theorem proof_gap_exercise_2932_8_7
    (h1 : ContinuousOn ex2932_8_integrand (Set.Icc 0 1))
    (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_integrand x = ex2932_8_powerIntegrand x)
    (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_powerIntegrand x =
        (∑' n : ℕ, (-1 : ℝ) ^ n * ((Nat.centralBinom n : ℝ) /. (4 ^ n)) * x ^ (4 * n)))
    (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_integrand x =
        (∑' n : ℕ, (-1 : ℝ) ^ n * ((Nat.centralBinom n : ℝ) /. (4 ^ n)) * x ^ (4 * n)))
    (h5 : DefInt 0 1 ex2932_8_integrand = DefInt 0 1 ex2932_8_powerIntegrand)
    (h6 : DefInt 0 1 ex2932_8_integrand = ex2932_8_binomSeries) :
    DefInt 0 1 ex2932_8_integrand = ex2932_8_writtenDecimalSeries := by
  sorry

theorem proof_gap_exercise_2932_8_8
    (h1 : ContinuousOn ex2932_8_integrand (Set.Icc 0 1))
    (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_integrand x = ex2932_8_powerIntegrand x)
    (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_powerIntegrand x =
        (∑' n : ℕ, (-1 : ℝ) ^ n * ((Nat.centralBinom n : ℝ) /. (4 ^ n)) * x ^ (4 * n)))
    (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_integrand x =
        (∑' n : ℕ, (-1 : ℝ) ^ n * ((Nat.centralBinom n : ℝ) /. (4 ^ n)) * x ^ (4 * n)))
    (h5 : DefInt 0 1 ex2932_8_integrand = DefInt 0 1 ex2932_8_powerIntegrand)
    (h6 : DefInt 0 1 ex2932_8_integrand = ex2932_8_binomSeries)
    (h7 : DefInt 0 1 ex2932_8_integrand = ex2932_8_writtenDecimalSeries) :
    ∃ Δ : ℝ, Δ ∈ (Set.univ : Set ℝ) ∧ 0 < Δ := by
  sorry

theorem proof_gap_exercise_2932_8_9
    (h1 : ContinuousOn ex2932_8_integrand (Set.Icc 0 1))
    (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_integrand x = ex2932_8_powerIntegrand x)
    (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_powerIntegrand x =
        (∑' n : ℕ, (-1 : ℝ) ^ n * ((Nat.centralBinom n : ℝ) /. (4 ^ n)) * x ^ (4 * n)))
    (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_integrand x =
        (∑' n : ℕ, (-1 : ℝ) ^ n * ((Nat.centralBinom n : ℝ) /. (4 ^ n)) * x ^ (4 * n)))
    (h5 : DefInt 0 1 ex2932_8_integrand = DefInt 0 1 ex2932_8_powerIntegrand)
    (h6 : DefInt 0 1 ex2932_8_integrand = ex2932_8_binomSeries)
    (h7 : DefInt 0 1 ex2932_8_integrand = ex2932_8_writtenDecimalSeries)
    (h8 : ∃ Δ : ℝ, Δ ∈ (Set.univ : Set ℝ) ∧ 0 < Δ) :
    ∃ Δ : ℝ, Δ ∈ (Set.univ : Set ℝ) ∧ Δ < ex2932_8_remainderBound := by
  sorry

theorem proof_gap_exercise_2932_8_10
    (h1 : ContinuousOn ex2932_8_integrand (Set.Icc 0 1))
    (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_integrand x = ex2932_8_powerIntegrand x)
    (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_powerIntegrand x =
        (∑' n : ℕ, (-1 : ℝ) ^ n * ((Nat.centralBinom n : ℝ) /. (4 ^ n)) * x ^ (4 * n)))
    (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_integrand x =
        (∑' n : ℕ, (-1 : ℝ) ^ n * ((Nat.centralBinom n : ℝ) /. (4 ^ n)) * x ^ (4 * n)))
    (h5 : DefInt 0 1 ex2932_8_integrand = DefInt 0 1 ex2932_8_powerIntegrand)
    (h6 : DefInt 0 1 ex2932_8_integrand = ex2932_8_binomSeries)
    (h7 : DefInt 0 1 ex2932_8_integrand = ex2932_8_writtenDecimalSeries)
    (h8 : ∃ Δ : ℝ, Δ ∈ (Set.univ : Set ℝ) ∧ 0 < Δ)
    (h9 : ∃ Δ : ℝ, Δ ∈ (Set.univ : Set ℝ) ∧ Δ < ex2932_8_remainderBound) :
    ex2932_8_remainderBound < 10 ^ (-3 : ℤ) := by
  sorry

theorem proof_gap_exercise_2932_8_11
    (h1 : ContinuousOn ex2932_8_integrand (Set.Icc 0 1))
    (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_integrand x = ex2932_8_powerIntegrand x)
    (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_powerIntegrand x =
        (∑' n : ℕ, (-1 : ℝ) ^ n * ((Nat.centralBinom n : ℝ) /. (4 ^ n)) * x ^ (4 * n)))
    (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x < 1 →
      ex2932_8_integrand x =
        (∑' n : ℕ, (-1 : ℝ) ^ n * ((Nat.centralBinom n : ℝ) /. (4 ^ n)) * x ^ (4 * n)))
    (h5 : DefInt 0 1 ex2932_8_integrand = DefInt 0 1 ex2932_8_powerIntegrand)
    (h6 : DefInt 0 1 ex2932_8_integrand = ex2932_8_binomSeries)
    (h7 : DefInt 0 1 ex2932_8_integrand = ex2932_8_writtenDecimalSeries)
    (h8 : ∃ Δ : ℝ, Δ ∈ (Set.univ : Set ℝ) ∧ 0 < Δ)
    (h9 : ∃ Δ : ℝ, Δ ∈ (Set.univ : Set ℝ) ∧ Δ < ex2932_8_remainderBound)
    (h10 : ex2932_8_remainderBound < 10 ^ (-3 : ℤ)) :
    approx 0.001 (DefInt 0 1 ex2932_8_integrand) 0.927 := by
  sorry
