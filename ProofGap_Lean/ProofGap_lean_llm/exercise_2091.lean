import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology

noncomputable section

def AntiderivSet (f : ℝ -> ℝ) : Set (ℝ -> ℝ) :=
  {F : ℝ -> ℝ | ∀ x : ℝ, deriv F x = f x}

def AntiderivSetFamily (f : ℕ -> ℝ -> ℝ) : Prop :=
  ∀ n : ℕ, ∃ F : ℝ -> ℝ, F ∈ AntiderivSet (f n)

def HasLiAntiderivative (li : ℝ -> ℝ) : Prop :=
  ∃ F : ℝ -> ℝ, ∀ u : ℝ, 0 < u ∧ u ≠ 1 → li u = F u ∧ deriv F u = 1 / Real.log u

def HasElementaryRepresentation (f : ℝ -> ℝ) : Prop :=
  ∃ F : ℝ -> ℝ, F ∈ AntiderivSet f

def HasElementaryLiRepresentation (li f : ℝ -> ℝ) : Prop :=
  ∃ G H : ℝ -> ℝ, HasElementaryRepresentation G ∧ ∀ x : ℝ, H x = G x + li (Real.exp x)

-- exercise: exercise_2091

-- gap 1: partial fraction decomposition when the rational denominator has only real roots.
theorem proof_gap_exercise_2091_1
    (R P li : ℝ -> ℝ) (a x : ℝ) (A B : ℕ -> ℕ -> ℝ) (g : ℕ -> ℕ -> ℝ -> ℝ)
    (b : ℕ -> ℝ) (k : ℕ -> ℕ) (l : ℕ)
    (hli : HasLiAntiderivative li)
    (hl : 0 < l) (hb : ∀ i, 1 ≤ i ∧ i ≤ l → 0 < k i) :
    ∀ x : ℝ, R x = P x +
      Finset.sum (Finset.Icc 1 l) (fun i =>
        Finset.sum (Finset.Icc 1 (k i)) (fun j => A i j / (x - b i) ^ j)) := by
  sorry

-- gap 2: integrate the partial fraction decomposition termwise against e^(a x).
theorem proof_gap_exercise_2091_2
    (R P li : ℝ -> ℝ) (a x : ℝ) (A B : ℕ -> ℕ -> ℝ) (g : ℕ -> ℕ -> ℝ -> ℝ)
    (b : ℕ -> ℝ) (k : ℕ -> ℕ) (l : ℕ)
    (hpf : ∀ x : ℝ, R x = P x +
      Finset.sum (Finset.Icc 1 l) (fun i =>
        Finset.sum (Finset.Icc 1 (k i)) (fun j => A i j / (x - b i) ^ j))) :
    AntiderivSet (fun x : ℝ => R x * Real.exp (a * x)) =
      {F : ℝ -> ℝ | ∃ G : ℝ -> ℝ, ∃ H : ℕ -> ℕ -> ℝ -> ℝ,
        G ∈ AntiderivSet (fun x : ℝ => P x * Real.exp (a * x)) ∧
        (∀ i j, H i j ∈ AntiderivSet (fun x : ℝ => Real.exp (a * x) / (x - b i) ^ j)) ∧
        ∀ x : ℝ, F x = G x +
          Finset.sum (Finset.Icc 1 l) (fun i =>
            Finset.sum (Finset.Icc 1 (k i)) (fun j => A i j * H i j x))} := by
  sorry

-- gap 3: for j = 1, substitute t = x - b_i.
theorem proof_gap_exercise_2091_3
    (R P li : ℝ -> ℝ) (a x : ℝ) (A B : ℕ -> ℕ -> ℝ) (g : ℕ -> ℕ -> ℝ -> ℝ)
    (b : ℕ -> ℝ) (k : ℕ -> ℕ) (l : ℕ) :
    ∀ i : ℕ, 1 ≤ i ∧ i ≤ l →
      AntiderivSet (fun x : ℝ => Real.exp (a * x) / (x - b i)) =
        {F : ℝ -> ℝ | ∃ G : ℝ -> ℝ,
          G ∈ AntiderivSet (fun t : ℝ => Real.exp (a * (b i + t)) / t) ∧
          ∀ t : ℝ, F (b i + t) = G t} := by
  sorry

-- gap 4: express the j = 1 transformed integral using li(e^(a t)).
theorem proof_gap_exercise_2091_4
    (R P li : ℝ -> ℝ) (a x : ℝ) (A B : ℕ -> ℕ -> ℝ) (g : ℕ -> ℕ -> ℝ -> ℝ)
    (b : ℕ -> ℝ) (k : ℕ -> ℕ) (l : ℕ)
    (hli : HasLiAntiderivative li) :
    ∀ i : ℕ, 1 ≤ i ∧ i ≤ l →
      {F : ℝ -> ℝ | ∃ G : ℝ -> ℝ,
        G ∈ AntiderivSet (fun t : ℝ => Real.exp (a * t) / t) ∧
        ∀ t : ℝ, F t = Real.exp (a * b i) * G t} =
      {F : ℝ -> ℝ | ∃ C : ℝ, ∀ t : ℝ, F t = Real.exp (a * b i) * li (Real.exp (a * t)) + C} := by
  sorry

-- gap 5: substitute back from t to x - b_i in the simple-pole case.
theorem proof_gap_exercise_2091_5
    (R P li : ℝ -> ℝ) (a x : ℝ) (A B : ℕ -> ℕ -> ℝ) (g : ℕ -> ℕ -> ℝ -> ℝ)
    (b : ℕ -> ℝ) (k : ℕ -> ℕ) (l : ℕ) :
    ∀ i : ℕ, 1 ≤ i ∧ i ≤ l →
      AntiderivSet (fun x : ℝ => Real.exp (a * x) / (x - b i)) =
        {F : ℝ -> ℝ | ∃ C : ℝ, ∀ x : ℝ,
          F x = Real.exp (a * b i) * li (Real.exp (a * (x - b i))) + C} := by
  sorry

-- gap 6: for j >= 2, substitute t = x - b_i.
theorem proof_gap_exercise_2091_6
    (R P li : ℝ -> ℝ) (a x : ℝ) (A B : ℕ -> ℕ -> ℝ) (g : ℕ -> ℕ -> ℝ -> ℝ)
    (b : ℕ -> ℝ) (k : ℕ -> ℕ) (l : ℕ) :
    ∀ i j : ℕ, 1 ≤ i ∧ i ≤ l ∧ 1 ≤ j ∧ j ≤ k i ∧ 2 ≤ j →
      AntiderivSet (fun x : ℝ => Real.exp (a * x) / (x - b i) ^ j) =
        AntiderivSet (fun t : ℝ => Real.exp (a * (b i + t)) / t ^ j) := by
  sorry

-- gap 7: rewrite the higher-pole integral as an integration-by-parts integral.
theorem proof_gap_exercise_2091_7
    (R P li : ℝ -> ℝ) (a x : ℝ) (A B : ℕ -> ℕ -> ℝ) (g : ℕ -> ℕ -> ℝ -> ℝ)
    (b : ℕ -> ℝ) (k : ℕ -> ℕ) (l : ℕ) :
    ∀ i j : ℕ, 1 ≤ i ∧ i ≤ l ∧ 1 ≤ j ∧ j ≤ k i ∧ 2 ≤ j →
      AntiderivSet (fun t : ℝ => Real.exp (a * (b i + t)) / t ^ j) =
        {F : ℝ -> ℝ | ∃ G : ℝ -> ℝ,
          G ∈ AntiderivSet (fun t : ℝ => Real.exp (a * t) * deriv (fun u : ℝ => 1 / u ^ (j - 1)) t) ∧
          ∀ t : ℝ, F t = Real.exp (a * b i) / (1 - (j : ℝ)) * G t} := by
  sorry

-- gap 8: integration by parts lowers the pole order from j to j - 1.
theorem proof_gap_exercise_2091_8
    (R P li : ℝ -> ℝ) (a x : ℝ) (A B : ℕ -> ℕ -> ℝ) (g : ℕ -> ℕ -> ℝ -> ℝ)
    (b : ℕ -> ℝ) (k : ℕ -> ℕ) (l : ℕ) :
    ∀ i j : ℕ, 1 ≤ i ∧ i ≤ l ∧ 1 ≤ j ∧ j ≤ k i ∧ 2 ≤ j →
      {F : ℝ -> ℝ | ∃ G : ℝ -> ℝ,
        G ∈ AntiderivSet (fun t : ℝ => Real.exp (a * t) * deriv (fun u : ℝ => 1 / u ^ (j - 1)) t) ∧
        ∀ t : ℝ, F t = Real.exp (a * b i) / (1 - (j : ℝ)) * G t} =
      {F : ℝ -> ℝ | ∃ H : ℝ -> ℝ,
        H ∈ AntiderivSet (fun t : ℝ => Real.exp (a * t) / t ^ (j - 1)) ∧
        ∀ t : ℝ, F t =
          Real.exp (a * b i) / (1 - (j : ℝ)) * Real.exp (a * t) * (1 / t ^ (j - 1)) -
          (a * Real.exp (a * b i)) / (1 - (j : ℝ)) * H t} := by
  sorry

-- gap 9: repeated reduction gives elementary part plus a li term.
theorem proof_gap_exercise_2091_9
    (R P li : ℝ -> ℝ) (a x : ℝ) (A B : ℕ -> ℕ -> ℝ) (g : ℕ -> ℕ -> ℝ -> ℝ)
    (b : ℕ -> ℝ) (k : ℕ -> ℕ) (l : ℕ) :
    ∀ i j : ℕ, 1 ≤ i ∧ i ≤ l ∧ 1 ≤ j ∧ j ≤ k i ∧ 2 ≤ j →
      AntiderivSet (fun x : ℝ => Real.exp (a * x) / (x - b i) ^ j) =
        {F : ℝ -> ℝ | ∃ C : ℝ, ∀ x : ℝ,
          F x = g i j x + B i j * li (Real.exp (a * (x - b i))) + C} := by
  sorry

-- gap 10: assemble the polynomial term, elementary terms g_ij, and li terms.
theorem proof_gap_exercise_2091_10
    (R P li G : ℝ -> ℝ) (a x : ℝ) (A B : ℕ -> ℕ -> ℝ) (g : ℕ -> ℕ -> ℝ -> ℝ)
    (b : ℕ -> ℝ) (k : ℕ -> ℕ) (l : ℕ)
    (hG : ∀ x : ℝ, G x =
      Finset.sum (Finset.Icc 1 l) (fun i =>
        Finset.sum (Finset.Icc 1 (k i)) (fun j => A i j * g i j x)) +
      Finset.sum (Finset.Icc 1 l) (fun i =>
        Finset.sum (Finset.Icc 1 (k i)) (fun j =>
          A i j * B i j * li (Real.exp (a * (x - b i)))))) :
    AntiderivSet (fun x : ℝ => R x * Real.exp (a * x)) = {F : ℝ -> ℝ | ∀ x : ℝ, F x = G x} := by
  sorry

-- gap 11: existence of a representing function G.
theorem proof_gap_exercise_2091_11
    (R P li : ℝ -> ℝ) (a x : ℝ) (A B : ℕ -> ℕ -> ℝ) (g : ℕ -> ℕ -> ℝ -> ℝ)
    (b : ℕ -> ℝ) (k : ℕ -> ℕ) (l : ℕ) :
    ∃ G : ℝ -> ℝ, AntiderivSet (fun x : ℝ => R x * Real.exp (a * x)) = {F : ℝ -> ℝ | ∀ x : ℝ, F x = G x} := by
  sorry

-- gap 12: final claim that the integral is representable by elementary functions and li.
theorem proof_gap_exercise_2091_12
    (R P li : ℝ -> ℝ) (a x : ℝ) (A B : ℕ -> ℕ -> ℝ) (g : ℕ -> ℕ -> ℝ -> ℝ)
    (b : ℕ -> ℝ) (k : ℕ -> ℕ) (l : ℕ)
    (hli : HasLiAntiderivative li) :
    ∃ G : ℝ -> ℝ, AntiderivSet (fun x : ℝ => R x * Real.exp (a * x)) = {F : ℝ -> ℝ | ∀ x : ℝ, F x = G x} := by
  sorry

end
