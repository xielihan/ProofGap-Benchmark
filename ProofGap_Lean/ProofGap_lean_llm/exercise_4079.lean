import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology

noncomputable section

def VolumeInt3 (V : Set (ℝ × ℝ × ℝ)) (f : ℝ × ℝ × ℝ -> ℝ) : ℝ :=
  ∫ p in V, f p

def VolumeInt2 (S : Set (ℝ × ℝ)) (f : ℝ × ℝ -> ℝ) : ℝ :=
  ∫ p in S, f p

def V4079 (a b c : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ^ (2 : ℕ) / a ^ (2 : ℕ) + p.2.1 ^ (2 : ℕ) / b ^ (2 : ℕ) + p.2.2 ^ (2 : ℕ) / c ^ (2 : ℕ) ≤ 1}

def P4079 (a b c x : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ (2 : ℕ) / (b ^ (2 : ℕ) * (1 - x ^ (2 : ℕ) / a ^ (2 : ℕ))) +
      p.2 ^ (2 : ℕ) / (c ^ (2 : ℕ) * (1 - x ^ (2 : ℕ) / a ^ (2 : ℕ))) ≤ 1}

def Q4079 (a b c y : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ (2 : ℕ) / (c ^ (2 : ℕ) * (1 - y ^ (2 : ℕ) / b ^ (2 : ℕ))) +
      p.2 ^ (2 : ℕ) / (a ^ (2 : ℕ) * (1 - y ^ (2 : ℕ) / b ^ (2 : ℕ))) ≤ 1}

def R4079 (a b c z : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ (2 : ℕ) / (a ^ (2 : ℕ) * (1 - z ^ (2 : ℕ) / c ^ (2 : ℕ))) +
      p.2 ^ (2 : ℕ) / (b ^ (2 : ℕ) * (1 - z ^ (2 : ℕ) / c ^ (2 : ℕ))) ≤ 1}

-- exercise: exercise_4079

theorem proof_gap_exercise_4079_1
  (a b c : ℝ) (V : Set (ℝ × ℝ × ℝ)) (P Q R : ℝ -> Set (ℝ × ℝ))
  (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (hV : V = V4079 a b c)
  (hP : ∀ x : ℝ, P x = P4079 a b c x)
  (hQ : ∀ y : ℝ, Q y = Q4079 a b c y)
  (hR : ∀ z : ℝ, R z = R4079 a b c z) :
  ∀ x : ℝ, -a ≤ x ∧ x ≤ a ->
    VolumeInt2 (P x) (fun _ => (1 : ℝ)) = Real.pi * b * c * (1 - x ^ (2 : ℕ) / a ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_4079_2
  (a b c : ℝ) (V : Set (ℝ × ℝ × ℝ)) (P Q R : ℝ -> Set (ℝ × ℝ))
  (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (hV : V = V4079 a b c)
  (hP : ∀ x : ℝ, P x = P4079 a b c x)
  (hQ : ∀ y : ℝ, Q y = Q4079 a b c y)
  (hR : ∀ z : ℝ, R z = R4079 a b c z)
  (h1 : ∀ x : ℝ, -a ≤ x ∧ x ≤ a ->
    VolumeInt2 (P x) (fun _ => (1 : ℝ)) = Real.pi * b * c * (1 - x ^ (2 : ℕ) / a ^ (2 : ℕ))) :
  ∀ y : ℝ, -b ≤ y ∧ y ≤ b ->
    VolumeInt2 (Q y) (fun _ => (1 : ℝ)) = Real.pi * a * c * (1 - y ^ (2 : ℕ) / b ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_4079_3
  (a b c : ℝ) (V : Set (ℝ × ℝ × ℝ)) (P Q R : ℝ -> Set (ℝ × ℝ))
  (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (hV : V = V4079 a b c)
  (hP : ∀ x : ℝ, P x = P4079 a b c x)
  (hQ : ∀ y : ℝ, Q y = Q4079 a b c y)
  (hR : ∀ z : ℝ, R z = R4079 a b c z)
  (h1 : ∀ x : ℝ, -a ≤ x ∧ x ≤ a ->
    VolumeInt2 (P x) (fun _ => (1 : ℝ)) = Real.pi * b * c * (1 - x ^ (2 : ℕ) / a ^ (2 : ℕ)))
  (h2 : ∀ y : ℝ, -b ≤ y ∧ y ≤ b ->
    VolumeInt2 (Q y) (fun _ => (1 : ℝ)) = Real.pi * a * c * (1 - y ^ (2 : ℕ) / b ^ (2 : ℕ))) :
  ∀ z : ℝ, -c ≤ z ∧ z ≤ c ->
    VolumeInt2 (R z) (fun _ => (1 : ℝ)) = Real.pi * a * b * (1 - z ^ (2 : ℕ) / c ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_4079_4
  (a b c : ℝ) (V : Set (ℝ × ℝ × ℝ)) (P Q R : ℝ -> Set (ℝ × ℝ))
  (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (hV : V = V4079 a b c)
  (hP : ∀ x : ℝ, P x = P4079 a b c x)
  (hQ : ∀ y : ℝ, Q y = Q4079 a b c y)
  (hR : ∀ z : ℝ, R z = R4079 a b c z)
  (h1 : ∀ x : ℝ, -a ≤ x ∧ x ≤ a ->
    VolumeInt2 (P x) (fun _ => (1 : ℝ)) = Real.pi * b * c * (1 - x ^ (2 : ℕ) / a ^ (2 : ℕ)))
  (h2 : ∀ y : ℝ, -b ≤ y ∧ y ≤ b ->
    VolumeInt2 (Q y) (fun _ => (1 : ℝ)) = Real.pi * a * c * (1 - y ^ (2 : ℕ) / b ^ (2 : ℕ)))
  (h3 : ∀ z : ℝ, -c ≤ z ∧ z ≤ c ->
    VolumeInt2 (R z) (fun _ => (1 : ℝ)) = Real.pi * a * b * (1 - z ^ (2 : ℕ) / c ^ (2 : ℕ))) :
  ∀ x : ℝ, ∀ y : ℝ, ∀ z : ℝ,
    VolumeInt3 V (fun p => p.1 ^ (2 : ℕ) / a ^ (2 : ℕ) + p.2.1 ^ (2 : ℕ) / b ^ (2 : ℕ) + p.2.2 ^ (2 : ℕ) / c ^ (2 : ℕ)) =
      (∫ x in (-a)..a, x ^ (2 : ℕ) / a ^ (2 : ℕ) * VolumeInt2 (P x) (fun _ => (1 : ℝ))) +
      (∫ y in (-b)..b, y ^ (2 : ℕ) / b ^ (2 : ℕ) * VolumeInt2 (Q y) (fun _ => (1 : ℝ))) +
      (∫ z in (-c)..c, z ^ (2 : ℕ) / c ^ (2 : ℕ) * VolumeInt2 (R z) (fun _ => (1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_4079_5
  (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
  ∀ x : ℝ,
    (∫ x in (-a)..a, x ^ (2 : ℕ) / a ^ (2 : ℕ) * Real.pi * b * c * (1 - x ^ (2 : ℕ) / a ^ (2 : ℕ))) =
      (4 * Real.pi * a * b * c) / 15 := by
  sorry

theorem proof_gap_exercise_4079_6
  (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
  ∀ y : ℝ,
    (∫ y in (-b)..b, y ^ (2 : ℕ) / b ^ (2 : ℕ) * Real.pi * a * c * (1 - y ^ (2 : ℕ) / b ^ (2 : ℕ))) =
      (4 * Real.pi * a * b * c) / 15 := by
  sorry

theorem proof_gap_exercise_4079_7
  (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
  ∀ z : ℝ,
    (∫ z in (-c)..c, z ^ (2 : ℕ) / c ^ (2 : ℕ) * Real.pi * a * b * (1 - z ^ (2 : ℕ) / c ^ (2 : ℕ))) =
      (4 * Real.pi * a * b * c) / 15 := by
  sorry

theorem proof_gap_exercise_4079_8
  (a b c : ℝ) (V : Set (ℝ × ℝ × ℝ)) (P Q R : ℝ -> Set (ℝ × ℝ))
  (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (hV : V = V4079 a b c)
  (hP : ∀ x : ℝ, P x = P4079 a b c x)
  (hQ : ∀ y : ℝ, Q y = Q4079 a b c y)
  (hR : ∀ z : ℝ, R z = R4079 a b c z)
  (h1 : ∀ x : ℝ, -a ≤ x ∧ x ≤ a ->
    VolumeInt2 (P x) (fun _ => (1 : ℝ)) = Real.pi * b * c * (1 - x ^ (2 : ℕ) / a ^ (2 : ℕ)))
  (h2 : ∀ y : ℝ, -b ≤ y ∧ y ≤ b ->
    VolumeInt2 (Q y) (fun _ => (1 : ℝ)) = Real.pi * a * c * (1 - y ^ (2 : ℕ) / b ^ (2 : ℕ)))
  (h3 : ∀ z : ℝ, -c ≤ z ∧ z ≤ c ->
    VolumeInt2 (R z) (fun _ => (1 : ℝ)) = Real.pi * a * b * (1 - z ^ (2 : ℕ) / c ^ (2 : ℕ)))
  (h4 : ∀ x : ℝ, ∀ y : ℝ, ∀ z : ℝ,
    VolumeInt3 V (fun p => p.1 ^ (2 : ℕ) / a ^ (2 : ℕ) + p.2.1 ^ (2 : ℕ) / b ^ (2 : ℕ) + p.2.2 ^ (2 : ℕ) / c ^ (2 : ℕ)) =
      (∫ x in (-a)..a, x ^ (2 : ℕ) / a ^ (2 : ℕ) * VolumeInt2 (P x) (fun _ => (1 : ℝ))) +
      (∫ y in (-b)..b, y ^ (2 : ℕ) / b ^ (2 : ℕ) * VolumeInt2 (Q y) (fun _ => (1 : ℝ))) +
      (∫ z in (-c)..c, z ^ (2 : ℕ) / c ^ (2 : ℕ) * VolumeInt2 (R z) (fun _ => (1 : ℝ))))
  (h5 : ∀ x : ℝ,
    (∫ x in (-a)..a, x ^ (2 : ℕ) / a ^ (2 : ℕ) * Real.pi * b * c * (1 - x ^ (2 : ℕ) / a ^ (2 : ℕ))) =
      (4 * Real.pi * a * b * c) / 15)
  (h6 : ∀ y : ℝ,
    (∫ y in (-b)..b, y ^ (2 : ℕ) / b ^ (2 : ℕ) * Real.pi * a * c * (1 - y ^ (2 : ℕ) / b ^ (2 : ℕ))) =
      (4 * Real.pi * a * b * c) / 15)
  (h7 : ∀ z : ℝ,
    (∫ z in (-c)..c, z ^ (2 : ℕ) / c ^ (2 : ℕ) * Real.pi * a * b * (1 - z ^ (2 : ℕ) / c ^ (2 : ℕ))) =
      (4 * Real.pi * a * b * c) / 15) :
  ∀ x : ℝ, ∀ y : ℝ, ∀ z : ℝ,
    VolumeInt3 V (fun p => p.1 ^ (2 : ℕ) / a ^ (2 : ℕ) + p.2.1 ^ (2 : ℕ) / b ^ (2 : ℕ) + p.2.2 ^ (2 : ℕ) / c ^ (2 : ℕ)) =
      (4 * Real.pi * a * b * c) / 5 := by
  sorry

end
