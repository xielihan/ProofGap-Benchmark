import Mathlib

set_option linter.style.longLine false

noncomputable section

abbrev RealSet : Set ℝ := Set.univ
abbrev CartesianProd (A B : Set ℝ) : Set (ℝ × ℝ) := Set.prod A B
abbrev ContinuousFuncOn (f : ℝ × ℝ -> ℝ) (C : Set (ℝ × ℝ)) : Prop := ContinuousOn f C
abbrev sqrtn (n : ℕ) (x : ℝ) : ℝ := Real.rpow x ((n : ℝ)⁻¹)
abbrev diff {α : Type*} (f : α -> ℝ) : ℝ := 1
abbrev ScalarCurveInt (C : Set (ℝ × ℝ)) (f : ℝ -> ℝ) : ℝ := 0
abbrev VectorCurveInt (C : Set (ℝ × ℝ)) (f : ℝ × ℝ -> ℝ) : ℝ := 0

def arcSpeedForm : ℝ -> ℝ := fun s => diff (fun s : ℝ => s)
def lineForm (P Q : ℝ × ℝ -> ℝ) : ℝ × ℝ -> ℝ :=
  fun p => P p * diff (fun p : ℝ × ℝ => p.1) + Q p * diff (fun p : ℝ × ℝ => p.2)
def directionalScalar (P Q : ℝ × ℝ -> ℝ) (α : ℝ) (p : ℝ × ℝ) : ℝ :=
  P p * Real.cos α + Q p * Real.sin α

-- exercise: exercise_4277

-- GAP 1: rewrite the vector line integral by direction cosines.
theorem proof_gap_exercise_4277_1
  (C : Set (ℝ × ℝ)) (P Q : ℝ × ℝ -> ℝ) (L M α x y : ℝ)
  (hC : C ⊆ CartesianProd RealSet RealSet)
  (hL : L ∈ RealSet) (hM : M ∈ RealSet) (hα : α ∈ RealSet) (hx : x ∈ RealSet) (hy : y ∈ RealSet)
  (hPcont : ContinuousFuncOn P C) (hQcont : ContinuousFuncOn Q C)
  (hLen : L = ScalarCurveInt C arcSpeedForm)
  (hMax : M = sSup ((fun p : ℝ × ℝ => sqrtn 2 (P p ^ 2 + Q p ^ 2)) '' C))
  : |VectorCurveInt C (lineForm P Q)| =
      |ScalarCurveInt C (fun s => directionalScalar P Q α (x, y) * diff (fun s : ℝ => s))| := by
  sorry

-- GAP 2: absolute value of integral is bounded by integral of absolute value.
theorem proof_gap_exercise_4277_2
  (C : Set (ℝ × ℝ)) (P Q : ℝ × ℝ -> ℝ) (L M α x y : ℝ)
  (hC : C ⊆ CartesianProd RealSet RealSet)
  (hL : L ∈ RealSet) (hM : M ∈ RealSet) (hα : α ∈ RealSet) (hx : x ∈ RealSet) (hy : y ∈ RealSet)
  (hPcont : ContinuousFuncOn P C) (hQcont : ContinuousFuncOn Q C)
  (hLen : L = ScalarCurveInt C arcSpeedForm)
  (hMax : M = sSup ((fun p : ℝ × ℝ => sqrtn 2 (P p ^ 2 + Q p ^ 2)) '' C))
  (h1 : |VectorCurveInt C (lineForm P Q)| =
      |ScalarCurveInt C (fun s => directionalScalar P Q α (x, y) * diff (fun s : ℝ => s))|)
  : |ScalarCurveInt C (fun s => directionalScalar P Q α (x, y) * diff (fun s : ℝ => s))| ≤
      ScalarCurveInt C (fun s => |directionalScalar P Q α (x, y)| * diff (fun s : ℝ => s)) := by
  sorry

-- GAP 3: trigonometric square identity.
theorem proof_gap_exercise_4277_3
  (C : Set (ℝ × ℝ)) (P Q : ℝ × ℝ -> ℝ) (L M α x y : ℝ)
  (hC : C ⊆ CartesianProd RealSet RealSet)
  (hL : L ∈ RealSet) (hM : M ∈ RealSet) (hα : α ∈ RealSet) (hx : x ∈ RealSet) (hy : y ∈ RealSet)
  (hPcont : ContinuousFuncOn P C) (hQcont : ContinuousFuncOn Q C)
  (hLen : L = ScalarCurveInt C arcSpeedForm)
  (hMax : M = sSup ((fun p : ℝ × ℝ => sqrtn 2 (P p ^ 2 + Q p ^ 2)) '' C))
  : (P (x, y) * Real.cos α + Q (x, y) * Real.sin α) ^ 2 +
      (P (x, y) * Real.sin α - Q (x, y) * Real.cos α) ^ 2 =
      P (x, y) ^ 2 + Q (x, y) ^ 2 := by
  sorry

-- GAP 4: first square is bounded by the sum of squares.
theorem proof_gap_exercise_4277_4
  (C : Set (ℝ × ℝ)) (P Q : ℝ × ℝ -> ℝ) (L M α x y : ℝ)
  (hC : C ⊆ CartesianProd RealSet RealSet)
  (hL : L ∈ RealSet) (hM : M ∈ RealSet) (hα : α ∈ RealSet) (hx : x ∈ RealSet) (hy : y ∈ RealSet)
  (hPcont : ContinuousFuncOn P C) (hQcont : ContinuousFuncOn Q C)
  (hLen : L = ScalarCurveInt C arcSpeedForm)
  (hMax : M = sSup ((fun p : ℝ × ℝ => sqrtn 2 (P p ^ 2 + Q p ^ 2)) '' C))
  (h3 : (P (x, y) * Real.cos α + Q (x, y) * Real.sin α) ^ 2 +
      (P (x, y) * Real.sin α - Q (x, y) * Real.cos α) ^ 2 =
      P (x, y) ^ 2 + Q (x, y) ^ 2)
  : (P (x, y) * Real.cos α + Q (x, y) * Real.sin α) ^ 2 ≤ P (x, y) ^ 2 + Q (x, y) ^ 2 := by
  sorry

-- GAP 5: square bound implies Euclidean norm bound.
theorem proof_gap_exercise_4277_5
  (C : Set (ℝ × ℝ)) (P Q : ℝ × ℝ -> ℝ) (L M α x y : ℝ)
  (hC : C ⊆ CartesianProd RealSet RealSet)
  (hL : L ∈ RealSet) (hM : M ∈ RealSet) (hα : α ∈ RealSet) (hx : x ∈ RealSet) (hy : y ∈ RealSet)
  (hPcont : ContinuousFuncOn P C) (hQcont : ContinuousFuncOn Q C)
  (hLen : L = ScalarCurveInt C arcSpeedForm)
  (hMax : M = sSup ((fun p : ℝ × ℝ => sqrtn 2 (P p ^ 2 + Q p ^ 2)) '' C))
  (h4 : (P (x, y) * Real.cos α + Q (x, y) * Real.sin α) ^ 2 ≤ P (x, y) ^ 2 + Q (x, y) ^ 2)
  : |P (x, y) * Real.cos α + Q (x, y) * Real.sin α| ≤ sqrtn 2 (P (x, y) ^ 2 + Q (x, y) ^ 2) := by
  sorry

-- GAP 6: maximum M bounds the pointwise norm on C.
theorem proof_gap_exercise_4277_6
  (C : Set (ℝ × ℝ)) (P Q : ℝ × ℝ -> ℝ) (L M α x y : ℝ)
  (hC : C ⊆ CartesianProd RealSet RealSet)
  (hL : L ∈ RealSet) (hM : M ∈ RealSet) (hα : α ∈ RealSet) (hx : x ∈ RealSet) (hy : y ∈ RealSet)
  (hp : (x, y) ∈ C)
  (hPcont : ContinuousFuncOn P C) (hQcont : ContinuousFuncOn Q C)
  (hLen : L = ScalarCurveInt C arcSpeedForm)
  (hMax : M = sSup ((fun p : ℝ × ℝ => sqrtn 2 (P p ^ 2 + Q p ^ 2)) '' C))
  : sqrtn 2 (P (x, y) ^ 2 + Q (x, y) ^ 2) ≤ M := by
  sorry

-- GAP 7: combine the pointwise bounds.
theorem proof_gap_exercise_4277_7
  (C : Set (ℝ × ℝ)) (P Q : ℝ × ℝ -> ℝ) (L M α x y : ℝ)
  (hC : C ⊆ CartesianProd RealSet RealSet)
  (hL : L ∈ RealSet) (hM : M ∈ RealSet) (hα : α ∈ RealSet) (hx : x ∈ RealSet) (hy : y ∈ RealSet)
  (hp : (x, y) ∈ C)
  (hPcont : ContinuousFuncOn P C) (hQcont : ContinuousFuncOn Q C)
  (hLen : L = ScalarCurveInt C arcSpeedForm)
  (hMax : M = sSup ((fun p : ℝ × ℝ => sqrtn 2 (P p ^ 2 + Q p ^ 2)) '' C))
  (h5 : |P (x, y) * Real.cos α + Q (x, y) * Real.sin α| ≤ sqrtn 2 (P (x, y) ^ 2 + Q (x, y) ^ 2))
  (h6 : sqrtn 2 (P (x, y) ^ 2 + Q (x, y) ^ 2) ≤ M)
  : |P (x, y) * Real.cos α + Q (x, y) * Real.sin α| ≤ M := by
  sorry

-- GAP 8: monotonicity of scalar curve integral.
theorem proof_gap_exercise_4277_8
  (C : Set (ℝ × ℝ)) (P Q : ℝ × ℝ -> ℝ) (L M α x y : ℝ)
  (hC : C ⊆ CartesianProd RealSet RealSet)
  (hL : L ∈ RealSet) (hM : M ∈ RealSet) (hα : α ∈ RealSet) (hx : x ∈ RealSet) (hy : y ∈ RealSet)
  (hPcont : ContinuousFuncOn P C) (hQcont : ContinuousFuncOn Q C)
  (hLen : L = ScalarCurveInt C arcSpeedForm)
  (hMax : M = sSup ((fun p : ℝ × ℝ => sqrtn 2 (P p ^ 2 + Q p ^ 2)) '' C))
  (h7 : |P (x, y) * Real.cos α + Q (x, y) * Real.sin α| ≤ M)
  : ScalarCurveInt C (fun s => |directionalScalar P Q α (x, y)| * diff (fun s : ℝ => s)) ≤
      ScalarCurveInt C (fun s => M * diff (fun s : ℝ => s)) := by
  sorry

-- GAP 9: pull the constant M out of the scalar curve integral.
theorem proof_gap_exercise_4277_9
  (C : Set (ℝ × ℝ)) (P Q : ℝ × ℝ -> ℝ) (L M α x y : ℝ)
  (hC : C ⊆ CartesianProd RealSet RealSet)
  (hL : L ∈ RealSet) (hM : M ∈ RealSet) (hα : α ∈ RealSet) (hx : x ∈ RealSet) (hy : y ∈ RealSet)
  (hPcont : ContinuousFuncOn P C) (hQcont : ContinuousFuncOn Q C)
  (hLen : L = ScalarCurveInt C arcSpeedForm)
  (hMax : M = sSup ((fun p : ℝ × ℝ => sqrtn 2 (P p ^ 2 + Q p ^ 2)) '' C))
  : ScalarCurveInt C (fun s => M * diff (fun s : ℝ => s)) = M * ScalarCurveInt C arcSpeedForm := by
  sorry

-- GAP 10: identify the arc-length integral as L.
theorem proof_gap_exercise_4277_10
  (C : Set (ℝ × ℝ)) (P Q : ℝ × ℝ -> ℝ) (L M α x y : ℝ)
  (hC : C ⊆ CartesianProd RealSet RealSet)
  (hL : L ∈ RealSet) (hM : M ∈ RealSet) (hα : α ∈ RealSet) (hx : x ∈ RealSet) (hy : y ∈ RealSet)
  (hPcont : ContinuousFuncOn P C) (hQcont : ContinuousFuncOn Q C)
  (hLen : L = ScalarCurveInt C arcSpeedForm)
  (hMax : M = sSup ((fun p : ℝ × ℝ => sqrtn 2 (P p ^ 2 + Q p ^ 2)) '' C))
  : M * ScalarCurveInt C arcSpeedForm = L * M := by
  sorry

-- GAP 11: constant integral equals L*M.
theorem proof_gap_exercise_4277_11
  (C : Set (ℝ × ℝ)) (P Q : ℝ × ℝ -> ℝ) (L M α x y : ℝ)
  (hC : C ⊆ CartesianProd RealSet RealSet)
  (hL : L ∈ RealSet) (hM : M ∈ RealSet) (hα : α ∈ RealSet) (hx : x ∈ RealSet) (hy : y ∈ RealSet)
  (hPcont : ContinuousFuncOn P C) (hQcont : ContinuousFuncOn Q C)
  (hLen : L = ScalarCurveInt C arcSpeedForm)
  (hMax : M = sSup ((fun p : ℝ × ℝ => sqrtn 2 (P p ^ 2 + Q p ^ 2)) '' C))
  (h9 : ScalarCurveInt C (fun s => M * diff (fun s : ℝ => s)) = M * ScalarCurveInt C arcSpeedForm)
  (h10 : M * ScalarCurveInt C arcSpeedForm = L * M)
  : ScalarCurveInt C (fun s => M * diff (fun s : ℝ => s)) = L * M := by
  sorry

-- GAP 12: assemble the estimate.
theorem proof_gap_exercise_4277_12
  (C : Set (ℝ × ℝ)) (P Q : ℝ × ℝ -> ℝ) (L M α x y : ℝ)
  (hC : C ⊆ CartesianProd RealSet RealSet)
  (hL : L ∈ RealSet) (hM : M ∈ RealSet) (hα : α ∈ RealSet) (hx : x ∈ RealSet) (hy : y ∈ RealSet)
  (hPcont : ContinuousFuncOn P C) (hQcont : ContinuousFuncOn Q C)
  (hLen : L = ScalarCurveInt C arcSpeedForm)
  (hMax : M = sSup ((fun p : ℝ × ℝ => sqrtn 2 (P p ^ 2 + Q p ^ 2)) '' C))
  (h1 : |VectorCurveInt C (lineForm P Q)| =
      |ScalarCurveInt C (fun s => directionalScalar P Q α (x, y) * diff (fun s : ℝ => s))|)
  (h2 : |ScalarCurveInt C (fun s => directionalScalar P Q α (x, y) * diff (fun s : ℝ => s))| ≤
      ScalarCurveInt C (fun s => |directionalScalar P Q α (x, y)| * diff (fun s : ℝ => s)))
  (h8 : ScalarCurveInt C (fun s => |directionalScalar P Q α (x, y)| * diff (fun s : ℝ => s)) ≤
      ScalarCurveInt C (fun s => M * diff (fun s : ℝ => s)))
  (h11 : ScalarCurveInt C (fun s => M * diff (fun s : ℝ => s)) = L * M)
  : |VectorCurveInt C (lineForm P Q)| ≤ L * M := by
  sorry

-- GAP 13: final statement repeats the assembled estimate.
theorem proof_gap_exercise_4277_13
  (C : Set (ℝ × ℝ)) (P Q : ℝ × ℝ -> ℝ) (L M α x y : ℝ)
  (hC : C ⊆ CartesianProd RealSet RealSet)
  (hL : L ∈ RealSet) (hM : M ∈ RealSet) (hα : α ∈ RealSet) (hx : x ∈ RealSet) (hy : y ∈ RealSet)
  (hPcont : ContinuousFuncOn P C) (hQcont : ContinuousFuncOn Q C)
  (hLen : L = ScalarCurveInt C arcSpeedForm)
  (hMax : M = sSup ((fun p : ℝ × ℝ => sqrtn 2 (P p ^ 2 + Q p ^ 2)) '' C))
  (h12 : |VectorCurveInt C (lineForm P Q)| ≤ L * M)
  : |VectorCurveInt C (lineForm P Q)| ≤ L * M := by
  sorry

