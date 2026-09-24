import Mathlib

set_option linter.style.longLine false

noncomputable section

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

abbrev RealSet : Set ℝ := Set.univ
abbrev NonNegIntegerSet : Set ℕ := Set.univ
abbrev PosIntegerSet : Set ℕ := {n | 0 < n}
abbrev CartesianProd (A B : Set ℝ) : Set (ℝ × ℝ) := Set.prod A B
abbrev sqrtn (n : ℕ) (x : ℝ) : ℝ := Real.rpow x ((n : ℝ)⁻¹)
abbrev DefInt (a b : ℝ) (f : ℝ -> ℝ) : ℝ := ∫ t in a..b, f t
abbrev diff {α : Type*} (f : α -> ℝ) : ℝ := 1
abbrev FunDeri (u : ℝ × ℝ -> ℝ) (coord order : ℕ) : ℝ × ℝ -> ℝ := u
abbrev totalDiff (z : ℝ × ℝ -> ℝ) : ℝ := 0

def logKernel (r : ℝ × ℝ -> ℝ) : ℝ × ℝ -> ℝ :=
  fun p => Real.log (1 /. r p)

def atanKernel : ℝ × ℝ -> ℝ :=
  fun p => Real.arctan (p.1 /. p.2)

def upperPotential (n m : ℕ) (C₁ : ℝ) : ℝ × ℝ -> ℝ :=
  fun p => FunDeri (FunDeri atanKernel 1 n) 2 m p + C₁

def lowerPotential (n m : ℕ) (C₂ : ℝ) : ℝ × ℝ -> ℝ :=
  fun p => FunDeri (FunDeri atanKernel 1 n) 2 m p + C₂

def halfPlanePotential (n m : ℕ) (C₁ C₂ : ℝ) : ℝ × ℝ -> ℝ :=
  fun p => if 0 < p.2 then upperPotential n m C₁ p else lowerPotential n m C₂ p

-- exercise: exercise_4276

-- GAP 1: x-partial of log(1/r).
theorem proof_gap_exercise_4276_1
  (z r P Q : ℝ × ℝ -> ℝ) (n m : ℕ) (C₁ C₂ : ℝ)
  (hn0 : n ∈ NonNegIntegerSet) (hm0 : m ∈ NonNegIntegerSet)
  (hC1 : C₁ ∈ RealSet) (hC2 : C₂ ∈ RealSet)
  (hn : n ∈ PosIntegerSet) (hm : m ∈ PosIntegerSet)
  (hr : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet -> r (x, y) = sqrtn 2 (x ^ 2 + y ^ 2))
  (hne : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet -> (x, y) ≠ ((0 : ℝ), (0 : ℝ)))
  : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet ∧ (x, y) ≠ ((0 : ℝ), (0 : ℝ)) ->
      FunDeri (logKernel r) 1 1 (x, y) = -(x /. (r (x, y) ^ 2)) := by
  sorry

-- GAP 2: y-partial of log(1/r).
theorem proof_gap_exercise_4276_2
  (z r P Q : ℝ × ℝ -> ℝ) (n m : ℕ) (C₁ C₂ : ℝ)
  (hn0 : n ∈ NonNegIntegerSet) (hm0 : m ∈ NonNegIntegerSet)
  (hC1 : C₁ ∈ RealSet) (hC2 : C₂ ∈ RealSet)
  (hn : n ∈ PosIntegerSet) (hm : m ∈ PosIntegerSet)
  (hr : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet -> r (x, y) = sqrtn 2 (x ^ 2 + y ^ 2))
  (hne : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet -> (x, y) ≠ ((0 : ℝ), (0 : ℝ)))
  (h1 : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet ∧ (x, y) ≠ ((0 : ℝ), (0 : ℝ)) ->
      FunDeri (logKernel r) 1 1 (x, y) = -(x /. (r (x, y) ^ 2)))
  : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet ∧ (x, y) ≠ ((0 : ℝ), (0 : ℝ)) ->
      FunDeri (logKernel r) 2 1 (x, y) = -(y /. (r (x, y) ^ 2)) := by
  sorry

-- GAP 3: harmonicity away from the origin.
theorem proof_gap_exercise_4276_3
  (z r P Q : ℝ × ℝ -> ℝ) (n m : ℕ) (C₁ C₂ : ℝ)
  (hn0 : n ∈ NonNegIntegerSet) (hm0 : m ∈ NonNegIntegerSet)
  (hC1 : C₁ ∈ RealSet) (hC2 : C₂ ∈ RealSet)
  (hn : n ∈ PosIntegerSet) (hm : m ∈ PosIntegerSet)
  (hr : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet -> r (x, y) = sqrtn 2 (x ^ 2 + y ^ 2))
  (hne : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet -> (x, y) ≠ ((0 : ℝ), (0 : ℝ)))
  (h1 : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet ∧ (x, y) ≠ ((0 : ℝ), (0 : ℝ)) ->
      FunDeri (logKernel r) 1 1 (x, y) = -(x /. (r (x, y) ^ 2)))
  (h2 : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet ∧ (x, y) ≠ ((0 : ℝ), (0 : ℝ)) ->
      FunDeri (logKernel r) 2 1 (x, y) = -(y /. (r (x, y) ^ 2)))
  : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet ∧ (x, y) ≠ ((0 : ℝ), (0 : ℝ)) ->
      FunDeri (logKernel r) 1 2 (x, y) + FunDeri (logKernel r) 2 2 (x, y) = 0 := by
  sorry

-- GAP 4: curl identity for P and Q.
theorem proof_gap_exercise_4276_4
  (z r P Q : ℝ × ℝ -> ℝ) (n m : ℕ) (C₁ C₂ : ℝ)
  (hn0 : n ∈ NonNegIntegerSet) (hm0 : m ∈ NonNegIntegerSet)
  (hC1 : C₁ ∈ RealSet) (hC2 : C₂ ∈ RealSet)
  (hn : n ∈ PosIntegerSet) (hm : m ∈ PosIntegerSet)
  (hr : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet -> r (x, y) = sqrtn 2 (x ^ 2 + y ^ 2))
  (hne : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet -> (x, y) ≠ ((0 : ℝ), (0 : ℝ)))
  (hlap : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet ∧ (x, y) ≠ ((0 : ℝ), (0 : ℝ)) ->
      FunDeri (logKernel r) 1 2 (x, y) + FunDeri (logKernel r) 2 2 (x, y) = 0)
  (hP : P = FunDeri (FunDeri (logKernel r) 1 (n + 2)) 2 (m - 1))
  (hQ : Q = fun p => - FunDeri (FunDeri (logKernel r) 1 (n - 1)) 2 (m + 2) p)
  : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet ∧ (x, y) ≠ ((0 : ℝ), (0 : ℝ)) ->
      FunDeri P 2 1 (x, y) - FunDeri Q 1 1 (x, y) =
        FunDeri (FunDeri (fun p => FunDeri (logKernel r) 1 2 p + FunDeri (logKernel r) 2 2 p) 1 n) 2 m (x, y) := by
  sorry

-- GAP 5: differentiating the zero Laplacian remains zero.
theorem proof_gap_exercise_4276_5
  (z r P Q : ℝ × ℝ -> ℝ) (n m : ℕ) (C₁ C₂ : ℝ)
  (hn0 : n ∈ NonNegIntegerSet) (hm0 : m ∈ NonNegIntegerSet)
  (hC1 : C₁ ∈ RealSet) (hC2 : C₂ ∈ RealSet)
  (hn : n ∈ PosIntegerSet) (hm : m ∈ PosIntegerSet)
  (hr : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet -> r (x, y) = sqrtn 2 (x ^ 2 + y ^ 2))
  (hne : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet -> (x, y) ≠ ((0 : ℝ), (0 : ℝ)))
  (hlap : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet ∧ (x, y) ≠ ((0 : ℝ), (0 : ℝ)) ->
      FunDeri (logKernel r) 1 2 (x, y) + FunDeri (logKernel r) 2 2 (x, y) = 0)
  (hcurl : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet ∧ (x, y) ≠ ((0 : ℝ), (0 : ℝ)) ->
      FunDeri P 2 1 (x, y) - FunDeri Q 1 1 (x, y) =
        FunDeri (FunDeri (fun p => FunDeri (logKernel r) 1 2 p + FunDeri (logKernel r) 2 2 p) 1 n) 2 m (x, y))
  : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet ∧ (x, y) ≠ ((0 : ℝ), (0 : ℝ)) ->
      FunDeri (FunDeri (fun p => FunDeri (logKernel r) 1 2 p + FunDeri (logKernel r) 2 2 p) 1 n) 2 m (x, y) = 0 := by
  sorry

-- GAP 6: curl vanishes.
theorem proof_gap_exercise_4276_6
  (z r P Q : ℝ × ℝ -> ℝ) (n m : ℕ) (C₁ C₂ : ℝ)
  (hn0 : n ∈ NonNegIntegerSet) (hm0 : m ∈ NonNegIntegerSet)
  (hC1 : C₁ ∈ RealSet) (hC2 : C₂ ∈ RealSet)
  (hn : n ∈ PosIntegerSet) (hm : m ∈ PosIntegerSet)
  (hr : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet -> r (x, y) = sqrtn 2 (x ^ 2 + y ^ 2))
  (hne : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet -> (x, y) ≠ ((0 : ℝ), (0 : ℝ)))
  (hcurl : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet ∧ (x, y) ≠ ((0 : ℝ), (0 : ℝ)) ->
      FunDeri P 2 1 (x, y) - FunDeri Q 1 1 (x, y) =
        FunDeri (FunDeri (fun p => FunDeri (logKernel r) 1 2 p + FunDeri (logKernel r) 2 2 p) 1 n) 2 m (x, y))
  (hzero : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet ∧ (x, y) ≠ ((0 : ℝ), (0 : ℝ)) ->
      FunDeri (FunDeri (fun p => FunDeri (logKernel r) 1 2 p + FunDeri (logKernel r) 2 2 p) 1 n) 2 m (x, y) = 0)
  : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet ∧ (x, y) ≠ ((0 : ℝ), (0 : ℝ)) ->
      FunDeri P 2 1 (x, y) - FunDeri Q 1 1 (x, y) = 0 := by
  sorry

-- GAP 7: upper half-plane integral formula.
theorem proof_gap_exercise_4276_7
  (z r P Q : ℝ × ℝ -> ℝ) (n m : ℕ) (C₁ C₂ : ℝ)
  (hn0 : n ∈ NonNegIntegerSet) (hm0 : m ∈ NonNegIntegerSet)
  (hC1 : C₁ ∈ RealSet) (hC2 : C₂ ∈ RealSet)
  (hn : n ∈ PosIntegerSet) (hm : m ∈ PosIntegerSet)
  (hcurl0 : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet ∧ (x, y) ≠ ((0 : ℝ), (0 : ℝ)) ->
      FunDeri P 2 1 (x, y) - FunDeri Q 1 1 (x, y) = 0)
  : ∀ y : ℝ, y ∈ RealSet ∧ y > 0 -> ∀ x : ℝ, x ∈ RealSet ∧ y > 0 ->
      z (x, y) =
        DefInt 0 x (fun x' => P (x', y) * diff (fun x' : ℝ => x')) +
        DefInt 1 y (fun y' => Q (0, y') * diff (fun y' : ℝ => y')) + C₁ := by
  sorry

-- GAP 8: upper half-plane antiderivative.
theorem proof_gap_exercise_4276_8
  (z r P Q : ℝ × ℝ -> ℝ) (n m : ℕ) (C₁ C₂ : ℝ)
  (hn0 : n ∈ NonNegIntegerSet) (hm0 : m ∈ NonNegIntegerSet)
  (hC1 : C₁ ∈ RealSet) (hC2 : C₂ ∈ RealSet)
  (hn : n ∈ PosIntegerSet) (hm : m ∈ PosIntegerSet)
  (hupper : ∀ y : ℝ, y ∈ RealSet ∧ y > 0 -> ∀ x : ℝ, x ∈ RealSet ∧ y > 0 ->
      z (x, y) =
        DefInt 0 x (fun x' => P (x', y) * diff (fun x' : ℝ => x')) +
        DefInt 1 y (fun y' => Q (0, y') * diff (fun y' : ℝ => y')) + C₁)
  : ∀ y : ℝ, y ∈ RealSet ∧ y > 0 -> ∀ x : ℝ, x ∈ RealSet ∧ y > 0 ->
      z (x, y) = upperPotential n m C₁ (x, y) := by
  sorry

-- GAP 9: lower half-plane integral formula.
theorem proof_gap_exercise_4276_9
  (z r P Q : ℝ × ℝ -> ℝ) (n m : ℕ) (C₁ C₂ : ℝ)
  (hn0 : n ∈ NonNegIntegerSet) (hm0 : m ∈ NonNegIntegerSet)
  (hC1 : C₁ ∈ RealSet) (hC2 : C₂ ∈ RealSet)
  (hn : n ∈ PosIntegerSet) (hm : m ∈ PosIntegerSet)
  (hupperPot : ∀ y : ℝ, y ∈ RealSet ∧ y > 0 -> ∀ x : ℝ, x ∈ RealSet ∧ y > 0 ->
      z (x, y) = upperPotential n m C₁ (x, y))
  : ∀ y : ℝ, y ∈ RealSet ∧ y < 0 -> ∀ x : ℝ, x ∈ RealSet ∧ y < 0 ->
      z (x, y) =
        DefInt 0 x (fun x' => P (x', y) * diff (fun x' : ℝ => x')) +
        DefInt (-1) y (fun y' => Q (0, y') * diff (fun y' : ℝ => y')) + C₂ := by
  sorry

-- GAP 10: lower half-plane antiderivative.
theorem proof_gap_exercise_4276_10
  (z r P Q : ℝ × ℝ -> ℝ) (n m : ℕ) (C₁ C₂ : ℝ)
  (hn0 : n ∈ NonNegIntegerSet) (hm0 : m ∈ NonNegIntegerSet)
  (hC1 : C₁ ∈ RealSet) (hC2 : C₂ ∈ RealSet)
  (hn : n ∈ PosIntegerSet) (hm : m ∈ PosIntegerSet)
  (hlower : ∀ y : ℝ, y ∈ RealSet ∧ y < 0 -> ∀ x : ℝ, x ∈ RealSet ∧ y < 0 ->
      z (x, y) =
        DefInt 0 x (fun x' => P (x', y) * diff (fun x' : ℝ => x')) +
        DefInt (-1) y (fun y' => Q (0, y') * diff (fun y' : ℝ => y')) + C₂)
  : ∀ y : ℝ, y ∈ RealSet ∧ y < 0 -> ∀ x : ℝ, x ∈ RealSet ∧ y < 0 ->
      z (x, y) = lowerPotential n m C₂ (x, y) := by
  sorry

-- GAP 11: piecewise upper/lower potential yields the requested differential form.
theorem proof_gap_exercise_4276_11
  (z r P Q : ℝ × ℝ -> ℝ) (n m : ℕ) (C₁ C₂ : ℝ)
  (hn0 : n ∈ NonNegIntegerSet) (hm0 : m ∈ NonNegIntegerSet)
  (hC1 : C₁ ∈ RealSet) (hC2 : C₂ ∈ RealSet)
  (hn : n ∈ PosIntegerSet) (hm : m ∈ PosIntegerSet)
  (hP : P = FunDeri (FunDeri (logKernel r) 1 (n + 2)) 2 (m - 1))
  (hQ : Q = fun p => - FunDeri (FunDeri (logKernel r) 1 (n - 1)) 2 (m + 2) p)
  (hupper : ∀ y : ℝ, y ∈ RealSet ∧ y > 0 -> ∀ x : ℝ, x ∈ RealSet ∧ y > 0 ->
      z (x, y) = upperPotential n m C₁ (x, y))
  (hlower : ∀ y : ℝ, y ∈ RealSet ∧ y < 0 -> ∀ x : ℝ, x ∈ RealSet ∧ y < 0 ->
      z (x, y) = lowerPotential n m C₂ (x, y))
  : ∀ x : ℝ, x ∈ RealSet -> ∀ y : ℝ, y ∈ RealSet ∧ y ≠ 0 ∧ z (x, y) = halfPlanePotential n m C₁ C₂ (x, y) ->
      totalDiff z =
        (FunDeri (FunDeri (logKernel r) 1 (n + 2)) 2 (m - 1) (x, y)) * diff (fun p : ℝ × ℝ => p.1) -
        (FunDeri (FunDeri (logKernel r) 1 (n - 1)) 2 (m + 2) (x, y)) * diff (fun p : ℝ × ℝ => p.2) := by
  sorry

