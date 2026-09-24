import Mathlib

set_option linter.style.longLine false

-- Real-valued suprema and infima; all source gaps retained verbatim below.

/- Exercise 1458, gap 1
PROOF GAP @1
ASSUM:
1. P : RealSet → RealSet
2. q ∈ RealSet
3. E_{P} ∈ RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ P(x) = x^{2} + q
5. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ E_{P} = sup({ |P(x)| | x ∈ [-1, 1] })

GOAL:
forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-1, 1) ⇒ FunDeri(P, 1, 1)(x) = 2 * x

METHOD:

-/
theorem proof_gap_exercise_1458_1
  (P : ℝ → ℝ) (q E_P : ℝ)
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : E_P ∈ (Set.univ : Set ℝ))
  (h4 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Icc (-1 : ℝ) 1 → P x = x ^ 2 + q)
  (h5 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Icc (-1 : ℝ) 1 → E_P = sSup ((fun t : ℝ => |P t|) '' Set.Icc (-1 : ℝ) 1))
  : (∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Ioo (-1 : ℝ) 1 → deriv P x = 2 * x) := by
  sorry

/- Exercise 1458, gap 2
PROOF GAP @2
ASSUM:
1. P : RealSet → RealSet
2. q ∈ RealSet
3. E_{P} ∈ RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ P(x) = x^{2} + q
5. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ E_{P} = sup({ |P(x)| | x ∈ [-1, 1] })
6. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-1, 1) ⇒ FunDeri(P, 1, 1)(x) = 2 * x

GOAL:
forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-1, 1) ⇒ (FunDeri(P, 1, 1)(x) = 0 ⇔ x = 0)

METHOD:

-/
theorem proof_gap_exercise_1458_2
  (P : ℝ → ℝ) (q E_P : ℝ)
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : E_P ∈ (Set.univ : Set ℝ))
  (h4 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Icc (-1 : ℝ) 1 → P x = x ^ 2 + q)
  (h5 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Icc (-1 : ℝ) 1 → E_P = sSup ((fun t : ℝ => |P t|) '' Set.Icc (-1 : ℝ) 1))
  (h6 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Ioo (-1 : ℝ) 1 → deriv P x = 2 * x)
  : (∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Ioo (-1 : ℝ) 1 → (deriv P x = 0 ↔ x = 0)) := by
  sorry

/- Exercise 1458, gap 3
PROOF GAP @3
ASSUM:
1. P : RealSet → RealSet
2. q ∈ RealSet
3. E_{P} ∈ RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ P(x) = x^{2} + q
5. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ E_{P} = sup({ |P(x)| | x ∈ [-1, 1] })
6. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-1, 1) ⇒ FunDeri(P, 1, 1)(x) = 2 * x
7. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-1, 1) ⇒ (FunDeri(P, 1, 1)(x) = 0 ⇔ x = 0)

GOAL:
E_{P} = max({ |P(0)|, |P(1)|, |P(-1)| })

METHOD:

-/
theorem proof_gap_exercise_1458_3
  (P : ℝ → ℝ) (q E_P : ℝ)
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : E_P ∈ (Set.univ : Set ℝ))
  (h4 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Icc (-1 : ℝ) 1 → P x = x ^ 2 + q)
  (h5 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Icc (-1 : ℝ) 1 → E_P = sSup ((fun t : ℝ => |P t|) '' Set.Icc (-1 : ℝ) 1))
  (h6 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Ioo (-1 : ℝ) 1 → deriv P x = 2 * x)
  (h7 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Ioo (-1 : ℝ) 1 → (deriv P x = 0 ↔ x = 0))
  : (E_P = max |P 0| (max |P 1| |P (-1)|)) := by
  sorry

/- Exercise 1458, gap 4
PROOF GAP @4
ASSUM:
1. P : RealSet → RealSet
2. q ∈ RealSet
3. E_{P} ∈ RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ P(x) = x^{2} + q
5. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ E_{P} = sup({ |P(x)| | x ∈ [-1, 1] })
6. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-1, 1) ⇒ FunDeri(P, 1, 1)(x) = 2 * x
7. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-1, 1) ⇒ (FunDeri(P, 1, 1)(x) = 0 ⇔ x = 0)
8. E_{P} = max({ |P(0)|, |P(1)|, |P(-1)| })

GOAL:
E_{P} = max({ |q|, |1 + q| })

METHOD:

-/
theorem proof_gap_exercise_1458_4
  (P : ℝ → ℝ) (q E_P : ℝ)
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : E_P ∈ (Set.univ : Set ℝ))
  (h4 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Icc (-1 : ℝ) 1 → P x = x ^ 2 + q)
  (h5 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Icc (-1 : ℝ) 1 → E_P = sSup ((fun t : ℝ => |P t|) '' Set.Icc (-1 : ℝ) 1))
  (h6 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Ioo (-1 : ℝ) 1 → deriv P x = 2 * x)
  (h7 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Ioo (-1 : ℝ) 1 → (deriv P x = 0 ↔ x = 0))
  (h8 : E_P = max |P 0| (max |P 1| |P (-1)|))
  : (E_P = max |q| |1 + q|) := by
  sorry

/- Exercise 1458, gap 5
PROOF GAP @5
ASSUM:
1. P : RealSet → RealSet
2. q ∈ RealSet
3. E_{P} ∈ RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ P(x) = x^{2} + q
5. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ E_{P} = sup({ |P(x)| | x ∈ [-1, 1] })
6. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-1, 1) ⇒ FunDeri(P, 1, 1)(x) = 2 * x
7. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-1, 1) ⇒ (FunDeri(P, 1, 1)(x) = 0 ⇔ x = 0)
8. E_{P} = max({ |P(0)|, |P(1)|, |P(-1)| })
9. E_{P} = max({ |q|, |1 + q| })

GOAL:
|q| = |1 + q| ⇒ E_{P} = min({ max({ |r|, |1 + r| }) | r ∈ RealSet })

METHOD:

-/
theorem proof_gap_exercise_1458_5
  (P : ℝ → ℝ) (q E_P : ℝ)
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : E_P ∈ (Set.univ : Set ℝ))
  (h4 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Icc (-1 : ℝ) 1 → P x = x ^ 2 + q)
  (h5 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Icc (-1 : ℝ) 1 → E_P = sSup ((fun t : ℝ => |P t|) '' Set.Icc (-1 : ℝ) 1))
  (h6 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Ioo (-1 : ℝ) 1 → deriv P x = 2 * x)
  (h7 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Ioo (-1 : ℝ) 1 → (deriv P x = 0 ↔ x = 0))
  (h8 : E_P = max |P 0| (max |P 1| |P (-1)|))
  (h9 : E_P = max |q| |1 + q|)
  : (|q| = |1 + q| → E_P = sInf (Set.range (fun r : ℝ => max |r| |1 + r|))) := by
  sorry

/- Exercise 1458, gap 6
PROOF GAP @6
ASSUM:
1. P : RealSet → RealSet
2. q ∈ RealSet
3. E_{P} ∈ RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ P(x) = x^{2} + q
5. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ E_{P} = sup({ |P(x)| | x ∈ [-1, 1] })
6. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-1, 1) ⇒ FunDeri(P, 1, 1)(x) = 2 * x
7. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-1, 1) ⇒ (FunDeri(P, 1, 1)(x) = 0 ⇔ x = 0)
8. E_{P} = max({ |P(0)|, |P(1)|, |P(-1)| })
9. E_{P} = max({ |q|, |1 + q| })
10. |q| = |1 + q| ⇒ E_{P} = min({ max({ |r|, |1 + r| }) | r ∈ RealSet })

GOAL:
q = -frac(1, 2) ⇒ |q| = |1 + q|

METHOD:

-/
theorem proof_gap_exercise_1458_6
  (P : ℝ → ℝ) (q E_P : ℝ)
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : E_P ∈ (Set.univ : Set ℝ))
  (h4 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Icc (-1 : ℝ) 1 → P x = x ^ 2 + q)
  (h5 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Icc (-1 : ℝ) 1 → E_P = sSup ((fun t : ℝ => |P t|) '' Set.Icc (-1 : ℝ) 1))
  (h6 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Ioo (-1 : ℝ) 1 → deriv P x = 2 * x)
  (h7 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Ioo (-1 : ℝ) 1 → (deriv P x = 0 ↔ x = 0))
  (h8 : E_P = max |P 0| (max |P 1| |P (-1)|))
  (h9 : E_P = max |q| |1 + q|)
  (h10 : |q| = |1 + q| → E_P = sInf (Set.range (fun r : ℝ => max |r| |1 + r|)))
  : (q = -(1 : ℝ) / 2 → |q| = |1 + q|) := by
  sorry

/- Exercise 1458, gap 7
PROOF GAP @7
ASSUM:
1. P : RealSet → RealSet
2. q ∈ RealSet
3. E_{P} ∈ RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ P(x) = x^{2} + q
5. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ E_{P} = sup({ |P(x)| | x ∈ [-1, 1] })
6. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-1, 1) ⇒ FunDeri(P, 1, 1)(x) = 2 * x
7. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-1, 1) ⇒ (FunDeri(P, 1, 1)(x) = 0 ⇔ x = 0)
8. E_{P} = max({ |P(0)|, |P(1)|, |P(-1)| })
9. E_{P} = max({ |q|, |1 + q| })
10. |q| = |1 + q| ⇒ E_{P} = min({ max({ |r|, |1 + r| }) | r ∈ RealSet })
11. q = -frac(1, 2) ⇒ |q| = |1 + q|

GOAL:
q = -frac(1, 2) ⇒ E_{P} = min({ max({ |r|, |1 + r| }) | r ∈ RealSet })

METHOD:

-/
theorem proof_gap_exercise_1458_7
  (P : ℝ → ℝ) (q E_P : ℝ)
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : E_P ∈ (Set.univ : Set ℝ))
  (h4 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Icc (-1 : ℝ) 1 → P x = x ^ 2 + q)
  (h5 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Icc (-1 : ℝ) 1 → E_P = sSup ((fun t : ℝ => |P t|) '' Set.Icc (-1 : ℝ) 1))
  (h6 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Ioo (-1 : ℝ) 1 → deriv P x = 2 * x)
  (h7 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Ioo (-1 : ℝ) 1 → (deriv P x = 0 ↔ x = 0))
  (h8 : E_P = max |P 0| (max |P 1| |P (-1)|))
  (h9 : E_P = max |q| |1 + q|)
  (h10 : |q| = |1 + q| → E_P = sInf (Set.range (fun r : ℝ => max |r| |1 + r|)))
  (h11 : q = -(1 : ℝ) / 2 → |q| = |1 + q|)
  : (q = -(1 : ℝ) / 2 → E_P = sInf (Set.range (fun r : ℝ => max |r| |1 + r|))) := by
  sorry

/- Exercise 1458, gap 8
PROOF GAP @8
ASSUM:
1. P : RealSet → RealSet
2. q ∈ RealSet
3. E_{P} ∈ RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ P(x) = x^{2} + q
5. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ E_{P} = sup({ |P(x)| | x ∈ [-1, 1] })
6. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-1, 1) ⇒ FunDeri(P, 1, 1)(x) = 2 * x
7. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-1, 1) ⇒ (FunDeri(P, 1, 1)(x) = 0 ⇔ x = 0)
8. E_{P} = max({ |P(0)|, |P(1)|, |P(-1)| })
9. E_{P} = max({ |q|, |1 + q| })
10. |q| = |1 + q| ⇒ E_{P} = min({ max({ |r|, |1 + r| }) | r ∈ RealSet })
11. q = -frac(1, 2) ⇒ |q| = |1 + q|
12. q = -frac(1, 2) ⇒ E_{P} = min({ max({ |r|, |1 + r| }) | r ∈ RealSet })

GOAL:
q = -frac(1, 2)

METHOD:

-/
theorem proof_gap_exercise_1458_8
  (P : ℝ → ℝ) (q E_P : ℝ)
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : E_P ∈ (Set.univ : Set ℝ))
  (h4 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Icc (-1 : ℝ) 1 → P x = x ^ 2 + q)
  (h5 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Icc (-1 : ℝ) 1 → E_P = sSup ((fun t : ℝ => |P t|) '' Set.Icc (-1 : ℝ) 1))
  (h6 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Ioo (-1 : ℝ) 1 → deriv P x = 2 * x)
  (h7 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Ioo (-1 : ℝ) 1 → (deriv P x = 0 ↔ x = 0))
  (h8 : E_P = max |P 0| (max |P 1| |P (-1)|))
  (h9 : E_P = max |q| |1 + q|)
  (h10 : |q| = |1 + q| → E_P = sInf (Set.range (fun r : ℝ => max |r| |1 + r|)))
  (h11 : q = -(1 : ℝ) / 2 → |q| = |1 + q|)
  (h12 : q = -(1 : ℝ) / 2 → E_P = sInf (Set.range (fun r : ℝ => max |r| |1 + r|)))
  : (q = -(1 : ℝ) / 2) := by
  sorry

/- Exercise 1458, gap 9
PROOF GAP @9
ASSUM:
1. P : RealSet → RealSet
2. q ∈ RealSet
3. E_{P} ∈ RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ P(x) = x^{2} + q
5. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ E_{P} = sup({ |P(x)| | x ∈ [-1, 1] })
6. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-1, 1) ⇒ FunDeri(P, 1, 1)(x) = 2 * x
7. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(-1, 1) ⇒ (FunDeri(P, 1, 1)(x) = 0 ⇔ x = 0)
8. E_{P} = max({ |P(0)|, |P(1)|, |P(-1)| })
9. E_{P} = max({ |q|, |1 + q| })
10. |q| = |1 + q| ⇒ E_{P} = min({ max({ |r|, |1 + r| }) | r ∈ RealSet })
11. q = -frac(1, 2) ⇒ |q| = |1 + q|
12. q = -frac(1, 2) ⇒ E_{P} = min({ max({ |r|, |1 + r| }) | r ∈ RealSet })
13. q = -frac(1, 2)

GOAL:
q = -frac(1, 2) ⇒ (forall (r), r ∈ RealSet ⇒ sup({ |x^{2} + q| | x ∈ [-1, 1] }) ≤ sup({ |x^{2} + r| | x ∈ [-1, 1] }))

METHOD:

-/
theorem proof_gap_exercise_1458_9
  (P : ℝ → ℝ) (q E_P : ℝ)
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : E_P ∈ (Set.univ : Set ℝ))
  (h4 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Icc (-1 : ℝ) 1 → P x = x ^ 2 + q)
  (h5 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Icc (-1 : ℝ) 1 → E_P = sSup ((fun t : ℝ => |P t|) '' Set.Icc (-1 : ℝ) 1))
  (h6 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Ioo (-1 : ℝ) 1 → deriv P x = 2 * x)
  (h7 : ∀ x : ℝ, x ∈ Set.univ ∧ x ∈ Set.Ioo (-1 : ℝ) 1 → (deriv P x = 0 ↔ x = 0))
  (h8 : E_P = max |P 0| (max |P 1| |P (-1)|))
  (h9 : E_P = max |q| |1 + q|)
  (h10 : |q| = |1 + q| → E_P = sInf (Set.range (fun r : ℝ => max |r| |1 + r|)))
  (h11 : q = -(1 : ℝ) / 2 → |q| = |1 + q|)
  (h12 : q = -(1 : ℝ) / 2 → E_P = sInf (Set.range (fun r : ℝ => max |r| |1 + r|)))
  (h13 : q = -(1 : ℝ) / 2)
  : (q = -(1 : ℝ) / 2 → ∀ r : ℝ, r ∈ Set.univ → sSup ((fun x : ℝ => |x ^ 2 + q|) '' Set.Icc (-1 : ℝ) 1) ≤ sSup ((fun x : ℝ => |x ^ 2 + r|) '' Set.Icc (-1 : ℝ) 1)) := by
  sorry
