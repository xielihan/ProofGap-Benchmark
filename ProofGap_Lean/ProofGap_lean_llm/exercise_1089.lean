import Mathlib

-- Differentials are continuous linear maps, restricted as fields to the stated domain.
namespace Exercise1089

abbrev Domain (a : ℝ) := {t : ℝ // |t| < |a|}

noncomputable def coefficient (a : ℝ) (t : Domain a) : ℝ :=
  (SignType.sign a : ℝ) / Real.sqrt (a ^ 2 - (t : ℝ) ^ 2)

noncomputable def differentialOn (a : ℝ) (f : ℝ → ℝ) :
    Domain a → (ℝ →L[ℝ] ℝ) :=
  fun t => fderiv ℝ f (t : ℝ)

end Exercise1089

/- Exercise 1089, gap 1
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet ∧ a ≠ 0
3. x ∈ RealSet ∧ |x| < |a|
4. forall (x), x ∈ RealSet ∧ |x| < |a| ⇒ y(x) = arcsin(frac(x, a))

GOAL:
forall (x), x ∈ RealSet ∧ |x| < |a| ⇒ FunDeri(y, 1, 1)(x) = frac(|a|, sqrtn(2, a^{2} - x^{2})) * frac(1, a) ∧ frac(|a|, sqrtn(2, a^{2} - x^{2})) * frac(1, a) = frac(sgn(a), sqrtn(2, a^{2} - x^{2}))

METHOD:

-/
theorem proof_gap_exercise_1089_1
  (y : ℝ → ℝ) (a x : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a ≠ 0)
  (hx : x ∈ (Set.univ : Set ℝ) ∧ |x| < |a|)
  (hy : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ |t| < |a| →
    y t = Real.arcsin (t / a))
  : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ |t| < |a| →
    deriv y t = (|a| / Real.sqrt (a ^ 2 - t ^ 2)) * (1 / a) ∧
    (|a| / Real.sqrt (a ^ 2 - t ^ 2)) * (1 / a) =
      (SignType.sign a : ℝ) / Real.sqrt (a ^ 2 - t ^ 2) := by
  sorry

/- Exercise 1089, gap 2
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet ∧ a ≠ 0
3. x ∈ RealSet ∧ |x| < |a|
4. forall (x), x ∈ RealSet ∧ |x| < |a| ⇒ y(x) = arcsin(frac(x, a))
5. forall (x), x ∈ RealSet ∧ |x| < |a| ⇒ FunDeri(y, 1, 1)(x) = frac(|a|, sqrtn(2, a^{2} - x^{2})) * frac(1, a) ∧ frac(|a|, sqrtn(2, a^{2} - x^{2})) * frac(1, a) = frac(sgn(a), sqrtn(2, a^{2} - x^{2}))

GOAL:
forall (x), x ∈ RealSet ∧ |x| < |a| ⇒ diff(y) = (fun x [x ∈ RealSet ∧ |x| < |a|] . frac(sgn(a), sqrtn(2, a^{2} - x^{2}))) * diff(fun x [x ∈ RealSet] . x)

METHOD:

-/
theorem proof_gap_exercise_1089_2
  (y : ℝ → ℝ) (a x : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a ≠ 0)
  (hx : x ∈ (Set.univ : Set ℝ) ∧ |x| < |a|)
  (hy : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ |t| < |a| →
    y t = Real.arcsin (t / a))
  (hderiv : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ |t| < |a| →
    deriv y t = (|a| / Real.sqrt (a ^ 2 - t ^ 2)) * (1 / a) ∧
    (|a| / Real.sqrt (a ^ 2 - t ^ 2)) * (1 / a) =
      (SignType.sign a : ℝ) / Real.sqrt (a ^ 2 - t ^ 2))
  : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ |t| < |a| →
    Exercise1089.differentialOn a y =
      (fun u : Exercise1089.Domain a =>
        Exercise1089.coefficient a u •
          Exercise1089.differentialOn a (fun v : ℝ => v) u) := by
  sorry
