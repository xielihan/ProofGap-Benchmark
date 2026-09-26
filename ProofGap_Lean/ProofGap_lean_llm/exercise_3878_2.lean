import Mathlib

set_option linter.style.longLine false

open MeasureTheory
open scoped Real

noncomputable section

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def improperIntegral (f : ℝ -> ℝ) : ℝ := ∫ t in Set.Ioi (0 : ℝ), f t ∂volume
def improperIntegrable (f : ℝ -> ℝ) : Prop := IntegrableOn f (Set.Ioi (0 : ℝ)) volume
def funDeri (f : ℝ -> ℝ) (n : ℕ) (a : ℝ) : ℝ := iteratedDeriv n f a

def e3878CosKernel (x lam alpha t : ℝ) : ℝ :=
  Real.rpow t (x - 1) * Real.exp (-lam * t * Real.cos alpha) * Real.cos (lam * t * Real.sin alpha)

def e3878SinKernel (x lam alpha t : ℝ) : ℝ :=
  Real.rpow t (x - 1) * Real.exp (-lam * t * Real.cos alpha) * Real.sin (lam * t * Real.sin alpha)

def e3878BaseKernel (x lam alpha t : ℝ) : ℝ :=
  Real.rpow t (x - 1) * Real.exp (-lam * t * Real.cos alpha)

def e3878LapKernel (x lam t : ℝ) : ℝ :=
  Real.rpow t (x - 1) * Real.exp (-lam * t)

def e3878DerivKernel (x lam alpha t : ℝ) : ℝ :=
  lam * Real.rpow t x * Real.exp (-lam * t * Real.cos alpha) *
    (Real.sin alpha * Real.cos (lam * t * Real.sin alpha) -
      Real.cos alpha * Real.sin (lam * t * Real.sin alpha))

-- exercise: exercise_3878_2

variable (x lam alpha : ℝ) (I I₁ Gamma Dalpha : ℝ -> ℝ)

abbrev e3878Hyp : Prop := 0 < x ∧ 0 < lam ∧ -(Real.pi /. 2) < alpha ∧ alpha < Real.pi /. 2
abbrev e3878CosInt : ℝ := improperIntegral (e3878CosKernel x lam alpha)
abbrev e3878SinInt : ℝ := improperIntegral (e3878SinKernel x lam alpha)
abbrev e3878BaseInt : ℝ := improperIntegral (e3878BaseKernel x lam alpha)
abbrev e3878LapInt : ℝ := improperIntegral (e3878LapKernel x lam)

theorem proof_gap_exercise_3878_2_1
  (h : e3878Hyp x lam alpha) :
  ∀ t : ℝ, 0 < t →
    |e3878CosKernel x lam alpha t| ≤ e3878BaseKernel x lam alpha t := by
  sorry

theorem proof_gap_exercise_3878_2_2
  (h : e3878Hyp x lam alpha)
  (h1 : ∀ t : ℝ, 0 < t → |e3878CosKernel x lam alpha t| ≤ e3878BaseKernel x lam alpha t) :
  ∃ u : ℝ -> ℝ,
    (∀ t : ℝ, 0 < t → u t = lam * t * Real.cos alpha) ∧
    e3878BaseInt x lam alpha =
      (1 /. Real.rpow (lam * Real.cos alpha) x) *
        improperIntegral (fun u => Real.rpow u (x - 1) * Real.exp (-u)) := by
  sorry

theorem proof_gap_exercise_3878_2_3
  (h : e3878Hyp x lam alpha)
  (h2 : ∃ u : ℝ -> ℝ,
    (∀ t : ℝ, 0 < t → u t = lam * t * Real.cos alpha) ∧
    e3878BaseInt x lam alpha =
      (1 /. Real.rpow (lam * Real.cos alpha) x) *
        improperIntegral (fun u => Real.rpow u (x - 1) * Real.exp (-u))) :
  ∃ u : ℝ -> ℝ,
    (∀ t : ℝ, 0 < t → u t = lam * t * Real.cos alpha) ∧
    e3878BaseInt x lam alpha = Gamma x /. Real.rpow (lam * Real.cos alpha) x := by
  sorry

theorem proof_gap_exercise_3878_2_4
  (h : e3878Hyp x lam alpha)
  (h3 : ∃ u : ℝ -> ℝ,
    (∀ t : ℝ, 0 < t → u t = lam * t * Real.cos alpha) ∧
    e3878BaseInt x lam alpha = Gamma x /. Real.rpow (lam * Real.cos alpha) x) :
  ∃ u : ℝ -> ℝ,
    (∀ t : ℝ, 0 < t → u t = lam * t * Real.cos alpha) ∧
    ∃ M : ℝ, Gamma x /. Real.rpow (lam * Real.cos alpha) x < M := by
  sorry

theorem proof_gap_exercise_3878_2_5
  (h : e3878Hyp x lam alpha)
  (h4 : ∃ u : ℝ -> ℝ,
    (∀ t : ℝ, 0 < t → u t = lam * t * Real.cos alpha) ∧
    ∃ M : ℝ, Gamma x /. Real.rpow (lam * Real.cos alpha) x < M) :
  ∃ u : ℝ -> ℝ,
    (∀ t : ℝ, 0 < t → u t = lam * t * Real.cos alpha) ∧
    ∃ M : ℝ, e3878BaseInt x lam alpha < M := by
  sorry

theorem proof_gap_exercise_3878_2_6
  (h : e3878Hyp x lam alpha) :
  improperIntegrable (e3878CosKernel x lam alpha) := by
  sorry

theorem proof_gap_exercise_3878_2_7
  (h : e3878Hyp x lam alpha) :
  improperIntegrable (e3878SinKernel x lam alpha) := by
  sorry

theorem proof_gap_exercise_3878_2_8
  (h : e3878Hyp x lam alpha)
  (hI : I alpha = e3878CosInt x lam alpha)
  (hI₁ : I₁ alpha = e3878SinInt x lam alpha) :
  ∀ t : ℝ, 0 < t →
    Dalpha (e3878CosKernel x lam alpha t) = e3878DerivKernel x lam alpha t := by
  sorry

theorem proof_gap_exercise_3878_2_9
  (h : e3878Hyp x lam alpha) :
  ∀ t : ℝ, 0 < t → ∀ eps : ℝ, 0 < eps → eps < Real.pi /. 2 → ∀ beta : ℝ,
    -(Real.pi /. 2) + eps ≤ beta → beta ≤ Real.pi /. 2 - eps →
      |Real.rpow t x * Real.exp (-lam * t * Real.cos beta) *
        (Real.sin beta * Real.cos (lam * t * Real.sin beta) -
          Real.cos beta * Real.sin (lam * t * Real.sin beta))| ≤
        2 * Real.rpow t x * Real.exp (-lam * t * Real.cos beta) := by
  sorry

theorem proof_gap_exercise_3878_2_10
  (h : e3878Hyp x lam alpha) :
  ∃ M : ℝ, improperIntegral (fun t => Real.rpow t x * Real.exp (-lam * t * Real.cos alpha)) < M := by
  sorry

theorem proof_gap_exercise_3878_2_11
  (h : e3878Hyp x lam alpha) :
  funDeri I 1 alpha = improperIntegral (fun t => Dalpha (e3878CosKernel x lam alpha t)) := by
  sorry

theorem proof_gap_exercise_3878_2_12
  (h : e3878Hyp x lam alpha) :
  funDeri I 1 alpha = -x * I₁ alpha := by
  sorry

theorem proof_gap_exercise_3878_2_13
  (h : e3878Hyp x lam alpha) :
  funDeri I₁ 1 alpha = x * I alpha := by
  sorry

theorem proof_gap_exercise_3878_2_14
  (h : e3878Hyp x lam alpha) :
  funDeri I 2 alpha + x ^ 2 * I alpha = 0 := by
  sorry

theorem proof_gap_exercise_3878_2_15
  (h : e3878Hyp x lam alpha) :
  ∃ C₁ : ℝ, ∃ C₂ : ℝ, I alpha = C₁ * Real.cos (alpha * x) + C₂ * Real.sin (alpha * x) := by
  sorry

theorem proof_gap_exercise_3878_2_16
  (h : e3878Hyp x lam alpha) :
  ∃ C₁ : ℝ, C₁ = I 0 := by
  sorry

theorem proof_gap_exercise_3878_2_17
  (h : e3878Hyp x lam alpha) :
  I 0 = e3878LapInt x lam := by
  sorry

theorem proof_gap_exercise_3878_2_18
  (h : e3878Hyp x lam alpha) :
  e3878LapInt x lam = Gamma x /. Real.rpow lam x := by
  sorry

theorem proof_gap_exercise_3878_2_19
  (h : e3878Hyp x lam alpha) :
  ∃ C₁ : ℝ, C₁ = Gamma x /. Real.rpow lam x := by
  sorry

theorem proof_gap_exercise_3878_2_20
  (h : e3878Hyp x lam alpha) :
  funDeri I 1 0 = -x * I₁ 0 := by
  sorry

theorem proof_gap_exercise_3878_2_21
  (h : e3878Hyp x lam alpha) :
  ∃ C₂ : ℝ, funDeri I 1 0 = C₂ * x := by
  sorry

theorem proof_gap_exercise_3878_2_22
  (h : e3878Hyp x lam alpha) :
  I₁ 0 = 0 := by
  sorry

theorem proof_gap_exercise_3878_2_23
  (h : e3878Hyp x lam alpha) :
  ∃ C₂ : ℝ, C₂ = 0 := by
  sorry

theorem proof_gap_exercise_3878_2_24
  (h : e3878Hyp x lam alpha) :
  I alpha = Gamma x /. Real.rpow lam x * Real.cos (alpha * x) := by
  sorry

theorem proof_gap_exercise_3878_2_25
  (h : e3878Hyp x lam alpha) :
  I₁ alpha = -(1 /. x) * funDeri I 1 alpha := by
  sorry

theorem proof_gap_exercise_3878_2_26
  (h : e3878Hyp x lam alpha) :
  -(1 /. x) * funDeri I 1 alpha = Gamma x /. Real.rpow lam x * Real.sin (alpha * x) := by
  sorry

theorem proof_gap_exercise_3878_2_27
  (h : e3878Hyp x lam alpha) :
  I₁ alpha = Gamma x /. Real.rpow lam x * Real.sin (alpha * x) := by
  sorry

theorem proof_gap_exercise_3878_2_28
  (h : e3878Hyp x lam alpha)
  (hI₁ : I₁ alpha = e3878SinInt x lam alpha) :
  e3878SinInt x lam alpha = Gamma x /. Real.rpow lam x * Real.sin (alpha * x) := by
  sorry

theorem proof_gap_exercise_3878_2_29
  (h : e3878Hyp x lam alpha) :
  e3878SinInt x lam alpha = Gamma x /. Real.rpow lam x * Real.sin (alpha * x) := by
  sorry

end
