import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace ProofGap.Exercise3576

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ

def direction (alpha beta gamma : ℝ) : Point3 :=
  ⟨Real.cos alpha, Real.cos beta, Real.cos gamma⟩

def isUnitDirection (alpha beta gamma : ℝ) : Prop :=
  (Real.cos alpha) ^ 2 + (Real.cos beta) ^ 2 +
    (Real.cos gamma) ^ 2 = 1

def familyFunction (alpha beta gamma : ℝ) (p : Point3) (t : ℝ) : ℝ :=
  (p.x - t * Real.cos alpha) ^ 2 +
    (p.y - t * Real.cos beta) ^ 2 +
    (p.z - t * Real.cos gamma) ^ 2 - 1

def parameterDerivative (alpha beta gamma : ℝ) (p : Point3) (t : ℝ) : ℝ :=
  deriv (fun s => familyFunction alpha beta gamma p s) t

def envelopeCondition (alpha beta gamma : ℝ) (p : Point3) (t : ℝ) : Prop :=
  familyFunction alpha beta gamma p t = 0 ∧
    parameterDerivative alpha beta gamma p t = 0

def envelope (alpha beta gamma : ℝ) : Set Point3 :=
  {p | ∃ t : ℝ, envelopeCondition alpha beta gamma p t}

def cylinder (alpha beta gamma : ℝ) : Set Point3 :=
  {p | p.x ^ 2 + p.y ^ 2 + p.z ^ 2 -
    (p.x * Real.cos alpha + p.y * Real.cos beta +
      p.z * Real.cos gamma) ^ 2 = 1}

private theorem parameterDerivative_eq (alpha beta gamma : ℝ)
    (p : Point3) (t : ℝ) :
    parameterDerivative alpha beta gamma p t =
      -2 * Real.cos alpha * (p.x - t * Real.cos alpha) -
        2 * Real.cos beta * (p.y - t * Real.cos beta) -
        2 * Real.cos gamma * (p.z - t * Real.cos gamma) := by
  have hx : HasDerivAt
      (fun s : ℝ => p.x - s * Real.cos alpha)
      (-Real.cos alpha) t := by
    simpa [Pi.sub_apply] using
      (hasDerivAt_const t p.x).sub
        ((hasDerivAt_id t).mul_const (Real.cos alpha))
  have hy : HasDerivAt
      (fun s : ℝ => p.y - s * Real.cos beta)
      (-Real.cos beta) t := by
    simpa [Pi.sub_apply] using
      (hasDerivAt_const t p.y).sub
        ((hasDerivAt_id t).mul_const (Real.cos beta))
  have hz : HasDerivAt
      (fun s : ℝ => p.z - s * Real.cos gamma)
      (-Real.cos gamma) t := by
    simpa [Pi.sub_apply] using
      (hasDerivAt_const t p.z).sub
        ((hasDerivAt_id t).mul_const (Real.cos gamma))
  have htotal :=
    (((hx.pow 2).add (hy.pow 2)).add (hz.pow 2)).sub
      (hasDerivAt_const t 1)
  unfold parameterDerivative familyFunction
  have hd := htotal.deriv
  change deriv (fun s =>
    (p.x - s * Real.cos alpha) ^ 2 +
      (p.y - s * Real.cos beta) ^ 2 +
      (p.z - s * Real.cos gamma) ^ 2 - 1) t = _ at hd
  rw [hd]
  ring

theorem gap1 (alpha beta gamma : ℝ)
    (hUnit : isUnitDirection alpha beta gamma) :
    ∀ p : Point3, ∀ t : ℝ,
      envelopeCondition alpha beta gamma p t →
      familyFunction alpha beta gamma p t = 0 := by
  intro p t h
  exact h.1

theorem gap2 (alpha beta gamma : ℝ)
    (hUnit : isUnitDirection alpha beta gamma) :
    ∀ p : Point3, ∀ t : ℝ,
      envelopeCondition alpha beta gamma p t →
      -2 * Real.cos alpha * (p.x - t * Real.cos alpha) -
        2 * Real.cos beta * (p.y - t * Real.cos beta) -
        2 * Real.cos gamma * (p.z - t * Real.cos gamma) = 0 := by
  intro p t h
  rw [← parameterDerivative_eq]
  exact h.2

theorem gap3 (alpha beta gamma : ℝ)
    (hUnit : isUnitDirection alpha beta gamma) :
    ∀ p : Point3, ∀ t : ℝ,
      -2 * Real.cos alpha * (p.x - t * Real.cos alpha) -
        2 * Real.cos beta * (p.y - t * Real.cos beta) -
        2 * Real.cos gamma * (p.z - t * Real.cos gamma) = 0 →
      t = p.x * Real.cos alpha + p.y * Real.cos beta +
        p.z * Real.cos gamma := by
  intro p t ht
  unfold isUnitDirection at hUnit
  linear_combination ht / 2 - t * hUnit

theorem gap4 (alpha beta gamma : ℝ)
    (hUnit : isUnitDirection alpha beta gamma) :
    ∀ p : Point3, ∀ t : ℝ,
      familyFunction alpha beta gamma p t = 0 →
      t = p.x * Real.cos alpha + p.y * Real.cos beta +
        p.z * Real.cos gamma →
      p.x ^ 2 + p.y ^ 2 + p.z ^ 2 -
        (p.x * Real.cos alpha + p.y * Real.cos beta +
          p.z * Real.cos gamma) ^ 2 = 1 := by
  intro p t hfamily ht
  unfold familyFunction at hfamily
  unfold isUnitDirection at hUnit
  rw [ht] at hfamily
  linear_combination hfamily -
    (p.x * Real.cos alpha + p.y * Real.cos beta +
      p.z * Real.cos gamma) ^ 2 * hUnit

theorem gap5 (alpha beta gamma : ℝ)
    (hUnit : isUnitDirection alpha beta gamma) :
    envelope alpha beta gamma = cylinder alpha beta gamma := by
  ext p
  constructor
  · intro hp
    change ∃ t : ℝ, envelopeCondition alpha beta gamma p t at hp
    change p.x ^ 2 + p.y ^ 2 + p.z ^ 2 -
      (p.x * Real.cos alpha + p.y * Real.cos beta +
        p.z * Real.cos gamma) ^ 2 = 1
    rcases hp with ⟨t, ht⟩
    exact gap4 alpha beta gamma hUnit p t
      (gap1 alpha beta gamma hUnit p t ht)
      (gap3 alpha beta gamma hUnit p t
        (gap2 alpha beta gamma hUnit p t ht))
  · intro hp
    change p.x ^ 2 + p.y ^ 2 + p.z ^ 2 -
      (p.x * Real.cos alpha + p.y * Real.cos beta +
        p.z * Real.cos gamma) ^ 2 = 1 at hp
    change ∃ t : ℝ, envelopeCondition alpha beta gamma p t
    let t :=
      p.x * Real.cos alpha + p.y * Real.cos beta +
        p.z * Real.cos gamma
    refine ⟨t, ?_, ?_⟩
    · unfold familyFunction
      unfold isUnitDirection at hUnit
      linear_combination hp + t ^ 2 * hUnit
    · rw [parameterDerivative_eq]
      unfold isUnitDirection at hUnit
      dsimp only [t]
      linear_combination
        2 * (p.x * Real.cos alpha + p.y * Real.cos beta +
          p.z * Real.cos gamma) * hUnit

end

end ProofGap.Exercise3576
