import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise3580

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ

def familyFunction (base point : Point3) (p q : ℝ) : ℝ :=
  point.z - base.z - p * (point.x - base.x) -
    q * (point.y - base.y)

def lagrangian (base point : Point3) (lam p q : ℝ) : ℝ :=
  familyFunction base point p q + lam * (p ^ 2 + q ^ 2 - 1)

def partialP (base point : Point3) (lam p q : ℝ) : ℝ :=
  deriv (fun t => lagrangian base point lam t q) p

def partialQ (base point : Point3) (lam p q : ℝ) : ℝ :=
  deriv (fun t => lagrangian base point lam p t) q

def envelopeCondition (base point : Point3) (lam p q : ℝ) : Prop :=
  familyFunction base point p q = 0 ∧ p ^ 2 + q ^ 2 = 1 ∧
    partialP base point lam p q = 0 ∧
    partialQ base point lam p q = 0

def envelope (base : Point3) : Set Point3 :=
  {point | ∃ lam p q : ℝ, envelopeCondition base point lam p q}

def cone (base : Point3) : Set Point3 :=
  {point | (point.z - base.z) ^ 2 =
    (point.x - base.x) ^ 2 + (point.y - base.y) ^ 2}

theorem gap1 (base point : Point3) (lam p q : ℝ)
    (hEnvelope : envelopeCondition base point lam p q) :
    point.z - base.z =
      p * (point.x - base.x) + q * (point.y - base.y) := by
  rcases hEnvelope with ⟨hFamily, _⟩
  unfold familyFunction at hFamily
  linarith

theorem gap2 (base point : Point3) (lam p q : ℝ)
    (hEnvelope : envelopeCondition base point lam p q) :
    p ^ 2 + q ^ 2 = 1 := by
  exact hEnvelope.2.1

theorem gap3 (base point : Point3) (lam p q : ℝ) :
    partialP base point lam p q =
      -(point.x - base.x) + 2 * lam * p := by
  unfold partialP lagrangian familyFunction
  have hBase :
      HasDerivAt (fun _ : ℝ => point.z - base.z) 0 p :=
    hasDerivAt_const p (point.z - base.z)
  have hLinear :
      HasDerivAt
        (fun t : ℝ => t * (point.x - base.x))
        (point.x - base.x) p := by
    convert (hasDerivAt_id p).mul_const (point.x - base.x) using 1 <;> ring
  have hQ :
      HasDerivAt
        (fun _ : ℝ => q * (point.y - base.y)) 0 p :=
    hasDerivAt_const p (q * (point.y - base.y))
  have hSq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * p) p := by
    convert (hasDerivAt_id p).mul (hasDerivAt_id p) using 1
    · funext t
      simp [pow_two]
    · simpa only [id, one_mul, mul_one, two_mul]
  have hConstraint :
      HasDerivAt (fun t : ℝ => t ^ 2 + q ^ 2 - 1) (2 * p) p := by
    convert (hSq.add_const (q ^ 2)).sub_const 1 using 1 <;> ring
  have hPenalty :
      HasDerivAt
        (fun t : ℝ => lam * (t ^ 2 + q ^ 2 - 1))
        (lam * (2 * p)) p :=
    hConstraint.const_mul lam
  convert (((hBase.sub hLinear).sub hQ).add hPenalty).deriv using 1 <;> ring

theorem gap4 (base point : Point3) (lam p q : ℝ)
    (hEnvelope : envelopeCondition base point lam p q) :
    -(point.x - base.x) + 2 * lam * p = 0 := by
  simpa only [gap3] using hEnvelope.2.2.1

theorem gap5 (base point : Point3) (lam p q : ℝ) :
    partialQ base point lam p q =
      -(point.y - base.y) + 2 * lam * q := by
  unfold partialQ lagrangian familyFunction
  have hBase :
      HasDerivAt (fun _ : ℝ => point.z - base.z) 0 q :=
    hasDerivAt_const q (point.z - base.z)
  have hP :
      HasDerivAt
        (fun _ : ℝ => p * (point.x - base.x)) 0 q :=
    hasDerivAt_const q (p * (point.x - base.x))
  have hLinear :
      HasDerivAt
        (fun t : ℝ => t * (point.y - base.y))
        (point.y - base.y) q := by
    convert (hasDerivAt_id q).mul_const (point.y - base.y) using 1 <;> ring
  have hSq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * q) q := by
    convert (hasDerivAt_id q).mul (hasDerivAt_id q) using 1
    · funext t
      simp [pow_two]
    · simpa only [id, one_mul, mul_one, two_mul]
  have hConstraint :
      HasDerivAt (fun t : ℝ => p ^ 2 + t ^ 2 - 1) (2 * q) q := by
    convert ((hasDerivAt_const q (p ^ 2)).add hSq).sub_const 1 using 1 <;> ring
  have hPenalty :
      HasDerivAt
        (fun t : ℝ => lam * (p ^ 2 + t ^ 2 - 1))
        (lam * (2 * q)) q :=
    hConstraint.const_mul lam
  convert (((hBase.sub hP).sub hLinear).add hPenalty).deriv using 1 <;> ring

theorem gap6 (base point : Point3) (lam p q : ℝ)
    (hEnvelope : envelopeCondition base point lam p q) :
    -(point.y - base.y) + 2 * lam * q = 0 := by
  simpa only [gap5] using hEnvelope.2.2.2

theorem gap7 (base point : Point3) (lam p q : ℝ)
    (hEnvelope : envelopeCondition base point lam p q) :
    2 * lam = point.z - base.z := by
  have hx : point.x - base.x = 2 * lam * p := by
    linarith [gap4 base point lam p q hEnvelope]
  have hy : point.y - base.y = 2 * lam * q := by
    linarith [gap6 base point lam p q hEnvelope]
  have hz := gap1 base point lam p q hEnvelope
  rw [hx, hy] at hz
  calc
    2 * lam = 2 * lam * (p ^ 2 + q ^ 2) := by
      rw [gap2 base point lam p q hEnvelope]
      ring
    _ = p * (2 * lam * p) + q * (2 * lam * q) := by ring
    _ = point.z - base.z := hz.symm

theorem gap8 (base point : Point3) (lam p q : ℝ)
    (hEnvelope : envelopeCondition base point lam p q)
    (hHeight : point.z - base.z ≠ 0) :
    p = (point.x - base.x) / (point.z - base.z) := by
  have hx : point.x - base.x = 2 * lam * p := by
    linarith [gap4 base point lam p q hEnvelope]
  apply (eq_div_iff hHeight).2
  rw [← gap7 base point lam p q hEnvelope, hx]
  ring

theorem gap9 (base point : Point3) (lam p q : ℝ)
    (hEnvelope : envelopeCondition base point lam p q)
    (hHeight : point.z - base.z ≠ 0) :
    q = (point.y - base.y) / (point.z - base.z) := by
  have hy : point.y - base.y = 2 * lam * q := by
    linarith [gap6 base point lam p q hEnvelope]
  apply (eq_div_iff hHeight).2
  rw [← gap7 base point lam p q hEnvelope, hy]
  ring

theorem gap10 (base point : Point3) (lam p q : ℝ)
    (hEnvelope : envelopeCondition base point lam p q) :
    (point.z - base.z) ^ 2 =
      (point.x - base.x) ^ 2 + (point.y - base.y) ^ 2 := by
  have hx : point.x - base.x = 2 * lam * p := by
    linarith [gap4 base point lam p q hEnvelope]
  have hy : point.y - base.y = 2 * lam * q := by
    linarith [gap6 base point lam p q hEnvelope]
  rw [← gap7 base point lam p q hEnvelope, hx, hy]
  calc
    (2 * lam) ^ 2 = (2 * lam) ^ 2 * (p ^ 2 + q ^ 2) := by
      rw [gap2 base point lam p q hEnvelope]
      ring
    _ = (2 * lam * p) ^ 2 + (2 * lam * q) ^ 2 := by ring

theorem gap11 (base : Point3) :
    envelope base = cone base := by
  apply Set.ext
  intro point
  constructor
  · intro hPoint
    change ∃ lam p q : ℝ, envelopeCondition base point lam p q at hPoint
    change (point.z - base.z) ^ 2 =
      (point.x - base.x) ^ 2 + (point.y - base.y) ^ 2
    rcases hPoint with ⟨lam, p, q, hEnvelope⟩
    exact gap10 base point lam p q hEnvelope
  · intro hPoint
    change (point.z - base.z) ^ 2 =
      (point.x - base.x) ^ 2 + (point.y - base.y) ^ 2 at hPoint
    change ∃ lam p q : ℝ, envelopeCondition base point lam p q
    by_cases hHeight : point.z - base.z = 0
    · have hx : point.x - base.x = 0 := by
        nlinarith [sq_nonneg (point.x - base.x),
          sq_nonneg (point.y - base.y)]
      have hy : point.y - base.y = 0 := by
        nlinarith [sq_nonneg (point.x - base.x),
          sq_nonneg (point.y - base.y)]
      refine ⟨0, 1, 0, ?_⟩
      simp [envelopeCondition, familyFunction, gap3, gap5, hHeight, hx, hy]
    · have hNorm :
          ((point.x - base.x) / (point.z - base.z)) ^ 2 +
              ((point.y - base.y) / (point.z - base.z)) ^ 2 = 1 := by
        field_simp [hHeight]
        nlinarith [hPoint]
      refine ⟨(point.z - base.z) / 2,
        (point.x - base.x) / (point.z - base.z),
        (point.y - base.y) / (point.z - base.z), ?_⟩
      refine ⟨?_, hNorm, ?_, ?_⟩
      · unfold familyFunction
        field_simp [hHeight]
        nlinarith [hPoint]
      · rw [gap3]
        field_simp [hHeight] <;> ring
      · rw [gap5]
        field_simp [hHeight] <;> ring

end

end ProofGap.Exercise3580
