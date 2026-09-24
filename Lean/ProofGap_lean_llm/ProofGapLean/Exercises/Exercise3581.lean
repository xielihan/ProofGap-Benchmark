import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3581

noncomputable section

structure Point2 where
  x : ℝ
  y : ℝ

def polynomial (p : Point2) : ℝ :=
  2 * p.x ^ 2 - p.x * p.y - p.y ^ 2 -
    6 * p.x - 3 * p.y + 5

def partialX (f : Point2 → ℝ) (p : Point2) : ℝ :=
  deriv (fun t => f ⟨t, p.y⟩) p.x

def partialY (f : Point2 → ℝ) (p : Point2) : ℝ :=
  deriv (fun t => f ⟨p.x, t⟩) p.y

def partialXX (f : Point2 → ℝ) (p : Point2) : ℝ :=
  partialX (partialX f) p

def partialXY (f : Point2 → ℝ) (p : Point2) : ℝ :=
  partialY (partialX f) p

def partialYY (f : Point2 → ℝ) (p : Point2) : ℝ :=
  partialY (partialY f) p

def partialXXX (f : Point2 → ℝ) (p : Point2) : ℝ :=
  partialX (partialXX f) p

def partialXXY (f : Point2 → ℝ) (p : Point2) : ℝ :=
  partialY (partialXX f) p

def partialXYY (f : Point2 → ℝ) (p : Point2) : ℝ :=
  partialY (partialXY f) p

def partialYYY (f : Point2 → ℝ) (p : Point2) : ℝ :=
  partialY (partialYY f) p

def basePoint : Point2 := ⟨1, -2⟩

def taylorPolynomial2 (p : Point2) : ℝ :=
  polynomial basePoint +
    partialX polynomial basePoint * (p.x - basePoint.x) +
    partialY polynomial basePoint * (p.y - basePoint.y) +
    (1 / 2 : ℝ) *
      (partialXX polynomial basePoint * (p.x - basePoint.x) ^ 2 +
        2 * partialXY polynomial basePoint *
          (p.x - basePoint.x) * (p.y - basePoint.y) +
        partialYY polynomial basePoint * (p.y - basePoint.y) ^ 2)

def remainder2 (p : Point2) : ℝ :=
  polynomial p - taylorPolynomial2 p

theorem gap1 :
    ∀ p : Point2, partialX polynomial p = 4 * p.x - p.y - 6 := by
  intro p
  unfold partialX
  change
    deriv
      (fun t : ℝ =>
        2 * t ^ 2 - t * p.y - p.y ^ 2 - 6 * t - 3 * p.y + 5)
      p.x = 4 * p.x - p.y - 6
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * p.x) p.x := by
    simpa [pow_two, two_mul] using
      ((hasDerivAt_id p.x).mul (hasDerivAt_id p.x))
  have h1 :=
    (hsq.const_mul 2).sub ((hasDerivAt_id p.x).mul_const p.y)
  have h2 := h1.sub (hasDerivAt_const p.x (p.y ^ 2))
  have h3 := h2.sub ((hasDerivAt_id p.x).const_mul 6)
  have h4 := h3.sub (hasDerivAt_const p.x (3 * p.y))
  have h5 := h4.add (hasDerivAt_const p.x 5)
  convert h5.deriv using 1 <;> ring

theorem gap2 :
    ∀ p : Point2, partialY polynomial p = -p.x - 2 * p.y - 3 := by
  intro p
  unfold partialY
  change
    deriv
      (fun t : ℝ =>
        2 * p.x ^ 2 - p.x * t - t ^ 2 - 6 * p.x - 3 * t + 5)
      p.y = -p.x - 2 * p.y - 3
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * p.y) p.y := by
    simpa [pow_two, two_mul] using
      ((hasDerivAt_id p.y).mul (hasDerivAt_id p.y))
  have h1 :=
    (hasDerivAt_const p.y (2 * p.x ^ 2)).sub
      ((hasDerivAt_id p.y).const_mul p.x)
  have h2 := h1.sub hsq
  have h3 := h2.sub (hasDerivAt_const p.y (6 * p.x))
  have h4 := h3.sub ((hasDerivAt_id p.y).const_mul 3)
  have h5 := h4.add (hasDerivAt_const p.y 5)
  convert h5.deriv using 1 <;> ring

theorem gap3 :
    ∀ p : Point2, partialXX polynomial p = 4 := by
  intro p
  change deriv (fun t : ℝ => partialX polynomial ⟨t, p.y⟩) p.x = 4
  have hfun :
      (fun t : ℝ => partialX polynomial ⟨t, p.y⟩) =
        (fun t : ℝ => 4 * t - p.y - 6) := by
    funext t
    exact gap1 ⟨t, p.y⟩
  rw [hfun]
  convert
    ((((hasDerivAt_const p.x 4).mul (hasDerivAt_id p.x)).sub
      (hasDerivAt_const p.x p.y)).sub
      (hasDerivAt_const p.x 6)).deriv using 1 <;> ring

theorem gap4 :
    ∀ p : Point2, partialXY polynomial p = -1 := by
  intro p
  change deriv (fun t : ℝ => partialX polynomial ⟨p.x, t⟩) p.y = -1
  have hfun :
      (fun t : ℝ => partialX polynomial ⟨p.x, t⟩) =
        (fun t : ℝ => 4 * p.x - t - 6) := by
    funext t
    exact gap1 ⟨p.x, t⟩
  rw [hfun]
  convert
    (((hasDerivAt_const p.y (4 * p.x)).sub
      (hasDerivAt_id p.y)).sub
      (hasDerivAt_const p.y 6)).deriv using 1 <;> ring

theorem gap5 :
    ∀ p : Point2, partialYY polynomial p = -2 := by
  intro p
  change deriv (fun t : ℝ => partialY polynomial ⟨p.x, t⟩) p.y = -2
  have hfun :
      (fun t : ℝ => partialY polynomial ⟨p.x, t⟩) =
        (fun t : ℝ => -p.x - 2 * t - 3) := by
    funext t
    exact gap2 ⟨p.x, t⟩
  rw [hfun]
  have h1 :=
    (hasDerivAt_const p.y (-p.x)).sub
      ((hasDerivAt_id p.y).const_mul 2)
  have h2 := h1.sub (hasDerivAt_const p.y 3)
  convert h2.deriv using 1 <;> ring

theorem gap6 :
    ∀ p : Point2,
      partialXXX polynomial p = 0 ∧ partialXXY polynomial p = 0 ∧
      partialXYY polynomial p = 0 ∧ partialYYY polynomial p = 0 := by
  intro p
  constructor
  · change deriv (fun t : ℝ => partialXX polynomial ⟨t, p.y⟩) p.x = 0
    have hfun :
        (fun t : ℝ => partialXX polynomial ⟨t, p.y⟩) =
          (fun _ : ℝ => (4 : ℝ)) := by
      funext t
      exact gap3 ⟨t, p.y⟩
    rw [hfun]
    simpa using (hasDerivAt_const p.x (4 : ℝ)).deriv
  constructor
  · change deriv (fun t : ℝ => partialXX polynomial ⟨p.x, t⟩) p.y = 0
    have hfun :
        (fun t : ℝ => partialXX polynomial ⟨p.x, t⟩) =
          (fun _ : ℝ => (4 : ℝ)) := by
      funext t
      exact gap3 ⟨p.x, t⟩
    rw [hfun]
    simpa using (hasDerivAt_const p.y (4 : ℝ)).deriv
  constructor
  · change deriv (fun t : ℝ => partialXY polynomial ⟨p.x, t⟩) p.y = 0
    have hfun :
        (fun t : ℝ => partialXY polynomial ⟨p.x, t⟩) =
          (fun _ : ℝ => (-1 : ℝ)) := by
      funext t
      exact gap4 ⟨p.x, t⟩
    rw [hfun]
    simpa using (hasDerivAt_const p.y (-1 : ℝ)).deriv
  · change deriv (fun t : ℝ => partialYY polynomial ⟨p.x, t⟩) p.y = 0
    have hfun :
        (fun t : ℝ => partialYY polynomial ⟨p.x, t⟩) =
          (fun _ : ℝ => (-2 : ℝ)) := by
      funext t
      exact gap5 ⟨p.x, t⟩
    rw [hfun]
    simpa using (hasDerivAt_const p.y (-2 : ℝ)).deriv

theorem gap7 :
    ∀ p : Point2, remainder2 p = 0 := by
  intro p
  simp [remainder2, taylorPolynomial2, polynomial, basePoint,
    gap1, gap2, gap3, gap4, gap5] <;> ring

theorem gap8 :
    polynomial basePoint = 5 := by
  norm_num [polynomial, basePoint]

theorem gap9 :
    partialX polynomial basePoint = 0 := by
  rw [gap1]
  norm_num [basePoint]

theorem gap10 :
    partialY polynomial basePoint = 0 := by
  rw [gap2]
  norm_num [basePoint]

theorem gap11 :
    partialXX polynomial basePoint = 4 := by
  exact gap3 basePoint

theorem gap12 :
    partialXY polynomial basePoint = -1 := by
  exact gap4 basePoint

theorem gap13 :
    partialYY polynomial basePoint = -2 := by
  exact gap5 basePoint

theorem gap14 :
    ∀ p : Point2,
      polynomial p =
        5 + 2 * (p.x - 1) ^ 2 -
          (p.x - 1) * (p.y + 2) - (p.y + 2) ^ 2 := by
  intro p
  simp [polynomial] <;> ring

end

end ProofGap.Exercise3581
