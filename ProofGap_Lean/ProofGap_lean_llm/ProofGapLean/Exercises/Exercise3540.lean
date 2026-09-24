import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3540

noncomputable section

abbrev Point3 := ℝ × (ℝ × ℝ)

def sphereImplicit (P : Point3) : ℝ :=
  P.1 ^ 2 + P.2.1 ^ 2 + P.2.2 ^ 2 - 169

def partialX3 (f : Point3 → ℝ) (P : Point3) : ℝ :=
  deriv (fun x => f (x, (P.2.1, P.2.2))) P.1

def partialY3 (f : Point3 → ℝ) (P : Point3) : ℝ :=
  deriv (fun y => f (P.1, (y, P.2.2))) P.2.1

def partialZ3 (f : Point3 → ℝ) (P : Point3) : ℝ :=
  deriv (fun z => f (P.1, (P.2.1, z))) P.2.2

def gradientF (P : Point3) : Point3 :=
  (partialX3 sphereImplicit P,
    (partialY3 sphereImplicit P, partialZ3 sphereImplicit P))

def basePoint : Point3 := (3, (4, 12))

def baseNormal : Point3 := gradientF basePoint

def scale (c : ℝ) (V : Point3) : Point3 :=
  (c * V.1, (c * V.2.1, c * V.2.2))

def dot (U V : Point3) : ℝ :=
  U.1 * V.1 + U.2.1 * V.2.1 + U.2.2 * V.2.2

def displacement (Q P : Point3) : Point3 :=
  (Q.1 - P.1, (Q.2.1 - P.2.1, Q.2.2 - P.2.2))

def planeFromPointNormal (P N : Point3) : Set Point3 :=
  {Q | dot N (displacement Q P) = 0}

def tangentPlane : Set Point3 :=
  planeFromPointNormal basePoint basePoint

def simplifiedPlane : Set Point3 :=
  {Q | 3 * Q.1 + 4 * Q.2.1 + 12 * Q.2.2 = 169}

def linePoint (P V : Point3) (s : ℝ) : Point3 :=
  (P.1 + s * V.1, (P.2.1 + s * V.2.1, P.2.2 + s * V.2.2))

def normalLine : Set Point3 :=
  {Q | ∃ s : ℝ, Q = linePoint basePoint basePoint s}

def shiftedLineEquations : Set Point3 :=
  {Q |
    (Q.1 - 3) * 4 = (Q.2.1 - 4) * 3 ∧
      (Q.2.1 - 4) * 12 = (Q.2.2 - 12) * 4}

def homogeneousLineEquations : Set Point3 :=
  {Q | Q.1 * 4 = Q.2.1 * 3 ∧ Q.2.1 * 12 = Q.2.2 * 4}

theorem gap1 :
    ∀ P, gradientF P = (2 * P.1, (2 * P.2.1, 2 * P.2.2)) := by
  intro P
  apply Prod.ext
  · change
      deriv
          (fun x : ℝ =>
            x ^ 2 + P.2.1 ^ 2 + P.2.2 ^ 2 - 169)
          P.1 =
        2 * P.1
    have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * P.1) P.1 := by
      simpa [pow_two, two_mul] using
        ((hasDerivAt_id P.1).mul (hasDerivAt_id P.1))
    have h := hsq.add_const (P.2.1 ^ 2)
    have h' := h.add_const (P.2.2 ^ 2)
    simpa using (h'.sub_const 169).deriv
  · apply Prod.ext
    · change
        deriv
            (fun y : ℝ =>
              P.1 ^ 2 + y ^ 2 + P.2.2 ^ 2 - 169)
            P.2.1 =
          2 * P.2.1
      have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * P.2.1) P.2.1 := by
        simpa [pow_two, two_mul] using
          ((hasDerivAt_id P.2.1).mul (hasDerivAt_id P.2.1))
      have h :=
        (hasDerivAt_const P.2.1 (P.1 ^ 2)).add hsq
      have h' := h.add_const (P.2.2 ^ 2)
      simpa using (h'.sub_const 169).deriv
    · change
        deriv
            (fun z : ℝ =>
              P.1 ^ 2 + P.2.1 ^ 2 + z ^ 2 - 169)
            P.2.2 =
          2 * P.2.2
      have hsq : HasDerivAt (fun z : ℝ => z ^ 2) (2 * P.2.2) P.2.2 := by
        simpa [pow_two, two_mul] using
          ((hasDerivAt_id P.2.2).mul (hasDerivAt_id P.2.2))
      have h :=
        (hasDerivAt_const P.2.2 (P.1 ^ 2 + P.2.1 ^ 2)).add hsq
      simpa using (h.sub_const 169).deriv

theorem gap2 :
    gradientF basePoint = (6, (8, 24)) := by
  rw [gap1]
  norm_num [basePoint]

theorem gap3 :
    (6, (8, 24)) = scale 2 basePoint := by
  norm_num [scale, basePoint]

theorem gap4 :
    baseNormal = scale 2 basePoint := by
  calc
    baseNormal = gradientF basePoint := rfl
    _ = (6, (8, 24)) := gap2
    _ = scale 2 basePoint := gap3

theorem gap5 :
    tangentPlane =
      {Q |
        3 * (Q.1 - 3) + 4 * (Q.2.1 - 4) +
          12 * (Q.2.2 - 12) = 0} := by
  rfl

theorem gap6 :
    {Q : Point3 |
        3 * (Q.1 - 3) + 4 * (Q.2.1 - 4) +
          12 * (Q.2.2 - 12) = 0} =
      simplifiedPlane := by
  apply Set.ext
  intro Q
  change
    (3 * (Q.1 - 3) + 4 * (Q.2.1 - 4) + 12 * (Q.2.2 - 12) = 0) ↔
      3 * Q.1 + 4 * Q.2.1 + 12 * Q.2.2 = 169
  constructor
  · intro h
    linarith
  · intro h
    linarith

theorem gap7 :
    tangentPlane = simplifiedPlane := by
  calc
    tangentPlane =
        {Q |
          3 * (Q.1 - 3) + 4 * (Q.2.1 - 4) +
            12 * (Q.2.2 - 12) = 0} := gap5
    _ = simplifiedPlane := gap6

theorem gap8 :
    normalLine = shiftedLineEquations := by
  apply Set.ext
  intro Q
  change
    (∃ s : ℝ, Q = linePoint basePoint basePoint s) ↔
      ((Q.1 - 3) * 4 = (Q.2.1 - 4) * 3 ∧
        (Q.2.1 - 4) * 12 = (Q.2.2 - 12) * 4)
  constructor
  · rintro ⟨s, rfl⟩
    dsimp [linePoint, basePoint]
    constructor <;> ring
  · intro h
    refine ⟨(Q.2.1 - 4) / 4, ?_⟩
    apply Prod.ext
    · change Q.1 = 3 + ((Q.2.1 - 4) / 4) * 3
      linarith [h.1]
    · apply Prod.ext
      · change Q.2.1 = 4 + ((Q.2.1 - 4) / 4) * 4
        ring
      · change Q.2.2 = 12 + ((Q.2.1 - 4) / 4) * 12
        linarith [h.2]

theorem gap9 :
    shiftedLineEquations = homogeneousLineEquations := by
  apply Set.ext
  intro Q
  change
    (((Q.1 - 3) * 4 = (Q.2.1 - 4) * 3 ∧
        (Q.2.1 - 4) * 12 = (Q.2.2 - 12) * 4)) ↔
      (Q.1 * 4 = Q.2.1 * 3 ∧ Q.2.1 * 12 = Q.2.2 * 4)
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

theorem gap10 :
    normalLine = homogeneousLineEquations := by
  calc
    normalLine = shiftedLineEquations := gap8
    _ = homogeneousLineEquations := gap9

end

end ProofGap.Exercise3540
