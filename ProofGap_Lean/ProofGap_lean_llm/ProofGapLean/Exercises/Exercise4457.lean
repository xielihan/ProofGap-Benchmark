import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4457

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def dot (p q : Vec3) : ℝ :=
  p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2

def partialX (f : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => f (x, p.2.1, p.2.2)) p.1

def partialY (f : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun y => f (p.1, y, p.2.2)) p.2.1

def partialZ (f : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun z => f (p.1, p.2.1, z)) p.2.2

def gradient (u : Vec3 → ℝ) (p : Vec3) : Vec3 :=
  (partialX u p, partialY u p, partialZ u p)

def curl (a : Vec3 → Vec3) (p : Vec3) : Vec3 :=
  (partialY (fun q => (a q).2.2) p -
      partialZ (fun q => (a q).2.1) p,
    partialZ (fun q => (a q).1) p -
      partialX (fun q => (a q).2.2) p,
    partialX (fun q => (a q).2.1) p -
      partialY (fun q => (a q).1) p)

def field (p : Vec3) : Vec3 :=
  let x := p.1
  let y := p.2.1
  let z := p.2.2
  (y * z * (2 * x + y + z),
    x * z * (x + 2 * y + z),
    x * y * (x + y + 2 * z))

def curlExpansion (p : Vec3) : Vec3 :=
  let x := p.1
  let y := p.2.1
  let z := p.2.2
  (x * (x + 2 * y + 2 * z) - x * (x + 2 * y + 2 * z),
    y * (2 * x + y + 2 * z) - y * (2 * x + y + 2 * z),
    z * (2 * x + 2 * y + z) - z * (2 * x + 2 * y + z))

def curlOfField (p : Vec3) : Vec3 :=
  curl field p

def basePotential (p : Vec3) : ℝ :=
  p.1 * p.2.1 * p.2.2 * (p.1 + p.2.1 + p.2.2)

def productRuleGradient (p : Vec3) : Vec3 :=
  let x := p.1
  let y := p.2.1
  let z := p.2.2
  (y * z * (x + y + z) + x * y * z,
    x * z * (x + y + z) + x * y * z,
    x * y * (x + y + z) + x * y * z)

def potentialDifferential (p v : Vec3) : ℝ :=
  dot (gradient basePotential p) v

def fieldOneForm (p v : Vec3) : ℝ :=
  dot (field p) v

def expandedOneForm (p v : Vec3) : ℝ :=
  let x := p.1
  let y := p.2.1
  let z := p.2.2
  y * z * (2 * x + y + z) * v.1 +
    x * z * (x + 2 * y + z) * v.2.1 +
    x * y * (x + y + 2 * z) * v.2.2

def productRuleOneForm (p v : Vec3) : ℝ :=
  let x := p.1
  let y := p.2.1
  let z := p.2.2
  x * y * z * (v.1 + v.2.1 + v.2.2) +
    (x + y + z) *
      (y * z * v.1 + z * x * v.2.1 + x * y * v.2.2)

def potentialFamily (C : ℝ) (p : Vec3) : ℝ :=
  basePotential p + C

def potentialFamilyGradient (C : ℝ) (p : Vec3) : Vec3 :=
  gradient (potentialFamily C) p

private theorem potentialFamilyGradient_eq_field (C : ℝ) (p : Vec3) :
    potentialFamilyGradient C p = field p := by
  rcases p with ⟨x, y, z⟩
  apply Prod.ext
  · dsimp [potentialFamilyGradient, gradient, partialX, potentialFamily,
      basePotential, field]
    have h :
        HasDerivAt (fun t : ℝ => t * y * z * (t + y + z) + C)
          (y * z * (2 * x + y + z)) x := by
      convert
        HasDerivAt.add
          ((((hasDerivAt_id x).mul (hasDerivAt_const x y)).mul
            (hasDerivAt_const x z)).mul
            (HasDerivAt.add
              (HasDerivAt.add (hasDerivAt_id x) (hasDerivAt_const x y))
              (hasDerivAt_const x z)))
          (hasDerivAt_const x C) using 1 <;> simp <;> ring
    exact h.deriv
  · apply Prod.ext
    · dsimp [potentialFamilyGradient, gradient, partialY, potentialFamily,
        basePotential, field]
      have h :
          HasDerivAt (fun t : ℝ => x * t * z * (x + t + z) + C)
            (x * z * (x + 2 * y + z)) y := by
        convert
          HasDerivAt.add
            ((((hasDerivAt_const y x).mul (hasDerivAt_id y)).mul
              (hasDerivAt_const y z)).mul
              (HasDerivAt.add
                (HasDerivAt.add (hasDerivAt_const y x) (hasDerivAt_id y))
                (hasDerivAt_const y z)))
            (hasDerivAt_const y C) using 1 <;> simp <;> ring
      exact h.deriv
    · dsimp [potentialFamilyGradient, gradient, partialZ, potentialFamily,
        basePotential, field]
      have h :
          HasDerivAt (fun t : ℝ => x * y * t * (x + y + t) + C)
            (x * y * (x + y + 2 * z)) z := by
        convert
          HasDerivAt.add
            ((((hasDerivAt_const z x).mul (hasDerivAt_const z y)).mul
              (hasDerivAt_id z)).mul
              (HasDerivAt.add
                (HasDerivAt.add (hasDerivAt_const z x)
                  (hasDerivAt_const z y))
                (hasDerivAt_id z)))
            (hasDerivAt_const z C) using 1 <;> simp <;> ring
      exact h.deriv

private theorem basePotentialGradient_eq_field (p : Vec3) :
    gradient basePotential p = field p := by
  have h := potentialFamilyGradient_eq_field 0 p
  change gradient (potentialFamily 0) p = field p at h
  have hfun : potentialFamily 0 = basePotential := by
    funext q
    simp [potentialFamily]
  rw [hfun] at h
  exact h

theorem gap1 (p : Vec3) :
    curlOfField p = curlExpansion p := by
  rcases p with ⟨x, y, z⟩
  have hyC :
      deriv (fun t : ℝ => x * t * (x + t + 2 * z)) y =
        x * (x + 2 * y + 2 * z) := by
    have h :
        HasDerivAt (fun t : ℝ => x * t * (x + t + 2 * z))
          (x * (x + 2 * y + 2 * z)) y := by
      convert
        (((hasDerivAt_const y x).mul (hasDerivAt_id y)).mul
          (HasDerivAt.add
            (HasDerivAt.add (hasDerivAt_const y x) (hasDerivAt_id y))
            (hasDerivAt_const y (2 * z)))) using 1 <;> simp <;> ring
    exact h.deriv
  have hzB :
      deriv (fun t : ℝ => x * t * (x + 2 * y + t)) z =
        x * (x + 2 * y + 2 * z) := by
    have h :
        HasDerivAt (fun t : ℝ => x * t * (x + 2 * y + t))
          (x * (x + 2 * y + 2 * z)) z := by
      convert
        (((hasDerivAt_const z x).mul (hasDerivAt_id z)).mul
          (HasDerivAt.add
            (HasDerivAt.add (hasDerivAt_const z x)
              (hasDerivAt_const z (2 * y)))
            (hasDerivAt_id z))) using 1 <;> simp <;> ring
    exact h.deriv
  have hzA :
      deriv (fun t : ℝ => y * t * (2 * x + y + t)) z =
        y * (2 * x + y + 2 * z) := by
    have h :
        HasDerivAt (fun t : ℝ => y * t * (2 * x + y + t))
          (y * (2 * x + y + 2 * z)) z := by
      convert
        (((hasDerivAt_const z y).mul (hasDerivAt_id z)).mul
          (HasDerivAt.add
            (HasDerivAt.add (hasDerivAt_const z (2 * x))
              (hasDerivAt_const z y))
            (hasDerivAt_id z))) using 1 <;> simp <;> ring
    exact h.deriv
  have hxC :
      deriv (fun t : ℝ => t * y * (t + y + 2 * z)) x =
        y * (2 * x + y + 2 * z) := by
    have h :
        HasDerivAt (fun t : ℝ => t * y * (t + y + 2 * z))
          (y * (2 * x + y + 2 * z)) x := by
      convert
        (((hasDerivAt_id x).mul (hasDerivAt_const x y)).mul
          (HasDerivAt.add
            (HasDerivAt.add (hasDerivAt_id x) (hasDerivAt_const x y))
            (hasDerivAt_const x (2 * z)))) using 1 <;> simp <;> ring
    exact h.deriv
  have hxB :
      deriv (fun t : ℝ => t * z * (t + 2 * y + z)) x =
        z * (2 * x + 2 * y + z) := by
    have h :
        HasDerivAt (fun t : ℝ => t * z * (t + 2 * y + z))
          (z * (2 * x + 2 * y + z)) x := by
      convert
        (((hasDerivAt_id x).mul (hasDerivAt_const x z)).mul
          (HasDerivAt.add
            (HasDerivAt.add (hasDerivAt_id x)
              (hasDerivAt_const x (2 * y)))
            (hasDerivAt_const x z))) using 1 <;> simp <;> ring
    exact h.deriv
  have hyA :
      deriv (fun t : ℝ => t * z * (2 * x + t + z)) y =
        z * (2 * x + 2 * y + z) := by
    have h :
        HasDerivAt (fun t : ℝ => t * z * (2 * x + t + z))
          (z * (2 * x + 2 * y + z)) y := by
      convert
        (((hasDerivAt_id y).mul (hasDerivAt_const y z)).mul
          (HasDerivAt.add
            (HasDerivAt.add (hasDerivAt_const y (2 * x))
              (hasDerivAt_id y))
            (hasDerivAt_const y z))) using 1 <;> simp <;> ring
    exact h.deriv
  apply Prod.ext
  · dsimp [curlOfField, curl, partialX, partialY, partialZ, field,
      curlExpansion]
    rw [hyC, hzB]
  · apply Prod.ext
    · dsimp [curlOfField, curl, partialX, partialY, partialZ, field,
        curlExpansion]
      rw [hzA, hxC]
    · dsimp [curlOfField, curl, partialX, partialY, partialZ, field,
        curlExpansion]
      rw [hxB, hyA]

theorem gap2 (p : Vec3) :
    curlExpansion p = (0, 0, 0) := by
  simp [curlExpansion]

theorem gap3 (p : Vec3) :
    curl field p = (0, 0, 0) ∧
      gradient basePotential p = field p := by
  constructor
  · calc
      curl field p = curlOfField p := rfl
      _ = curlExpansion p := gap1 p
      _ = (0, 0, 0) := gap2 p
  · exact basePotentialGradient_eq_field p

theorem gap4 (p : Vec3) :
    gradient basePotential p = field p ↔
      ∀ v : Vec3, potentialDifferential p v = fieldOneForm p v := by
  constructor
  · intro h v
    simpa [potentialDifferential, fieldOneForm, h]
  · intro _
    exact basePotentialGradient_eq_field p

theorem gap5 (p v : Vec3) :
    fieldOneForm p v = expandedOneForm p v := by
  rfl

theorem gap6 (p v : Vec3) :
    potentialDifferential p v = expandedOneForm p v := by
  have hgrad : gradient basePotential p = field p :=
    basePotentialGradient_eq_field p
  calc
    potentialDifferential p v = fieldOneForm p v := by
      simp [potentialDifferential, fieldOneForm, hgrad]
    _ = expandedOneForm p v := gap5 p v

theorem gap7 (p v : Vec3) :
    expandedOneForm p v = productRuleOneForm p v := by
  dsimp [expandedOneForm, productRuleOneForm]
  ring

theorem gap8 (p v : Vec3) :
    productRuleOneForm p v = dot (gradient basePotential p) v := by
  rw [basePotentialGradient_eq_field p]
  dsimp [productRuleOneForm, dot, field]
  ring

theorem gap9 (p v : Vec3) :
    potentialDifferential p v = fieldOneForm p v := by
  exact (gap6 p v).trans (gap5 p v).symm

theorem gap10 (p : Vec3) :
    ∀ C : ℝ, potentialFamilyGradient C p = field p := by
  intro C
  exact potentialFamilyGradient_eq_field C p

end

end ProofGap.Exercise4457
