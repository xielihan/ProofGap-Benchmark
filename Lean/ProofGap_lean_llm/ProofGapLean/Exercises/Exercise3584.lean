import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3584

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ

def quadratic (A B C D E F : ℝ) (p : Point3) : ℝ :=
  A * p.x ^ 2 + B * p.y ^ 2 + C * p.z ^ 2 +
    2 * D * p.x * p.y + 2 * E * p.x * p.z + 2 * F * p.y * p.z

def partialX (f : Point3 → ℝ) (p : Point3) : ℝ :=
  deriv (fun t => f ⟨t, p.y, p.z⟩) p.x

def partialY (f : Point3 → ℝ) (p : Point3) : ℝ :=
  deriv (fun t => f ⟨p.x, t, p.z⟩) p.y

def partialZ (f : Point3 → ℝ) (p : Point3) : ℝ :=
  deriv (fun t => f ⟨p.x, p.y, t⟩) p.z

def partialXX (f : Point3 → ℝ) (p : Point3) : ℝ :=
  partialX (partialX f) p

def partialXY (f : Point3 → ℝ) (p : Point3) : ℝ :=
  partialY (partialX f) p

def partialYY (f : Point3 → ℝ) (p : Point3) : ℝ :=
  partialY (partialY f) p

def partialYZ (f : Point3 → ℝ) (p : Point3) : ℝ :=
  partialZ (partialY f) p

def partialZZ (f : Point3 → ℝ) (p : Point3) : ℝ :=
  partialZ (partialZ f) p

def partialZX (f : Point3 → ℝ) (p : Point3) : ℝ :=
  partialX (partialZ f) p

def add (p d : Point3) : Point3 :=
  ⟨p.x + d.x, p.y + d.y, p.z + d.z⟩

def linearTerm (A B C D E F : ℝ) (p d : Point3) : ℝ :=
  2 * (d.x * (A * p.x + D * p.y + E * p.z) +
    d.y * (B * p.y + D * p.x + F * p.z) +
    d.z * (C * p.z + E * p.x + F * p.y))

def quadraticStep (A B C D E F : ℝ) (d : Point3) : ℝ :=
  A * d.x ^ 2 + B * d.y ^ 2 + C * d.z ^ 2 +
    2 * D * d.x * d.y + 2 * E * d.x * d.z + 2 * F * d.y * d.z

def remainder2 (A B C D E F : ℝ) (p d : Point3) : ℝ :=
  quadratic A B C D E F (add p d) -
    (quadratic A B C D E F p + linearTerm A B C D E F p d +
      quadraticStep A B C D E F d)

private theorem deriv_quadratic_polynomial (a b c x : ℝ) :
    deriv (fun t : ℝ => a * t ^ 2 + b * t + c) x = 2 * a * x + b := by
  have hid : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
  have hsquare :
      HasDerivAt (fun t : ℝ => t * t) (1 * x + x * 1) x := hid.mul hid
  have ha :
      HasDerivAt (fun t : ℝ => a * (t * t))
        (0 * (x * x) + a * (1 * x + x * 1)) x :=
    (hasDerivAt_const x a).mul hsquare
  have hb :
      HasDerivAt (fun t : ℝ => b * t) (0 * x + b * 1) x :=
    (hasDerivAt_const x b).mul hid
  have hc : HasDerivAt (fun _ : ℝ => c) 0 x := hasDerivAt_const x c
  have htarget :
      HasDerivAt (fun t : ℝ => a * t ^ 2 + b * t + c) (2 * a * x + b) x := by
    convert (ha.add hb).add hc using 1
    all_goals
      try funext t
      dsimp
      ring
  exact htarget.deriv

theorem gap1 (A B C D E F : ℝ) :
    ∀ p : Point3,
      partialX (quadratic A B C D E F) p =
        2 * (A * p.x + D * p.y + E * p.z) := by
  intro p
  change deriv (fun t : ℝ => quadratic A B C D E F ⟨t, p.y, p.z⟩) p.x = _
  have hfun :
      (fun t : ℝ => quadratic A B C D E F ⟨t, p.y, p.z⟩) =
        (fun t : ℝ =>
          A * t ^ 2 + (2 * D * p.y + 2 * E * p.z) * t +
            (B * p.y ^ 2 + C * p.z ^ 2 + 2 * F * p.y * p.z)) := by
    funext t
    unfold quadratic
    ring
  rw [hfun, deriv_quadratic_polynomial]
  ring

theorem gap2 (A B C D E F : ℝ) :
    ∀ p : Point3, partialXX (quadratic A B C D E F) p = 2 * A := by
  intro p
  change deriv
    (fun t : ℝ => partialX (quadratic A B C D E F) ⟨t, p.y, p.z⟩) p.x = _
  have hfun :
      (fun t : ℝ => partialX (quadratic A B C D E F) ⟨t, p.y, p.z⟩) =
        (fun t : ℝ =>
          0 * t ^ 2 + (2 * A) * t + 2 * (D * p.y + E * p.z)) := by
    funext t
    rw [gap1 A B C D E F]
    ring
  rw [hfun, deriv_quadratic_polynomial]
  ring

theorem gap3 (A B C D E F : ℝ) :
    ∀ p : Point3, partialXY (quadratic A B C D E F) p = 2 * D := by
  intro p
  change deriv
    (fun t : ℝ => partialX (quadratic A B C D E F) ⟨p.x, t, p.z⟩) p.y = _
  have hfun :
      (fun t : ℝ => partialX (quadratic A B C D E F) ⟨p.x, t, p.z⟩) =
        (fun t : ℝ =>
          0 * t ^ 2 + (2 * D) * t + 2 * (A * p.x + E * p.z)) := by
    funext t
    rw [gap1 A B C D E F]
    ring
  rw [hfun, deriv_quadratic_polynomial]
  ring

theorem gap4 (A B C D E F : ℝ) :
    ∀ p : Point3,
      partialY (quadratic A B C D E F) p =
        2 * (B * p.y + D * p.x + F * p.z) := by
  intro p
  change deriv (fun t : ℝ => quadratic A B C D E F ⟨p.x, t, p.z⟩) p.y = _
  have hfun :
      (fun t : ℝ => quadratic A B C D E F ⟨p.x, t, p.z⟩) =
        (fun t : ℝ =>
          B * t ^ 2 + (2 * D * p.x + 2 * F * p.z) * t +
            (A * p.x ^ 2 + C * p.z ^ 2 + 2 * E * p.x * p.z)) := by
    funext t
    unfold quadratic
    ring
  rw [hfun, deriv_quadratic_polynomial]
  ring

theorem gap5 (A B C D E F : ℝ) :
    ∀ p : Point3, partialYY (quadratic A B C D E F) p = 2 * B := by
  intro p
  change deriv
    (fun t : ℝ => partialY (quadratic A B C D E F) ⟨p.x, t, p.z⟩) p.y = _
  have hfun :
      (fun t : ℝ => partialY (quadratic A B C D E F) ⟨p.x, t, p.z⟩) =
        (fun t : ℝ =>
          0 * t ^ 2 + (2 * B) * t + 2 * (D * p.x + F * p.z)) := by
    funext t
    rw [gap4 A B C D E F]
    ring
  rw [hfun, deriv_quadratic_polynomial]
  ring

theorem gap6 (A B C D E F : ℝ) :
    ∀ p : Point3, partialYZ (quadratic A B C D E F) p = 2 * F := by
  intro p
  change deriv
    (fun t : ℝ => partialY (quadratic A B C D E F) ⟨p.x, p.y, t⟩) p.z = _
  have hfun :
      (fun t : ℝ => partialY (quadratic A B C D E F) ⟨p.x, p.y, t⟩) =
        (fun t : ℝ =>
          0 * t ^ 2 + (2 * F) * t + 2 * (B * p.y + D * p.x)) := by
    funext t
    rw [gap4 A B C D E F]
    ring
  rw [hfun, deriv_quadratic_polynomial]
  ring

theorem gap7 (A B C D E F : ℝ) :
    ∀ p : Point3,
      partialZ (quadratic A B C D E F) p =
        2 * (C * p.z + E * p.x + F * p.y) := by
  intro p
  change deriv (fun t : ℝ => quadratic A B C D E F ⟨p.x, p.y, t⟩) p.z = _
  have hfun :
      (fun t : ℝ => quadratic A B C D E F ⟨p.x, p.y, t⟩) =
        (fun t : ℝ =>
          C * t ^ 2 + (2 * E * p.x + 2 * F * p.y) * t +
            (A * p.x ^ 2 + B * p.y ^ 2 + 2 * D * p.x * p.y)) := by
    funext t
    unfold quadratic
    ring
  rw [hfun, deriv_quadratic_polynomial]
  ring

theorem gap8 (A B C D E F : ℝ) :
    ∀ p : Point3, partialZZ (quadratic A B C D E F) p = 2 * C := by
  intro p
  change deriv
    (fun t : ℝ => partialZ (quadratic A B C D E F) ⟨p.x, p.y, t⟩) p.z = _
  have hfun :
      (fun t : ℝ => partialZ (quadratic A B C D E F) ⟨p.x, p.y, t⟩) =
        (fun t : ℝ =>
          0 * t ^ 2 + (2 * C) * t + 2 * (E * p.x + F * p.y)) := by
    funext t
    rw [gap7 A B C D E F]
    ring
  rw [hfun, deriv_quadratic_polynomial]
  ring

theorem gap9 (A B C D E F : ℝ) :
    ∀ p : Point3, partialZX (quadratic A B C D E F) p = 2 * E := by
  intro p
  change deriv
    (fun t : ℝ => partialZ (quadratic A B C D E F) ⟨t, p.y, p.z⟩) p.x = _
  have hfun :
      (fun t : ℝ => partialZ (quadratic A B C D E F) ⟨t, p.y, p.z⟩) =
        (fun t : ℝ =>
          0 * t ^ 2 + (2 * E) * t + 2 * (C * p.z + F * p.y)) := by
    funext t
    rw [gap7 A B C D E F]
    ring
  rw [hfun, deriv_quadratic_polynomial]
  ring

theorem gap10 (A B C D E F : ℝ) :
    ∀ p d : Point3, remainder2 A B C D E F p d = 0 := by
  intro p d
  unfold remainder2 quadratic add linearTerm quadraticStep
  ring

theorem gap11 (A B C D E F : ℝ) :
    ∀ p d : Point3,
      quadratic A B C D E F (add p d) =
        quadratic A B C D E F p + linearTerm A B C D E F p d +
          quadraticStep A B C D E F d := by
  intro p d
  have h := gap10 A B C D E F p d
  unfold remainder2 at h
  exact sub_eq_zero.mp h

theorem gap12 (A B C D E F : ℝ) :
    ∀ p d : Point3,
      quadratic A B C D E F (add p d) =
        quadratic A B C D E F p +
          2 * (d.x * (A * p.x + D * p.y + E * p.z) +
            d.y * (B * p.y + D * p.x + F * p.z) +
            d.z * (C * p.z + E * p.x + F * p.y)) +
          A * d.x ^ 2 + B * d.y ^ 2 + C * d.z ^ 2 +
          2 * D * d.x * d.y + 2 * E * d.x * d.z +
          2 * F * d.y * d.z := by
  intro p d
  rw [gap11 A B C D E F p d]
  unfold linearTerm quadraticStep
  ring

theorem gap13 (A B C D E F : ℝ) :
    ∀ p d : Point3,
      quadratic A B C D E F (add p d) =
        quadratic A B C D E F p +
          2 * (d.x * (A * p.x + D * p.y + E * p.z) +
            d.y * (D * p.x + B * p.y + F * p.z) +
            d.z * (E * p.x + F * p.y + C * p.z)) +
          quadratic A B C D E F d := by
  intro p d
  rw [gap11 A B C D E F p d]
  unfold linearTerm quadraticStep quadratic
  ring

end

end ProofGap.Exercise3584
