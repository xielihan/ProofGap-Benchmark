import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise3423

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ

def partialX (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => u s y) x

def partialY (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => u x s) y

def radialValue (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  x ^ 2 + y ^ 2 + (z x y) ^ 2

def denominator (Φ : ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (c x y : ℝ) : ℝ :=
  c - 2 * z x y * deriv Φ (radialValue z x y)

def solvedX (Φ : ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (a c x y : ℝ) : ℝ :=
  (2 * x * deriv Φ (radialValue z x y) - a) /
    denominator Φ z c x y

def solvedY (Φ : ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (b c x y : ℝ) : ℝ :=
  (2 * y * deriv Φ (radialValue z x y) - b) /
    denominator Φ z c x y

def weightedNumerator (Φ : ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (a b c x y : ℝ) : ℝ :=
  (2 * x * deriv Φ (radialValue z x y) - a) *
      (c * y - b * z x y) +
    (2 * y * deriv Φ (radialValue z x y) - b) *
      (a * z x y - c * x)

def surface (Φ : ℝ → ℝ) (a b c : ℝ) : Set Point3 :=
  {p | a * p.x + b * p.y + c * p.z =
    Φ (p.x ^ 2 + p.y ^ 2 + p.z ^ 2)}

def plane (a b c d : ℝ) : Set Point3 :=
  {p | a * p.x + b * p.y + c * p.z = d}

def sphere (d : ℝ) : Set Point3 :=
  {p | p.x ^ 2 + p.y ^ 2 + p.z ^ 2 = d ^ 2}

def dot3 (p q : Point3) : ℝ :=
  p.x * q.x + p.y * q.y + p.z * q.z

def cross3 (p q : Point3) : Point3 :=
  ⟨p.y * q.z - p.z * q.y,
    p.z * q.x - p.x * q.z,
    p.x * q.y - p.y * q.x⟩

def graphNormal (z : ℝ → ℝ → ℝ) (p : Point3) : Point3 :=
  ⟨partialX z p.x p.y, partialY z p.x p.y, -1⟩

def coefficientVector (a b c : ℝ) : Point3 :=
  ⟨a, b, c⟩

def axisLine (a b c : ℝ) : Set Point3 :=
  {p | p.x / a = p.y / b ∧ p.y / b = p.z / c}

theorem gap1 (Φ : ℝ → ℝ) (z : ℝ → ℝ → ℝ) (a b c : ℝ)
    (hImplicit :
      ∀ x y,
        a * x + b * y + c * z x y = Φ (radialValue z x y))
    (hRegular :
      ∀ x y,
        DifferentiableAt ℝ (fun s => z s y) x ∧
          DifferentiableAt ℝ Φ (radialValue z x y)) :
    ∀ x y,
      a + c * partialX z x y =
        deriv Φ (radialValue z x y) *
          (2 * x + 2 * z x y * partialX z x y) := by
  intro x y
  have hz : HasDerivAt (fun s : ℝ => z s y) (partialX z x y) x := by
    simpa [partialX] using (hRegular x y).1.hasDerivAt
  have hleft :
      HasDerivAt (fun s : ℝ => a * s + b * y + c * z s y)
        (a + c * partialX z x y) x := by
    convert (((hasDerivAt_id x).const_mul a).add
      (hasDerivAt_const x (b * y))).add (hz.const_mul c) using 1 <;> ring
  have hx2 : HasDerivAt (fun s : ℝ => s * s) (2 * x) x := by
    convert (hasDerivAt_id x).mul (hasDerivAt_id x) using 1 <;>
      simp [id] <;> ring
  have hz2 : HasDerivAt (fun s : ℝ => z s y * z s y)
      (2 * z x y * partialX z x y) x := by
    convert hz.mul hz using 1 <;> ring
  have hrad : HasDerivAt (fun s : ℝ => radialValue z s y)
      (2 * x + 2 * z x y * partialX z x y) x := by
    have hy2 : HasDerivAt (fun _ : ℝ => y * y) 0 x :=
      hasDerivAt_const x (y * y)
    simpa [radialValue, pow_two] using (hx2.add hy2).add hz2
  have hright : HasDerivAt (fun s : ℝ => Φ (radialValue z s y))
      (deriv Φ (radialValue z x y) *
        (2 * x + 2 * z x y * partialX z x y)) x := by
    simpa [Function.comp_apply] using
      ((hRegular x y).2.hasDerivAt.comp x hrad)
  have hfun :
      (fun s : ℝ => a * s + b * y + c * z s y) =
        (fun s : ℝ => Φ (radialValue z s y)) :=
    funext (fun s => hImplicit s y)
  calc
    a + c * partialX z x y =
        deriv (fun s : ℝ => a * s + b * y + c * z s y) x :=
      hleft.deriv.symm
    _ = deriv (fun s : ℝ => Φ (radialValue z s y)) x :=
      congrArg (fun f : ℝ → ℝ => deriv f x) hfun
    _ = deriv Φ (radialValue z x y) *
          (2 * x + 2 * z x y * partialX z x y) :=
      hright.deriv

theorem gap2 (Φ : ℝ → ℝ) (z : ℝ → ℝ → ℝ) (a b c : ℝ)
    (hImplicit :
      ∀ x y,
        a * x + b * y + c * z x y = Φ (radialValue z x y))
    (hRegular :
      ∀ x y,
        DifferentiableAt ℝ (fun s => z x s) y ∧
          DifferentiableAt ℝ Φ (radialValue z x y)) :
    ∀ x y,
      b + c * partialY z x y =
        deriv Φ (radialValue z x y) *
          (2 * y + 2 * z x y * partialY z x y) := by
  intro x y
  have hz : HasDerivAt (fun s : ℝ => z x s) (partialY z x y) y := by
    simpa [partialY] using (hRegular x y).1.hasDerivAt
  have hleft :
      HasDerivAt (fun s : ℝ => a * x + b * s + c * z x s)
        (b + c * partialY z x y) y := by
    convert ((hasDerivAt_const y (a * x)).add
      ((hasDerivAt_id y).const_mul b)).add (hz.const_mul c) using 1 <;> ring
  have hy2 : HasDerivAt (fun s : ℝ => s * s) (2 * y) y := by
    convert (hasDerivAt_id y).mul (hasDerivAt_id y) using 1 <;>
      simp [id] <;> ring
  have hz2 : HasDerivAt (fun s : ℝ => z x s * z x s)
      (2 * z x y * partialY z x y) y := by
    convert hz.mul hz using 1 <;> ring
  have hrad : HasDerivAt (fun s : ℝ => radialValue z x s)
      (2 * y + 2 * z x y * partialY z x y) y := by
    have hx2 : HasDerivAt (fun _ : ℝ => x * x) 0 y :=
      hasDerivAt_const y (x * x)
    simpa [radialValue, pow_two] using (hx2.add hy2).add hz2
  have hright : HasDerivAt (fun s : ℝ => Φ (radialValue z x s))
      (deriv Φ (radialValue z x y) *
        (2 * y + 2 * z x y * partialY z x y)) y := by
    simpa [Function.comp_apply] using
      ((hRegular x y).2.hasDerivAt.comp y hrad)
  have hfun :
      (fun s : ℝ => a * x + b * s + c * z x s) =
        (fun s : ℝ => Φ (radialValue z x s)) :=
    funext (fun s => hImplicit x s)
  calc
    b + c * partialY z x y =
        deriv (fun s : ℝ => a * x + b * s + c * z x s) y :=
      hleft.deriv.symm
    _ = deriv (fun s : ℝ => Φ (radialValue z x s)) y :=
      congrArg (fun f : ℝ → ℝ => deriv f y) hfun
    _ = deriv Φ (radialValue z x y) *
          (2 * y + 2 * z x y * partialY z x y) :=
      hright.deriv

theorem gap3 (Φ : ℝ → ℝ) (z : ℝ → ℝ → ℝ) (a c : ℝ)
    (hDifferentiated :
      ∀ x y,
        a + c * partialX z x y =
          deriv Φ (radialValue z x y) *
            (2 * x + 2 * z x y * partialX z x y))
    (hDenom : ∀ x y, denominator Φ z c x y ≠ 0) :
    ∀ x y, partialX z x y = solvedX Φ z a c x y := by
  intro x y
  unfold solvedX
  apply (eq_div_iff (hDenom x y)).2
  have h := hDifferentiated x y
  unfold denominator
  ring_nf at h ⊢
  linarith

theorem gap4 (Φ : ℝ → ℝ) (z : ℝ → ℝ → ℝ) (b c : ℝ)
    (hDifferentiated :
      ∀ x y,
        b + c * partialY z x y =
          deriv Φ (radialValue z x y) *
            (2 * y + 2 * z x y * partialY z x y))
    (hDenom : ∀ x y, denominator Φ z c x y ≠ 0) :
    ∀ x y, partialY z x y = solvedY Φ z b c x y := by
  intro x y
  unfold solvedY
  apply (eq_div_iff (hDenom x y)).2
  have h := hDifferentiated x y
  unfold denominator
  ring_nf at h ⊢
  linarith

theorem gap5 (Φ : ℝ → ℝ) (z : ℝ → ℝ → ℝ) (a b c : ℝ)
    (hX : ∀ x y, partialX z x y = solvedX Φ z a c x y)
    (hY : ∀ x y, partialY z x y = solvedY Φ z b c x y) :
    ∀ x y,
      (c * y - b * z x y) * partialX z x y +
          (a * z x y - c * x) * partialY z x y =
        weightedNumerator Φ z a b c x y / denominator Φ z c x y := by
  intro x y
  rw [hX x y, hY x y]
  unfold solvedX solvedY weightedNumerator
  ring

theorem gap6 (Φ : ℝ → ℝ) (z : ℝ → ℝ → ℝ) (a b c : ℝ) :
    ∀ x y,
      weightedNumerator Φ z a b c x y / denominator Φ z c x y =
        (denominator Φ z c x y * (b * x - a * y)) /
          denominator Φ z c x y := by
  intro x y
  unfold weightedNumerator denominator
  ring

theorem gap7 (Φ : ℝ → ℝ) (z : ℝ → ℝ → ℝ) (a b c : ℝ)
    (hDenom : ∀ x y, denominator Φ z c x y ≠ 0) :
    ∀ x y,
      (denominator Φ z c x y * (b * x - a * y)) /
          denominator Φ z c x y =
        b * x - a * y := by
  intro x y
  field_simp [hDenom x y]

theorem gap8 (Φ : ℝ → ℝ) (z : ℝ → ℝ → ℝ) (a b c : ℝ)
    (hSubstitute :
      ∀ x y,
        (c * y - b * z x y) * partialX z x y +
            (a * z x y - c * x) * partialY z x y =
          weightedNumerator Φ z a b c x y / denominator Φ z c x y)
    (hCollect :
      ∀ x y,
        weightedNumerator Φ z a b c x y / denominator Φ z c x y =
          (denominator Φ z c x y * (b * x - a * y)) /
            denominator Φ z c x y)
    (hCancel :
      ∀ x y,
        (denominator Φ z c x y * (b * x - a * y)) /
            denominator Φ z c x y =
          b * x - a * y) :
    ∀ x y,
      (c * y - b * z x y) * partialX z x y +
          (a * z x y - c * x) * partialY z x y =
        b * x - a * y := by
  intro x y
  calc
    (c * y - b * z x y) * partialX z x y +
          (a * z x y - c * x) * partialY z x y =
        weightedNumerator Φ z a b c x y / denominator Φ z c x y :=
      hSubstitute x y
    _ = (denominator Φ z c x y * (b * x - a * y)) /
          denominator Φ z c x y := hCollect x y
    _ = b * x - a * y := hCancel x y

theorem gap9 (Φ : ℝ → ℝ) (z : ℝ → ℝ → ℝ) (a b c : ℝ)
    (hIdentity :
      ∀ x y,
        (c * y - b * z x y) * partialX z x y +
            (a * z x y - c * x) * partialY z x y =
          b * x - a * y) :
    ∀ p n r, p ∈ surface Φ a b c →
      p.z = z p.x p.y →
      n = graphNormal z p →
      r = coefficientVector a b c →
      dot3 n (cross3 p r) = 0 := by
  intro p n r hp hpz hn hr
  subst n
  subst r
  have h := hIdentity p.x p.y
  simp only [dot3, graphNormal, cross3, coefficientVector]
  rw [hpz]
  ring_nf at h ⊢
  linarith

theorem gap10 (Φ : ℝ → ℝ) (a b c d : ℝ) :
    ∀ p, p ∈ surface Φ a b c →
      p ∈ plane a b c d →
      p ∈ sphere d →
      d = Φ (d ^ 2) := by
  intro p hs hp hsp
  change a * p.x + b * p.y + c * p.z =
    Φ (p.x ^ 2 + p.y ^ 2 + p.z ^ 2) at hs
  change a * p.x + b * p.y + c * p.z = d at hp
  change p.x ^ 2 + p.y ^ 2 + p.z ^ 2 = d ^ 2 at hsp
  calc
    d = a * p.x + b * p.y + c * p.z := hp.symm
    _ = Φ (p.x ^ 2 + p.y ^ 2 + p.z ^ 2) := hs
    _ = Φ (d ^ 2) := congrArg Φ hsp

theorem gap11 (Φ : ℝ → ℝ) (a b c d : ℝ) (C : Set Point3)
    (hCurve : C = plane a b c d ∩ sphere d)
    (hRadius : d = Φ (d ^ 2)) :
    C ⊆ surface Φ a b c := by
  intro p hp
  rw [hCurve] at hp
  rcases hp with ⟨hp, hsp⟩
  change a * p.x + b * p.y + c * p.z = d at hp
  change p.x ^ 2 + p.y ^ 2 + p.z ^ 2 = d ^ 2 at hsp
  change a * p.x + b * p.y + c * p.z =
    Φ (p.x ^ 2 + p.y ^ 2 + p.z ^ 2)
  calc
    a * p.x + b * p.y + c * p.z = d := hp
    _ = Φ (d ^ 2) := hRadius
    _ = Φ (p.x ^ 2 + p.y ^ 2 + p.z ^ 2) := congrArg Φ hsp.symm

theorem gap12 (a b c d : ℝ) (C : Set Point3)
    (hCurve : C = plane a b c d ∩ sphere d) :
    C ⊆ sphere d := by
  intro p hp
  rw [hCurve] at hp
  exact hp.2

theorem gap13 (a b c : ℝ) :
    axisLine a b c =
      {p : Point3 | p.x / a = p.y / b ∧ p.y / b = p.z / c} := by
  rfl

theorem gap14 (z : ℝ → ℝ → ℝ) (a b c : ℝ)
    (hResult :
      ∀ x y,
        (c * y - b * z x y) * partialX z x y +
            (a * z x y - c * x) * partialY z x y =
          b * x - a * y) :
    ∀ x y,
      (c * y - b * z x y) * partialX z x y +
          (a * z x y - c * x) * partialY z x y =
        b * x - a * y := by
  exact hResult

end

end ProofGap.Exercise3423
