import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3421

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ

def partialX (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => u s y) x

def partialY (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => u x s) y

def phiX (Φ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => Φ s y) x

def phiY (Φ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => Φ x s) y

def denominator (Φ : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (a b x y : ℝ) : ℝ :=
  a * phiX Φ (x - a * z x y) (y - b * z x y) +
    b * phiY Φ (x - a * z x y) (y - b * z x y)

def surface (Φ : ℝ → ℝ → ℝ) (a b : ℝ) : Set Point3 :=
  {p | Φ (p.x - a * p.z) (p.y - b * p.z) = 0}

def dot3 (p q : Point3) : ℝ :=
  p.x * q.x + p.y * q.y + p.z * q.z

def graphNormal (z : ℝ → ℝ → ℝ) (p : Point3) : Point3 :=
  ⟨partialX z p.x p.y, partialY z p.x p.y, -1⟩

def characteristicDirection (a b : ℝ) : Point3 :=
  ⟨a, b, 1⟩

def characteristicLine (a b : ℝ) (p : Point3) : Set Point3 :=
  {q | ∃ s : ℝ,
    q = ⟨p.x + s * a, p.y + s * b, p.z + s⟩}

private theorem chain_rule_uncurry
    (Φ : ℝ → ℝ → ℝ) (u v : ℝ → ℝ) (t : ℝ)
    (hu : DifferentiableAt ℝ u t)
    (hv : DifferentiableAt ℝ v t)
    (hΦ : DifferentiableAt ℝ (Function.uncurry Φ) (u t, v t)) :
    deriv (fun s => Φ (u s) (v s)) t =
      phiX Φ (u t) (v t) * deriv u t +
        phiY Φ (u t) (v t) * deriv v t := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ :=
    fderiv ℝ (Function.uncurry Φ) (u t, v t)
  have hcurve :
      HasDerivAt (fun s : ℝ => (u s, v s))
        (deriv u t, deriv v t) t :=
    hu.hasDerivAt.prodMk hv.hasDerivAt
  have hcomp :
      HasDerivAt (fun s : ℝ => Φ (u s) (v s))
        (L (deriv u t, deriv v t)) t := by
    simpa [L, Function.comp_def, Function.uncurry] using
      hΦ.hasFDerivAt.comp_hasDerivAt t hcurve
  have hxcurve :
      HasDerivAt (fun s : ℝ => (s, v t)) (1, 0) (u t) :=
    (hasDerivAt_id (u t)).prodMk
      (hasDerivAt_const (x := u t) (c := v t))
  have hxcomp :
      HasDerivAt (fun s : ℝ => Φ s (v t)) (L (1, 0)) (u t) := by
    simpa [L, Function.comp_def, Function.uncurry] using
      hΦ.hasFDerivAt.comp_hasDerivAt (u t) hxcurve
  have hx : phiX Φ (u t) (v t) = L (1, 0) := by
    simpa [phiX] using hxcomp.deriv
  have hycurve :
      HasDerivAt (fun s : ℝ => (u t, s)) (0, 1) (v t) :=
    (hasDerivAt_const (x := v t) (c := u t)).prodMk
      (hasDerivAt_id (v t))
  have hycomp :
      HasDerivAt (fun s : ℝ => Φ (u t) s) (L (0, 1)) (v t) := by
    simpa [L, Function.comp_def, Function.uncurry] using
      hΦ.hasFDerivAt.comp_hasDerivAt (v t) hycurve
  have hy : phiY Φ (u t) (v t) = L (0, 1) := by
    simpa [phiY] using hycomp.deriv
  calc
    deriv (fun s => Φ (u s) (v s)) t =
        L (deriv u t, deriv v t) := hcomp.deriv
    _ = L ((deriv u t) • (1, 0) + (deriv v t) • (0, 1)) := by
      apply congrArg L
      ext <;> simp
    _ = (deriv u t) • L (1, 0) + (deriv v t) • L (0, 1) := by
      rw [map_add, map_smul, map_smul]
    _ = phiX Φ (u t) (v t) * deriv u t +
        phiY Φ (u t) (v t) * deriv v t := by
      rw [← hx, ← hy]
      simp [smul_eq_mul, mul_comm]

theorem gap1 (Φ : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ) (a b : ℝ)
    (hImplicit : ∀ x y, Φ (x - a * z x y) (y - b * z x y) = 0)
    (hRegular :
      ∀ x y,
        DifferentiableAt ℝ (fun s => z s y) x ∧
          DifferentiableAt ℝ (Function.uncurry Φ)
            (x - a * z x y, y - b * z x y)) :
    ∀ x y,
      phiX Φ (x - a * z x y) (y - b * z x y) *
          (1 - a * partialX z x y) -
        b * phiY Φ (x - a * z x y) (y - b * z x y) *
          partialX z x y = 0 := by
  intro x y
  have hu : HasDerivAt (fun s : ℝ => s - a * z s y)
      (1 - a * partialX z x y) x := by
    simpa [partialX] using
      ((hasDerivAt_id x).sub
        ((hRegular x y).1.hasDerivAt.const_mul a))
  have hv : HasDerivAt (fun s : ℝ => y - b * z s y)
      (-b * partialX z x y) x := by
    simpa [partialX] using
      ((hasDerivAt_const (x := x) (c := y)).sub
        ((hRegular x y).1.hasDerivAt.const_mul b))
  have hzero :
      deriv (fun s : ℝ => Φ (s - a * z s y) (y - b * z s y)) x = 0 := by
    have hfun :
        (fun s : ℝ => Φ (s - a * z s y) (y - b * z s y)) =
          (fun _ : ℝ => 0) := by
      funext s
      exact hImplicit s y
    rw [hfun]
    simp
  have hchain :=
    chain_rule_uncurry Φ (fun s : ℝ => s - a * z s y)
      (fun s : ℝ => y - b * z s y) x
      hu.differentiableAt hv.differentiableAt (hRegular x y).2
  rw [hzero, hu.deriv, hv.deriv] at hchain
  calc
    phiX Φ (x - a * z x y) (y - b * z x y) *
          (1 - a * partialX z x y) -
        b * phiY Φ (x - a * z x y) (y - b * z x y) *
          partialX z x y =
        phiX Φ (x - a * z x y) (y - b * z x y) *
            (1 - a * partialX z x y) +
          phiY Φ (x - a * z x y) (y - b * z x y) *
            (-b * partialX z x y) := by ring_nf
    _ = 0 := hchain.symm

theorem gap2 (Φ : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ) (a b : ℝ)
    (hImplicit : ∀ x y, Φ (x - a * z x y) (y - b * z x y) = 0)
    (hRegular :
      ∀ x y,
        DifferentiableAt ℝ (fun s => z x s) y ∧
          DifferentiableAt ℝ (Function.uncurry Φ)
            (x - a * z x y, y - b * z x y)) :
    ∀ x y,
      -phiX Φ (x - a * z x y) (y - b * z x y) *
            a * partialY z x y +
        phiY Φ (x - a * z x y) (y - b * z x y) *
          (1 - b * partialY z x y) = 0 := by
  intro x y
  have hu : HasDerivAt (fun s : ℝ => x - a * z x s)
      (-a * partialY z x y) y := by
    simpa [partialY] using
      ((hasDerivAt_const (x := y) (c := x)).sub
        ((hRegular x y).1.hasDerivAt.const_mul a))
  have hv : HasDerivAt (fun s : ℝ => s - b * z x s)
      (1 - b * partialY z x y) y := by
    simpa [partialY] using
      ((hasDerivAt_id y).sub
        ((hRegular x y).1.hasDerivAt.const_mul b))
  have hzero :
      deriv (fun s : ℝ => Φ (x - a * z x s) (s - b * z x s)) y = 0 := by
    have hfun :
        (fun s : ℝ => Φ (x - a * z x s) (s - b * z x s)) =
          (fun _ : ℝ => 0) := by
      funext s
      exact hImplicit x s
    rw [hfun]
    simp
  have hchain :=
    chain_rule_uncurry Φ (fun s : ℝ => x - a * z x s)
      (fun s : ℝ => s - b * z x s) y
      hu.differentiableAt hv.differentiableAt (hRegular x y).2
  rw [hzero, hu.deriv, hv.deriv] at hchain
  calc
    -phiX Φ (x - a * z x y) (y - b * z x y) *
          a * partialY z x y +
        phiY Φ (x - a * z x y) (y - b * z x y) *
          (1 - b * partialY z x y) =
        phiX Φ (x - a * z x y) (y - b * z x y) *
            (-a * partialY z x y) +
          phiY Φ (x - a * z x y) (y - b * z x y) *
            (1 - b * partialY z x y) := by ring_nf
    _ = 0 := hchain.symm

theorem gap3 (Φ : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ) (a b : ℝ)
    (hDifferentiated :
      ∀ x y,
        phiX Φ (x - a * z x y) (y - b * z x y) *
            (1 - a * partialX z x y) -
          b * phiY Φ (x - a * z x y) (y - b * z x y) *
            partialX z x y = 0)
    (hDenom : ∀ x y, denominator Φ z a b x y ≠ 0) :
    ∀ x y,
      partialX z x y =
        phiX Φ (x - a * z x y) (y - b * z x y) /
          denominator Φ z a b x y := by
  intro x y
  apply (eq_div_iff (hDenom x y)).2
  unfold denominator
  nlinarith [hDifferentiated x y]

theorem gap4 (Φ : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ) (a b : ℝ)
    (hDifferentiated :
      ∀ x y,
        -phiX Φ (x - a * z x y) (y - b * z x y) *
              a * partialY z x y +
          phiY Φ (x - a * z x y) (y - b * z x y) *
            (1 - b * partialY z x y) = 0)
    (hDenom : ∀ x y, denominator Φ z a b x y ≠ 0) :
    ∀ x y,
      partialY z x y =
        phiY Φ (x - a * z x y) (y - b * z x y) /
          denominator Φ z a b x y := by
  intro x y
  apply (eq_div_iff (hDenom x y)).2
  unfold denominator
  nlinarith [hDifferentiated x y]

theorem gap5 (Φ : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ) (a b : ℝ)
    (hX :
      ∀ x y,
        partialX z x y =
          phiX Φ (x - a * z x y) (y - b * z x y) /
            denominator Φ z a b x y) :
    ∀ x y,
      a * partialX z x y =
        (a * phiX Φ (x - a * z x y) (y - b * z x y)) /
          denominator Φ z a b x y := by
  intro x y
  rw [hX x y]
  ring_nf

theorem gap6 (Φ : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ) (a b : ℝ)
    (hY :
      ∀ x y,
        partialY z x y =
          phiY Φ (x - a * z x y) (y - b * z x y) /
            denominator Φ z a b x y) :
    ∀ x y,
      b * partialY z x y =
        (b * phiY Φ (x - a * z x y) (y - b * z x y)) /
          denominator Φ z a b x y := by
  intro x y
  rw [hY x y]
  ring_nf

theorem gap7 (Φ : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ) (a b : ℝ)
    (hX :
      ∀ x y,
        a * partialX z x y =
          (a * phiX Φ (x - a * z x y) (y - b * z x y)) /
            denominator Φ z a b x y)
    (hY :
      ∀ x y,
        b * partialY z x y =
          (b * phiY Φ (x - a * z x y) (y - b * z x y)) /
            denominator Φ z a b x y)
    (hDenom : ∀ x y, denominator Φ z a b x y ≠ 0) :
    ∀ x y, a * partialX z x y + b * partialY z x y = 1 := by
  intro x y
  rw [hX x y, hY x y, ← add_div]
  change denominator Φ z a b x y / denominator Φ z a b x y = 1
  exact div_self (hDenom x y)

theorem gap8 (Φ : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ) (a b : ℝ)
    (hEuler : ∀ x y, a * partialX z x y + b * partialY z x y = 1) :
    ∀ p n r, p ∈ surface Φ a b →
      n = graphNormal z p →
      r = characteristicDirection a b →
      dot3 n r = 0 := by
  intro p n r hp hn hr
  subst n
  subst r
  dsimp [dot3, graphNormal, characteristicDirection]
  nlinarith [hEuler p.x p.y]

theorem gap9 (Φ : ℝ → ℝ → ℝ) (a b : ℝ) :
    ∀ p l, p ∈ surface Φ a b →
      l = characteristicLine a b p →
      l ⊆ surface Φ a b := by
  intro p l hp hl
  subst l
  intro q hq
  rcases hq with ⟨s, rfl⟩
  change Φ (p.x - a * p.z) (p.y - b * p.z) = 0 at hp
  change
    Φ ((p.x + s * a) - a * (p.z + s))
      ((p.y + s * b) - b * (p.z + s)) = 0
  have hx :
      (p.x + s * a) - a * (p.z + s) = p.x - a * p.z := by
    ring_nf
  have hy :
      (p.y + s * b) - b * (p.z + s) = p.y - b * p.z := by
    ring_nf
  rw [hx, hy]
  exact hp

theorem gap10 (Φ : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ) (a b : ℝ)
    (hResult : ∀ x y, a * partialX z x y + b * partialY z x y = 1) :
    ∀ x y, a * partialX z x y + b * partialY z x y = 1 := by
  intro x y
  exact hResult x y

end

end ProofGap.Exercise3421
