import Mathlib.Analysis.Calculus.Deriv.Basic
import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3422

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

def ratioX (z : ℝ → ℝ → ℝ) (x₀ z₀ x y : ℝ) : ℝ :=
  (x - x₀) / (z x y - z₀)

def ratioY (z : ℝ → ℝ → ℝ) (y₀ z₀ x y : ℝ) : ℝ :=
  (y - y₀) / (z x y - z₀)

def denominator (Φ : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x₀ y₀ z₀ x y : ℝ) : ℝ :=
  (x - x₀) * phiX Φ (ratioX z x₀ z₀ x y) (ratioY z y₀ z₀ x y) +
    (y - y₀) * phiY Φ (ratioX z x₀ z₀ x y) (ratioY z y₀ z₀ x y)

def surface (Φ : ℝ → ℝ → ℝ) (p₀ : Point3) : Set Point3 :=
  {p |
    Φ ((p.x - p₀.x) / (p.z - p₀.z))
      ((p.y - p₀.y) / (p.z - p₀.z)) = 0}

def dot3 (p q : Point3) : ℝ :=
  p.x * q.x + p.y * q.y + p.z * q.z

def graphNormal (z : ℝ → ℝ → ℝ) (p : Point3) : Point3 :=
  ⟨partialX z p.x p.y, partialY z p.x p.y, -1⟩

def radialDirection (p₀ p : Point3) : Point3 :=
  ⟨p.x - p₀.x, p.y - p₀.y, p.z - p₀.z⟩

def radialLine (p₀ p : Point3) : Set Point3 :=
  {q | ∃ s : ℝ,
    q = ⟨p₀.x + s * (p.x - p₀.x),
      p₀.y + s * (p.y - p₀.y),
      p₀.z + s * (p.z - p₀.z)⟩}

private theorem hasDerivAt_binary_comp
    (Φ : ℝ → ℝ → ℝ) (a b : ℝ → ℝ) (x a' b' : ℝ)
    (hΦ : DifferentiableAt ℝ (Function.uncurry Φ) (a x, b x))
    (ha : HasDerivAt a a' x) (hb : HasDerivAt b b' x) :
    HasDerivAt (fun s => Φ (a s) (b s))
      (phiX Φ (a x) (b x) * a' + phiY Φ (a x) (b x) * b') x := by
  let F : ℝ × ℝ → ℝ := Function.uncurry Φ
  let L : (ℝ × ℝ) →L[ℝ] ℝ := fderiv ℝ F (a x, b x)
  have hF : HasFDerivAt F L (a x, b x) := hΦ.hasFDerivAt
  have hcompF :=
    hF.comp x (ha.hasFDerivAt.prodMk hb.hasFDerivAt)
  have hcomp :
      HasDerivAt (fun s => Φ (a s) (b s)) (L (a', b')) x := by
    convert hcompF.hasDerivAt using 1 <;>
      simp [F, L, Function.comp_def]
  have hfirstF :=
    hF.comp (a x)
      ((hasDerivAt_id (a x)).hasFDerivAt.prodMk
        (hasDerivAt_const (a x) (b x)).hasFDerivAt)
  have hfirst :
      HasDerivAt (fun s => Φ s (b x)) (L (1, 0)) (a x) := by
    convert hfirstF.hasDerivAt using 1 <;>
      simp [F, L, Function.comp_def]
  have hsecondF :=
    hF.comp (b x)
      ((hasDerivAt_const (b x) (a x)).hasFDerivAt.prodMk
        (hasDerivAt_id (b x)).hasFDerivAt)
  have hsecond :
      HasDerivAt (fun s => Φ (a x) s) (L (0, 1)) (b x) := by
    convert hsecondF.hasDerivAt using 1 <;>
      simp [F, L, Function.comp_def]
  have hLx : L (1, 0) = phiX Φ (a x) (b x) := by
    simpa [phiX] using hfirst.deriv.symm
  have hLy : L (0, 1) = phiY Φ (a x) (b x) := by
    simpa [phiY] using hsecond.deriv.symm
  have hlin :
      L (a', b') =
        phiX Φ (a x) (b x) * a' + phiY Φ (a x) (b x) * b' := by
    calc
      L (a', b') = L (a' • (1, 0) + b' • (0, 1)) := by
        congr 1
        ext <;> simp
      _ = a' • L (1, 0) + b' • L (0, 1) := by
        rw [map_add, map_smul, map_smul]
      _ = phiX Φ (a x) (b x) * a' +
          phiY Φ (a x) (b x) * b' := by
        rw [hLx, hLy]
        simp [mul_comm]
  rw [hlin] at hcomp
  exact hcomp

theorem gap1 (Φ : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x₀ y₀ z₀ : ℝ)
    (hImplicit :
      ∀ x y, Φ (ratioX z x₀ z₀ x y) (ratioY z y₀ z₀ x y) = 0)
    (hNonzero : ∀ x y, z x y - z₀ ≠ 0)
    (hRegular :
      ∀ x y,
        DifferentiableAt ℝ (fun s => z s y) x ∧
          DifferentiableAt ℝ (Function.uncurry Φ)
            (ratioX z x₀ z₀ x y, ratioY z y₀ z₀ x y)) :
    ∀ x y,
      phiX Φ (ratioX z x₀ z₀ x y) (ratioY z y₀ z₀ x y) *
          ((z x y - z₀ - (x - x₀) * partialX z x y) /
            (z x y - z₀) ^ 2) -
        phiY Φ (ratioX z x₀ z₀ x y) (ratioY z y₀ z₀ x y) *
          (((y - y₀) * partialX z x y) / (z x y - z₀) ^ 2) = 0 := by
  intro x y
  have hd : HasDerivAt (fun s => z s y - z₀) (partialX z x y) x := by
    simpa [partialX] using
      ((hRegular x y).1.hasDerivAt.sub_const z₀)
  have ha :
      HasDerivAt (fun s => ratioX z x₀ z₀ s y)
        ((z x y - z₀ - (x - x₀) * partialX z x y) /
          (z x y - z₀) ^ 2) x := by
    simpa [ratioX] using
      ((hasDerivAt_id x).sub_const x₀).div hd (hNonzero x y)
  have hb :
      HasDerivAt (fun s => ratioY z y₀ z₀ s y)
        (-((y - y₀) * partialX z x y) /
          (z x y - z₀) ^ 2) x := by
    simpa [ratioY] using
      (hasDerivAt_const x (y - y₀)).div hd (hNonzero x y)
  have hc :=
    hasDerivAt_binary_comp Φ
      (fun s => ratioX z x₀ z₀ s y)
      (fun s => ratioY z y₀ z₀ s y) x
      ((z x y - z₀ - (x - x₀) * partialX z x y) /
        (z x y - z₀) ^ 2)
      (-((y - y₀) * partialX z x y) /
        (z x y - z₀) ^ 2)
      (hRegular x y).2 ha hb
  have hz :
      HasDerivAt
        (fun s =>
          Φ (ratioX z x₀ z₀ s y) (ratioY z y₀ z₀ s y)) 0 x := by
    simpa only [hImplicit] using (hasDerivAt_const x (0 : ℝ))
  have h := hc.unique hz
  simpa [neg_div, mul_neg, sub_eq_add_neg] using h

theorem gap2 (Φ : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x₀ y₀ z₀ : ℝ)
    (hImplicit :
      ∀ x y, Φ (ratioX z x₀ z₀ x y) (ratioY z y₀ z₀ x y) = 0)
    (hNonzero : ∀ x y, z x y - z₀ ≠ 0)
    (hRegular :
      ∀ x y,
        DifferentiableAt ℝ (fun s => z x s) y ∧
          DifferentiableAt ℝ (Function.uncurry Φ)
            (ratioX z x₀ z₀ x y, ratioY z y₀ z₀ x y)) :
    ∀ x y,
      -phiX Φ (ratioX z x₀ z₀ x y) (ratioY z y₀ z₀ x y) *
            (((x - x₀) * partialY z x y) / (z x y - z₀) ^ 2) +
        phiY Φ (ratioX z x₀ z₀ x y) (ratioY z y₀ z₀ x y) *
          ((z x y - z₀ - (y - y₀) * partialY z x y) /
            (z x y - z₀) ^ 2) = 0 := by
  intro x y
  have hd : HasDerivAt (fun s => z x s - z₀) (partialY z x y) y := by
    simpa [partialY] using
      ((hRegular x y).1.hasDerivAt.sub_const z₀)
  have ha :
      HasDerivAt (fun s => ratioX z x₀ z₀ x s)
        (-((x - x₀) * partialY z x y) /
          (z x y - z₀) ^ 2) y := by
    simpa [ratioX] using
      (hasDerivAt_const y (x - x₀)).div hd (hNonzero x y)
  have hb :
      HasDerivAt (fun s => ratioY z y₀ z₀ x s)
        ((z x y - z₀ - (y - y₀) * partialY z x y) /
          (z x y - z₀) ^ 2) y := by
    simpa [ratioY] using
      ((hasDerivAt_id y).sub_const y₀).div hd (hNonzero x y)
  have hc :=
    hasDerivAt_binary_comp Φ
      (fun s => ratioX z x₀ z₀ x s)
      (fun s => ratioY z y₀ z₀ x s) y
      (-((x - x₀) * partialY z x y) /
        (z x y - z₀) ^ 2)
      ((z x y - z₀ - (y - y₀) * partialY z x y) /
        (z x y - z₀) ^ 2)
      (hRegular x y).2 ha hb
  have hz :
      HasDerivAt
        (fun s =>
          Φ (ratioX z x₀ z₀ x s) (ratioY z y₀ z₀ x s)) 0 y := by
    simpa only [hImplicit] using (hasDerivAt_const y (0 : ℝ))
  have h := hc.unique hz
  simpa [neg_div, mul_neg, neg_mul, sub_eq_add_neg] using h

theorem gap3 (Φ : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x₀ y₀ z₀ : ℝ)
    (hDifferentiated :
      ∀ x y,
        phiX Φ (ratioX z x₀ z₀ x y) (ratioY z y₀ z₀ x y) *
            ((z x y - z₀ - (x - x₀) * partialX z x y) /
              (z x y - z₀) ^ 2) -
          phiY Φ (ratioX z x₀ z₀ x y) (ratioY z y₀ z₀ x y) *
            (((y - y₀) * partialX z x y) / (z x y - z₀) ^ 2) = 0)
    (hZ : ∀ x y, z x y - z₀ ≠ 0)
    (hDenom : ∀ x y, denominator Φ z x₀ y₀ z₀ x y ≠ 0) :
    ∀ x y,
      partialX z x y =
        ((z x y - z₀) *
            phiX Φ (ratioX z x₀ z₀ x y) (ratioY z y₀ z₀ x y)) /
          denominator Φ z x₀ y₀ z₀ x y := by
  intro x y
  have hd := hDifferentiated x y
  apply (eq_div_iff (hDenom x y)).2
  simp only [denominator]
  field_simp [hZ x y] at hd
  nlinarith [hd]

theorem gap4 (Φ : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x₀ y₀ z₀ : ℝ)
    (hDifferentiated :
      ∀ x y,
        -phiX Φ (ratioX z x₀ z₀ x y) (ratioY z y₀ z₀ x y) *
              (((x - x₀) * partialY z x y) / (z x y - z₀) ^ 2) +
          phiY Φ (ratioX z x₀ z₀ x y) (ratioY z y₀ z₀ x y) *
            ((z x y - z₀ - (y - y₀) * partialY z x y) /
              (z x y - z₀) ^ 2) = 0)
    (hZ : ∀ x y, z x y - z₀ ≠ 0)
    (hDenom : ∀ x y, denominator Φ z x₀ y₀ z₀ x y ≠ 0) :
    ∀ x y,
      partialY z x y =
        ((z x y - z₀) *
            phiY Φ (ratioX z x₀ z₀ x y) (ratioY z y₀ z₀ x y)) /
          denominator Φ z x₀ y₀ z₀ x y := by
  intro x y
  have hd := hDifferentiated x y
  apply (eq_div_iff (hDenom x y)).2
  simp only [denominator]
  field_simp [hZ x y] at hd
  nlinarith [hd]

theorem gap5 (Φ : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x₀ y₀ z₀ : ℝ)
    (hX :
      ∀ x y,
        partialX z x y =
          ((z x y - z₀) *
              phiX Φ (ratioX z x₀ z₀ x y) (ratioY z y₀ z₀ x y)) /
            denominator Φ z x₀ y₀ z₀ x y)
    (hY :
      ∀ x y,
        partialY z x y =
          ((z x y - z₀) *
              phiY Φ (ratioX z x₀ z₀ x y) (ratioY z y₀ z₀ x y)) /
            denominator Φ z x₀ y₀ z₀ x y)
    (hDenom : ∀ x y, denominator Φ z x₀ y₀ z₀ x y ≠ 0) :
    ∀ x y,
      (x - x₀) * partialX z x y + (y - y₀) * partialY z x y =
        z x y - z₀ := by
  intro x y
  rw [hX x y, hY x y]
  have hD := hDenom x y
  simp only [denominator] at hD ⊢
  field_simp [hD] <;> ring

theorem gap6 (Φ : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ) (p₀ : Point3)
    (hEuler :
      ∀ x y,
        (x - p₀.x) * partialX z x y + (y - p₀.y) * partialY z x y =
          z x y - p₀.z) :
    ∀ p n r, p ∈ surface Φ p₀ →
      p.z = z p.x p.y →
      n = graphNormal z p →
      r = radialDirection p₀ p →
      dot3 n r = 0 := by
  intro p n r hp hz hn hr
  subst n
  subst r
  simp only [dot3, graphNormal, radialDirection]
  rw [hz]
  nlinarith [hEuler p.x p.y]

theorem gap7 (Φ : ℝ → ℝ → ℝ) (p₀ : Point3)
    (hVertex : Φ 0 0 = 0) :
    ∀ p l, p ∈ surface Φ p₀ →
      p.z - p₀.z ≠ 0 →
      l = radialLine p₀ p →
      l ⊆ surface Φ p₀ := by
  intro p l hp hpz hl
  subst l
  intro q hq
  rcases hq with ⟨s, rfl⟩
  change
    Φ
        ((p₀.x + s * (p.x - p₀.x) - p₀.x) /
          (p₀.z + s * (p.z - p₀.z) - p₀.z))
        ((p₀.y + s * (p.y - p₀.y) - p₀.y) /
          (p₀.z + s * (p.z - p₀.z) - p₀.z)) = 0
  change
    Φ ((p.x - p₀.x) / (p.z - p₀.z))
      ((p.y - p₀.y) / (p.z - p₀.z)) = 0 at hp
  by_cases hs : s = 0
  · subst s
    simpa using hVertex
  · have hnx :
        p₀.x + s * (p.x - p₀.x) - p₀.x =
          s * (p.x - p₀.x) := by
      ring
    have hny :
        p₀.y + s * (p.y - p₀.y) - p₀.y =
          s * (p.y - p₀.y) := by
      ring
    have hdz :
        p₀.z + s * (p.z - p₀.z) - p₀.z =
          s * (p.z - p₀.z) := by
      ring
    have hx :
        (p₀.x + s * (p.x - p₀.x) - p₀.x) /
            (p₀.z + s * (p.z - p₀.z) - p₀.z) =
          (p.x - p₀.x) / (p.z - p₀.z) := by
      rw [hnx, hdz]
      field_simp [hs, hpz] <;> ring
    have hy :
        (p₀.y + s * (p.y - p₀.y) - p₀.y) /
            (p₀.z + s * (p.z - p₀.z) - p₀.z) =
          (p.y - p₀.y) / (p.z - p₀.z) := by
      rw [hny, hdz]
      field_simp [hs, hpz] <;> ring
    rw [hx, hy]
    exact hp

theorem gap8 (z : ℝ → ℝ → ℝ) (x₀ y₀ z₀ : ℝ)
    (hResult :
      ∀ x y,
        (x - x₀) * partialX z x y + (y - y₀) * partialY z x y =
          z x y - z₀) :
    ∀ x y,
      (x - x₀) * partialX z x y + (y - y₀) * partialY z x y =
        z x y - z₀ := by
  exact hResult

end

end ProofGap.Exercise3422
