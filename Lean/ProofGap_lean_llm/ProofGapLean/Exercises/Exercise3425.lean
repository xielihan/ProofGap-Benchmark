import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3425

noncomputable section

def partialX (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => z s y) x

def partialY (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => z x s) y

def arg1 (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  x + z x y / y

def arg2 (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  y + z x y / x

def F1 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => F s (arg2 z x y)) (arg1 z x y)

def F2 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => F (arg1 z x y) s) (arg2 z x y)

def gradientPairing (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  x * F1 F z x y + y * F2 F z x y

def combinedNumerator (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  y * z x y * F2 F z x y - x ^ 2 * y * F1 F z x y +
    x * z x y * F1 F z x y - x * y ^ 2 * F2 F z x y

private theorem deriv_uncurry_comp
    (F : ℝ → ℝ → ℝ) (u v : ℝ → ℝ) (x : ℝ)
    (hF : DifferentiableAt ℝ (Function.uncurry F) (u x, v x))
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    deriv (fun t => F (u t) (v t)) x =
      deriv (fun s => F s (v x)) (u x) * deriv u x +
        deriv (fun s => F (u x) s) (v x) * deriv v x := by
  let L := fderiv ℝ (Function.uncurry F) (u x, v x)
  have huv := hu.hasDerivAt.hasFDerivAt.prodMk hv.hasDerivAt.hasFDerivAt
  have hcomp :
      deriv (fun t => F (u t) (v t)) x =
        L (deriv u x, deriv v x) := by
    have hc := hF.hasFDerivAt.comp x huv
    simpa [L] using hc.hasDerivAt.deriv
  have hline1 :=
    (hasDerivAt_id (u x)).hasFDerivAt.prodMk
      (hasDerivAt_const (x := u x) (v x)).hasFDerivAt
  have hfirst :
      deriv (fun s => F s (v x)) (u x) = L (1, 0) := by
    have hc := hF.hasFDerivAt.comp (u x) hline1
    simpa [L] using hc.hasDerivAt.deriv
  have hline2 :=
    (hasDerivAt_const (x := v x) (u x)).hasFDerivAt.prodMk
      (hasDerivAt_id (v x)).hasFDerivAt
  have hsecond :
      deriv (fun s => F (u x) s) (v x) = L (0, 1) := by
    have hc := hF.hasFDerivAt.comp (v x) hline2
    simpa [L] using hc.hasDerivAt.deriv
  rw [hcomp, hfirst, hsecond]
  have hvec :
      (deriv u x, deriv v x) =
        deriv u x • (1, 0) + deriv v x • (0, 1) := by
    ext <;> simp
  rw [hvec, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

theorem gap1 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hImplicit : ∀ x y, F (arg1 z x y) (arg2 z x y) = 0)
    (hx : x ≠ 0)
    (hy : y ≠ 0)
    (hF : DifferentiableAt ℝ (Function.uncurry F) (arg1 z x y, arg2 z x y))
    (hz : Differentiable ℝ (Function.uncurry z)) :
    F1 F z x y * (1 + partialX z x y / y) +
      F2 F z x y * ((x * partialX z x y - z x y) / x ^ 2) = 0 := by
  have hpair :=
    (hasDerivAt_id x).hasFDerivAt.prodMk
      (hasDerivAt_const (x := x) y).hasFDerivAt
  have hzx : DifferentiableAt ℝ (fun s => z s y) x := by
    simpa using (hz (x, y)).comp x hpair.differentiableAt
  have hu : HasDerivAt (fun s => arg1 z s y)
      (1 + partialX z x y / y) x := by
    simpa [arg1, partialX] using
      (hasDerivAt_id x).add (hzx.hasDerivAt.div_const y)
  have hv : HasDerivAt (fun s => arg2 z s y)
      ((x * partialX z x y - z x y) / x ^ 2) x := by
    simpa [arg2, partialX, mul_comm] using
      (hzx.hasDerivAt.div (hasDerivAt_id x) hx)
  have hzero :
      deriv (fun s => F (arg1 z s y) (arg2 z s y)) x = 0 := by
    have heq : (fun s => F (arg1 z s y) (arg2 z s y)) =
        (fun _ : ℝ => 0) := by
      funext s
      exact hImplicit s y
    rw [heq]
    simp
  have hchain := deriv_uncurry_comp F (fun s => arg1 z s y)
    (fun s => arg2 z s y) x hF hu.differentiableAt hv.differentiableAt
  have hchain' :
      deriv (fun s => F (arg1 z s y) (arg2 z s y)) x =
        F1 F z x y * (1 + partialX z x y / y) +
          F2 F z x y * ((x * partialX z x y - z x y) / x ^ 2) := by
    simpa [F1, F2, hu.deriv, hv.deriv] using hchain
  exact hchain'.symm.trans hzero

theorem gap2 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hImplicit : ∀ x y, F (arg1 z x y) (arg2 z x y) = 0)
    (hx : x ≠ 0)
    (hy : y ≠ 0)
    (hF : DifferentiableAt ℝ (Function.uncurry F) (arg1 z x y, arg2 z x y))
    (hz : Differentiable ℝ (Function.uncurry z)) :
    F1 F z x y * ((y * partialY z x y - z x y) / y ^ 2) +
      F2 F z x y * (1 + partialY z x y / x) = 0 := by
  have hpair :=
    (hasDerivAt_const (x := y) x).hasFDerivAt.prodMk
      (hasDerivAt_id y).hasFDerivAt
  have hzy : DifferentiableAt ℝ (fun s => z x s) y := by
    simpa using (hz (x, y)).comp y hpair.differentiableAt
  have hu : HasDerivAt (fun s => arg1 z x s)
      ((y * partialY z x y - z x y) / y ^ 2) y := by
    simpa [arg1, partialY, mul_comm] using
      (hzy.hasDerivAt.div (hasDerivAt_id y) hy)
  have hv : HasDerivAt (fun s => arg2 z x s)
      (1 + partialY z x y / x) y := by
    simpa [arg2, partialY] using
      (hasDerivAt_id y).add (hzy.hasDerivAt.div_const x)
  have hzero :
      deriv (fun s => F (arg1 z x s) (arg2 z x s)) y = 0 := by
    have heq : (fun s => F (arg1 z x s) (arg2 z x s)) =
        (fun _ : ℝ => 0) := by
      funext s
      exact hImplicit x s
    rw [heq]
    simp
  have hchain := deriv_uncurry_comp F (fun s => arg1 z x s)
    (fun s => arg2 z x s) y hF hu.differentiableAt hv.differentiableAt
  have hchain' :
      deriv (fun s => F (arg1 z x s) (arg2 z x s)) y =
        F1 F z x y * ((y * partialY z x y - z x y) / y ^ 2) +
          F2 F z x y * (1 + partialY z x y / x) := by
    simpa [F1, F2, hu.deriv, hv.deriv] using hchain
  exact hchain'.symm.trans hzero

theorem gap3 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hDifferentiated :
      F1 F z x y * (1 + partialX z x y / y) +
        F2 F z x y * ((x * partialX z x y - z x y) / x ^ 2) = 0)
    (hx : x ≠ 0)
    (hy : y ≠ 0)
    (hGradient : gradientPairing F z x y ≠ 0) :
    partialX z x y =
      (y * z x y * F2 F z x y - x ^ 2 * y * F1 F z x y) /
        (x * gradientPairing F z x y) := by
  unfold gradientPairing at hGradient ⊢
  field_simp [hx, hy] at hDifferentiated
  field_simp [hx, hGradient]
  ring_nf at hDifferentiated ⊢
  linarith

theorem gap4 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hDifferentiated :
      F1 F z x y * ((y * partialY z x y - z x y) / y ^ 2) +
        F2 F z x y * (1 + partialY z x y / x) = 0)
    (hx : x ≠ 0)
    (hy : y ≠ 0)
    (hGradient : gradientPairing F z x y ≠ 0) :
    partialY z x y =
      (x * z x y * F1 F z x y - x * y ^ 2 * F2 F z x y) /
        (y * gradientPairing F z x y) := by
  unfold gradientPairing at hGradient ⊢
  field_simp [hx, hy] at hDifferentiated
  field_simp [hy, hGradient]
  ring_nf at hDifferentiated ⊢
  linarith

theorem gap5 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hX :
      partialX z x y =
        (y * z x y * F2 F z x y - x ^ 2 * y * F1 F z x y) /
          (x * gradientPairing F z x y))
    (hY :
      partialY z x y =
        (x * z x y * F1 F z x y - x * y ^ 2 * F2 F z x y) /
          (y * gradientPairing F z x y))
    (hx : x ≠ 0)
    (hy : y ≠ 0) :
    x * partialX z x y + y * partialY z x y =
      combinedNumerator F z x y / gradientPairing F z x y := by
  rw [hX, hY]
  by_cases hG : gradientPairing F z x y = 0
  · simp [hG]
  · unfold combinedNumerator
    field_simp [hx, hy, hG] <;> ring

theorem gap6 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ) :
    ∀ x y,
      combinedNumerator F z x y / gradientPairing F z x y =
        ((z x y - x * y) * gradientPairing F z x y) /
          gradientPairing F z x y := by
  intro x y
  unfold combinedNumerator gradientPairing
  ring

theorem gap7 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hGradient : gradientPairing F z x y ≠ 0) :
    ((z x y - x * y) * gradientPairing F z x y) /
        gradientPairing F z x y =
      z x y - x * y := by
  simp [hGradient]

theorem gap8 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hCombined :
      x * partialX z x y + y * partialY z x y =
        combinedNumerator F z x y / gradientPairing F z x y)
    (hFactor :
      combinedNumerator F z x y / gradientPairing F z x y =
        ((z x y - x * y) * gradientPairing F z x y) /
          gradientPairing F z x y)
    (hCancel :
      ((z x y - x * y) * gradientPairing F z x y) /
          gradientPairing F z x y =
        z x y - x * y) :
    x * partialX z x y + y * partialY z x y =
      z x y - x * y := by
  exact hCombined.trans (hFactor.trans hCancel)

theorem gap9 (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hResult :
      x * partialX z x y + y * partialY z x y =
        z x y - x * y) :
    x * partialX z x y + y * partialY z x y =
      z x y - x * y := by
  exact hResult

end

end ProofGap.Exercise3425
