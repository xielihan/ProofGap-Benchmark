import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod

namespace ProofGap.Exercise3352

noncomputable section

def curve (x : ℝ) : ℝ :=
  x ^ 2

def partialX (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => u s y) x

def partialY (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => u x s) y

def IsC1 (u : ℝ → ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 (Function.uncurry u)

private theorem parabola_hasDerivAt (x : ℝ) :
    HasDerivAt curve (2 * x) x := by
  change HasDerivAt (fun s : ℝ => s ^ 2) (2 * x) x
  simpa [pow_two, two_mul] using
    (hasDerivAt_id x).mul (hasDerivAt_id x)

theorem gap1 (u : ℝ → ℝ → ℝ) (hu : IsC1 u) :
    ∀ x,
      deriv (fun s => u s (s ^ 2)) x =
        partialX u x (curve x) + partialY u x (curve x) * deriv curve x := by
  intro x
  have hu' : ContDiff ℝ 1 (Function.uncurry u) := hu
  have hdiff : Differentiable ℝ (Function.uncurry u) :=
    hu'.differentiable one_ne_zero
  let L : (ℝ × ℝ) →L[ℝ] ℝ :=
    fderiv ℝ (Function.uncurry u) (x, curve x)
  have hF : HasFDerivAt (Function.uncurry u) L (x, curve x) := by
    simpa [L] using hdiff.differentiableAt.hasFDerivAt
  have hsquare : HasDerivAt (fun s : ℝ => s ^ 2) (2 * x) x := by
    simpa only [curve] using parabola_hasDerivAt x
  let A : ℝ →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ)
  let B : ℝ →L[ℝ] (ℝ × ℝ) :=
    (0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ)
  have hA :
      HasDerivAt (fun s : ℝ => A s) ((1, 0) : ℝ × ℝ) x := by
    simpa [A] using
      A.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_id x)
  have hBsquare :
      HasDerivAt (fun s : ℝ => B (s ^ 2)) ((0, 2 * x) : ℝ × ℝ) x := by
    simpa [B] using
      B.hasFDerivAt.comp_hasDerivAt x hsquare
  have hpathEq :
      ((fun s : ℝ => A s) + (fun s : ℝ => B (s ^ 2))) =
        (fun s : ℝ => (s, s ^ 2)) := by
    funext s
    simp [A, B]
  have hpath :
      HasDerivAt (fun s : ℝ => (s, s ^ 2)) ((1, 2 * x) : ℝ × ℝ) x := by
    rw [← hpathEq]
    simpa using hA.add hBsquare
  have htotal :
      deriv (fun s : ℝ => u s (s ^ 2)) x = L (1, 2 * x) := by
    simpa using (hF.comp_hasDerivAt x hpath).deriv
  have hpathXEq :
      ((fun s : ℝ => A s) +
          (fun _ : ℝ => ((0, curve x) : ℝ × ℝ))) =
        (fun s : ℝ => (s, curve x)) := by
    funext s
    simp [A]
  have hpathX :
      HasDerivAt (fun s : ℝ => (s, curve x)) ((1, 0) : ℝ × ℝ) x := by
    rw [← hpathXEq]
    simpa using
      hA.add
        (hasDerivAt_const (x : ℝ) ((0, curve x) : ℝ × ℝ))
  have hB :
      HasDerivAt (fun s : ℝ => B s) ((0, 1) : ℝ × ℝ) (curve x) := by
    simpa [B] using
      B.hasFDerivAt.comp_hasDerivAt (curve x)
        (hasDerivAt_id (curve x))
  have hpathYEq :
      ((fun _ : ℝ => ((x, 0) : ℝ × ℝ)) + (fun s : ℝ => B s)) =
        (fun s : ℝ => (x, s)) := by
    funext s
    simp [B]
  have hpathY :
      HasDerivAt (fun s : ℝ => (x, s)) ((0, 1) : ℝ × ℝ) (curve x) := by
    rw [← hpathYEq]
    simpa using
      (hasDerivAt_const (curve x : ℝ) ((x, 0) : ℝ × ℝ)).add hB
  have hpartialX : partialX u x (curve x) = L (1, 0) := by
    simpa [partialX] using (hF.comp_hasDerivAt x hpathX).deriv
  have hpartialY : partialY u x (curve x) = L (0, 1) := by
    simpa [partialY] using
      (hF.comp_hasDerivAt (curve x) hpathY).deriv
  have hcurve : deriv curve x = 2 * x :=
    (parabola_hasDerivAt x).deriv
  have hlinear :
      L (1, 2 * x) = L (1, 0) + L (0, 1) * (2 * x) := by
    rw [show ((1, 2 * x) : ℝ × ℝ) =
        (1, 0) + (2 * x) • (0, 1) by ext <;> simp]
    rw [map_add, map_smul]
    simp [smul_eq_mul, mul_comm]
  calc
    deriv (fun s : ℝ => u s (s ^ 2)) x = L (1, 2 * x) := htotal
    _ = L (1, 0) + L (0, 1) * (2 * x) := hlinear
    _ = partialX u x (curve x) +
          partialY u x (curve x) * deriv curve x := by
      rw [hpartialX, hpartialY, hcurve]

theorem gap2 (u : ℝ → ℝ → ℝ) :
    ∀ x, u x (curve x) = u x (x ^ 2) := by
  intro x
  rfl

theorem gap3 (u : ℝ → ℝ → ℝ)
    (huCurve : ∀ x, u x (curve x) = 1) :
    ∀ x, u x (x ^ 2) = 1 := by
  intro x
  simpa [curve] using huCurve x

theorem gap4 (u : ℝ → ℝ → ℝ)
    (huCurve : ∀ x, u x (curve x) = 1) :
    ∀ x, u x (curve x) = 1 := by
  exact huCurve

theorem gap5 (u : ℝ → ℝ → ℝ)
    (huCurve : ∀ x, u x (curve x) = 1) :
    ∀ x, deriv (fun s => u s (s ^ 2)) x = 0 := by
  intro x
  have hconst : (fun s : ℝ => u s (s ^ 2)) = (fun _ : ℝ => (1 : ℝ)) := by
    funext s
    simpa [curve] using huCurve s
  rw [hconst]
  simp

theorem gap6 (u : ℝ → ℝ → ℝ)
    (hux : ∀ x, partialX u x (curve x) = x) :
    ∀ x, partialX u x (curve x) = x := by
  exact hux

theorem gap7 :
    ∀ x, deriv curve x = 2 * x := by
  intro x
  exact (parabola_hasDerivAt x).deriv

theorem gap8 (u : ℝ → ℝ → ℝ) (hu : IsC1 u)
    (huCurve : ∀ x, u x (curve x) = 1)
    (hux : ∀ x, partialX u x (curve x) = x) :
    ∀ x, x + 2 * x * partialY u x (curve x) = 0 := by
  intro x
  have hchain := gap1 u hu x
  rw [gap5 u huCurve x, hux x, gap7 x] at hchain
  calc
    x + 2 * x * partialY u x (curve x) =
        x + partialY u x (curve x) * (2 * x) := by ring
    _ = 0 := hchain.symm

theorem gap9 (u : ℝ → ℝ → ℝ) (hu : IsC1 u)
    (huCurve : ∀ x, u x (curve x) = 1)
    (hux : ∀ x, partialX u x (curve x) = x) :
    ∀ x, x ≠ 0 → partialY u x (curve x) = -(1 / 2 : ℝ) := by
  intro x hx
  have h := gap8 u hu huCurve hux x
  have hfactor :
      x * (1 + 2 * partialY u x (curve x)) = 0 := by
    calc
      x * (1 + 2 * partialY u x (curve x)) =
          x + 2 * x * partialY u x (curve x) := by ring
      _ = 0 := h
  have hy : 1 + 2 * partialY u x (curve x) = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hx
  linarith

end

end ProofGap.Exercise3352
