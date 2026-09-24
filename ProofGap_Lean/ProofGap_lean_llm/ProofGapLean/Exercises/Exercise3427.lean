import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3427

noncomputable section

def partialX (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => u s y) x

def partialY (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => u x s) y

def differential (u : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialX u x y * dx + partialY u x y * dy

def fullDifferential (f : ℝ → ℝ) (α : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  α x y * dx + (1 / α x y) * dy +
    (x - y / (α x y) ^ 2 + deriv f (α x y)) *
      differential α x y dx dy

def reducedDifferential (α : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  α x y * dx + (1 / α x y) * dy

theorem gap1 (f : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (hRepresentation :
      ∀ x y, z x y = α x y * x + y / α x y + f (α x y))
    (hαNonzero : ∀ x y, α x y ≠ 0)
    (hf : Differentiable ℝ f)
    (hα : Differentiable ℝ (Function.uncurry α))
    (hz : Differentiable ℝ (Function.uncurry z)) :
    ∀ x y dx dy,
      differential z x y dx dy = fullDifferential f α x y dx dy := by
  intro x y dx dy
  have hpairX : DifferentiableAt ℝ (fun s : ℝ => (s, y)) x := by
    fun_prop
  have hpairY : DifferentiableAt ℝ (fun s : ℝ => (x, s)) y := by
    fun_prop
  have hαx : DifferentiableAt ℝ (fun s : ℝ => α s y) x := by
    simpa [Function.uncurry, Function.comp_def] using
      (hα (x, y)).comp x hpairX
  have hαy : DifferentiableAt ℝ (fun s : ℝ => α x s) y := by
    simpa [Function.uncurry, Function.comp_def] using
      (hα (x, y)).comp y hpairY
  have hfαx :
      HasDerivAt (fun s : ℝ => f (α s y))
        (deriv f (α x y) * deriv (fun s : ℝ => α s y) x) x := by
    simpa [Function.comp_def] using
      (HasDerivAt.comp x
        (DifferentiableAt.hasDerivAt (hf (α x y)))
        (DifferentiableAt.hasDerivAt hαx))
  have hfαy :
      HasDerivAt (fun s : ℝ => f (α x s))
        (deriv f (α x y) * deriv (fun s : ℝ => α x s) y) y := by
    simpa [Function.comp_def] using
      (HasDerivAt.comp y
        (DifferentiableAt.hasDerivAt (hf (α x y)))
        (DifferentiableAt.hasDerivAt hαy))
  have hderivX :=
    (((hαx.hasDerivAt.mul (hasDerivAt_id x)).add
      ((hasDerivAt_const (x := x) (c := y)).div
        hαx.hasDerivAt (hαNonzero x y))).add hfαx)
  have hderivY :=
    (((hαy.hasDerivAt.mul (hasDerivAt_const (x := y) (c := x))).add
      ((hasDerivAt_id y).div hαy.hasDerivAt (hαNonzero x y))).add hfαy)
  have hrawX := hderivX.deriv
  change
    deriv (fun s : ℝ => α s y * s + y / α s y + f (α s y)) x = _
      at hrawX
  dsimp only [id] at hrawX
  have hrawY := hderivY.deriv
  change
    deriv (fun s : ℝ => α x s * x + s / α x s + f (α x s)) y = _
      at hrawY
  dsimp only [id] at hrawY
  have hdx :
      deriv (fun s : ℝ => z s y) x =
        α x y +
          (x - y / (α x y) ^ 2 + deriv f (α x y)) *
            deriv (fun s : ℝ => α s y) x := by
    rw [show (fun s : ℝ => z s y) =
        (fun s : ℝ => α s y * s + y / α s y + f (α s y)) by
      funext s
      exact hRepresentation s y]
    rw [hrawX]
    field_simp [hαNonzero x y] <;> ring_nf
  have hdy :
      deriv (fun s : ℝ => z x s) y =
        1 / α x y +
          (x - y / (α x y) ^ 2 + deriv f (α x y)) *
            deriv (fun s : ℝ => α x s) y := by
    rw [show (fun s : ℝ => z x s) =
        (fun s : ℝ => α x s * x + s / α x s + f (α x s)) by
      funext s
      exact hRepresentation x s]
    rw [hrawY]
    field_simp [hαNonzero x y] <;> ring_nf
  simp only [fullDifferential, differential, partialX, partialY]
  rw [hdx, hdy]
  ring

theorem gap2 (f : ℝ → ℝ) (α : ℝ → ℝ → ℝ)
    (hStationary :
      ∀ x y, 0 = x - y / (α x y) ^ 2 + deriv f (α x y)) :
    ∀ x y dx dy,
      fullDifferential f α x y dx dy =
        reducedDifferential α x y dx dy := by
  intro x y dx dy
  unfold fullDifferential reducedDifferential
  rw [← hStationary x y]
  simp

theorem gap3 (f : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (hFull :
      ∀ x y dx dy,
        differential z x y dx dy = fullDifferential f α x y dx dy)
    (hReduce :
      ∀ x y dx dy,
        fullDifferential f α x y dx dy =
          reducedDifferential α x y dx dy) :
    ∀ x y dx dy,
      differential z x y dx dy = reducedDifferential α x y dx dy := by
  intro x y dx dy
  exact (hFull x y dx dy).trans (hReduce x y dx dy)

theorem gap4 (α z : ℝ → ℝ → ℝ)
    (hDifferential :
      ∀ x y dx dy,
        differential z x y dx dy = reducedDifferential α x y dx dy) :
    ∀ x y, partialX z x y = α x y := by
  intro x y
  simpa [differential, reducedDifferential] using
    hDifferential x y 1 0

theorem gap5 (α z : ℝ → ℝ → ℝ)
    (hDifferential :
      ∀ x y dx dy,
        differential z x y dx dy = reducedDifferential α x y dx dy) :
    ∀ x y, partialY z x y = 1 / α x y := by
  intro x y
  simpa [differential, reducedDifferential] using
    hDifferential x y 0 1

theorem gap6 (α z : ℝ → ℝ → ℝ)
    (hX : ∀ x y, partialX z x y = α x y)
    (hY : ∀ x y, partialY z x y = 1 / α x y) :
    ∀ x y,
      partialX z x y * partialY z x y =
        α x y * (1 / α x y) := by
  intro x y
  rw [hX x y, hY x y]

theorem gap7 (α : ℝ → ℝ → ℝ)
    (hαNonzero : ∀ x y, α x y ≠ 0) :
    ∀ x y, α x y * (1 / α x y) = 1 := by
  intro x y
  simp [one_div, hαNonzero x y]

theorem gap8 (α z : ℝ → ℝ → ℝ)
    (hProduct :
      ∀ x y,
        partialX z x y * partialY z x y =
          α x y * (1 / α x y))
    (hCancel : ∀ x y, α x y * (1 / α x y) = 1) :
    ∀ x y, partialX z x y * partialY z x y = 1 := by
  intro x y
  exact (hProduct x y).trans (hCancel x y)

theorem gap9 (z : ℝ → ℝ → ℝ)
    (hResult : ∀ x y, partialX z x y * partialY z x y = 1) :
    ∀ x y, partialX z x y * partialY z x y = 1 := by
  exact hResult

end

end ProofGap.Exercise3427
