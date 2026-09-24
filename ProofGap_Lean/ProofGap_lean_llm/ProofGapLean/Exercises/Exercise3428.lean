import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise3428

noncomputable section

def partialX (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => u s y) x

def partialY (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => u x s) y

def differential (u : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialX u x y * dx + partialY u x y * dy

def gapValue (f : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  z x y - f (α x y)

def firstDifferentialRhs (α : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  (y ^ 2 - (α x y) ^ 2) * 2 * x * dx +
    x ^ 2 * (2 * y * dy - 2 * α x y * differential α x y dx dy)

def expandedRhs (f : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  x * (y ^ 2 - (α x y) ^ 2) * dx + x ^ 2 * y * dy -
    (α x y * x ^ 2 - gapValue f α z x y * deriv f (α x y)) *
      differential α x y dx dy

theorem gap1 (f : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (hImplicit :
      ∀ x y,
        (gapValue f α z x y) ^ 2 =
          x ^ 2 * (y ^ 2 - (α x y) ^ 2))
    (hf : Differentiable ℝ f)
    (hα : Differentiable ℝ (Function.uncurry α))
    (hz : Differentiable ℝ (Function.uncurry z)) :
    ∀ x y dx dy,
      2 * gapValue f α z x y *
          (differential z x y dx dy -
            deriv f (α x y) * differential α x y dx dy) =
        firstDifferentialRhs α x y dx dy := by
  intro x y dx dy
  have hαx : Differentiable ℝ (fun s => α s y) := by fun_prop
  have hzx : Differentiable ℝ (fun s => z s y) := by fun_prop
  have hαdx : HasDerivAt (fun s => α s y) (partialX α x y) x := by
    simpa only [partialX] using hαx.differentiableAt.hasDerivAt
  have hzdx : HasDerivAt (fun s => z s y) (partialX z x y) x := by
    simpa only [partialX] using hzx.differentiableAt.hasDerivAt
  have hfAt : HasDerivAt f (deriv f (α x y)) (α x y) :=
    hf.differentiableAt.hasDerivAt
  have hfαdx : HasDerivAt (fun s => f (α s y))
      (deriv f (α x y) * partialX α x y) x := by
    simpa only [Function.comp_apply] using hfAt.comp x hαdx
  have hgdx : HasDerivAt (fun s => gapValue f α z s y)
      (partialX z x y -
        deriv f (α x y) * partialX α x y) x := by
    simpa only [gapValue] using hzdx.sub hfαdx
  have hrhsX := ((hasDerivAt_id x).pow 2).mul
    ((hasDerivAt_const x (y ^ 2)).sub (hαdx.pow 2))
  have heqX :
      (fun s : ℝ => (gapValue f α z s y) ^ 2) =
        (fun s => s ^ 2 * (y ^ 2 - (α s y) ^ 2)) := by
    funext s
    exact hImplicit s y
  have hdeqX := congrArg (fun q : ℝ → ℝ => deriv q x) heqX
  change deriv (fun s : ℝ => (gapValue f α z s y) ^ 2) x =
    deriv (fun s => s ^ 2 * (y ^ 2 - (α s y) ^ 2)) x at hdeqX
  have hlX := (hgdx.pow 2).deriv
  change deriv (fun s : ℝ => (gapValue f α z s y) ^ 2) x = _ at hlX
  have hrX := hrhsX.deriv
  change deriv (fun s : ℝ =>
    s ^ 2 * (y ^ 2 - (α s y) ^ 2)) x = _ at hrX
  have hX :
      2 * gapValue f α z x y *
          (partialX z x y -
            deriv f (α x y) * partialX α x y) =
        (y ^ 2 - (α x y) ^ 2) * 2 * x +
          x ^ 2 * (-2 * α x y * partialX α x y) := by
    calc
      _ = deriv (fun s : ℝ =>
          (gapValue f α z s y) ^ 2) x := by
        rw [hlX]
        ring
      _ = deriv (fun s : ℝ =>
          s ^ 2 * (y ^ 2 - (α s y) ^ 2)) x := hdeqX
      _ = _ := by
        rw [hrX]
        simp only [id_eq, Pi.sub_apply, Pi.pow_apply]
        ring
  have hαy : Differentiable ℝ (fun s => α x s) := by fun_prop
  have hzy : Differentiable ℝ (fun s => z x s) := by fun_prop
  have hαdy : HasDerivAt (fun s => α x s) (partialY α x y) y := by
    simpa only [partialY] using hαy.differentiableAt.hasDerivAt
  have hzdy : HasDerivAt (fun s => z x s) (partialY z x y) y := by
    simpa only [partialY] using hzy.differentiableAt.hasDerivAt
  have hfαdy : HasDerivAt (fun s => f (α x s))
      (deriv f (α x y) * partialY α x y) y := by
    simpa only [Function.comp_apply] using hfAt.comp y hαdy
  have hgdy : HasDerivAt (fun s => gapValue f α z x s)
      (partialY z x y -
        deriv f (α x y) * partialY α x y) y := by
    simpa only [gapValue] using hzdy.sub hfαdy
  have hrhsY := (hasDerivAt_const y (x ^ 2)).mul
    (((hasDerivAt_id y).pow 2).sub (hαdy.pow 2))
  have heqY :
      (fun s : ℝ => (gapValue f α z x s) ^ 2) =
        (fun s => x ^ 2 * (s ^ 2 - (α x s) ^ 2)) := by
    funext s
    exact hImplicit x s
  have hdeqY := congrArg (fun q : ℝ → ℝ => deriv q y) heqY
  change deriv (fun s : ℝ => (gapValue f α z x s) ^ 2) y =
    deriv (fun s => x ^ 2 * (s ^ 2 - (α x s) ^ 2)) y at hdeqY
  have hlY := (hgdy.pow 2).deriv
  change deriv (fun s : ℝ => (gapValue f α z x s) ^ 2) y = _ at hlY
  have hrY := hrhsY.deriv
  change deriv (fun s : ℝ =>
    x ^ 2 * (s ^ 2 - (α x s) ^ 2)) y = _ at hrY
  have hY :
      2 * gapValue f α z x y *
          (partialY z x y -
            deriv f (α x y) * partialY α x y) =
        x ^ 2 * (2 * y - 2 * α x y * partialY α x y) := by
    calc
      _ = deriv (fun s : ℝ =>
          (gapValue f α z x s) ^ 2) y := by
        rw [hlY]
        ring
      _ = deriv (fun s : ℝ =>
          x ^ 2 * (s ^ 2 - (α x s) ^ 2)) y := hdeqY
      _ = _ := by
        rw [hrY]
        simp only [id_eq, Pi.sub_apply, Pi.pow_apply]
        ring
  unfold firstDifferentialRhs differential
  linear_combination dx * hX + dy * hY

theorem gap2 (f : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (hDifferentiated :
      ∀ x y dx dy,
        2 * gapValue f α z x y *
            (differential z x y dx dy -
              deriv f (α x y) * differential α x y dx dy) =
          firstDifferentialRhs α x y dx dy) :
    ∀ x y dx dy,
      gapValue f α z x y * differential z x y dx dy =
        expandedRhs f α z x y dx dy := by
  intro x y dx dy
  have hd := hDifferentiated x y dx dy
  unfold firstDifferentialRhs at hd
  unfold expandedRhs
  linear_combination hd / 2

theorem gap3 (f : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (hStationary :
      ∀ x y,
        gapValue f α z x y * deriv f (α x y) = α x y * x ^ 2) :
    ∀ x y dx dy,
      expandedRhs f α z x y dx dy =
        x * (y ^ 2 - (α x y) ^ 2) * dx + x ^ 2 * y * dy := by
  intro x y dx dy
  unfold expandedRhs
  rw [hStationary x y]
  ring

theorem gap4 (f : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (hExpanded :
      ∀ x y dx dy,
        gapValue f α z x y * differential z x y dx dy =
          expandedRhs f α z x y dx dy)
    (hRemoveParameter :
      ∀ x y dx dy,
        expandedRhs f α z x y dx dy =
          x * (y ^ 2 - (α x y) ^ 2) * dx + x ^ 2 * y * dy) :
    ∀ x y dx dy,
      gapValue f α z x y * differential z x y dx dy =
        x * (y ^ 2 - (α x y) ^ 2) * dx + x ^ 2 * y * dy := by
  intro x y dx dy
  exact (hExpanded x y dx dy).trans (hRemoveParameter x y dx dy)

theorem gap5 (f : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (hDifferential :
      ∀ x y dx dy,
        gapValue f α z x y * differential z x y dx dy =
          x * (y ^ 2 - (α x y) ^ 2) * dx + x ^ 2 * y * dy)
    (hNonzero : ∀ x y, gapValue f α z x y ≠ 0) :
    ∀ x y,
      partialX z x y =
        x * (y ^ 2 - (α x y) ^ 2) / gapValue f α z x y := by
  intro x y
  apply (eq_div_iff (hNonzero x y)).2
  have hd := hDifferential x y 1 0
  simp only [differential, mul_one, mul_zero, add_zero] at hd
  simpa only [mul_comm] using hd

theorem gap6 (f : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (hDifferential :
      ∀ x y dx dy,
        gapValue f α z x y * differential z x y dx dy =
          x * (y ^ 2 - (α x y) ^ 2) * dx + x ^ 2 * y * dy)
    (hNonzero : ∀ x y, gapValue f α z x y ≠ 0) :
    ∀ x y,
      partialY z x y = x ^ 2 * y / gapValue f α z x y := by
  intro x y
  apply (eq_div_iff (hNonzero x y)).2
  have hd := hDifferential x y 0 1
  simp only [differential, mul_zero, mul_one, zero_add] at hd
  simpa only [mul_comm] using hd

theorem gap7 (f : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (hX :
      ∀ x y,
        partialX z x y =
          x * (y ^ 2 - (α x y) ^ 2) / gapValue f α z x y)
    (hY :
      ∀ x y,
        partialY z x y = x ^ 2 * y / gapValue f α z x y) :
    ∀ x y,
      partialX z x y * partialY z x y =
        (x ^ 3 * y * (y ^ 2 - (α x y) ^ 2)) /
          (gapValue f α z x y) ^ 2 := by
  intro x y
  rw [hX x y, hY x y]
  simp only [div_eq_mul_inv]
  ring

theorem gap8 (f : ℝ → ℝ) (α z : ℝ → ℝ → ℝ) :
    ∀ x y,
      (x ^ 3 * y * (y ^ 2 - (α x y) ^ 2)) /
          (gapValue f α z x y) ^ 2 =
        x * y *
          ((x ^ 2 * (y ^ 2 - (α x y) ^ 2)) /
            (gapValue f α z x y) ^ 2) := by
  intro x y
  ring

theorem gap9 (f : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (hImplicit :
      ∀ x y,
        (gapValue f α z x y) ^ 2 =
          x ^ 2 * (y ^ 2 - (α x y) ^ 2))
    (hNonzero : ∀ x y, gapValue f α z x y ≠ 0) :
    ∀ x y,
      x * y *
          ((x ^ 2 * (y ^ 2 - (α x y) ^ 2)) /
            (gapValue f α z x y) ^ 2) =
        x * y := by
  intro x y
  rw [← hImplicit x y]
  field_simp [hNonzero x y]

theorem gap10 (f : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (hProduct :
      ∀ x y,
        partialX z x y * partialY z x y =
          (x ^ 3 * y * (y ^ 2 - (α x y) ^ 2)) /
            (gapValue f α z x y) ^ 2)
    (hFactor :
      ∀ x y,
        (x ^ 3 * y * (y ^ 2 - (α x y) ^ 2)) /
            (gapValue f α z x y) ^ 2 =
          x * y *
            ((x ^ 2 * (y ^ 2 - (α x y) ^ 2)) /
              (gapValue f α z x y) ^ 2))
    (hCancel :
      ∀ x y,
        x * y *
            ((x ^ 2 * (y ^ 2 - (α x y) ^ 2)) /
              (gapValue f α z x y) ^ 2) =
          x * y) :
    ∀ x y, partialX z x y * partialY z x y = x * y := by
  intro x y
  exact (hProduct x y).trans ((hFactor x y).trans (hCancel x y))

theorem gap11 (z : ℝ → ℝ → ℝ)
    (hResult : ∀ x y, partialX z x y * partialY z x y = x * y) :
    ∀ x y, partialX z x y * partialY z x y = x * y := by
  exact hResult

end

end ProofGap.Exercise3428
