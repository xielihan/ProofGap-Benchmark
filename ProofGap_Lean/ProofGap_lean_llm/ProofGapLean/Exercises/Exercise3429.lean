import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3429

noncomputable section

def px (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => u s y) x

def py (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => u x s) y

def pxx (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  px (px u) x y

def pxy (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  py (px u) x y

def pyy (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  py (py u) x y

def stationary (φ ψ : ℝ → ℝ) (α : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  x + y * deriv φ (α x y) + deriv ψ (α x y)

def expandedX (φ ψ : ℝ → ℝ) (α : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  α x y + x * px α x y +
    y * deriv φ (α x y) * px α x y +
    deriv ψ (α x y) * px α x y

def expandedY (φ ψ : ℝ → ℝ) (α : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  x * py α x y + φ (α x y) +
    y * deriv φ (α x y) * py α x y +
    deriv ψ (α x y) * py α x y

def hessianDet (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  pxx z x y * pyy z x y - (pxy z x y) ^ 2

theorem gap1 (φ ψ : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (hRepresentation :
      ∀ x y, z x y = α x y * x + y * φ (α x y) + ψ (α x y))
    (hφ : Differentiable ℝ φ)
    (hψ : Differentiable ℝ ψ)
    (hα : Differentiable ℝ (Function.uncurry α)) :
    ∀ x y, px z x y = expandedX φ ψ α x y := by
  intro x y
  have hp : DifferentiableAt ℝ (fun s : ℝ => (s, y)) x := by
    fun_prop
  have hαx : DifferentiableAt ℝ (fun s : ℝ => α s y) x := by
    simpa [Function.uncurry] using (hα (x, y)).comp x hp
  have ha : HasDerivAt (fun s : ℝ => α s y) (px α x y) x := by
    simpa only [px] using hαx.hasDerivAt
  have hφa :
      HasDerivAt (fun s : ℝ => φ (α s y))
        (deriv φ (α x y) * px α x y) x := by
    simpa [Function.comp_def, mul_comm] using
      ((hφ (α x y)).hasDerivAt.scomp x ha)
  have hψa :
      HasDerivAt (fun s : ℝ => ψ (α s y))
        (deriv ψ (α x y) * px α x y) x := by
    simpa [Function.comp_def, mul_comm] using
      ((hψ (α x y)).hasDerivAt.scomp x ha)
  have hz' :
      HasDerivAt
        (fun s : ℝ => α s y * s + y * φ (α s y) + ψ (α s y))
        (expandedX φ ψ α x y) x := by
    convert (((ha.mul (hasDerivAt_id x)).add
      ((hasDerivAt_const (x := x) y).mul hφa)).add hψa) using 1 <;>
      simp [expandedX] <;> ring
  calc
    px z x y =
        deriv
          (fun s : ℝ => α s y * s + y * φ (α s y) + ψ (α s y)) x := by
      exact congrArg (fun f : ℝ → ℝ => deriv f x)
        (funext fun s => hRepresentation s y)
    _ = expandedX φ ψ α x y := hz'.deriv

theorem gap2 (φ ψ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) :
    ∀ x y,
      expandedX φ ψ α x y =
        α x y + stationary φ ψ α x y * px α x y := by
  intro x y
  unfold expandedX stationary
  ring

theorem gap3 (φ ψ : ℝ → ℝ) (α : ℝ → ℝ → ℝ)
    (hStationary : ∀ x y, stationary φ ψ α x y = 0) :
    ∀ x y,
      α x y + stationary φ ψ α x y * px α x y = α x y := by
  intro x y
  rw [hStationary x y]
  ring

theorem gap4 (φ ψ : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (hExpanded : ∀ x y, px z x y = expandedX φ ψ α x y)
    (hCollect :
      ∀ x y,
        expandedX φ ψ α x y =
          α x y + stationary φ ψ α x y * px α x y)
    (hStationary :
      ∀ x y,
        α x y + stationary φ ψ α x y * px α x y = α x y) :
    ∀ x y, px z x y = α x y := by
  intro x y
  calc
    px z x y = expandedX φ ψ α x y := hExpanded x y
    _ = α x y + stationary φ ψ α x y * px α x y := hCollect x y
    _ = α x y := hStationary x y

theorem gap5 (α z : ℝ → ℝ → ℝ)
    (hX : ∀ x y, px z x y = α x y) :
    ∀ x y, pxx z x y = px α x y := by
  have hfun : px z = α := by
    funext x y
    exact hX x y
  intro x y
  unfold pxx
  rw [hfun]

theorem gap6 (α z : ℝ → ℝ → ℝ)
    (hX : ∀ x y, px z x y = α x y) :
    ∀ x y, pxy z x y = py α x y := by
  have hfun : px z = α := by
    funext x y
    exact hX x y
  intro x y
  unfold pxy
  rw [hfun]

theorem gap7 (φ ψ : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (hRepresentation :
      ∀ x y, z x y = α x y * x + y * φ (α x y) + ψ (α x y))
    (hφ : Differentiable ℝ φ)
    (hψ : Differentiable ℝ ψ)
    (hα : Differentiable ℝ (Function.uncurry α)) :
    ∀ x y, py z x y = expandedY φ ψ α x y := by
  intro x y
  have hp : DifferentiableAt ℝ (fun s : ℝ => (x, s)) y := by
    fun_prop
  have hαy : DifferentiableAt ℝ (fun s : ℝ => α x s) y := by
    simpa [Function.uncurry] using (hα (x, y)).comp y hp
  have ha : HasDerivAt (fun s : ℝ => α x s) (py α x y) y := by
    simpa only [py] using hαy.hasDerivAt
  have hφa :
      HasDerivAt (fun s : ℝ => φ (α x s))
        (deriv φ (α x y) * py α x y) y := by
    simpa [Function.comp_def, mul_comm] using
      ((hφ (α x y)).hasDerivAt.scomp y ha)
  have hψa :
      HasDerivAt (fun s : ℝ => ψ (α x s))
        (deriv ψ (α x y) * py α x y) y := by
    simpa [Function.comp_def, mul_comm] using
      ((hψ (α x y)).hasDerivAt.scomp y ha)
  have hz' :
      HasDerivAt
        (fun s : ℝ => α x s * x + s * φ (α x s) + ψ (α x s))
        (expandedY φ ψ α x y) y := by
    convert (((ha.mul (hasDerivAt_const (x := y) x)).add
      ((hasDerivAt_id y).mul hφa)).add hψa) using 1 <;>
      simp [expandedY] <;> ring
  calc
    py z x y =
        deriv
          (fun s : ℝ => α x s * x + s * φ (α x s) + ψ (α x s)) y := by
      exact congrArg (fun f : ℝ → ℝ => deriv f y)
        (funext fun s => hRepresentation x s)
    _ = expandedY φ ψ α x y := hz'.deriv

theorem gap8 (φ ψ : ℝ → ℝ) (α : ℝ → ℝ → ℝ)
    (hStationary : ∀ x y, stationary φ ψ α x y = 0) :
    ∀ x y, expandedY φ ψ α x y = φ (α x y) := by
  intro x y
  calc
    expandedY φ ψ α x y =
        φ (α x y) + stationary φ ψ α x y * py α x y := by
      unfold expandedY stationary
      ring
    _ = φ (α x y) := by
      rw [hStationary x y]
      ring

theorem gap9 (φ ψ : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (hExpanded : ∀ x y, py z x y = expandedY φ ψ α x y)
    (hReduce : ∀ x y, expandedY φ ψ α x y = φ (α x y)) :
    ∀ x y, py z x y = φ (α x y) := by
  intro x y
  calc
    py z x y = expandedY φ ψ α x y := hExpanded x y
    _ = φ (α x y) := hReduce x y

theorem gap10 (φ : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (hY : ∀ x y, py z x y = φ (α x y))
    (hφ : Differentiable ℝ φ)
    (hα : Differentiable ℝ (Function.uncurry α)) :
    ∀ x y, pyy z x y = deriv φ (α x y) * py α x y := by
  intro x y
  have hp : DifferentiableAt ℝ (fun s : ℝ => (x, s)) y := by
    fun_prop
  have hαy : DifferentiableAt ℝ (fun s : ℝ => α x s) y := by
    simpa [Function.uncurry] using (hα (x, y)).comp y hp
  have ha : HasDerivAt (fun s : ℝ => α x s) (py α x y) y := by
    simpa only [py] using hαy.hasDerivAt
  have hcomp :
      HasDerivAt (fun s : ℝ => φ (α x s))
        (deriv φ (α x y) * py α x y) y := by
    simpa [Function.comp_def, mul_comm] using
      ((hφ (α x y)).hasDerivAt.scomp y ha)
  calc
    pyy z x y = deriv (fun s : ℝ => φ (α x s)) y := by
      exact congrArg (fun f : ℝ → ℝ => deriv f y)
        (funext fun s => hY x s)
    _ = deriv φ (α x y) * py α x y := hcomp.deriv

theorem gap11 (φ : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (hY : ∀ x y, py z x y = φ (α x y))
    (hφ : Differentiable ℝ φ)
    (hα : Differentiable ℝ (Function.uncurry α)) :
    ∀ x y, px (py z) x y = deriv φ (α x y) * px α x y := by
  intro x y
  have hp : DifferentiableAt ℝ (fun s : ℝ => (s, y)) x := by
    fun_prop
  have hαx : DifferentiableAt ℝ (fun s : ℝ => α s y) x := by
    simpa [Function.uncurry] using (hα (x, y)).comp x hp
  have ha : HasDerivAt (fun s : ℝ => α s y) (px α x y) x := by
    simpa only [px] using hαx.hasDerivAt
  have hcomp :
      HasDerivAt (fun s : ℝ => φ (α s y))
        (deriv φ (α x y) * px α x y) x := by
    simpa [Function.comp_def, mul_comm] using
      ((hφ (α x y)).hasDerivAt.scomp x ha)
  calc
    px (py z) x y = deriv (fun s : ℝ => φ (α s y)) x := by
      exact congrArg (fun f : ℝ → ℝ => deriv f x)
        (funext fun s => hY s y)
    _ = deriv φ (α x y) * px α x y := hcomp.deriv

theorem gap12 (φ : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (hXX : ∀ x y, pxx z x y = px α x y)
    (hXY : ∀ x y, pxy z x y = py α x y)
    (hYY :
      ∀ x y, pyy z x y = deriv φ (α x y) * py α x y) :
    ∀ x y,
      hessianDet z x y =
        px α x y * py α x y * deriv φ (α x y) -
          (py α x y) ^ 2 := by
  intro x y
  unfold hessianDet
  rw [hXX x y, hYY x y, hXY x y]
  ring

theorem gap13 (φ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) :
    ∀ x y,
      px α x y * py α x y * deriv φ (α x y) -
          (py α x y) ^ 2 =
        py α x y * (deriv φ (α x y) * px α x y - py α x y) := by
  intro x y
  ring

theorem gap14 (φ : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (hSubstitute :
      ∀ x y,
        hessianDet z x y =
          px α x y * py α x y * deriv φ (α x y) -
            (py α x y) ^ 2)
    (hFactor :
      ∀ x y,
        px α x y * py α x y * deriv φ (α x y) -
            (py α x y) ^ 2 =
          py α x y * (deriv φ (α x y) * px α x y - py α x y)) :
    ∀ x y,
      hessianDet z x y =
        py α x y * (deriv φ (α x y) * px α x y - py α x y) := by
  intro x y
  calc
    hessianDet z x y =
        px α x y * py α x y * deriv φ (α x y) -
          (py α x y) ^ 2 := hSubstitute x y
    _ = py α x y *
        (deriv φ (α x y) * px α x y - py α x y) := hFactor x y

theorem gap15 (φ : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (hXY : ∀ x y, pxy z x y = py α x y)
    (hYX :
      ∀ x y,
        px (py z) x y = deriv φ (α x y) * px α x y)
    (hz : ContDiff ℝ 2 (Function.uncurry z)) :
    ∀ x y, py α x y = deriv φ (α x y) * px α x y := by
  intro x y
  have hzDiff : Differentiable ℝ (Function.uncurry z) :=
    hz.differentiable (by decide)
  have hpxF (a b : ℝ) :
      px z a b =
        fderiv ℝ (Function.uncurry z) (a, b) ((1, 0) : ℝ × ℝ) := by
    have hline :=
      (hasDerivAt_id a).prodMk (hasDerivAt_const (x := a) b)
    have hcomp :=
      (hzDiff (a, b)).hasFDerivAt.comp a hline
    unfold px
    simpa [Function.comp_def, Function.uncurry] using
      hcomp.hasDerivAt.deriv
  have hpyF (a b : ℝ) :
      py z a b =
        fderiv ℝ (Function.uncurry z) (a, b) ((0, 1) : ℝ × ℝ) := by
    have hline :=
      (hasDerivAt_const (x := b) a).prodMk (hasDerivAt_id b)
    have hcomp :=
      (hzDiff (a, b)).hasFDerivAt.comp b hline
    unfold py
    simpa [Function.comp_def, Function.uncurry] using
      hcomp.hasDerivAt.deriv
  have hDFcont :
      ContDiffAt ℝ 1 (fderiv ℝ (Function.uncurry z)) (x, y) := by
    first
    | simpa using hz.contDiffAt.fderiv_right
    | simpa using (hz.contDiffAt.fderiv_right (by norm_num))
  have hDF :
      DifferentiableAt ℝ (fderiv ℝ (Function.uncurry z)) (x, y) :=
    hDFcont.differentiableAt (by norm_num)
  have hmixXY :
      HasDerivAt
        (fun t : ℝ =>
          fderiv ℝ (Function.uncurry z) (x, t)
            ((1, 0) : ℝ × ℝ))
        (fderiv ℝ (fderiv ℝ (Function.uncurry z)) (x, y)
          ((0, 1) : ℝ × ℝ) ((1, 0) : ℝ × ℝ)) y := by
    have hline :=
      (hasDerivAt_const (x := y) x).prodMk (hasDerivAt_id y)
    have hinner := hDF.hasFDerivAt.comp y hline
    have houter :=
      (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).hasFDerivAt.comp
        y hinner
    simpa [Function.comp_def] using houter.hasDerivAt
  have hmixYX :
      HasDerivAt
        (fun t : ℝ =>
          fderiv ℝ (Function.uncurry z) (t, y)
            ((0, 1) : ℝ × ℝ))
        (fderiv ℝ (fderiv ℝ (Function.uncurry z)) (x, y)
          ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) x := by
    have hline :=
      (hasDerivAt_id x).prodMk (hasDerivAt_const (x := x) y)
    have hinner := hDF.hasFDerivAt.comp x hline
    have houter :=
      (ContinuousLinearMap.apply ℝ ℝ ((0, 1) : ℝ × ℝ)).hasFDerivAt.comp
        x hinner
    simpa [Function.comp_def] using houter.hasDerivAt
  have hpXY :
      pxy z x y =
        fderiv ℝ (fderiv ℝ (Function.uncurry z)) (x, y)
          ((0, 1) : ℝ × ℝ) ((1, 0) : ℝ × ℝ) := by
    unfold pxy py
    rw [show (fun s : ℝ => px z x s) =
        (fun s : ℝ =>
          fderiv ℝ (Function.uncurry z) (x, s)
            ((1, 0) : ℝ × ℝ)) by
      funext s
      exact hpxF x s]
    exact hmixXY.deriv
  have hpYX :
      px (py z) x y =
        fderiv ℝ (fderiv ℝ (Function.uncurry z)) (x, y)
          ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) := by
    unfold px
    rw [show (fun s : ℝ => py z s y) =
        (fun s : ℝ =>
          fderiv ℝ (Function.uncurry z) (s, y)
            ((0, 1) : ℝ × ℝ)) by
      funext s
      exact hpyF s y]
    exact hmixYX.deriv
  have hsymm :
      fderiv ℝ (fderiv ℝ (Function.uncurry z)) (x, y)
          ((0, 1) : ℝ × ℝ) ((1, 0) : ℝ × ℝ) =
        fderiv ℝ (fderiv ℝ (Function.uncurry z)) (x, y)
          ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) := by
    first
    | simpa using
        (hz.contDiffAt.isSymmSndFDerivAt
          ((0, 1) : ℝ × ℝ) ((1, 0) : ℝ × ℝ))
    | simpa using
        (hz.contDiffAt.isSymmSndFDerivAt (by norm_num)
          ((0, 1) : ℝ × ℝ) ((1, 0) : ℝ × ℝ))
  calc
    py α x y = pxy z x y := (hXY x y).symm
    _ = fderiv ℝ (fderiv ℝ (Function.uncurry z)) (x, y)
          ((0, 1) : ℝ × ℝ) ((1, 0) : ℝ × ℝ) := hpXY
    _ = fderiv ℝ (fderiv ℝ (Function.uncurry z)) (x, y)
          ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) := hsymm
    _ = px (py z) x y := hpYX.symm
    _ = deriv φ (α x y) * px α x y := hYX x y

theorem gap16 (φ : ℝ → ℝ) (α z : ℝ → ℝ → ℝ)
    (hFactor :
      ∀ x y,
        hessianDet z x y =
          py α x y * (deriv φ (α x y) * px α x y - py α x y))
    (hRelation :
      ∀ x y, py α x y = deriv φ (α x y) * px α x y) :
    ∀ x y, hessianDet z x y = 0 := by
  intro x y
  rw [hFactor x y, hRelation x y]
  ring

theorem gap17 (z : ℝ → ℝ → ℝ)
    (hResult : ∀ x y, hessianDet z x y = 0) :
    ∀ x y, hessianDet z x y = 0 := by
  exact hResult

end

end ProofGap.Exercise3429
