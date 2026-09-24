import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3515

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f t y) x

def partialXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f x t) y

def partialYX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY f t y) x

def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY f x t) y

def C2 (f : ℝ → ℝ → ℝ) : Prop :=
  Differentiable ℝ (Function.uncurry f) ∧
    Differentiable ℝ (Function.uncurry (partialX f)) ∧
    Differentiable ℝ (Function.uncurry (partialY f))

def coordU (x y : ℝ) : ℝ := x + y

def coordV (x y : ℝ) : ℝ := x - y

def wMap (x y z : ℝ) : ℝ := x * y - z

def physicalResidual (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialX z x y + partialY z x y

def transformedResidual (W : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  u - 2 * partialX W u v

def physicalOperator (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialXX z x y + 2 * partialXY z x y + partialYY z x y

private theorem partialX_eq_fderiv (f : ℝ → ℝ → ℝ) (x y : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    partialX f x y =
      fderiv ℝ (Function.uncurry f) (x, y) (1, 0) := by
  unfold partialX
  have hp : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  have h := (hf.hasFDerivAt.comp x hp.hasFDerivAt).hasDerivAt.deriv
  simpa [Function.uncurry] using h

private theorem partialY_eq_fderiv (f : ℝ → ℝ → ℝ) (x y : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    partialY f x y =
      fderiv ℝ (Function.uncurry f) (x, y) (0, 1) := by
  unfold partialY
  have hp : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  have h := (hf.hasFDerivAt.comp y hp.hasFDerivAt).hasDerivAt.deriv
  simpa [Function.uncurry] using h

private theorem hasDerivAt_coord_x (f : ℝ → ℝ → ℝ) (x y : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f)
      (coordU x y, coordV x y)) :
    HasDerivAt (fun t => f (coordU t y) (coordV t y))
      (partialX f (coordU x y) (coordV x y) +
        partialY f (coordU x y) (coordV x y)) x := by
  have hp : HasDerivAt (fun t : ℝ => (coordU t y, coordV t y))
      (1, 1) x := by
    have hu := (hasDerivAt_id x).add_const y
    have hv := (hasDerivAt_id x).sub_const y
    convert (hu.hasFDerivAt.prodMk hv.hasFDerivAt).hasDerivAt using 1 <;>
      simp [coordU, coordV, id]
  have h := (hf.hasFDerivAt.comp x hp.hasFDerivAt).hasDerivAt
  rw [partialX_eq_fderiv f _ _ hf, partialY_eq_fderiv f _ _ hf]
  have hlin :
      fderiv ℝ (Function.uncurry f) (coordU x y, coordV x y)
          ((1 : ℝ), (1 : ℝ)) =
        fderiv ℝ (Function.uncurry f) (coordU x y, coordV x y) (1, 0) +
          fderiv ℝ (Function.uncurry f) (coordU x y, coordV x y) (0, 1) := by
    rw [show ((1 : ℝ), (1 : ℝ)) = (1, 0) + (0, 1) by ext <;> simp, map_add]
  convert h using 1 <;> simp [Function.uncurry, hlin]

private theorem hasDerivAt_coord_y (f : ℝ → ℝ → ℝ) (x y : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f)
      (coordU x y, coordV x y)) :
    HasDerivAt (fun t => f (coordU x t) (coordV x t))
      (partialX f (coordU x y) (coordV x y) -
        partialY f (coordU x y) (coordV x y)) y := by
  have hp : HasDerivAt (fun t : ℝ => (coordU x t, coordV x t))
      (1, -1) y := by
    have hu := (hasDerivAt_id y).add_const x
    have hv := (hasDerivAt_const y x).sub (hasDerivAt_id y)
    convert (hu.hasFDerivAt.prodMk hv.hasFDerivAt).hasDerivAt using 1 <;>
      simp [coordU, coordV, id] <;> ring
  have h := (hf.hasFDerivAt.comp y hp.hasFDerivAt).hasDerivAt
  rw [partialX_eq_fderiv f _ _ hf, partialY_eq_fderiv f _ _ hf]
  have hlin :
      fderiv ℝ (Function.uncurry f) (coordU x y, coordV x y)
          ((1 : ℝ), (-1 : ℝ)) =
        fderiv ℝ (Function.uncurry f) (coordU x y, coordV x y) (1, 0) -
          fderiv ℝ (Function.uncurry f) (coordU x y, coordV x y) (0, 1) := by
    rw [show ((1 : ℝ), (-1 : ℝ)) = (1, 0) - (0, 1) by ext <;> simp, map_sub]
  convert h using 1 <;> simp [Function.uncurry, hlin]

theorem gap1 :
    ∀ x y, partialX coordU x y = partialY coordU x y := by
  intro x y
  unfold partialX partialY coordU
  have hx : deriv (fun t : ℝ => t + y) x = 1 := by
    simpa [id] using ((hasDerivAt_id x).add_const y).deriv
  have hy : deriv (fun t : ℝ => x + t) y = 1 := by
    convert ((hasDerivAt_id y).const_add x).deriv using 1 <;> simp [id]
  rw [hx, hy]

theorem gap2 :
    ∀ x y, partialY coordU x y = partialX coordV x y := by
  intro x y
  unfold partialX partialY coordU coordV
  have hy : deriv (fun t : ℝ => x + t) y = 1 := by
    convert ((hasDerivAt_id y).const_add x).deriv using 1 <;> simp [id]
  have hx : deriv (fun t : ℝ => t - y) x = 1 := by
    simpa [id] using ((hasDerivAt_id x).sub_const y).deriv
  rw [hy, hx]

theorem gap3 :
    ∀ x y, partialX coordV x y = 1 := by
  intro x y
  unfold partialX coordV
  exact ((hasDerivAt_id x).sub_const y).deriv

theorem gap4 :
    ∀ x y, partialX coordU x y = 1 := by
  intro x y
  unfold partialX coordU
  exact ((hasDerivAt_id x).add_const y).deriv

theorem gap5 :
    ∀ x y, partialY coordV x y = -1 := by
  intro x y
  unfold partialY coordV
  convert ((hasDerivAt_const y x).sub (hasDerivAt_id y)).deriv using 1 <;>
    simp [id]

theorem gap6 (z : ℝ → ℝ → ℝ) :
    ∀ x y,
      deriv (fun t => wMap t y (z x y)) x = y := by
  intro x y
  convert ((hasDerivAt_id x).mul_const y).sub_const (z x y) |>.deriv using 1 <;>
    simp [wMap, id]

theorem gap7 (z : ℝ → ℝ → ℝ) :
    ∀ x y,
      deriv (fun t => wMap x t (z x y)) y = x := by
  intro x y
  convert ((hasDerivAt_id y).const_mul x).sub_const (z x y) |>.deriv using 1 <;>
    simp [wMap, id, mul_comm]

theorem gap8 (z : ℝ → ℝ → ℝ) :
    ∀ x y,
      deriv (fun t => wMap x y t) (z x y) = -1 := by
  intro x y
  convert (hasDerivAt_const (z x y) (x * y)).sub (hasDerivAt_id (z x y)) |>.deriv
    using 1 <;> simp [wMap, id]

theorem gap9 (z W : ℝ → ℝ → ℝ)
    (hz : C2 z) (hW : C2 W)
    (hRelation : ∀ x y,
      W (coordU x y) (coordV x y) = wMap x y (z x y)) :
    ∀ x y,
      partialX z x y =
        y - partialX W (coordU x y) (coordV x y) -
          partialY W (coordU x y) (coordV x y) := by
  intro x y
  have hzLine : DifferentiableAt ℝ (fun t => z t y) x := by
    have hp : DifferentiableAt ℝ (fun t : ℝ => (t, y)) x :=
      differentiableAt_id.prodMk (differentiableAt_const (c := y))
    simpa [Function.comp_def, Function.uncurry] using
      (hz.1 (x, y)).comp x hp
  have hleft := hasDerivAt_coord_x W x y (hW.1 _)
  have hright :
      HasDerivAt (fun t => wMap t y (z t y))
        (y - partialX z x y) x := by
    convert ((hasDerivAt_id x).mul_const y).sub hzLine.hasDerivAt using 1 <;>
      simp [wMap, partialX, id]
  have hfun :
      (fun t => W (coordU t y) (coordV t y)) =
        (fun t => wMap t y (z t y)) := by
    funext t
    exact hRelation t y
  have hd :=
    (hleft.deriv.symm).trans
      ((congrArg (fun g : ℝ → ℝ => deriv g x) hfun).trans hright.deriv)
  linarith

theorem gap10 (z W : ℝ → ℝ → ℝ)
    (hz : C2 z) (hW : C2 W)
    (hRelation : ∀ x y,
      W (coordU x y) (coordV x y) = wMap x y (z x y)) :
    ∀ x y,
      partialY z x y =
        x - partialX W (coordU x y) (coordV x y) +
          partialY W (coordU x y) (coordV x y) := by
  intro x y
  have hzLine : DifferentiableAt ℝ (fun t => z x t) y := by
    have hp : DifferentiableAt ℝ (fun t : ℝ => (x, t)) y :=
      (differentiableAt_const (c := x)).prodMk differentiableAt_id
    simpa [Function.comp_def, Function.uncurry] using
      (hz.1 (x, y)).comp y hp
  have hleft := hasDerivAt_coord_y W x y (hW.1 _)
  have hright :
      HasDerivAt (fun t => wMap x t (z x t))
        (x - partialY z x y) y := by
    convert ((hasDerivAt_id y).const_mul x).sub hzLine.hasDerivAt using 1 <;>
      simp [wMap, partialY, id, mul_comm]
  have hfun :
      (fun t => W (coordU x t) (coordV x t)) =
        (fun t => wMap x t (z x t)) := by
    funext t
    exact hRelation x t
  have hd :=
    (hleft.deriv.symm).trans
      ((congrArg (fun g : ℝ → ℝ => deriv g y) hfun).trans hright.deriv)
  linarith

theorem gap11 (z W : ℝ → ℝ → ℝ)
    (hz : C2 z) (hW : C2 W)
    (hRelation : ∀ x y,
      W (coordU x y) (coordV x y) = wMap x y (z x y)) :
    ∀ x y,
      physicalResidual z x y =
        x + y - 2 * partialX W (coordU x y) (coordV x y) := by
  intro x y
  rw [physicalResidual, gap9 z W hz hW hRelation x y,
    gap10 z W hz hW hRelation x y]
  ring

theorem gap12 (W : ℝ → ℝ → ℝ) :
    ∀ x y,
      x + y - 2 * partialX W (coordU x y) (coordV x y) =
        coordU x y - 2 * partialX W (coordU x y) (coordV x y) := by
  intro x y
  rfl

theorem gap13 (z W : ℝ → ℝ → ℝ)
    (hResidual : ∀ x y,
      physicalResidual z x y =
        x + y - 2 * partialX W (coordU x y) (coordV x y)) :
    ∀ x y,
      physicalResidual z x y =
        transformedResidual W (coordU x y) (coordV x y) := by
  intro x y
  simpa [transformedResidual, coordU] using hResidual x y

-- Statement correction: expanding the derivative of a sum of first partials
-- requires differentiability of those first partial functions.
theorem gap14 (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hz : C2 z)
    (hMixed : partialYX z x y = partialXY z x y) :
    physicalOperator z x y =
      partialX (physicalResidual z) x y + partialY (physicalResidual z) x y := by
  have hpairX : DifferentiableAt ℝ (fun t : ℝ => (t, y)) x :=
    differentiableAt_id.prodMk (differentiableAt_const (c := y))
  have hpairY : DifferentiableAt ℝ (fun t : ℝ => (x, t)) y :=
    (differentiableAt_const (c := x)).prodMk differentiableAt_id
  have hxx : DifferentiableAt ℝ (fun t => partialX z t y) x := by
    simpa [Function.comp_def, Function.uncurry] using
      (hz.2.1 (x, y)).comp x hpairX
  have hyx : DifferentiableAt ℝ (fun t => partialY z t y) x := by
    simpa [Function.comp_def, Function.uncurry] using
      (hz.2.2 (x, y)).comp x hpairX
  have hxy : DifferentiableAt ℝ (fun t => partialX z x t) y := by
    simpa [Function.comp_def, Function.uncurry] using
      (hz.2.1 (x, y)).comp y hpairY
  have hyy : DifferentiableAt ℝ (fun t => partialY z x t) y := by
    simpa [Function.comp_def, Function.uncurry] using
      (hz.2.2 (x, y)).comp y hpairY
  have hX :
      partialX (physicalResidual z) x y =
        partialXX z x y + partialYX z x y := by
    have h := hxx.hasDerivAt.add hyx.hasDerivAt
    simpa [partialX, partialXX, partialYX, physicalResidual] using h.deriv
  have hY :
      partialY (physicalResidual z) x y =
        partialXY z x y + partialYY z x y := by
    have h := hxy.hasDerivAt.add hyy.hasDerivAt
    simpa [partialY, partialXY, partialYY, physicalResidual] using h.deriv
  rw [hX, hY, hMixed]
  unfold physicalOperator
  ring

theorem gap15 (z W : ℝ → ℝ → ℝ) (x y : ℝ)
    (hz : C2 z) (hW : C2 W)
    (hResidual : ∀ a b,
      physicalResidual z a b =
        transformedResidual W (coordU a b) (coordV a b)) :
    partialX (physicalResidual z) x y + partialY (physicalResidual z) x y =
      2 * partialX (transformedResidual W) (coordU x y) (coordV x y) := by
  have hT :
      Differentiable ℝ (Function.uncurry (transformedResidual W)) := by
    intro p
    change DifferentiableAt ℝ
      (fun q : ℝ × ℝ => q.1 - 2 * partialX W q.1 q.2) p
    exact differentiableAt_fst.sub
      ((differentiableAt_const (c := (2 : ℝ))).mul (hW.2.1 p))
  have hx :
      partialX (physicalResidual z) x y =
        partialX (transformedResidual W) (coordU x y) (coordV x y) +
          partialY (transformedResidual W) (coordU x y) (coordV x y) := by
    have hfun :
        (fun t => physicalResidual z t y) =
          (fun t => transformedResidual W (coordU t y) (coordV t y)) := by
      funext t
      exact hResidual t y
    calc
      partialX (physicalResidual z) x y =
          deriv (fun t => physicalResidual z t y) x := rfl
      _ = deriv
          (fun t => transformedResidual W (coordU t y) (coordV t y)) x :=
        congrArg (fun g : ℝ → ℝ => deriv g x) hfun
      _ = _ := (hasDerivAt_coord_x (transformedResidual W) x y (hT _)).deriv
  have hy :
      partialY (physicalResidual z) x y =
        partialX (transformedResidual W) (coordU x y) (coordV x y) -
          partialY (transformedResidual W) (coordU x y) (coordV x y) := by
    have hfun :
        (fun t => physicalResidual z x t) =
          (fun t => transformedResidual W (coordU x t) (coordV x t)) := by
      funext t
      exact hResidual x t
    calc
      partialY (physicalResidual z) x y =
          deriv (fun t => physicalResidual z x t) y := rfl
      _ = deriv
          (fun t => transformedResidual W (coordU x t) (coordV x t)) y :=
        congrArg (fun g : ℝ → ℝ => deriv g y) hfun
      _ = _ := (hasDerivAt_coord_y (transformedResidual W) x y (hT _)).deriv
  rw [hx, hy]
  ring

theorem gap16 (W : ℝ → ℝ → ℝ) (u v : ℝ)
    (hW : C2 W) :
    2 * partialX (transformedResidual W) u v =
      2 - 4 * partialXX W u v := by
  have hline : DifferentiableAt ℝ (fun t => partialX W t v) u := by
    have hp : DifferentiableAt ℝ (fun t : ℝ => (t, v)) u :=
      differentiableAt_id.prodMk (differentiableAt_const (c := v))
    simpa [Function.comp_def, Function.uncurry] using
      (hW.2.1 (u, v)).comp u hp
  have hderiv :
      HasDerivAt (fun t => t - 2 * partialX W t v)
        (1 - 2 * partialXX W u v) u := by
    convert (hasDerivAt_id u).sub
      ((hasDerivAt_const u (2 : ℝ)).mul hline.hasDerivAt) using 1 <;>
      simp [partialXX, id]
  have hvalue :
      partialX (transformedResidual W) u v =
        1 - 2 * partialXX W u v := by
    simpa [partialX, transformedResidual] using hderiv.deriv
  rw [hvalue]
  ring

theorem gap17 (z W : ℝ → ℝ → ℝ) (x y : ℝ)
    (hMixed : partialYX z x y = partialXY z x y)
    (hz : C2 z) (hW : C2 W)
    (hRelation : ∀ a b,
      W (coordU a b) (coordV a b) = wMap a b (z a b))
    (hPDE : physicalOperator z x y = 0) :
    2 - 4 * partialXX W (coordU x y) (coordV x y) = 0 := by
  have hResidual := gap11 z W hz hW hRelation
  have hTransformed := gap13 z W hResidual
  have hOp := gap14 z x y hz hMixed
  have hChain := gap15 z W x y hz hW hTransformed
  have hCalc := gap16 W (coordU x y) (coordV x y) hW
  exact (hCalc.symm.trans (hChain.symm.trans (hOp.symm.trans hPDE)))

theorem gap18 (z W : ℝ → ℝ → ℝ) (x y : ℝ)
    (hMixed : partialYX z x y = partialXY z x y)
    (hz : C2 z) (hW : C2 W)
    (hRelation : ∀ a b,
      W (coordU a b) (coordV a b) = wMap a b (z a b))
    (hPDE : physicalOperator z x y = 0) :
    partialX (physicalResidual z) x y + partialY (physicalResidual z) x y = 0 := by
  exact (gap14 z x y hz hMixed).symm.trans hPDE

theorem gap19 (z W : ℝ → ℝ → ℝ)
    (hz : C2 z) (hW : C2 W)
    (hMixed : ∀ x y, partialYX z x y = partialXY z x y)
    (hRelation : ∀ x y,
      W (coordU x y) (coordV x y) = wMap x y (z x y))
    (hPDE : ∀ x y, physicalOperator z x y = 0) :
    ∀ u v, partialXX W u v = (1 : ℝ) / 2 := by
  intro u v
  let x : ℝ := (u + v) / 2
  let y : ℝ := (u - v) / 2
  have h := gap17 z W x y (hMixed x y) hz hW hRelation (hPDE x y)
  have hu : coordU x y = u := by
    simp [x, y, coordU]
    ring
  have hv : coordV x y = v := by
    simp [x, y, coordV]
    ring
  rw [hu, hv] at h
  linarith

end

end ProofGap.Exercise3515
