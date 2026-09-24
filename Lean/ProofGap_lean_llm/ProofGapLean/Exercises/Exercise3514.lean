import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3514

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

def coordV (x y : ℝ) : ℝ := y / x

def wMap (x y z : ℝ) : ℝ := z / x

def physicalResidual (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialX z x y - partialY z x y

def transformedResidual (W : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  W u v - (1 + v) * partialY W u v

def physicalOperator (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialXX z x y - 2 * partialXY z x y + partialYY z x y

private theorem hasDerivAt_partialX
    (f : ℝ → ℝ → ℝ) (x y : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    HasDerivAt (fun t => f t y) (partialX f x y) x := by
  have hc : DifferentiableAt ℝ (fun t : ℝ => (t, y)) x := by
    fun_prop
  have hs := hf.fun_comp' x hc
  simpa [partialX, Function.uncurry] using hs.hasDerivAt

private theorem hasDerivAt_partialY
    (f : ℝ → ℝ → ℝ) (x y : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    HasDerivAt (fun t => f x t) (partialY f x y) y := by
  have hc : DifferentiableAt ℝ (fun t : ℝ => (x, t)) y := by
    fun_prop
  have hs := hf.fun_comp' y hc
  simpa [partialY, Function.uncurry] using hs.hasDerivAt

private theorem fderiv_uncurry_apply
    (F : ℝ → ℝ → ℝ) (a b da db : ℝ)
    (hF : DifferentiableAt ℝ (Function.uncurry F) (a, b)) :
    fderiv ℝ (Function.uncurry F) (a, b) (da, db) =
      partialX F a b * da + partialY F a b * db := by
  have hxCurve : HasDerivAt (fun t : ℝ => (t, b)) (1, 0) a := by
    simpa [id] using
      (hasDerivAt_id a).prodMk (hasDerivAt_const a b)
  have hyCurve : HasDerivAt (fun t : ℝ => (a, t)) (0, 1) b := by
    simpa [id] using
      (hasDerivAt_const b a).prodMk (hasDerivAt_id b)
  have hxComp := hF.hasFDerivAt.comp_hasDerivAt a hxCurve
  have hyComp := hF.hasFDerivAt.comp_hasDerivAt b hyCurve
  have hx :
      partialX F a b =
        fderiv ℝ (Function.uncurry F) (a, b) (1, 0) := by
    simpa [partialX, Function.comp_def, Function.uncurry] using hxComp.deriv
  have hy :
      partialY F a b =
        fderiv ℝ (Function.uncurry F) (a, b) (0, 1) := by
    simpa [partialY, Function.comp_def, Function.uncurry] using hyComp.deriv
  let L := fderiv ℝ (Function.uncurry F) (a, b)
  calc
    L (da, db) =
        L (da • (1, 0) + db • (0, 1)) := by
      congr 1
      ext <;> simp
    _ = da • L (1, 0) + db • L (0, 1) := by
      rw [map_add, map_smul, map_smul]
    _ = partialX F a b * da + partialY F a b * db := by
      rw [← hx, ← hy]
      simp [smul_eq_mul]
      ring

private theorem hasDerivAt_comp₂
    (F : ℝ → ℝ → ℝ) (f g : ℝ → ℝ) (t f' g' : ℝ)
    (hF : DifferentiableAt ℝ (Function.uncurry F) (f t, g t))
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => F (f s) (g s))
      (partialX F (f t) (g t) * f' +
        partialY F (f t) (g t) * g') t := by
  have h := hF.hasFDerivAt.comp_hasDerivAt t (hf.prodMk hg)
  rw [fderiv_uncurry_apply F (f t) (g t) f' g' hF] at h
  simpa [Function.comp_def, Function.uncurry] using h

private theorem hasDerivAt_coordV_X (x y : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t => coordV t y) (-y / x ^ 2) x := by
  have h := (hasDerivAt_const x y).div (hasDerivAt_id x) hx
  convert h using 1 <;>
    simp [coordV, id_eq] <;>
    field_simp [hx] <;> ring

private theorem hasDerivAt_coordV_Y (x y : ℝ) :
    HasDerivAt (fun t => coordV x t) (1 / x) y := by
  convert (hasDerivAt_id y).div_const x using 1 <;>
    simp [coordV, id_eq]

theorem gap1 :
    ∀ x y, partialX coordU x y = partialY coordU x y := by
  intro x y
  change deriv (fun t : ℝ => t + y) x =
    deriv (fun t : ℝ => x + t) y
  calc
    deriv (fun t : ℝ => t + y) x = 1 := by
      convert ((hasDerivAt_id x).add_const y).deriv using 1 <;> simp
    _ = deriv (fun t : ℝ => x + t) y := by
      symm
      convert ((hasDerivAt_const y x).add (hasDerivAt_id y)).deriv using 1 <;>
        simp

theorem gap2 :
    ∀ x y, partialY coordU x y = 1 := by
  intro x y
  change deriv (fun t : ℝ => x + t) y = 1
  convert ((hasDerivAt_const y x).add (hasDerivAt_id y)).deriv using 1 <;>
    simp

theorem gap3 :
    ∀ x y, partialX coordU x y = 1 := by
  intro x y
  change deriv (fun t : ℝ => t + y) x = 1
  convert ((hasDerivAt_id x).add_const y).deriv using 1 <;> simp

theorem gap4 :
    ∀ x y, x ≠ 0 → partialX coordV x y = -y / x ^ 2 := by
  intro x y hx
  exact (hasDerivAt_coordV_X x y hx).deriv

theorem gap5 :
    ∀ x y, x ≠ 0 → partialY coordV x y = 1 / x := by
  intro x y hx
  exact (hasDerivAt_coordV_Y x y).deriv

theorem gap6 (z : ℝ → ℝ → ℝ) :
    ∀ x y, x ≠ 0 →
      deriv (fun t => wMap t y (z x y)) x = -z x y / x ^ 2 := by
  intro x y hx
  have h := (hasDerivAt_const x (z x y)).div (hasDerivAt_id x) hx
  convert h.deriv using 1 <;>
    simp [wMap, id_eq] <;>
    field_simp [hx] <;> ring

theorem gap7 (z : ℝ → ℝ → ℝ) :
    ∀ x y, partialY (fun a b => wMap a b (z x y)) x y = 0 := by
  intro x y
  simp [partialY, wMap]

theorem gap8 (z : ℝ → ℝ → ℝ) :
    ∀ x y, x ≠ 0 →
      deriv (fun t => wMap x y t) (z x y) = 1 / x := by
  intro x y hx
  convert ((hasDerivAt_id (z x y)).div_const x).deriv using 1 <;>
    simp [wMap, id_eq]

theorem gap9 (z W : ℝ → ℝ → ℝ)
    (hz : C2 z) (hW : C2 W)
    (hRelation : ∀ x y, x ≠ 0 →
      W (coordU x y) (coordV x y) = z x y / x) :
    ∀ x y, x ≠ 0 →
      partialX z x y =
        x * (partialX W (coordU x y) (coordV x y) -
          y / x ^ 2 * partialY W (coordU x y) (coordV x y) +
          z x y / x ^ 2) := by
  intro x y hx
  have hzAt := hz.1 (x, y)
  have hWAt := hW.1 (coordU x y, coordV x y)
  have hzX := hasDerivAt_partialX z x y hzAt
  have hu : HasDerivAt (fun t => coordU t y) 1 x := by
    simpa [coordU] using (hasDerivAt_id x).add_const y
  have hv : HasDerivAt (fun t => coordV t y) (-y / x ^ 2) x := by
    exact hasDerivAt_coordV_X x y hx
  have hleft := hasDerivAt_comp₂ W (fun t => coordU t y)
    (fun t => coordV t y) x 1 (-y / x ^ 2) hWAt hu hv
  have hright :
      HasDerivAt (fun t => z t y / t)
        ((partialX z x y * x - z x y) / x ^ 2) x := by
    convert hzX.div (hasDerivAt_id x) hx using 1 <;>
      simp [id_eq] <;> ring
  have heq :
      (fun t => W (coordU t y) (coordV t y)) =ᶠ[nhds x]
        fun t => z t y / t := by
    filter_upwards [eventually_ne_nhds hx] with t ht
    exact hRelation t y ht
  have hd := heq.deriv_eq
  rw [hleft.deriv, hright.deriv] at hd
  field_simp [hx] at hd ⊢
  ring_nf at hd ⊢
  linarith

theorem gap10 (W z : ℝ → ℝ → ℝ) :
    ∀ x y, x ≠ 0 →
      x * (partialX W (coordU x y) (coordV x y) -
          y / x ^ 2 * partialY W (coordU x y) (coordV x y) +
          z x y / x ^ 2) =
        x * partialX W (coordU x y) (coordV x y) -
          y / x * partialY W (coordU x y) (coordV x y) + z x y / x := by
  intro x y hx
  field_simp [hx]

theorem gap11 (z W : ℝ → ℝ → ℝ)
    (hFormula : ∀ x y, x ≠ 0 →
      partialX z x y =
        x * (partialX W (coordU x y) (coordV x y) -
          y / x ^ 2 * partialY W (coordU x y) (coordV x y) +
          z x y / x ^ 2)) :
    ∀ x y, x ≠ 0 →
      partialX z x y =
        x * partialX W (coordU x y) (coordV x y) -
          y / x * partialY W (coordU x y) (coordV x y) + z x y / x := by
  intro x y hx
  rw [hFormula x y hx, gap10 W z x y hx]

theorem gap12 (z W : ℝ → ℝ → ℝ)
    (hz : C2 z) (hW : C2 W)
    (hRelation : ∀ x y, x ≠ 0 →
      W (coordU x y) (coordV x y) = z x y / x) :
    ∀ x y, x ≠ 0 →
      partialY z x y =
        x * (partialX W (coordU x y) (coordV x y) +
          1 / x * partialY W (coordU x y) (coordV x y)) := by
  intro x y hx
  have hzAt := hz.1 (x, y)
  have hWAt := hW.1 (coordU x y, coordV x y)
  have hzY := hasDerivAt_partialY z x y hzAt
  have hu : HasDerivAt (fun t => coordU x t) 1 y := by
    simpa [coordU] using (hasDerivAt_const y x).add (hasDerivAt_id y)
  have hv : HasDerivAt (fun t => coordV x t) (1 / x) y := by
    exact hasDerivAt_coordV_Y x y
  have hleft := hasDerivAt_comp₂ W (fun t => coordU x t)
    (fun t => coordV x t) y 1 (1 / x) hWAt hu hv
  have hright : HasDerivAt (fun t => z x t / x)
      (partialY z x y / x) y :=
    hzY.div_const x
  have heq :
      (fun t => W (coordU x t) (coordV x t)) =ᶠ[nhds y]
        fun t => z x t / x := by
    filter_upwards with t
    exact hRelation x t hx
  have hd := heq.deriv_eq
  rw [hleft.deriv, hright.deriv] at hd
  field_simp [hx] at hd ⊢
  ring_nf at hd ⊢
  linarith

theorem gap13 (W : ℝ → ℝ → ℝ) :
    ∀ x y, x ≠ 0 →
      x * (partialX W (coordU x y) (coordV x y) +
          1 / x * partialY W (coordU x y) (coordV x y)) =
        x * partialX W (coordU x y) (coordV x y) +
          partialY W (coordU x y) (coordV x y) := by
  intro x y hx
  field_simp [hx]

theorem gap14 (z W : ℝ → ℝ → ℝ)
    (hFormula : ∀ x y, x ≠ 0 →
      partialY z x y =
        x * (partialX W (coordU x y) (coordV x y) +
          1 / x * partialY W (coordU x y) (coordV x y))) :
    ∀ x y, x ≠ 0 →
      partialY z x y =
        x * partialX W (coordU x y) (coordV x y) +
          partialY W (coordU x y) (coordV x y) := by
  intro x y hx
  rw [hFormula x y hx, gap13 W x y hx]

theorem gap15 (z W : ℝ → ℝ → ℝ)
    (hz : C2 z) (hW : C2 W)
    (hRelation : ∀ x y, x ≠ 0 →
      W (coordU x y) (coordV x y) = z x y / x) :
    ∀ x y, x ≠ 0 →
      physicalResidual z x y =
        transformedResidual W (coordU x y) (coordV x y) := by
  intro x y hx
  rw [physicalResidual, transformedResidual]
  rw [gap11 z W (gap9 z W hz hW hRelation) x y hx]
  rw [gap14 z W (gap12 z W hz hW hRelation) x y hx]
  rw [hRelation x y hx]
  unfold coordV
  field_simp [hx]
  ring

-- Statement correction: C2 regularity is required before distributing `deriv`
-- over the residual difference.
theorem gap16 (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hz : C2 z)
    (hMixed : partialYX z x y = partialXY z x y) :
    physicalOperator z x y =
      partialX (physicalResidual z) x y - partialY (physicalResidual z) x y := by
  have hxx : HasDerivAt (fun t => partialX z t y) (partialXX z x y) x := by
    exact hasDerivAt_partialX (partialX z) x y (hz.2.1 (x, y))
  have hyx : HasDerivAt (fun t => partialY z t y) (partialYX z x y) x := by
    exact hasDerivAt_partialX (partialY z) x y (hz.2.2 (x, y))
  have hxy : HasDerivAt (fun t => partialX z x t) (partialXY z x y) y := by
    exact hasDerivAt_partialY (partialX z) x y (hz.2.1 (x, y))
  have hyy : HasDerivAt (fun t => partialY z x t) (partialYY z x y) y := by
    exact hasDerivAt_partialY (partialY z) x y (hz.2.2 (x, y))
  have hxres : partialX (physicalResidual z) x y =
      partialXX z x y - partialYX z x y := by
    unfold partialX
    simpa [physicalResidual] using (hxx.sub hyx).deriv
  have hyres : partialY (physicalResidual z) x y =
      partialXY z x y - partialYY z x y := by
    unfold partialY
    simpa [physicalResidual] using (hxy.sub hyy).deriv
  rw [hxres, hyres, physicalOperator, hMixed]
  ring

theorem gap17 (z W : ℝ → ℝ → ℝ) (x y : ℝ)
    (hx : x ≠ 0)
    (hz : C2 z) (hW : C2 W)
    (hResidual : ∀ a b, a ≠ 0 →
      physicalResidual z a b =
        transformedResidual W (coordU a b) (coordV a b)) :
    partialX (physicalResidual z) x y - partialY (physicalResidual z) x y =
      partialY (transformedResidual W) (coordU x y) (coordV x y) *
        (-y / x ^ 2 - 1 / x) := by
  let R := transformedResidual W
  have hR : DifferentiableAt ℝ (Function.uncurry R)
      (coordU x y, coordV x y) := by
    dsimp only [R, transformedResidual, Function.uncurry]
    have hfac :
        DifferentiableAt ℝ (fun p : ℝ × ℝ => 1 + p.2)
          (coordU x y, coordV x y) := by
      fun_prop
    exact (hW.1 _).sub (hfac.mul (hW.2.2 _))
  have hEqX :
      (fun t => physicalResidual z t y) =ᶠ[nhds x]
        fun t => R (coordU t y) (coordV t y) := by
    filter_upwards [eventually_ne_nhds hx] with t ht
    exact hResidual t y ht
  have hEqY :
      (fun t => physicalResidual z x t) =ᶠ[nhds y]
        fun t => R (coordU x t) (coordV x t) := by
    filter_upwards with t
    exact hResidual x t hx
  have huX : HasDerivAt (fun t => coordU t y) 1 x := by
    simpa [coordU] using (hasDerivAt_id x).add_const y
  have hvX : HasDerivAt (fun t => coordV t y) (-y / x ^ 2) x := by
    exact hasDerivAt_coordV_X x y hx
  have huY : HasDerivAt (fun t => coordU x t) 1 y := by
    simpa [coordU] using (hasDerivAt_const y x).add (hasDerivAt_id y)
  have hvY : HasDerivAt (fun t => coordV x t) (1 / x) y := by
    exact hasDerivAt_coordV_Y x y
  have hchainX := hasDerivAt_comp₂ R (fun t => coordU t y)
    (fun t => coordV t y) x 1 (-y / x ^ 2) hR huX hvX
  have hchainY := hasDerivAt_comp₂ R (fun t => coordU x t)
    (fun t => coordV x t) y 1 (1 / x) hR huY hvY
  have hpx :
      partialX (physicalResidual z) x y =
        partialX R (coordU x y) (coordV x y) +
          partialY R (coordU x y) (coordV x y) * (-y / x ^ 2) := by
    calc
      partialX (physicalResidual z) x y =
          deriv (fun t => physicalResidual z t y) x := rfl
      _ = deriv (fun t => R (coordU t y) (coordV t y)) x := hEqX.deriv_eq
      _ = _ := by simpa using hchainX.deriv
  have hpy :
      partialY (physicalResidual z) x y =
        partialX R (coordU x y) (coordV x y) +
          partialY R (coordU x y) (coordV x y) * (1 / x) := by
    calc
      partialY (physicalResidual z) x y =
          deriv (fun t => physicalResidual z x t) y := rfl
      _ = deriv (fun t => R (coordU x t) (coordV x t)) y := hEqY.deriv_eq
      _ = _ := by simpa using hchainY.deriv
  dsimp [R] at hpx hpy ⊢
  rw [hpx, hpy]
  ring

private theorem partialY_transformedResidual (W : ℝ → ℝ → ℝ)
    (u v : ℝ) (hW : C2 W) :
    partialY (transformedResidual W) u v =
      -(1 + v) * partialYY W u v := by
  change deriv (fun t => transformedResidual W u t) v =
    -(1 + v) * partialY (partialY W) u v
  have hW0 := hasDerivAt_partialY W u v (hW.1 (u, v))
  have hWy := hasDerivAt_partialY (partialY W) u v (hW.2.2 (u, v))
  have hfac : HasDerivAt (fun t : ℝ => 1 + t) 1 v := by
    simpa using (hasDerivAt_const v 1).add (hasDerivAt_id v)
  have h := hW0.sub (hfac.mul hWy)
  convert h.deriv using 1 <;> ring

theorem gap18 (z W : ℝ → ℝ → ℝ) (x y : ℝ)
    (hx : x ≠ 0)
    (hz : C2 z) (hW : C2 W)
    (hResidual : ∀ a b, a ≠ 0 →
      physicalResidual z a b =
        transformedResidual W (coordU a b) (coordV a b)) :
    partialX (physicalResidual z) x y - partialY (physicalResidual z) x y =
      1 / x * (1 + coordV x y) ^ 2 *
        partialYY W (coordU x y) (coordV x y) := by
  rw [gap17 z W x y hx hz hW hResidual]
  rw [partialY_transformedResidual W (coordU x y) (coordV x y) hW]
  unfold coordV
  field_simp [hx]
  ring

theorem gap19 (z W : ℝ → ℝ → ℝ) (x y : ℝ)
    (hx : x ≠ 0)
    (hMixed : partialYX z x y = partialXY z x y)
    (hz : C2 z) (hW : C2 W)
    (hRelation : ∀ a b, a ≠ 0 →
      W (coordU a b) (coordV a b) = z a b / a)
    (hPDE : physicalOperator z x y = 0) :
    1 / x * (1 + coordV x y) ^ 2 *
      partialYY W (coordU x y) (coordV x y) = 0 := by
  have hres := gap15 z W hz hW hRelation
  have h16 := gap16 z x y hz hMixed
  have h18 := gap18 z W x y hx hz hW hres
  rw [hPDE] at h16
  linarith

theorem gap20 (z W : ℝ → ℝ → ℝ) (x y : ℝ)
    (hx : x ≠ 0)
    (hMixed : partialYX z x y = partialXY z x y)
    (hz : C2 z) (hW : C2 W)
    (hRelation : ∀ a b, a ≠ 0 →
      W (coordU a b) (coordV a b) = z a b / a)
    (hPDE : physicalOperator z x y = 0) :
    partialX (physicalResidual z) x y - partialY (physicalResidual z) x y = 0 := by
  rw [← gap16 z x y hz hMixed]
  exact hPDE

theorem gap21 (z W : ℝ → ℝ → ℝ) (x y : ℝ)
    (hx : x ≠ 0)
    (hChart : 1 + coordV x y ≠ 0)
    (hMixed : partialYX z x y = partialXY z x y)
    (hz : C2 z) (hW : C2 W)
    (hRelation : ∀ a b, a ≠ 0 →
      W (coordU a b) (coordV a b) = z a b / a)
    (hPDE : physicalOperator z x y = 0) :
    partialYY W (coordU x y) (coordV x y) = 0 := by
  have hzero := gap19 z W x y hx hMixed hz hW hRelation hPDE
  have hxinv : 1 / x ≠ 0 := one_div_ne_zero hx
  exact (mul_eq_zero.mp hzero |>.resolve_left
    (mul_ne_zero hxinv (pow_ne_zero 2 hChart)))

end

end ProofGap.Exercise3514
