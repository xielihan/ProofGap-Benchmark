import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3520

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

def discriminant (x y : ℝ) : ℝ := x ^ 2 - y ^ 2

def radius (x y : ℝ) : ℝ := Real.sqrt (discriminant x y)

def coordU (x y : ℝ) : ℝ := x + y

def coordV (x y : ℝ) : ℝ := x - y

def physicalPDE (z : ℝ → ℝ → ℝ) (x y : ℝ) : Prop :=
  partialXX z x y + partialYY z x y =
    2 * (x * partialX z x y - y * partialY z x y) / discriminant x y -
      3 * (x ^ 2 + y ^ 2) * z x y / discriminant x y ^ 2

def normalizedExpression (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  1 / discriminant x y * partialXX z x y +
    1 / discriminant x y * partialYY z x y -
    2 * x / discriminant x y ^ 2 * partialX z x y +
    2 * y / discriminant x y ^ 2 * partialY z x y

def fluxDivergence (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialX (fun a b => 1 / discriminant a b * partialX z a b) x y +
    partialY (fun a b => 1 / discriminant a b * partialY z a b) x y

private theorem hasDerivAt_discriminant_x (x y : ℝ) :
    HasDerivAt (fun t : ℝ => discriminant t y) (2 * x) x := by
  convert ((hasDerivAt_id x).pow 2).sub_const (y ^ 2) using 1 <;>
    simp [discriminant]

private theorem hasDerivAt_discriminant_y (x y : ℝ) :
    HasDerivAt (fun t : ℝ => discriminant x t) (-2 * y) y := by
  convert (hasDerivAt_const (x := y) (x ^ 2)).sub
    ((hasDerivAt_id y).pow 2) using 1 <;>
    simp [discriminant]

private theorem hasDerivAt_partialX (f : ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ (Function.uncurry f)) (x y : ℝ) :
    HasDerivAt (fun t : ℝ => f t y) (partialX f x y) x := by
  unfold partialX
  exact (hf.differentiableAt.comp x
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y).differentiableAt).hasDerivAt

private theorem hasDerivAt_partialY (f : ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ (Function.uncurry f)) (x y : ℝ) :
    HasDerivAt (fun t : ℝ => f x t) (partialY f x y) y := by
  unfold partialY
  exact (hf.differentiableAt.comp y
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y).differentiableAt).hasDerivAt

private theorem hasDerivAt_coordX (f : ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ (Function.uncurry f)) (x y : ℝ) :
    HasDerivAt (fun t : ℝ => f (coordU t y) (coordV t y))
      (partialX f (coordU x y) (coordV x y) +
        partialY f (coordU x y) (coordV x y)) x := by
  let L := fderiv ℝ (Function.uncurry f)
    (coordU x y, coordV x y)
  have hF : HasFDerivAt (Function.uncurry f) L
      (coordU x y, coordV x y) := by
    exact hf.differentiableAt.hasFDerivAt
  have hxF := hF.comp (coordU x y)
    (hasFDerivAt_prodMk_left (𝕜 := ℝ)
      (coordU x y) (coordV x y))
  have hyF := hF.comp (coordV x y)
    (hasFDerivAt_prodMk_right (𝕜 := ℝ)
      (coordU x y) (coordV x y))
  have hxL : HasDerivAt
      (fun t : ℝ => f t (coordV x y)) (L (1, 0)) (coordU x y) := by
    convert hxF.hasDerivAt using 1 <;> simp [Function.uncurry]
  have hyL : HasDerivAt
      (fun t : ℝ => f (coordU x y) t) (L (0, 1)) (coordV x y) := by
    convert hyF.hasDerivAt using 1 <;> simp [Function.uncurry]
  have hx : L (1, 0) = partialX f (coordU x y) (coordV x y) :=
    hxL.unique (hasDerivAt_partialX f hf (coordU x y) (coordV x y))
  have hy : L (0, 1) = partialY f (coordU x y) (coordV x y) :=
    hyL.unique (hasDerivAt_partialY f hf (coordU x y) (coordV x y))
  have hm := hF.comp x
    (((hasDerivAt_id x).add_const y).hasFDerivAt.prodMk
      ((hasDerivAt_id x).sub_const y).hasFDerivAt)
  have hmL : HasDerivAt
      (fun t : ℝ => f (coordU t y) (coordV t y)) (L (1, 1)) x := by
    convert hm.hasDerivAt using 1 <;>
      simp [coordU, coordV, Function.uncurry]
  have hcoeff :
      L (1, 1) =
        partialX f (coordU x y) (coordV x y) +
          partialY f (coordU x y) (coordV x y) := by
    calc
      L (1, 1) = L ((1, 0) + (0, 1)) := by norm_num
      _ = L (1, 0) + L (0, 1) := map_add L _ _
      _ = partialX f (coordU x y) (coordV x y) +
          partialY f (coordU x y) (coordV x y) := by rw [hx, hy]
  rw [hcoeff] at hmL
  exact hmL

private theorem hasDerivAt_coordY (f : ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ (Function.uncurry f)) (x y : ℝ) :
    HasDerivAt (fun t : ℝ => f (coordU x t) (coordV x t))
      (partialX f (coordU x y) (coordV x y) -
        partialY f (coordU x y) (coordV x y)) y := by
  let L := fderiv ℝ (Function.uncurry f)
    (coordU x y, coordV x y)
  have hF : HasFDerivAt (Function.uncurry f) L
      (coordU x y, coordV x y) := by
    exact hf.differentiableAt.hasFDerivAt
  have hxF := hF.comp (coordU x y)
    (hasFDerivAt_prodMk_left (𝕜 := ℝ)
      (coordU x y) (coordV x y))
  have hyF := hF.comp (coordV x y)
    (hasFDerivAt_prodMk_right (𝕜 := ℝ)
      (coordU x y) (coordV x y))
  have hxL : HasDerivAt
      (fun t : ℝ => f t (coordV x y)) (L (1, 0)) (coordU x y) := by
    convert hxF.hasDerivAt using 1 <;> simp [Function.uncurry]
  have hyL : HasDerivAt
      (fun t : ℝ => f (coordU x y) t) (L (0, 1)) (coordV x y) := by
    convert hyF.hasDerivAt using 1 <;> simp [Function.uncurry]
  have hx : L (1, 0) = partialX f (coordU x y) (coordV x y) :=
    hxL.unique (hasDerivAt_partialX f hf (coordU x y) (coordV x y))
  have hy : L (0, 1) = partialY f (coordU x y) (coordV x y) :=
    hyL.unique (hasDerivAt_partialY f hf (coordU x y) (coordV x y))
  have hm := hF.comp y
    (((hasDerivAt_const (x := y) x).add (hasDerivAt_id y)).hasFDerivAt.prodMk
      ((hasDerivAt_const (x := y) x).sub (hasDerivAt_id y)).hasFDerivAt)
  have hmL : HasDerivAt
      (fun t : ℝ => f (coordU x t) (coordV x t)) (L (1, -1)) y := by
    convert hm.hasDerivAt using 1 <;>
      simp [coordU, coordV, Function.uncurry]
  have hcoeff :
      L (1, -1) =
        partialX f (coordU x y) (coordV x y) -
          partialY f (coordU x y) (coordV x y) := by
    calc
      L (1, -1) = L ((1, 0) - (0, 1)) := by norm_num
      _ = L (1, 0) - L (0, 1) := map_sub L _ _
      _ = partialX f (coordU x y) (coordV x y) -
          partialY f (coordU x y) (coordV x y) := by rw [hx, hy]
  rw [hcoeff] at hmL
  exact hmL

private theorem hasDerivAt_radius_x (x y : ℝ)
    (hd : 0 < discriminant x y) :
    HasDerivAt (fun t : ℝ => radius t y) (x / radius x y) x := by
  have hr0 : radius x y ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hd)
  have h := (Real.hasDerivAt_sqrt (ne_of_gt hd)).comp x
    (hasDerivAt_discriminant_x x y)
  have h' : HasDerivAt (fun t : ℝ => radius t y)
      (1 / (2 * radius x y) * (2 * x)) x := by
    simpa only [Function.comp_apply, radius] using h
  convert h' using 1
  field_simp [hr0]

private theorem hasDerivAt_radius_y (x y : ℝ)
    (hd : 0 < discriminant x y) :
    HasDerivAt (fun t : ℝ => radius x t) (-y / radius x y) y := by
  have hr0 : radius x y ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hd)
  have h := (Real.hasDerivAt_sqrt (ne_of_gt hd)).comp y
    (hasDerivAt_discriminant_y x y)
  have h' : HasDerivAt (fun t : ℝ => radius x t)
      (1 / (2 * radius x y) * (-2 * y)) y := by
    simpa only [Function.comp_apply, radius] using h
  convert h' using 1
  field_simp [hr0]

private theorem eventually_discriminant_x_pos (x y : ℝ)
    (hd : 0 < discriminant x y) :
    ∀ᶠ t in nhds x, 0 < discriminant t y := by
  exact (hasDerivAt_discriminant_x x y).continuousAt.eventually
    (Ioi_mem_nhds hd)

private theorem eventually_discriminant_y_pos (x y : ℝ)
    (hd : 0 < discriminant x y) :
    ∀ᶠ t in nhds y, 0 < discriminant x t := by
  exact (hasDerivAt_discriminant_y x y).continuousAt.eventually
    (Ioi_mem_nhds hd)

theorem gap1 (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hd : discriminant x y ≠ 0)
    (hPDE : physicalPDE z x y) :
    normalizedExpression z x y =
      -3 * (x ^ 2 + y ^ 2) * z x y / discriminant x y ^ 3 := by
  unfold normalizedExpression physicalPDE at *
  field_simp [hd] at hPDE ⊢
  linarith

theorem gap2 (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hd : discriminant x y ≠ 0)
    (hz : C2 z)
    (hNormalized : normalizedExpression z x y =
      -3 * (x ^ 2 + y ^ 2) * z x y / discriminant x y ^ 3) :
    fluxDivergence z x y =
      -3 * (x ^ 2 + y ^ 2) * z x y / discriminant x y ^ 3 := by
  rcases hz with ⟨hz, hzx, hzy⟩
  have hdx := hasDerivAt_discriminant_x x y
  have hdy := hasDerivAt_discriminant_y x y
  have hpx : HasDerivAt (fun t : ℝ => partialX z t y) (partialXX z x y) x := by
    simpa [partialXX, partialX] using
      (hasDerivAt_partialX (partialX z) hzx x y)
  have hpy : HasDerivAt (fun t : ℝ => partialY z x t) (partialYY z x y) y := by
    simpa [partialYY, partialY] using
      (hasDerivAt_partialY (partialY z) hzy x y)
  have hx := (hdx.inv hd).mul hpx
  have hy := (hdy.inv hd).mul hpy
  have hx' :
      deriv (fun t : ℝ =>
        1 / discriminant t y * partialX z t y) x =
        -(2 * x) / discriminant x y ^ 2 * partialX z x y +
          1 / discriminant x y * partialXX z x y := by
    simpa [one_div] using hx.deriv
  have hy' :
      deriv (fun t : ℝ =>
        1 / discriminant x t * partialY z x t) y =
        -(-2 * y) / discriminant x y ^ 2 * partialY z x y +
          1 / discriminant x y * partialYY z x y := by
    simpa [one_div] using hy.deriv
  have hflux : fluxDivergence z x y = normalizedExpression z x y := by
    unfold fluxDivergence
    change
      deriv (fun t : ℝ =>
          1 / discriminant t y * partialX z t y) x +
        deriv (fun t : ℝ =>
          1 / discriminant x t * partialY z x t) y =
        normalizedExpression z x y
    rw [hx', hy']
    unfold normalizedExpression
    field_simp [hd] <;> ring
  calc
    fluxDivergence z x y = normalizedExpression z x y := hflux
    _ = -3 * (x ^ 2 + y ^ 2) * z x y /
        discriminant x y ^ 3 := hNormalized

theorem gap3 (z W : ℝ → ℝ → ℝ) (x y : ℝ)
    (hd : 0 < discriminant x y)
    (hz : C2 z) (hW : C2 W)
    (hRelation : ∀ a b, 0 < discriminant a b →
      W (coordU a b) (coordV a b) = z a b / radius a b) :
    partialX z x y =
      radius x y *
          (partialX W (coordU x y) (coordV x y) +
            partialY W (coordU x y) (coordV x y)) +
        x * z x y / discriminant x y := by
  have hr : 0 < radius x y := Real.sqrt_pos.2 hd
  have hr0 : radius x y ≠ 0 := ne_of_gt hr
  have hlocal :
      (fun t : ℝ => W (coordU t y) (coordV t y)) =ᶠ[nhds x]
        (fun t => z t y / radius t y) := by
    apply (eventually_discriminant_x_pos x y hd).mono
    intro t ht
    exact hRelation t y ht
  have hleft := hasDerivAt_coordX W hW.1 x y
  have hright : HasDerivAt (fun t : ℝ => z t y / radius t y)
      ((partialX z x y * radius x y - z x y * (x / radius x y)) /
        radius x y ^ 2) x :=
    (hasDerivAt_partialX z hz.1 x y).div
      (hasDerivAt_radius_x x y hd) hr0
  have heq := (hleft.congr_of_eventuallyEq hlocal.symm).unique hright
  have hrsq : radius x y ^ 2 = discriminant x y :=
    Real.sq_sqrt (le_of_lt hd)
  rw [← hrsq]
  field_simp [hr0] at heq ⊢
  nlinarith [heq]

theorem gap4 (z W : ℝ → ℝ → ℝ) (x y : ℝ)
    (hd : 0 < discriminant x y)
    (hz : C2 z) (hW : C2 W)
    (hRelation : ∀ a b, 0 < discriminant a b →
      W (coordU a b) (coordV a b) = z a b / radius a b) :
    partialY z x y =
      radius x y *
          (partialX W (coordU x y) (coordV x y) -
            partialY W (coordU x y) (coordV x y)) -
        y * z x y / discriminant x y := by
  have hr : 0 < radius x y := Real.sqrt_pos.2 hd
  have hr0 : radius x y ≠ 0 := ne_of_gt hr
  have hlocal :
      (fun t : ℝ => W (coordU x t) (coordV x t)) =ᶠ[nhds y]
        (fun t => z x t / radius x t) := by
    apply (eventually_discriminant_y_pos x y hd).mono
    intro t ht
    exact hRelation x t ht
  have hleft := hasDerivAt_coordY W hW.1 x y
  have hright : HasDerivAt (fun t : ℝ => z x t / radius x t)
      ((partialY z x y * radius x y - z x y * (-y / radius x y)) /
        radius x y ^ 2) y :=
    (hasDerivAt_partialY z hz.1 x y).div
      (hasDerivAt_radius_y x y hd) hr0
  have heq := (hleft.congr_of_eventuallyEq hlocal.symm).unique hright
  have hrsq : radius x y ^ 2 = discriminant x y :=
    Real.sq_sqrt (le_of_lt hd)
  rw [← hrsq]
  field_simp [hr0] at heq ⊢
  nlinarith [heq]

theorem gap5 (z W : ℝ → ℝ → ℝ) (x y : ℝ)
    (hd : 0 < discriminant x y)
    (hz : C2 z) (hW : C2 W)
    (hMixed : partialYX W (coordU x y) (coordV x y) =
      partialXY W (coordU x y) (coordV x y))
    (hRelation : ∀ a b, 0 < discriminant a b →
      W (coordU a b) (coordV a b) = z a b / radius a b) :
    partialX (fun a b => 1 / discriminant a b * partialX z a b) x y =
      z x y / discriminant x y ^ 2 -
        3 * x ^ 2 * z x y / discriminant x y ^ 3 +
        1 / radius x y *
          (partialXX W (coordU x y) (coordV x y) +
            2 * partialXY W (coordU x y) (coordV x y) +
            partialYY W (coordU x y) (coordV x y)) := by
  have hd0 : discriminant x y ≠ 0 := ne_of_gt hd
  have hr : 0 < radius x y := Real.sqrt_pos.2 hd
  have hr0 : radius x y ≠ 0 := ne_of_gt hr
  have hzx := hasDerivAt_partialX z hz.1 x y
  have hdx := hasDerivAt_discriminant_x x y
  have hrx := hasDerivAt_radius_x x y hd
  have hAx : HasDerivAt
      (fun t : ℝ => partialX W (coordU t y) (coordV t y))
      (partialXX W (coordU x y) (coordV x y) +
        partialXY W (coordU x y) (coordV x y)) x := by
    simpa [partialXX, partialXY] using
      (hasDerivAt_coordX (partialX W) hW.2.1 x y)
  have hAy : HasDerivAt
      (fun t : ℝ => partialY W (coordU t y) (coordV t y))
      (partialYX W (coordU x y) (coordV x y) +
        partialYY W (coordU x y) (coordV x y)) x := by
    simpa [partialYX, partialYY] using
      (hasDerivAt_coordX (partialY W) hW.2.2 x y)
  have hA := hAx.add hAy
  rw [hMixed] at hA
  have hterm1 :=
    ((hasDerivAt_id x).mul hzx).div (hdx.pow 2) (pow_ne_zero 2 hd0)
  have hterm2 := hA.div hrx hr0
  have hR := hterm1.add hterm2
  have hlocal :
      (fun t : ℝ => 1 / discriminant t y * partialX z t y) =ᶠ[nhds x]
        (((id : ℝ → ℝ) * (fun t : ℝ => z t y)) /
            ((fun t : ℝ => discriminant t y) ^ 2) +
          ((fun t : ℝ =>
              partialX W (coordU t y) (coordV t y)) +
            (fun t : ℝ =>
              partialY W (coordU t y) (coordV t y))) /
            (fun t : ℝ => radius t y)) := by
    apply (eventually_discriminant_x_pos x y hd).mono
    intro t ht
    have hrt : 0 < radius t y := Real.sqrt_pos.2 ht
    have hfirst := gap3 z W t y ht hz hW hRelation
    have hdeq : discriminant t y = radius t y ^ 2 :=
      (Real.sq_sqrt (le_of_lt ht)).symm
    change 1 / discriminant t y * partialX z t y =
      t * z t y / discriminant t y ^ 2 +
        (partialX W (coordU t y) (coordV t y) +
          partialY W (coordU t y) (coordV t y)) / radius t y
    rw [hfirst, hdeq]
    field_simp [ne_of_gt hrt] <;> ring
  have hOrig := hR.congr_of_eventuallyEq hlocal
  have hfirst := gap3 z W x y hd hz hW hRelation
  have hdeq : discriminant x y = radius x y ^ 2 :=
    (Real.sq_sqrt (le_of_lt hd)).symm
  change deriv (fun t : ℝ =>
    1 / discriminant t y * partialX z t y) x = _
  rw [hOrig.deriv]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply,
    Pi.pow_apply, id_eq]
  rw [hfirst, hdeq]
  field_simp [hr0] <;> ring

theorem gap6 (z W : ℝ → ℝ → ℝ) (x y : ℝ)
    (hd : 0 < discriminant x y)
    (hz : C2 z) (hW : C2 W)
    (hMixed : partialYX W (coordU x y) (coordV x y) =
      partialXY W (coordU x y) (coordV x y))
    (hRelation : ∀ a b, 0 < discriminant a b →
      W (coordU a b) (coordV a b) = z a b / radius a b) :
    partialY (fun a b => 1 / discriminant a b * partialY z a b) x y =
      -z x y / discriminant x y ^ 2 -
        3 * y ^ 2 * z x y / discriminant x y ^ 3 +
        1 / radius x y *
          (partialXX W (coordU x y) (coordV x y) -
            2 * partialXY W (coordU x y) (coordV x y) +
            partialYY W (coordU x y) (coordV x y)) := by
  have hd0 : discriminant x y ≠ 0 := ne_of_gt hd
  have hr : 0 < radius x y := Real.sqrt_pos.2 hd
  have hr0 : radius x y ≠ 0 := ne_of_gt hr
  have hzy := hasDerivAt_partialY z hz.1 x y
  have hdy := hasDerivAt_discriminant_y x y
  have hry := hasDerivAt_radius_y x y hd
  have hX : HasDerivAt
      (fun t : ℝ => partialX W (coordU x t) (coordV x t))
      (partialXX W (coordU x y) (coordV x y) -
        partialXY W (coordU x y) (coordV x y)) y := by
    simpa [partialXX, partialXY] using
      (hasDerivAt_coordY (partialX W) hW.2.1 x y)
  have hY : HasDerivAt
      (fun t : ℝ => partialY W (coordU x t) (coordV x t))
      (partialYX W (coordU x y) (coordV x y) -
        partialYY W (coordU x y) (coordV x y)) y := by
    simpa [partialYX, partialYY] using
      (hasDerivAt_coordY (partialY W) hW.2.2 x y)
  have hC := hX.sub hY
  rw [hMixed] at hC
  have hterm1 :=
    (((hasDerivAt_id y).mul hzy).div (hdy.pow 2)
      (pow_ne_zero 2 hd0)).neg
  have hterm2 := hC.div hry hr0
  have hR := hterm1.add hterm2
  have hlocal :
      (fun t : ℝ => 1 / discriminant x t * partialY z x t) =ᶠ[nhds y]
        (-(((id : ℝ → ℝ) * (fun t : ℝ => z x t)) /
            ((fun t : ℝ => discriminant x t) ^ 2)) +
          ((fun t : ℝ =>
              partialX W (coordU x t) (coordV x t)) -
            (fun t : ℝ =>
              partialY W (coordU x t) (coordV x t))) /
            (fun t : ℝ => radius x t)) := by
    apply (eventually_discriminant_y_pos x y hd).mono
    intro t ht
    have hrt : 0 < radius x t := Real.sqrt_pos.2 ht
    have hfirst := gap4 z W x t ht hz hW hRelation
    have hdeq : discriminant x t = radius x t ^ 2 :=
      (Real.sq_sqrt (le_of_lt ht)).symm
    change 1 / discriminant x t * partialY z x t =
      -(t * z x t / discriminant x t ^ 2) +
        (partialX W (coordU x t) (coordV x t) -
          partialY W (coordU x t) (coordV x t)) / radius x t
    rw [hfirst, hdeq]
    field_simp [ne_of_gt hrt] <;> ring
  have hOrig := hR.congr_of_eventuallyEq hlocal
  have hfirst := gap4 z W x y hd hz hW hRelation
  have hdeq : discriminant x y = radius x y ^ 2 :=
    (Real.sq_sqrt (le_of_lt hd)).symm
  change deriv (fun t : ℝ =>
    1 / discriminant x t * partialY z x t) y = _
  rw [hOrig.deriv]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply,
    Pi.pow_apply, id_eq]
  rw [hfirst, hdeq]
  field_simp [hr0] <;> ring

theorem gap7 (z W : ℝ → ℝ → ℝ) (x y : ℝ)
    (hd : 0 < discriminant x y)
    (hz : C2 z) (hW : C2 W)
    (hMixed : partialYX W (coordU x y) (coordV x y) =
      partialXY W (coordU x y) (coordV x y))
    (hRelation : ∀ a b, 0 < discriminant a b →
      W (coordU a b) (coordV a b) = z a b / radius a b)
    (hPDE : physicalPDE z x y) :
    partialXX W (coordU x y) (coordV x y) +
      partialYY W (coordU x y) (coordV x y) = 0 := by
  have hd0 : discriminant x y ≠ 0 := ne_of_gt hd
  have hr0 : radius x y ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hd)
  have hn := gap1 z x y hd0 hPDE
  have hf := gap2 z x y hd0 hz hn
  have hx := gap5 z W x y hd hz hW hMixed hRelation
  have hy := gap6 z W x y hd hz hW hMixed hRelation
  have hzero :
      2 / radius x y *
        (partialXX W (coordU x y) (coordV x y) +
          partialYY W (coordU x y) (coordV x y)) = 0 := by
    calc
      2 / radius x y *
          (partialXX W (coordU x y) (coordV x y) +
            partialYY W (coordU x y) (coordV x y)) =
          fluxDivergence z x y -
            (-3 * (x ^ 2 + y ^ 2) * z x y / discriminant x y ^ 3) := by
              unfold fluxDivergence
              rw [hx, hy]
              ring
      _ = 0 := by rw [hf]; ring
  have hc : 2 / radius x y ≠ 0 := div_ne_zero (by norm_num) hr0
  exact (mul_eq_zero.mp hzero).resolve_left hc

end

end ProofGap.Exercise3520
