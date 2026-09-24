import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3490

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialX (partialX f) x y

def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialY (partialY f) x y

def asinhCoordinate (x : ℝ) : ℝ :=
  Real.log (x + Real.sqrt (1 + x ^ 2))

private theorem hasDerivAt_sqrtOneAddSq (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sqrt (1 + t ^ 2))
      (x / Real.sqrt (1 + x ^ 2)) x := by
  have hx : 0 < 1 + x ^ 2 := by positivity
  have hs : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 hx
  have hq : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * x) x := by
    convert
      (hasDerivAt_const (x := x) (c := (1 : ℝ))).add
        ((hasDerivAt_id x).pow 2) using 1 <;> simp <;> ring
  convert (Real.hasDerivAt_sqrt hx.ne').comp x hq using 1 <;>
    field_simp [hs.ne'] <;> ring

private theorem hasDerivAt_asinhCoordinate (x : ℝ) :
    HasDerivAt asinhCoordinate (1 / Real.sqrt (1 + x ^ 2)) x := by
  have hx : 0 < 1 + x ^ 2 := by positivity
  have hs : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 hx
  have hsquare : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt hx.le
  have harg : 0 < x + Real.sqrt (1 + x ^ 2) := by
    nlinarith [Real.sqrt_nonneg (1 + x ^ 2),
      sq_nonneg (Real.sqrt (1 + x ^ 2) + x),
      sq_nonneg (Real.sqrt (1 + x ^ 2) - x)]
  have hinner : HasDerivAt
      (fun t : ℝ => t + Real.sqrt (1 + t ^ 2))
      (1 + x / Real.sqrt (1 + x ^ 2)) x :=
    (hasDerivAt_id x).add (hasDerivAt_sqrtOneAddSq x)
  unfold asinhCoordinate
  convert (Real.hasDerivAt_log harg.ne').comp x hinner using 1 <;>
    field_simp [hs.ne', harg.ne'] <;> ring

private theorem hasDerivAt_invSqrtOneAddSq (x : ℝ) :
    HasDerivAt (fun t : ℝ => 1 / Real.sqrt (1 + t ^ 2))
      (-(x / ((1 + x ^ 2) * Real.sqrt (1 + x ^ 2)))) x := by
  have hx : 0 < 1 + x ^ 2 := by positivity
  have hs : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 hx
  have hsquare : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt hx.le
  have h : HasDerivAt (fun t : ℝ => 1 / Real.sqrt (1 + t ^ 2))
      (-(x / Real.sqrt (1 + x ^ 2)) /
        Real.sqrt (1 + x ^ 2) ^ 2) x := by
    simpa only [one_div] using
      (hasDerivAt_sqrtOneAddSq x).inv hs.ne'
  convert h using 1
  rw [hsquare]
  field_simp [hx.ne', hs.ne']

private theorem tendsto_pair_left (x y : ℝ) :
    Filter.Tendsto (fun t : ℝ => (t, y)) (nhds x) (nhds (x, y)) := by
  rw [nhds_prod_eq]
  exact Filter.tendsto_id.prodMk tendsto_const_nhds

private theorem tendsto_pair_right (x y : ℝ) :
    Filter.Tendsto (fun t : ℝ => (x, t)) (nhds y) (nhds (x, y)) := by
  rw [nhds_prod_eq]
  exact tendsto_const_nhds.prodMk Filter.tendsto_id

private theorem hasDerivAt_coordinate_comp_x
    (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      Z p.1 p.2 = z (u p.1 p.2) (v p.1 p.2))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      u p.1 p.2 = asinhCoordinate p.1)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      v p.1 p.2 = asinhCoordinate p.2)
    (hDiffz : DifferentiableAt ℝ (Function.uncurry z) (u x y, v x y)) :
    HasDerivAt (fun t : ℝ => Z t y)
      (partialX z (u x y) (v x y) *
        (1 / Real.sqrt (1 + x ^ 2))) x := by
  have hline := tendsto_pair_left x y
  have hComposeLine := hline.eventually hCompose
  have hUline :
      (fun t : ℝ => u t y) =ᶠ[nhds x] (fun t : ℝ => asinhCoordinate t) := by
    simpa using hline.eventually hU
  have hVline :
      (fun t : ℝ => v t y) =ᶠ[nhds x] (fun _ : ℝ => asinhCoordinate y) := by
    simpa using hline.eventually hV
  have hv0 : v x y = asinhCoordinate y := hVline.eq_of_nhds
  have hlocal :
      (fun t : ℝ => Z t y) =ᶠ[nhds x]
        (fun t : ℝ => z (u t y) (v x y)) := by
    filter_upwards [hComposeLine, hVline] with t hcomp hv
    rw [hcomp, hv, hv0]
  have hu : HasDerivAt (fun t : ℝ => u t y)
      (1 / Real.sqrt (1 + x ^ 2)) x :=
    (hasDerivAt_asinhCoordinate x).congr_of_eventuallyEq hUline
  have hid : DifferentiableAt ℝ (fun a : ℝ => a) (u x y) :=
    differentiableAt_id
  have hc : DifferentiableAt ℝ (fun _ : ℝ => v x y) (u x y) :=
    differentiableAt_const (v x y)
  have hp : DifferentiableAt ℝ (fun a : ℝ => (a, v x y)) (u x y) :=
    hid.prodMk hc
  have hz : DifferentiableAt ℝ (fun a : ℝ => z a (v x y)) (u x y) := by
    simpa [Function.uncurry] using hDiffz.comp (u x y) hp
  simpa [partialX] using
    (hz.hasDerivAt.comp x hu).congr_of_eventuallyEq hlocal

private theorem hasDerivAt_coordinate_comp_y
    (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      Z p.1 p.2 = z (u p.1 p.2) (v p.1 p.2))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      u p.1 p.2 = asinhCoordinate p.1)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      v p.1 p.2 = asinhCoordinate p.2)
    (hDiffz : DifferentiableAt ℝ (Function.uncurry z) (u x y, v x y)) :
    HasDerivAt (fun t : ℝ => Z x t)
      (partialY z (u x y) (v x y) *
        (1 / Real.sqrt (1 + y ^ 2))) y := by
  have hline := tendsto_pair_right x y
  have hComposeLine := hline.eventually hCompose
  have hUline :
      (fun t : ℝ => u x t) =ᶠ[nhds y] (fun _ : ℝ => asinhCoordinate x) := by
    simpa using hline.eventually hU
  have hVline :
      (fun t : ℝ => v x t) =ᶠ[nhds y] (fun t : ℝ => asinhCoordinate t) := by
    simpa using hline.eventually hV
  have hu0 : u x y = asinhCoordinate x := hUline.eq_of_nhds
  have hlocal :
      (fun t : ℝ => Z x t) =ᶠ[nhds y]
        (fun t : ℝ => z (u x y) (v x t)) := by
    filter_upwards [hComposeLine, hUline] with t hcomp hu
    rw [hcomp, hu, hu0]
  have hv : HasDerivAt (fun t : ℝ => v x t)
      (1 / Real.sqrt (1 + y ^ 2)) y :=
    (hasDerivAt_asinhCoordinate y).congr_of_eventuallyEq hVline
  have hc : DifferentiableAt ℝ (fun _ : ℝ => u x y) (v x y) :=
    differentiableAt_const (u x y)
  have hid : DifferentiableAt ℝ (fun b : ℝ => b) (v x y) :=
    differentiableAt_id
  have hp : DifferentiableAt ℝ (fun b : ℝ => (u x y, b)) (v x y) :=
    hc.prodMk hid
  have hz : DifferentiableAt ℝ (fun b : ℝ => z (u x y) b) (v x y) := by
    simpa [Function.uncurry] using hDiffz.comp (v x y) hp
  simpa [partialY] using
    (hz.hasDerivAt.comp y hv).congr_of_eventuallyEq hlocal

theorem gap1 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      Z p.1 p.2 = z (u p.1 p.2) (v p.1 p.2))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y), u p.1 p.2 = asinhCoordinate p.1)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y), v p.1 p.2 = asinhCoordinate p.2)
    (hDiffz : DifferentiableAt ℝ (Function.uncurry z) (u x y, v x y)) :
    partialX Z x y =
      partialX z (u x y) (v x y) * partialX u x y := by
  have hUline :
      (fun t : ℝ => u t y) =ᶠ[nhds x] (fun t : ℝ => asinhCoordinate t) := by
    simpa using (tendsto_pair_left x y).eventually hU
  have hu : HasDerivAt (fun t : ℝ => u t y)
      (1 / Real.sqrt (1 + x ^ 2)) x :=
    (hasDerivAt_asinhCoordinate x).congr_of_eventuallyEq hUline
  change deriv (fun t : ℝ => Z t y) x = _
  rw [show partialX u x y = 1 / Real.sqrt (1 + x ^ 2) by
    simpa [partialX] using hu.deriv]
  exact (hasDerivAt_coordinate_comp_x u v z Z x y hCompose hU hV hDiffz).deriv

theorem gap2 (u z : ℝ → ℝ → ℝ) (x y v : ℝ)
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y), u p.1 p.2 = asinhCoordinate p.1) :
    partialX z (u x y) v * partialX u x y =
      1 / Real.sqrt (1 + x ^ 2) * partialX z (u x y) v := by
  have hUline :
      (fun t : ℝ => u t y) =ᶠ[nhds x] (fun t : ℝ => asinhCoordinate t) := by
    simpa using (tendsto_pair_left x y).eventually hU
  have hu : HasDerivAt (fun t : ℝ => u t y)
      (1 / Real.sqrt (1 + x ^ 2)) x :=
    (hasDerivAt_asinhCoordinate x).congr_of_eventuallyEq hUline
  rw [show partialX u x y = 1 / Real.sqrt (1 + x ^ 2) by
    simpa [partialX] using hu.deriv]
  ring

theorem gap3 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hChain :
      partialX Z x y = partialX z (u x y) (v x y) * partialX u x y)
    (hCoordinateDerivative :
      partialX z (u x y) (v x y) * partialX u x y =
        1 / Real.sqrt (1 + x ^ 2) * partialX z (u x y) (v x y)) :
    partialX Z x y =
      1 / Real.sqrt (1 + x ^ 2) * partialX z (u x y) (v x y) := by
  rw [hChain, hCoordinateDerivative]

theorem gap4 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      Z p.1 p.2 = z (u p.1 p.2) (v p.1 p.2))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y), u p.1 p.2 = asinhCoordinate p.1)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y), v p.1 p.2 = asinhCoordinate p.2)
    (hDiffz : DifferentiableAt ℝ (Function.uncurry z) (u x y, v x y)) :
    partialY Z x y =
      1 / Real.sqrt (1 + y ^ 2) * partialY z (u x y) (v x y) := by
  have h := hasDerivAt_coordinate_comp_y u v z Z x y hCompose hU hV hDiffz
  change deriv (fun t : ℝ => Z x t) y = _
  rw [h.deriv]
  ring

theorem gap5 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hZx : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialX Z p.1 p.2 =
        1 / Real.sqrt (1 + p.1 ^ 2) *
          partialX z (u p.1 p.2) (v p.1 p.2))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y), u p.1 p.2 = asinhCoordinate p.1)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y), v p.1 p.2 = asinhCoordinate p.2)
    (hDiffZu :
      DifferentiableAt ℝ (Function.uncurry (partialX z)) (u x y, v x y)) :
    partialXX Z x y =
      -(x / ((1 + x ^ 2) * Real.sqrt (1 + x ^ 2))) *
          partialX z (u x y) (v x y) +
        1 / (1 + x ^ 2) * partialXX z (u x y) (v x y) := by
  have hW : HasDerivAt
      (fun t : ℝ => partialX z (u t y) (v t y))
      (partialXX z (u x y) (v x y) *
        (1 / Real.sqrt (1 + x ^ 2))) x := by
    simpa [partialXX] using
      (hasDerivAt_coordinate_comp_x u v (partialX z)
        (fun a b => partialX z (u a b) (v a b)) x y
        (Filter.Eventually.of_forall (fun _ => rfl)) hU hV hDiffZu)
  have hprod := (hasDerivAt_invSqrtOneAddSq x).mul hW
  have hZline :
      (fun t : ℝ => partialX Z t y) =ᶠ[nhds x]
        (fun t : ℝ =>
          1 / Real.sqrt (1 + t ^ 2) *
            partialX z (u t y) (v t y)) := by
    simpa using (tendsto_pair_left x y).eventually hZx
  have hfinal : HasDerivAt (fun t : ℝ => partialX Z t y)
      (-(x / ((1 + x ^ 2) * Real.sqrt (1 + x ^ 2))) *
            partialX z (u x y) (v x y) +
          1 / Real.sqrt (1 + x ^ 2) *
            (partialXX z (u x y) (v x y) *
              (1 / Real.sqrt (1 + x ^ 2)))) x :=
    hprod.congr_of_eventuallyEq hZline
  have hx : 0 < 1 + x ^ 2 := by positivity
  have hs : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 hx
  have hsquare : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt hx.le
  have hinv :
      1 / Real.sqrt (1 + x ^ 2) *
          (partialXX z (u x y) (v x y) *
            (1 / Real.sqrt (1 + x ^ 2))) =
        1 / (1 + x ^ 2) * partialXX z (u x y) (v x y) := by
    calc
      1 / Real.sqrt (1 + x ^ 2) *
            (partialXX z (u x y) (v x y) *
              (1 / Real.sqrt (1 + x ^ 2))) =
          1 / (Real.sqrt (1 + x ^ 2) ^ 2) *
            partialXX z (u x y) (v x y) := by
              field_simp [hs.ne']
              <;> ring
      _ = 1 / (1 + x ^ 2) * partialXX z (u x y) (v x y) := by
        rw [hsquare]
  rw [hinv] at hfinal
  change deriv (fun t : ℝ => partialX Z t y) x = _
  exact hfinal.deriv

theorem gap6 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hZy : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialY Z p.1 p.2 =
        1 / Real.sqrt (1 + p.2 ^ 2) *
          partialY z (u p.1 p.2) (v p.1 p.2))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y), u p.1 p.2 = asinhCoordinate p.1)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y), v p.1 p.2 = asinhCoordinate p.2)
    (hDiffZv :
      DifferentiableAt ℝ (Function.uncurry (partialY z)) (u x y, v x y)) :
    partialYY Z x y =
      -(y / ((1 + y ^ 2) * Real.sqrt (1 + y ^ 2))) *
          partialY z (u x y) (v x y) +
        1 / (1 + y ^ 2) * partialYY z (u x y) (v x y) := by
  have hW : HasDerivAt
      (fun t : ℝ => partialY z (u x t) (v x t))
      (partialYY z (u x y) (v x y) *
        (1 / Real.sqrt (1 + y ^ 2))) y := by
    simpa [partialYY] using
      (hasDerivAt_coordinate_comp_y u v (partialY z)
        (fun a b => partialY z (u a b) (v a b)) x y
        (Filter.Eventually.of_forall (fun _ => rfl)) hU hV hDiffZv)
  have hprod := (hasDerivAt_invSqrtOneAddSq y).mul hW
  have hZline :
      (fun t : ℝ => partialY Z x t) =ᶠ[nhds y]
        (fun t : ℝ =>
          1 / Real.sqrt (1 + t ^ 2) *
            partialY z (u x t) (v x t)) := by
    simpa using (tendsto_pair_right x y).eventually hZy
  have hfinal : HasDerivAt (fun t : ℝ => partialY Z x t)
      (-(y / ((1 + y ^ 2) * Real.sqrt (1 + y ^ 2))) *
            partialY z (u x y) (v x y) +
          1 / Real.sqrt (1 + y ^ 2) *
            (partialYY z (u x y) (v x y) *
              (1 / Real.sqrt (1 + y ^ 2)))) y :=
    hprod.congr_of_eventuallyEq hZline
  have hy : 0 < 1 + y ^ 2 := by positivity
  have hs : 0 < Real.sqrt (1 + y ^ 2) := Real.sqrt_pos.2 hy
  have hsquare : Real.sqrt (1 + y ^ 2) ^ 2 = 1 + y ^ 2 :=
    Real.sq_sqrt hy.le
  have hinv :
      1 / Real.sqrt (1 + y ^ 2) *
          (partialYY z (u x y) (v x y) *
            (1 / Real.sqrt (1 + y ^ 2))) =
        1 / (1 + y ^ 2) * partialYY z (u x y) (v x y) := by
    calc
      1 / Real.sqrt (1 + y ^ 2) *
            (partialYY z (u x y) (v x y) *
              (1 / Real.sqrt (1 + y ^ 2))) =
          1 / (Real.sqrt (1 + y ^ 2) ^ 2) *
            partialYY z (u x y) (v x y) := by
              field_simp [hs.ne']
              <;> ring
      _ = 1 / (1 + y ^ 2) * partialYY z (u x y) (v x y) := by
        rw [hsquare]
  rw [hinv] at hfinal
  change deriv (fun t : ℝ => partialY Z x t) y = _
  exact hfinal.deriv

theorem gap7 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hPDE :
      (1 + x ^ 2) * partialXX Z x y +
          (1 + y ^ 2) * partialYY Z x y +
          x * partialX Z x y + y * partialY Z x y = 0)
    (hZx :
      partialX Z x y =
        1 / Real.sqrt (1 + x ^ 2) * partialX z (u x y) (v x y))
    (hZy :
      partialY Z x y =
        1 / Real.sqrt (1 + y ^ 2) * partialY z (u x y) (v x y))
    (hZxx :
      partialXX Z x y =
        -(x / ((1 + x ^ 2) * Real.sqrt (1 + x ^ 2))) *
            partialX z (u x y) (v x y) +
          1 / (1 + x ^ 2) * partialXX z (u x y) (v x y))
    (hZyy :
      partialYY Z x y =
        -(y / ((1 + y ^ 2) * Real.sqrt (1 + y ^ 2))) *
            partialY z (u x y) (v x y) +
          1 / (1 + y ^ 2) * partialYY z (u x y) (v x y)) :
    partialXX z (u x y) (v x y) + partialYY z (u x y) (v x y) = 0 := by
  rw [hZxx, hZyy, hZx, hZy] at hPDE
  have hx : 0 < 1 + x ^ 2 := by positivity
  have hy : 0 < 1 + y ^ 2 := by positivity
  have hsx : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 hx
  have hsy : 0 < Real.sqrt (1 + y ^ 2) := Real.sqrt_pos.2 hy
  calc
    partialXX z (u x y) (v x y) + partialYY z (u x y) (v x y) =
        (1 + x ^ 2) *
            (-(x / ((1 + x ^ 2) * Real.sqrt (1 + x ^ 2))) *
                partialX z (u x y) (v x y) +
              1 / (1 + x ^ 2) * partialXX z (u x y) (v x y)) +
          (1 + y ^ 2) *
            (-(y / ((1 + y ^ 2) * Real.sqrt (1 + y ^ 2))) *
                partialY z (u x y) (v x y) +
              1 / (1 + y ^ 2) * partialYY z (u x y) (v x y)) +
          x * (1 / Real.sqrt (1 + x ^ 2) *
            partialX z (u x y) (v x y)) +
          y * (1 / Real.sqrt (1 + y ^ 2) *
            partialY z (u x y) (v x y)) := by
              field_simp [hx.ne', hy.ne', hsx.ne', hsy.ne']
              ring
    _ = 0 := hPDE

end

end ProofGap.Exercise3490
