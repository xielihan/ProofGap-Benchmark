import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Sqrt

namespace ProofGap.Exercise3503_1

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun t => f t y) x
def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun t => f x t) y
def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := partialX (partialX f) x y
def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := partialY (partialY f) x y
def d1 (f : ℝ → ℝ) (r : ℝ) : ℝ := deriv f r
def d2 (f : ℝ → ℝ) (r : ℝ) : ℝ := deriv (deriv f) r

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

private theorem eventuallyEq_coordX
    {F G : ℝ × ℝ → ℝ} {x y : ℝ}
    (h : F =ᶠ[nhds (x, y)] G) :
    (fun t => F (t, y)) =ᶠ[nhds x] fun t => G (t, y) := by
  have hc : Filter.Tendsto (fun t : ℝ => (t, y))
      (nhds x) (nhds (x, y)) :=
    continuousAt_id.prodMk continuousAt_const
  simpa [Function.comp_def] using h.comp_tendsto hc

private theorem eventuallyEq_coordY
    {F G : ℝ × ℝ → ℝ} {x y : ℝ}
    (h : F =ᶠ[nhds (x, y)] G) :
    (fun t => F (x, t)) =ᶠ[nhds y] fun t => G (x, t) := by
  have hc : Filter.Tendsto (fun t : ℝ => (x, t))
      (nhds y) (nhds (x, y)) :=
    continuousAt_const.prodMk continuousAt_id
  simpa [Function.comp_def] using h.comp_tendsto hc

private theorem radius_sq
    (r : ℝ → ℝ → ℝ) (x y : ℝ) (hr : 0 < r x y)
    (hRadius : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      r p.1 p.2 = Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) :
    x ^ 2 + y ^ 2 = r x y ^ 2 := by
  have hp : r x y = Real.sqrt (x ^ 2 + y ^ 2) :=
    hRadius.self_of_nhds
  have hsqrtPos : 0 < Real.sqrt (x ^ 2 + y ^ 2) := by
    rw [← hp]
    exact hr
  have harg : 0 ≤ x ^ 2 + y ^ 2 :=
    le_of_lt (Real.sqrt_pos.mp hsqrtPos)
  calc
    x ^ 2 + y ^ 2 = Real.sqrt (x ^ 2 + y ^ 2) ^ 2 :=
      (Real.sq_sqrt harg).symm
    _ = r x y ^ 2 := by rw [hp]

private theorem hasDerivAt_radiusX
    (r : ℝ → ℝ → ℝ) (x y : ℝ) (hr : 0 < r x y)
    (hRadius : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      r p.1 p.2 = Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) :
    HasDerivAt (fun t => r t y) (x / r x y) x := by
  have hp : r x y = Real.sqrt (x ^ 2 + y ^ 2) :=
    hRadius.self_of_nhds
  have hsq := radius_sq r x y hr hRadius
  have harg : 0 < x ^ 2 + y ^ 2 := by
    rw [hsq]
    positivity
  have hinner :
      HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).add_const (y ^ 2) using 1 <;>
      simp [id] <;> ring
  have hsqrt0 :
      HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 + y ^ 2))
        (1 / (2 * Real.sqrt (x ^ 2 + y ^ 2)) * (2 * x)) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_sqrt (ne_of_gt harg)).comp x hinner
  have hsqrt :
      HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 + y ^ 2))
        (x / r x y) x := by
    apply hsqrt0.congr_deriv
    rw [← hp]
    field_simp [ne_of_gt hr]
  exact hsqrt.congr_of_eventuallyEq (eventuallyEq_coordX hRadius)

private theorem hasDerivAt_radiusY
    (r : ℝ → ℝ → ℝ) (x y : ℝ) (hr : 0 < r x y)
    (hRadius : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      r p.1 p.2 = Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) :
    HasDerivAt (fun t => r x t) (y / r x y) y := by
  have hp : r x y = Real.sqrt (x ^ 2 + y ^ 2) :=
    hRadius.self_of_nhds
  have hsq := radius_sq r x y hr hRadius
  have harg : 0 < x ^ 2 + y ^ 2 := by
    rw [hsq]
    positivity
  have hinner :
      HasDerivAt (fun t : ℝ => x ^ 2 + t ^ 2) (2 * y) y := by
    convert (hasDerivAt_const y (x ^ 2)).add ((hasDerivAt_id y).pow 2) using 1 <;>
      simp [id] <;> ring
  have hsqrt0 :
      HasDerivAt (fun t : ℝ => Real.sqrt (x ^ 2 + t ^ 2))
        (1 / (2 * Real.sqrt (x ^ 2 + y ^ 2)) * (2 * y)) y := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_sqrt (ne_of_gt harg)).comp y hinner
  have hsqrt :
      HasDerivAt (fun t : ℝ => Real.sqrt (x ^ 2 + t ^ 2))
        (y / r x y) y := by
    apply hsqrt0.congr_deriv
    rw [← hp]
    field_simp [ne_of_gt hr]
  exact hsqrt.congr_of_eventuallyEq (eventuallyEq_coordY hRadius)

theorem gap1 (r U : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (x y : ℝ)
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (x, y), U p.1 p.2 = f (r p.1 p.2))
    (hDifff : DifferentiableAt ℝ f (r x y))
    (hDiffr : DifferentiableAt ℝ (Function.uncurry r) (x, y)) :
    partialX U x y = d1 f (r x y) * partialX r x y := by
  have hlocal :
      (fun t : ℝ => U t y) =ᶠ[nhds x] fun t => f (r t y) := by
    simpa using eventuallyEq_coordX hCompose
  have hf : HasDerivAt f (d1 f (r x y)) (r x y) := by
    simpa [d1] using hDifff.hasDerivAt
  have hcomp := hf.comp x (hasDerivAt_partialX r x y hDiffr)
  calc
    partialX U x y = deriv (fun t => U t y) x := rfl
    _ = deriv (fun t => f (r t y)) x := hlocal.deriv_eq
    _ = d1 f (r x y) * partialX r x y := by
      simpa [Function.comp_def] using hcomp.deriv

theorem gap2 (r : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (x y : ℝ)
    (hr : 0 < r x y)
    (hRadius : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      r p.1 p.2 = Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) :
    d1 f (r x y) * partialX r x y =
      d1 f (r x y) * (x / r x y) := by
  rw [show partialX r x y = x / r x y by
    exact (hasDerivAt_radiusX r x y hr hRadius).deriv]

theorem gap3 (r U : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (x y : ℝ)
    (hChain : partialX U x y = d1 f (r x y) * partialX r x y)
    (hRadiusDerivative : d1 f (r x y) * partialX r x y =
      d1 f (r x y) * (x / r x y)) :
    partialX U x y = d1 f (r x y) * (x / r x y) := by
  exact hChain.trans hRadiusDerivative

theorem gap4 (r U : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (x y : ℝ)
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (x, y), U p.1 p.2 = f (r p.1 p.2))
    (hDifff : DifferentiableAt ℝ f (r x y))
    (hDiffr : DifferentiableAt ℝ (Function.uncurry r) (x, y)) :
    partialY U x y = d1 f (r x y) * partialY r x y := by
  have hlocal :
      (fun t : ℝ => U x t) =ᶠ[nhds y] fun t => f (r x t) := by
    simpa using eventuallyEq_coordY hCompose
  have hf : HasDerivAt f (d1 f (r x y)) (r x y) := by
    simpa [d1] using hDifff.hasDerivAt
  have hcomp := hf.comp y (hasDerivAt_partialY r x y hDiffr)
  calc
    partialY U x y = deriv (fun t => U x t) y := rfl
    _ = deriv (fun t => f (r x t)) y := hlocal.deriv_eq
    _ = d1 f (r x y) * partialY r x y := by
      simpa [Function.comp_def] using hcomp.deriv

theorem gap5 (r U : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (x y : ℝ)
    (hUx : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialX U p.1 p.2 = d1 f (r p.1 p.2) * (p.1 / r p.1 p.2)) :
    partialXX U x y =
      partialX (fun a b => d1 f (r a b) * (a / r a b)) x y := by
  simpa [partialXX, partialX] using
    (eventuallyEq_coordX hUx).deriv_eq

theorem gap6 (r : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (x y : ℝ)
    (hr : 0 < r x y)
    (hRadius : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      r p.1 p.2 = Real.sqrt (p.1 ^ 2 + p.2 ^ 2))
    (hC2f : ContDiffAt ℝ 2 f (r x y)) :
    partialX (fun a b => d1 f (r a b) * (a / r a b)) x y =
      x ^ 2 / r x y ^ 2 * d2 f (r x y) +
        y ^ 2 / r x y ^ 3 * d1 f (r x y) := by
  have hrx := hasDerivAt_radiusX r x y hr hRadius
  have hsq := radius_sq r x y hr hRadius
  have hdfDiff : DifferentiableAt ℝ (deriv f) (r x y) :=
    (hC2f.derivWithin (m := 1) (by norm_num)).differentiableAt
      (by decide)
  have hdf :
      HasDerivAt (fun ρ => d1 f ρ) (d2 f (r x y)) (r x y) := by
    simpa [d1, d2] using hdfDiff.hasDerivAt
  have hcomp :
      HasDerivAt (fun t => d1 f (r t y))
        (d2 f (r x y) * (x / r x y)) x := by
    simpa [Function.comp_def] using hdf.comp x hrx
  have hquotRaw :
      HasDerivAt (fun t => t / r t y)
        ((r x y - x * (x / r x y)) / r x y ^ 2) x := by
    simpa [id] using (hasDerivAt_id x).fun_div hrx (ne_of_gt hr)
  have hquotCoeff :
      (r x y - x * (x / r x y)) / r x y ^ 2 =
        y ^ 2 / r x y ^ 3 := by
    field_simp [ne_of_gt hr]
    nlinarith [hsq]
  have hquot :
      HasDerivAt (fun t => t / r t y) (y ^ 2 / r x y ^ 3) x :=
    hquotRaw.congr_deriv hquotCoeff
  have hprod :=
    hcomp.mul hquot
  have hprod' :
      HasDerivAt
        (fun t => d1 f (r t y) * (t / r t y))
        (x ^ 2 / r x y ^ 2 * d2 f (r x y) +
          y ^ 2 / r x y ^ 3 * d1 f (r x y)) x := by
    convert hprod using 1 <;>
      (try simp only [Pi.mul_apply]) <;> ring
  exact hprod'.deriv

theorem gap7 (r U : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (x y : ℝ)
    (hDifferentiate : partialXX U x y =
      partialX (fun a b => d1 f (r a b) * (a / r a b)) x y)
    (hExpanded : partialX (fun a b => d1 f (r a b) * (a / r a b)) x y =
      x ^ 2 / r x y ^ 2 * d2 f (r x y) +
        y ^ 2 / r x y ^ 3 * d1 f (r x y)) :
    partialXX U x y = x ^ 2 / r x y ^ 2 * d2 f (r x y) +
      y ^ 2 / r x y ^ 3 * d1 f (r x y) := by
  exact hDifferentiate.trans hExpanded

theorem gap8 (r U : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (x y : ℝ)
    (hr : 0 < r x y)
    (hRadius : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      r p.1 p.2 = Real.sqrt (p.1 ^ 2 + p.2 ^ 2))
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (x, y), U p.1 p.2 = f (r p.1 p.2))
    (hC2f : ContDiffAt ℝ 2 f (r x y)) :
    partialYY U x y = y ^ 2 / r x y ^ 2 * d2 f (r x y) +
      x ^ 2 / r x y ^ 3 * d1 f (r x y) := by
  have hsq := radius_sq r x y hr hRadius
  have harg : 0 < x ^ 2 + y ^ 2 := by
    rw [hsq]
    positivity
  have hinnerC2 :
      ContDiffAt ℝ 2 (fun t : ℝ => x ^ 2 + t ^ 2) y := by
    fun_prop
  have hsqrtC2 :
      ContDiffAt ℝ 2 (fun t : ℝ => Real.sqrt (x ^ 2 + t ^ 2)) y :=
    hinnerC2.sqrt (ne_of_gt harg)
  have hRadiusLine :
      (fun t : ℝ => r x t) =ᶠ[nhds y]
        (fun t : ℝ => Real.sqrt (x ^ 2 + t ^ 2)) :=
    eventuallyEq_coordY hRadius
  have hrC2 : ContDiffAt ℝ 2 (fun t : ℝ => r x t) y :=
    hsqrtC2.congr_of_eventuallyEq hRadiusLine
  have hpos : ∀ᶠ t in nhds y, 0 < r x t :=
    hrC2.continuousAt.eventually (eventually_gt_nhds hr)
  have hcoord :
      Filter.Tendsto (fun t : ℝ => (x, t))
        (nhds y) (nhds (x, y)) :=
    continuousAt_const.prodMk continuousAt_id
  have hRadiusEq :
      (fun p : ℝ × ℝ => r p.1 p.2) =ᶠ[nhds (x, y)]
        (fun p : ℝ × ℝ =>
          Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) :=
    hRadius
  have hRadiusNear :
      ∀ᶠ t in nhds y,
        (fun p : ℝ × ℝ => r p.1 p.2) =ᶠ[nhds (x, t)]
          (fun p : ℝ × ℝ =>
            Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) :=
    hcoord.eventually hRadiusEq.eventuallyEq_nhds
  have hderivRadius :
      (fun t => deriv (fun s => r x s) t) =ᶠ[nhds y]
        (fun t => t / r x t) := by
    filter_upwards [hpos, hRadiusNear] with t ht hRt
    exact (hasDerivAt_radiusY r x t ht hRt).deriv
  have hry := hasDerivAt_radiusY r x y hr hRadius
  have hquotRaw :
      HasDerivAt (fun t => t / r x t)
        ((r x y - y * (y / r x y)) / r x y ^ 2) y := by
    simpa [id] using (hasDerivAt_id y).fun_div hry (ne_of_gt hr)
  have hquotCoeff :
      (r x y - y * (y / r x y)) / r x y ^ 2 =
        x ^ 2 / r x y ^ 3 := by
    field_simp [ne_of_gt hr]
    nlinarith [hsq]
  have hquot :
      HasDerivAt (fun t => t / r x t)
        (x ^ 2 / r x y ^ 3) y :=
    hquotRaw.congr_deriv hquotCoeff
  have hRadiusSecond :
      iteratedDeriv 2 (fun t : ℝ => r x t) y =
        x ^ 2 / r x y ^ 3 := by
    calc
      iteratedDeriv 2 (fun t : ℝ => r x t) y =
          deriv (deriv (fun t : ℝ => r x t)) y := by
            simp [iteratedDeriv_succ, iteratedDeriv_zero]
      _ = deriv (fun t => t / r x t) y :=
        hderivRadius.deriv_eq
      _ = x ^ 2 / r x y ^ 3 := hquot.deriv
  have hComposeLine :
      (fun t : ℝ => U x t) =ᶠ[nhds y]
        (fun t : ℝ => f (r x t)) :=
    eventuallyEq_coordY hCompose
  have hUSecond :
      partialYY U x y =
        iteratedDeriv 2 (f ∘ fun t : ℝ => r x t) y := by
    calc
      partialYY U x y =
          deriv (deriv (fun t : ℝ => U x t)) y := rfl
      _ = deriv (deriv (fun t : ℝ => f (r x t))) y :=
        hComposeLine.deriv.deriv_eq
      _ = iteratedDeriv 2 (f ∘ fun t : ℝ => r x t) y := by
        simp [iteratedDeriv_succ, iteratedDeriv_zero, Function.comp_def]
  have hchain :=
    iteratedDeriv_comp_two (g := f) (f := fun t : ℝ => r x t)
      hC2f hrC2
  rw [hUSecond, hchain, hry.deriv, hRadiusSecond]
  simp [d1, d2, iteratedDeriv_succ, iteratedDeriv_zero]
  ring

theorem gap9 (r U : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (x y : ℝ)
    (hr : 0 < r x y)
    (hRadiusSq : x ^ 2 + y ^ 2 = r x y ^ 2)
    (hUxx : partialXX U x y = x ^ 2 / r x y ^ 2 * d2 f (r x y) +
      y ^ 2 / r x y ^ 3 * d1 f (r x y))
    (hUyy : partialYY U x y = y ^ 2 / r x y ^ 2 * d2 f (r x y) +
      x ^ 2 / r x y ^ 3 * d1 f (r x y)) :
    partialXX U x y + partialYY U x y =
      d2 f (r x y) + 1 / r x y * d1 f (r x y) := by
  rw [hUxx, hUyy]
  calc
    x ^ 2 / r x y ^ 2 * d2 f (r x y) +
          y ^ 2 / r x y ^ 3 * d1 f (r x y) +
        (y ^ 2 / r x y ^ 2 * d2 f (r x y) +
          x ^ 2 / r x y ^ 3 * d1 f (r x y)) =
      (x ^ 2 + y ^ 2) / r x y ^ 2 * d2 f (r x y) +
        (x ^ 2 + y ^ 2) / r x y ^ 3 * d1 f (r x y) := by
      ring
    _ = r x y ^ 2 / r x y ^ 2 * d2 f (r x y) +
        r x y ^ 2 / r x y ^ 3 * d1 f (r x y) := by
      rw [hRadiusSq]
    _ = d2 f (r x y) + 1 / r x y * d1 f (r x y) := by
      field_simp [ne_of_gt hr]

theorem gap10 (r U : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (x y : ℝ)
    (hPhysicalPDE : partialXX U x y + partialYY U x y = 0)
    (hRadialFormula : partialXX U x y + partialYY U x y =
      d2 f (r x y) + 1 / r x y * d1 f (r x y)) :
    d2 f (r x y) + 1 / r x y * d1 f (r x y) = 0 := by
  exact hRadialFormula.symm.trans hPhysicalPDE

theorem gap11 (r U : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (x y : ℝ)
    (hFormula : partialXX U x y + partialYY U x y =
      d2 f (r x y) + 1 / r x y * d1 f (r x y))
    (hODE : d2 f (r x y) + 1 / r x y * d1 f (r x y) = 0) :
    partialXX U x y + partialYY U x y = 0 := by
  exact hFormula.trans hODE

theorem gap12 (r U : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (x y : ℝ)
    (hr : r x y ≠ 0)
    (hDiffDf : DifferentiableAt ℝ (deriv f) (r x y))
    (hRadialFormula : partialXX U x y + partialYY U x y =
      d2 f (r x y) + 1 / r x y * d1 f (r x y)) :
    partialXX U x y + partialYY U x y =
      1 / r x y * d1 (fun ρ => ρ * d1 f ρ) (r x y) := by
  have hprod :
      HasDerivAt (fun ρ => ρ * d1 f ρ)
        (d1 f (r x y) + r x y * d2 f (r x y)) (r x y) := by
    convert (hasDerivAt_id (r x y)).mul hDiffDf.hasDerivAt using 1 <;>
      simp [d1, d2, id] <;> ring
  have hd :
      d1 (fun ρ => ρ * d1 f ρ) (r x y) =
        d1 f (r x y) + r x y * d2 f (r x y) := by
    exact hprod.deriv
  calc
    partialXX U x y + partialYY U x y =
        d2 f (r x y) + 1 / r x y * d1 f (r x y) :=
      hRadialFormula
    _ = 1 / r x y * d1 (fun ρ => ρ * d1 f ρ) (r x y) := by
      rw [hd]
      field_simp [hr]
      ring

theorem gap13 (r U : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (x y : ℝ)
    (hPhysicalPDE : partialXX U x y + partialYY U x y = 0)
    (hDivergenceForm : partialXX U x y + partialYY U x y =
      1 / r x y * d1 (fun ρ => ρ * d1 f ρ) (r x y)) :
    1 / r x y * d1 (fun ρ => ρ * d1 f ρ) (r x y) = 0 := by
  exact hDivergenceForm.symm.trans hPhysicalPDE

theorem gap14 (r U : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (x y : ℝ)
    (hDivergenceForm : partialXX U x y + partialYY U x y =
      1 / r x y * d1 (fun ρ => ρ * d1 f ρ) (r x y))
    (hZero : 1 / r x y * d1 (fun ρ => ρ * d1 f ρ) (r x y) = 0) :
    partialXX U x y + partialYY U x y = 0 := by
  exact hDivergenceForm.trans hZero

end

end ProofGap.Exercise3503_1
