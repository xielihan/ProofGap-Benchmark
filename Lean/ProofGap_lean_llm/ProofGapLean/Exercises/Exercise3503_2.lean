import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3503_2

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun t => f t y) x
def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun t => f x t) y
def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := partialX (partialX f) x y
def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := partialY (partialY f) x y
def laplacian (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := partialXX f x y + partialYY f x y
def d1 (f : ℝ → ℝ) (r : ℝ) : ℝ := deriv f r
def d2 (f : ℝ → ℝ) (r : ℝ) : ℝ := deriv (deriv f) r
def d3 (f : ℝ → ℝ) (r : ℝ) : ℝ := deriv (deriv (deriv f)) r
def d4 (f : ℝ → ℝ) (r : ℝ) : ℝ := deriv (deriv (deriv (deriv f))) r

def radialLaplacian (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  d2 f r + 1 / r * d1 f r

def radialBilaplacian (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  d4 f r + 2 / r * d3 f r - 1 / r ^ 2 * d2 f r + 1 / r ^ 3 * d1 f r

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

private theorem eventuallyEq_laplacian
    {F G : ℝ → ℝ → ℝ} {x y : ℝ}
    (h : Function.uncurry F =ᶠ[nhds (x, y)] Function.uncurry G) :
    (fun p : ℝ × ℝ => laplacian F p.1 p.2) =ᶠ[nhds (x, y)]
      fun p => laplacian G p.1 p.2 := by
  filter_upwards [h.eventuallyEq_nhds] with p hp
  have hx := eventuallyEq_coordX hp
  have hy := eventuallyEq_coordY hp
  have hxx : partialXX F p.1 p.2 = partialXX G p.1 p.2 := by
    exact hx.deriv.deriv_eq
  have hyy : partialYY F p.1 p.2 = partialYY G p.1 p.2 := by
    exact hy.deriv.deriv_eq
  simp only [laplacian]
  rw [hxx, hyy]

private theorem hasDerivAt_radiusX (x y : ℝ)
    (hR : 0 < Real.sqrt (x ^ 2 + y ^ 2)) :
    HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 + y ^ 2))
      (x / Real.sqrt (x ^ 2 + y ^ 2)) x := by
  have hq : 0 < x ^ 2 + y ^ 2 := Real.sqrt_pos.mp hR
  have hinner : HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * x) x := by
    convert (hasDerivAt_pow 2 x).add_const (y ^ 2) using 1 <;>
      norm_num <;> ring
  have hs := (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x hinner
  convert hs using 1 <;>
    simp <;> field_simp [ne_of_gt hR] <;> ring

private theorem hasDerivAt_radiusY (x y : ℝ)
    (hR : 0 < Real.sqrt (x ^ 2 + y ^ 2)) :
    HasDerivAt (fun t : ℝ => Real.sqrt (x ^ 2 + t ^ 2))
      (y / Real.sqrt (x ^ 2 + y ^ 2)) y := by
  have hq : 0 < x ^ 2 + y ^ 2 := Real.sqrt_pos.mp hR
  have hinner : HasDerivAt (fun t : ℝ => x ^ 2 + t ^ 2) (2 * y) y := by
    convert (hasDerivAt_const y (x ^ 2)).add (hasDerivAt_pow 2 y) using 1 <;>
      norm_num <;> ring
  have hs := (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp y hinner
  convert hs using 1 <;>
    simp <;> field_simp [ne_of_gt hR] <;> ring

private theorem radialX_first (f : ℝ → ℝ) (x y : ℝ)
    (hR : 0 < Real.sqrt (x ^ 2 + y ^ 2))
    (hf : ContDiffAt ℝ 2 f (Real.sqrt (x ^ 2 + y ^ 2))) :
    deriv (fun t => f (Real.sqrt (t ^ 2 + y ^ 2))) x =
      d1 f (Real.sqrt (x ^ 2 + y ^ 2)) *
        (x / Real.sqrt (x ^ 2 + y ^ 2)) := by
  have hf' : HasDerivAt f (d1 f (Real.sqrt (x ^ 2 + y ^ 2)))
      (Real.sqrt (x ^ 2 + y ^ 2)) := by
    simpa [d1] using (hf.differentiableAt (by decide)).hasDerivAt
  exact (hf'.comp x (hasDerivAt_radiusX x y hR)).deriv

private theorem radialY_first (f : ℝ → ℝ) (x y : ℝ)
    (hR : 0 < Real.sqrt (x ^ 2 + y ^ 2))
    (hf : ContDiffAt ℝ 2 f (Real.sqrt (x ^ 2 + y ^ 2))) :
    deriv (fun t => f (Real.sqrt (x ^ 2 + t ^ 2))) y =
      d1 f (Real.sqrt (x ^ 2 + y ^ 2)) *
        (y / Real.sqrt (x ^ 2 + y ^ 2)) := by
  have hf' : HasDerivAt f (d1 f (Real.sqrt (x ^ 2 + y ^ 2)))
      (Real.sqrt (x ^ 2 + y ^ 2)) := by
    simpa [d1] using (hf.differentiableAt (by decide)).hasDerivAt
  exact (hf'.comp y (hasDerivAt_radiusY x y hR)).deriv

private theorem radialX_second (f : ℝ → ℝ) (x y : ℝ)
    (hR : 0 < Real.sqrt (x ^ 2 + y ^ 2))
    (hf : ContDiffAt ℝ 2 f (Real.sqrt (x ^ 2 + y ^ 2))) :
    deriv (fun t => deriv (fun s => f (Real.sqrt (s ^ 2 + y ^ 2))) t) x =
      d2 f (Real.sqrt (x ^ 2 + y ^ 2)) *
          (x / Real.sqrt (x ^ 2 + y ^ 2)) ^ 2 +
        d1 f (Real.sqrt (x ^ 2 + y ^ 2)) *
          (1 / Real.sqrt (x ^ 2 + y ^ 2) -
            x ^ 2 / Real.sqrt (x ^ 2 + y ^ 2) ^ 3) := by
  let R : ℝ → ℝ := fun t => Real.sqrt (t ^ 2 + y ^ 2)
  have hRX := hasDerivAt_radiusX x y hR
  have hratio : HasDerivAt (fun t => t / R t)
      (1 / R x - x ^ 2 / R x ^ 3) x := by
    have h := (hasDerivAt_id x).div hRX (ne_of_gt hR)
    convert h using 1 <;>
      dsimp [R] <;> field_simp [ne_of_gt hR] <;> ring
  have hc1 : ContDiffAt ℝ 1 (deriv f) (R x) :=
    hf.derivWithin (by norm_num)
  have hd1 : HasDerivAt (d1 f) (d2 f (R x)) (R x) := by
    change HasDerivAt (deriv f) (deriv (deriv f) (R x)) (R x)
    exact (hc1.differentiableAt (by decide)).hasDerivAt
  have hcomp : HasDerivAt (fun t => d1 f (R t))
      (d2 f (R x) * (x / R x)) x := by
    exact hd1.comp x hRX
  have hG := hcomp.mul hratio
  have heq :
      (fun t => deriv (fun s => f (Real.sqrt (s ^ 2 + y ^ 2))) t) =ᶠ[nhds x]
        fun t => d1 f (R t) * (t / R t) := by
    have htend : Filter.Tendsto R (nhds x) (nhds (R x)) := hRX.continuousAt
    filter_upwards [htend.eventually (hf.eventually (by norm_num)),
      hRX.continuousAt.eventually (Ioi_mem_nhds hR)] with t htC htR
    simpa [R] using radialX_first f t y htR htC
  calc
    deriv (fun t => deriv (fun s => f (Real.sqrt (s ^ 2 + y ^ 2))) t) x =
        deriv (fun t => d1 f (R t) * (t / R t)) x := heq.deriv_eq
    _ = d2 f (R x) * (x / R x) ^ 2 +
        d1 f (R x) * (1 / R x - x ^ 2 / R x ^ 3) := by
      have hd := hG.deriv
      change deriv (fun t => d1 f (R t) * (t / R t)) x =
        d2 f (R x) * (x / R x) * (x / R x) +
          d1 f (R x) * (1 / R x - x ^ 2 / R x ^ 3) at hd
      rw [hd]
      ring

private theorem radialY_second (f : ℝ → ℝ) (x y : ℝ)
    (hR : 0 < Real.sqrt (x ^ 2 + y ^ 2))
    (hf : ContDiffAt ℝ 2 f (Real.sqrt (x ^ 2 + y ^ 2))) :
    deriv (fun t => deriv (fun s => f (Real.sqrt (x ^ 2 + s ^ 2))) t) y =
      d2 f (Real.sqrt (x ^ 2 + y ^ 2)) *
          (y / Real.sqrt (x ^ 2 + y ^ 2)) ^ 2 +
        d1 f (Real.sqrt (x ^ 2 + y ^ 2)) *
          (1 / Real.sqrt (x ^ 2 + y ^ 2) -
            y ^ 2 / Real.sqrt (x ^ 2 + y ^ 2) ^ 3) := by
  let R : ℝ → ℝ := fun t => Real.sqrt (x ^ 2 + t ^ 2)
  have hRY := hasDerivAt_radiusY x y hR
  have hratio : HasDerivAt (fun t => t / R t)
      (1 / R y - y ^ 2 / R y ^ 3) y := by
    have h := (hasDerivAt_id y).div hRY (ne_of_gt hR)
    convert h using 1 <;>
      dsimp [R] <;> field_simp [ne_of_gt hR] <;> ring
  have hc1 : ContDiffAt ℝ 1 (deriv f) (R y) :=
    hf.derivWithin (by norm_num)
  have hd1 : HasDerivAt (d1 f) (d2 f (R y)) (R y) := by
    change HasDerivAt (deriv f) (deriv (deriv f) (R y)) (R y)
    exact (hc1.differentiableAt (by decide)).hasDerivAt
  have hcomp : HasDerivAt (fun t => d1 f (R t))
      (d2 f (R y) * (y / R y)) y := by
    exact hd1.comp y hRY
  have hG := hcomp.mul hratio
  have heq :
      (fun t => deriv (fun s => f (Real.sqrt (x ^ 2 + s ^ 2))) t) =ᶠ[nhds y]
        fun t => d1 f (R t) * (t / R t) := by
    have htend : Filter.Tendsto R (nhds y) (nhds (R y)) := hRY.continuousAt
    filter_upwards [htend.eventually (hf.eventually (by norm_num)),
      hRY.continuousAt.eventually (Ioi_mem_nhds hR)] with t htC htR
    simpa [R] using radialY_first f x t htR htC
  calc
    deriv (fun t => deriv (fun s => f (Real.sqrt (x ^ 2 + s ^ 2))) t) y =
        deriv (fun t => d1 f (R t) * (t / R t)) y := heq.deriv_eq
    _ = d2 f (R y) * (y / R y) ^ 2 +
        d1 f (R y) * (1 / R y - y ^ 2 / R y ^ 3) := by
      have hd := hG.deriv
      change deriv (fun t => d1 f (R t) * (t / R t)) y =
        d2 f (R y) * (y / R y) * (y / R y) +
          d1 f (R y) * (1 / R y - y ^ 2 / R y ^ 3) at hd
      rw [hd]
      ring

private theorem laplacian_radial_comp (f : ℝ → ℝ) (x y : ℝ)
    (hR : 0 < Real.sqrt (x ^ 2 + y ^ 2))
    (hf : ContDiffAt ℝ 2 f (Real.sqrt (x ^ 2 + y ^ 2))) :
    laplacian (fun a b => f (Real.sqrt (a ^ 2 + b ^ 2))) x y =
      radialLaplacian f (Real.sqrt (x ^ 2 + y ^ 2)) := by
  have hq : 0 < x ^ 2 + y ^ 2 := Real.sqrt_pos.mp hR
  have hsqrt :
      Real.sqrt (x ^ 2 + y ^ 2) ^ 2 = x ^ 2 + y ^ 2 := by
    rw [Real.sq_sqrt (le_of_lt hq)]
  unfold laplacian
  rw [show partialXX (fun a b => f (Real.sqrt (a ^ 2 + b ^ 2))) x y =
      d2 f (Real.sqrt (x ^ 2 + y ^ 2)) *
          (x / Real.sqrt (x ^ 2 + y ^ 2)) ^ 2 +
        d1 f (Real.sqrt (x ^ 2 + y ^ 2)) *
          (1 / Real.sqrt (x ^ 2 + y ^ 2) -
            x ^ 2 / Real.sqrt (x ^ 2 + y ^ 2) ^ 3) by
      exact radialX_second f x y hR hf]
  rw [show partialYY (fun a b => f (Real.sqrt (a ^ 2 + b ^ 2))) x y =
      d2 f (Real.sqrt (x ^ 2 + y ^ 2)) *
          (y / Real.sqrt (x ^ 2 + y ^ 2)) ^ 2 +
        d1 f (Real.sqrt (x ^ 2 + y ^ 2)) *
          (1 / Real.sqrt (x ^ 2 + y ^ 2) -
            y ^ 2 / Real.sqrt (x ^ 2 + y ^ 2) ^ 3) by
      exact radialY_second f x y hR hf]
  unfold radialLaplacian
  field_simp [ne_of_gt hR]
  rw [hsqrt]
  ring

private theorem contDiffAt_radialLaplacian (f : ℝ → ℝ) (r : ℝ)
    (hr : r ≠ 0) (hf : ContDiffAt ℝ 4 f r) :
    ContDiffAt ℝ 2 (radialLaplacian f) r := by
  have hc1 : ContDiffAt ℝ 3 (deriv f) r :=
    hf.derivWithin (by norm_num)
  have hc2 : ContDiffAt ℝ 2 (deriv (deriv f)) r :=
    hc1.derivWithin (by norm_num)
  have hinv : ContDiffAt ℝ 2 (fun t : ℝ => 1 / t) r := by
    simpa [one_div] using (contDiffAt_id.inv hr : ContDiffAt ℝ 2 (fun t : ℝ => t⁻¹) r)
  change ContDiffAt ℝ 2
    (fun t => deriv (deriv f) t + (1 / t) * deriv f t) r
  simpa [one_div] using hc2.add (hinv.mul (hc1.of_le (by norm_num)))

private theorem radialLaplacian_eq_div_d1 (g : ℝ → ℝ) (r : ℝ)
    (hr : r ≠ 0) (hg : ContDiffAt ℝ 2 g r) :
    radialLaplacian g r =
      1 / r * d1 (fun ρ => ρ * d1 g ρ) r := by
  have hc1 : ContDiffAt ℝ 1 (deriv g) r :=
    hg.derivWithin (by norm_num)
  have hd : HasDerivAt (d1 g) (d2 g r) r := by
    change HasDerivAt (deriv g) (deriv (deriv g) r) r
    exact (hc1.differentiableAt (by decide)).hasDerivAt
  have hmul := (hasDerivAt_id r).mul hd
  rw [show d1 (fun ρ => ρ * d1 g ρ) r = d1 g r + r * d2 g r by
    simpa [d1, id_eq] using hmul.deriv]
  unfold radialLaplacian
  field_simp [hr]
  ring

private theorem derivative_tower (f : ℝ → ℝ) (r : ℝ)
    (hf : ContDiffAt ℝ 4 f r) :
    HasDerivAt f (d1 f r) r ∧
      HasDerivAt (d1 f) (d2 f r) r ∧
      HasDerivAt (d2 f) (d3 f r) r ∧
      HasDerivAt (d3 f) (d4 f r) r := by
  have hf0 := hf.differentiableAt (by decide)
  have hc1 : ContDiffAt ℝ 3 (deriv f) r :=
    hf.derivWithin (by norm_num)
  have hc2 : ContDiffAt ℝ 2 (deriv (deriv f)) r :=
    hc1.derivWithin (by norm_num)
  have hc3 : ContDiffAt ℝ 1 (deriv (deriv (deriv f))) r :=
    hc2.derivWithin (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [d1] using hf0.hasDerivAt
  · change HasDerivAt (deriv f) (deriv (deriv f) r) r
    exact (hc1.differentiableAt (by decide)).hasDerivAt
  · change HasDerivAt (deriv (deriv f))
      (deriv (deriv (deriv f)) r) r
    exact (hc2.differentiableAt (by decide)).hasDerivAt
  · change HasDerivAt (deriv (deriv (deriv f)))
      (deriv (deriv (deriv (deriv f))) r) r
    exact (hc3.differentiableAt (by decide)).hasDerivAt

private theorem hasDerivAt_inv_id (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun ρ : ℝ => 1 / ρ) (-1 / r ^ 2) r := by
  convert (hasDerivAt_const r 1).div (hasDerivAt_id r) hr using 1 <;>
    simp [id_eq] <;> field_simp [hr] <;> ring

private theorem radialLaplacian_d1_formula (f : ℝ → ℝ) (r : ℝ)
    (hr : r ≠ 0) (hf : ContDiffAt ℝ 4 f r) :
    d1 (radialLaplacian f) r =
      d3 f r - 1 / r ^ 2 * d1 f r + 1 / r * d2 f r := by
  rcases derivative_tower f r hf with ⟨hf0, hf1, hf2, hf3⟩
  have hi := hasDerivAt_inv_id r hr
  have h :
      HasDerivAt (radialLaplacian f)
        (d3 f r + ((-1 / r ^ 2) * d1 f r + (1 / r) * d2 f r)) r := by
    dsimp [radialLaplacian]
    exact hf2.add (hi.mul hf1)
  calc
    d1 (radialLaplacian f) r =
        d3 f r + ((-1 / r ^ 2) * d1 f r + (1 / r) * d2 f r) := by
      simpa [d1] using h.deriv
    _ = d3 f r - 1 / r ^ 2 * d1 f r + 1 / r * d2 f r := by
      ring

private theorem hasDerivAt_neg_inv_sq (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun ρ : ℝ => -1 / ρ ^ 2) (2 / r ^ 3) r := by
  have h := (hasDerivAt_const r (-1)).div (hasDerivAt_pow 2 r)
    (pow_ne_zero 2 hr)
  convert h using 1 <;>
    simp [id_eq] <;> field_simp [hr] <;> ring

private theorem hasDerivAt_radialLaplacian_d1 (f : ℝ → ℝ) (r : ℝ)
    (hr : r ≠ 0) (hf : ContDiffAt ℝ 4 f r) :
    HasDerivAt (fun ρ => d1 (radialLaplacian f) ρ)
      (d4 f r + 2 / r ^ 3 * d1 f r -
        2 / r ^ 2 * d2 f r + 1 / r * d3 f r) r := by
  rcases derivative_tower f r hf with ⟨hf0, hf1, hf2, hf3⟩
  have hi := hasDerivAt_inv_id r hr
  have hisq := hasDerivAt_neg_inv_sq r hr
  let G : ℝ → ℝ := fun ρ =>
    d3 f ρ + (-1 / ρ ^ 2) * d1 f ρ + (1 / ρ) * d2 f ρ
  have hG : HasDerivAt G
      (d4 f r + (2 / r ^ 3 * d1 f r + (-1 / r ^ 2) * d2 f r) +
        ((-1 / r ^ 2) * d2 f r + (1 / r) * d3 f r)) r := by
    dsimp [G]
    exact (hf3.add (hisq.mul hf1)).add (hi.mul hf2)
  have heq :
      (fun ρ => d1 (radialLaplacian f) ρ) =ᶠ[nhds r] G := by
    filter_upwards [hf.eventually (by norm_num), eventually_ne_nhds hr] with ρ hρC hρ
    dsimp [G]
    rw [radialLaplacian_d1_formula f ρ hρ hρC]
    ring
  convert hG.congr_of_eventuallyEq heq using 1 <;> ring

theorem gap1 (r U : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (x y : ℝ)
    (hr : 0 < r x y)
    (hRadius : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      r p.1 p.2 = Real.sqrt (p.1 ^ 2 + p.2 ^ 2))
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (x, y), U p.1 p.2 = f (r p.1 p.2))
    (hC4f : ContDiffAt ℝ 4 f (r x y)) :
    laplacian (fun a b => laplacian U a b) x y =
      1 / r x y *
        d1 (fun ρ => ρ * d1 (radialLaplacian f) ρ) (r x y) := by
  let R : ℝ × ℝ → ℝ := fun p => Real.sqrt (p.1 ^ 2 + p.2 ^ 2)
  let E : ℝ → ℝ → ℝ := fun a b => f (Real.sqrt (a ^ 2 + b ^ 2))
  have hRval : r x y = R (x, y) := by
    simpa [R] using hRadius.self_of_nhds
  have hRpos : 0 < R (x, y) := by simpa [← hRval] using hr
  have hC4R : ContDiffAt ℝ 4 f (R (x, y)) := by
    simpa [← hRval] using hC4f
  have hRtend : Filter.Tendsto R (nhds (x, y)) (nhds (R (x, y))) := by
    have hc : ContinuousAt R (x, y) := by
      dsimp [R]
      fun_prop
    exact hc
  have hUE :
      Function.uncurry U =ᶠ[nhds (x, y)] Function.uncurry E := by
    filter_upwards [hCompose, hRadius] with p hpU hpR
    simp only [Function.uncurry]
    rw [hpU, hpR]
  have hLapUE := eventuallyEq_laplacian hUE
  have hLapFormula :
      (fun p : ℝ × ℝ => laplacian E p.1 p.2) =ᶠ[nhds (x, y)]
        fun p => radialLaplacian f (R p) := by
    filter_upwards [
      hRtend.eventually (hC4R.eventually (by norm_num)),
      hRtend.eventually (Ioi_mem_nhds hRpos)] with p hpC hpR
    simpa [E, R] using
      laplacian_radial_comp f p.1 p.2 hpR (hpC.of_le (by norm_num))
  have hLapU :
      (fun p : ℝ × ℝ => laplacian U p.1 p.2) =ᶠ[nhds (x, y)]
        fun p => radialLaplacian f (R p) :=
    hLapUE.trans hLapFormula
  have hOuter := eventuallyEq_laplacian
    (F := fun a b => laplacian U a b)
    (G := fun a b => radialLaplacian f (Real.sqrt (a ^ 2 + b ^ 2)))
    (by simpa [R, Function.uncurry] using hLapU)
  have hOuterAt :
      laplacian (fun a b => laplacian U a b) x y =
        laplacian (fun a b => radialLaplacian f
          (Real.sqrt (a ^ 2 + b ^ 2))) x y := by
    simpa using hOuter.self_of_nhds
  let g := radialLaplacian f
  have hg : ContDiffAt ℝ 2 g (R (x, y)) := by
    exact contDiffAt_radialLaplacian f (R (x, y)) (ne_of_gt hRpos) hC4R
  rw [hOuterAt]
  rw [show laplacian (fun a b => radialLaplacian f
      (Real.sqrt (a ^ 2 + b ^ 2))) x y =
        radialLaplacian g (R (x, y)) by
      simpa [g, R] using
        laplacian_radial_comp g x y hRpos hg]
  rw [radialLaplacian_eq_div_d1 g (R (x, y)) (ne_of_gt hRpos) hg]
  simpa [g, hRval]

theorem gap2 (f : ℝ → ℝ) (r : ℝ)
    (hr : r ≠ 0)
    (hC4f : ContDiffAt ℝ 4 f r) :
    1 / r * d1 (fun ρ => ρ * d1 (radialLaplacian f) ρ) r =
      radialBilaplacian f r := by
  have hD := hasDerivAt_radialLaplacian_d1 f r hr hC4f
  have hmul := (hasDerivAt_id r).mul hD
  rw [show d1 (fun ρ => ρ * d1 (radialLaplacian f) ρ) r =
      d1 (radialLaplacian f) r + r *
        (d4 f r + 2 / r ^ 3 * d1 f r -
          2 / r ^ 2 * d2 f r + 1 / r * d3 f r) by
      simpa [d1, id_eq] using hmul.deriv]
  rw [radialLaplacian_d1_formula f r hr hC4f]
  unfold radialBilaplacian
  field_simp [hr]
  ring

theorem gap3 (r U : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (x y : ℝ)
    (hBiharmonic : laplacian (fun a b => laplacian U a b) x y = 0)
    (hFormula : laplacian (fun a b => laplacian U a b) x y =
      radialBilaplacian f (r x y)) :
    radialBilaplacian f (r x y) = 0 := by
  rw [← hFormula]
  exact hBiharmonic

theorem gap4 (r : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (x y : ℝ)
    (hExpanded :
      1 / r x y * d1 (fun ρ => ρ * d1 (radialLaplacian f) ρ) (r x y) =
        radialBilaplacian f (r x y))
    (hZero : radialBilaplacian f (r x y) = 0) :
    1 / r x y * d1 (fun ρ => ρ * d1 (radialLaplacian f) ρ) (r x y) = 0 := by
  rw [hExpanded, hZero]

end

end ProofGap.Exercise3503_2
