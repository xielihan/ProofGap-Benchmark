import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3408

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) := deriv (fun t => f t y) x
def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) := deriv (fun t => f x t) y
def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) := deriv (fun t => partialX f t y) x

def cot (a : ℝ) := Real.cos a / Real.sin a
def parametricZx (a b : ℝ) := -cot a * Real.cos b
def parametricZxPhi (a b : ℝ) := Real.cos b / (Real.sin a) ^ 2
def parametricZxPsi (a b : ℝ) := cot a * Real.sin b

def firstSecondForm (a b : ℝ) :=
  -(Real.cos b ^ 2 + Real.sin b ^ 2 * Real.sin a ^ 2) / Real.sin a ^ 3

def finalSecondForm (a b : ℝ) :=
  -(Real.sin a ^ 2 + Real.cos a ^ 2 * Real.cos b ^ 2) / Real.sin a ^ 3

private theorem differentiableAt_fst_slice
    (f : ℝ → ℝ → ℝ) (x y : ℝ)
    (h : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    DifferentiableAt ℝ (fun t => f t y) x := by
  have hid : DifferentiableAt ℝ (fun t : ℝ => t) x := differentiableAt_id
  have hc : DifferentiableAt ℝ (fun _ : ℝ => y) x :=
    differentiableAt_const (x := x) y
  have hg : DifferentiableAt ℝ (fun t : ℝ => (t, y)) x :=
    DifferentiableAt.prodMk hid hc
  simpa [Function.uncurry] using h.comp x hg

private theorem eventually_fst_slice
    (x y : ℝ) {P : ℝ × ℝ → Prop}
    (h : ∀ᶠ p : ℝ × ℝ in nhds (x, y), P p) :
    ∀ᶠ t : ℝ in nhds x, P (t, y) := by
  have hid : DifferentiableAt ℝ (fun t : ℝ => t) x := differentiableAt_id
  have hc : DifferentiableAt ℝ (fun _ : ℝ => y) x :=
    differentiableAt_const (x := x) y
  have hg : DifferentiableAt ℝ (fun t : ℝ => (t, y)) x :=
    DifferentiableAt.prodMk hid hc
  exact hg.continuousAt.tendsto.eventually h

theorem gap1 (φ ψ : ℝ → ℝ → ℝ) (x y : ℝ)
    (hφDiff : DifferentiableAt ℝ (Function.uncurry φ) (x, y))
    (hψDiff : DifferentiableAt ℝ (Function.uncurry ψ) (x, y))
    (hX : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      p.1 = Real.cos (φ p.1 p.2) * Real.cos (ψ p.1 p.2)) :
    1 = -Real.sin (φ x y) * Real.cos (ψ x y) * partialX φ x y -
      Real.cos (φ x y) * Real.sin (ψ x y) * partialX ψ x y := by
  have hφx := differentiableAt_fst_slice φ x y hφDiff
  have hψx := differentiableAt_fst_slice ψ x y hψDiff
  have hφderiv : HasDerivAt (fun t => φ t y) (partialX φ x y) x := by
    simpa [partialX] using hφx.hasDerivAt
  have hψderiv : HasDerivAt (fun t => ψ t y) (partialX ψ x y) x := by
    simpa [partialX] using hψx.hasDerivAt
  have hcosφ : HasDerivAt (fun t => Real.cos (φ t y))
      (-Real.sin (φ x y) * partialX φ x y) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_cos (φ x y)).comp x hφderiv
  have hcosψ : HasDerivAt (fun t => Real.cos (ψ t y))
      (-Real.sin (ψ x y) * partialX ψ x y) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_cos (ψ x y)).comp x hψderiv
  have hrhs : HasDerivAt
      (fun t => Real.cos (φ t y) * Real.cos (ψ t y))
      (-Real.sin (φ x y) * Real.cos (ψ x y) * partialX φ x y -
        Real.cos (φ x y) * Real.sin (ψ x y) * partialX ψ x y) x := by
    convert hcosφ.mul hcosψ using 1 <;> ring
  have hX' : (fun t : ℝ => t) =ᶠ[nhds x]
      (fun t => Real.cos (φ t y) * Real.cos (ψ t y)) := by
    simpa using eventually_fst_slice x y hX
  calc
    1 = deriv (fun t : ℝ => t) x := (hasDerivAt_id x).deriv.symm
    _ = deriv (fun t => Real.cos (φ t y) * Real.cos (ψ t y)) x := hX'.deriv_eq
    _ = _ := hrhs.deriv

theorem gap2 (φ ψ : ℝ → ℝ → ℝ) (x y : ℝ)
    (hφDiff : DifferentiableAt ℝ (Function.uncurry φ) (x, y))
    (hψDiff : DifferentiableAt ℝ (Function.uncurry ψ) (x, y))
    (hY : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      p.2 = Real.cos (φ p.1 p.2) * Real.sin (ψ p.1 p.2)) :
    0 = -Real.sin (φ x y) * Real.sin (ψ x y) * partialX φ x y +
      Real.cos (φ x y) * Real.cos (ψ x y) * partialX ψ x y := by
  have hφx := differentiableAt_fst_slice φ x y hφDiff
  have hψx := differentiableAt_fst_slice ψ x y hψDiff
  have hφderiv : HasDerivAt (fun t => φ t y) (partialX φ x y) x := by
    simpa [partialX] using hφx.hasDerivAt
  have hψderiv : HasDerivAt (fun t => ψ t y) (partialX ψ x y) x := by
    simpa [partialX] using hψx.hasDerivAt
  have hcosφ : HasDerivAt (fun t => Real.cos (φ t y))
      (-Real.sin (φ x y) * partialX φ x y) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_cos (φ x y)).comp x hφderiv
  have hsinψ : HasDerivAt (fun t => Real.sin (ψ t y))
      (Real.cos (ψ x y) * partialX ψ x y) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sin (ψ x y)).comp x hψderiv
  have hrhs : HasDerivAt
      (fun t => Real.cos (φ t y) * Real.sin (ψ t y))
      (-Real.sin (φ x y) * Real.sin (ψ x y) * partialX φ x y +
        Real.cos (φ x y) * Real.cos (ψ x y) * partialX ψ x y) x := by
    convert hcosφ.mul hsinψ using 1 <;> ring
  have hY' : (fun _ : ℝ => y) =ᶠ[nhds x]
      (fun t => Real.cos (φ t y) * Real.sin (ψ t y)) := by
    simpa using eventually_fst_slice x y hY
  calc
    0 = deriv (fun _ : ℝ => y) x := (hasDerivAt_const (x := x) (c := y)).deriv.symm
    _ = deriv (fun t => Real.cos (φ t y) * Real.sin (ψ t y)) x := hY'.deriv_eq
    _ = _ := hrhs.deriv

theorem gap3 (φ ψ : ℝ → ℝ → ℝ) (x y : ℝ)
    (hSin : Real.sin (φ x y) ≠ 0)
    (hCos : Real.cos (φ x y) ≠ 0)
    (h1 : 1 = -Real.sin (φ x y) * Real.cos (ψ x y) * partialX φ x y -
      Real.cos (φ x y) * Real.sin (ψ x y) * partialX ψ x y)
    (h2 : 0 = -Real.sin (φ x y) * Real.sin (ψ x y) * partialX φ x y +
      Real.cos (φ x y) * Real.cos (ψ x y) * partialX ψ x y) :
    partialX φ x y = -Real.cos (ψ x y) / Real.sin (φ x y) := by
  have hp : -Real.sin (φ x y) * partialX φ x y = Real.cos (ψ x y) := by
    linear_combination
      -Real.cos (ψ x y) * h1 - Real.sin (ψ x y) * h2 +
      (Real.sin (φ x y) * partialX φ x y) *
        Real.sin_sq_add_cos_sq (ψ x y)
  field_simp [hSin]
  nlinarith [hp]

theorem gap4 (φ ψ : ℝ → ℝ → ℝ) (x y : ℝ)
    (hSin : Real.sin (φ x y) ≠ 0)
    (hCos : Real.cos (φ x y) ≠ 0)
    (h1 : 1 = -Real.sin (φ x y) * Real.cos (ψ x y) * partialX φ x y -
      Real.cos (φ x y) * Real.sin (ψ x y) * partialX ψ x y)
    (h2 : 0 = -Real.sin (φ x y) * Real.sin (ψ x y) * partialX φ x y +
      Real.cos (φ x y) * Real.cos (ψ x y) * partialX ψ x y) :
    partialX ψ x y = -Real.sin (ψ x y) / Real.cos (φ x y) := by
  have hq : -Real.cos (φ x y) * partialX ψ x y = Real.sin (ψ x y) := by
    linear_combination
      -Real.sin (ψ x y) * h1 + Real.cos (ψ x y) * h2 +
      (Real.cos (φ x y) * partialX ψ x y) *
        Real.sin_sq_add_cos_sq (ψ x y)
  field_simp [hCos]
  nlinarith [hq]

theorem gap5 (φ z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hφDiff : DifferentiableAt ℝ (Function.uncurry φ) (x, y))
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y))
    (hZ : ∀ᶠ p : ℝ × ℝ in nhds (x, y), z p.1 p.2 = Real.sin (φ p.1 p.2)) :
    partialX z x y = Real.cos (φ x y) * partialX φ x y := by
  have hφx := differentiableAt_fst_slice φ x y hφDiff
  have hφderiv : HasDerivAt (fun t => φ t y) (partialX φ x y) x := by
    simpa [partialX] using hφx.hasDerivAt
  have hsin : HasDerivAt (fun t => Real.sin (φ t y))
      (Real.cos (φ x y) * partialX φ x y) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sin (φ x y)).comp x hφderiv
  have hZ' : (fun t => z t y) =ᶠ[nhds x]
      (fun t => Real.sin (φ t y)) := by
    simpa using eventually_fst_slice x y hZ
  calc
    partialX z x y = deriv (fun t => z t y) x := rfl
    _ = deriv (fun t => Real.sin (φ t y)) x := hZ'.deriv_eq
    _ = _ := hsin.deriv

theorem gap6 (φ ψ : ℝ → ℝ → ℝ) (x y : ℝ)
    (hSin : Real.sin (φ x y) ≠ 0)
    (hφ : partialX φ x y = -Real.cos (ψ x y) / Real.sin (φ x y)) :
    Real.cos (φ x y) * partialX φ x y = parametricZx (φ x y) (ψ x y) := by
  rw [hφ]
  unfold parametricZx cot
  field_simp [hSin]

theorem gap7 (φ ψ z : ℝ → ℝ → ℝ) (x y : ℝ)
    (h1 : partialX z x y = Real.cos (φ x y) * partialX φ x y)
    (h2 : Real.cos (φ x y) * partialX φ x y =
      parametricZx (φ x y) (ψ x y)) :
    partialX z x y = parametricZx (φ x y) (ψ x y) := by
  exact h1.trans h2

theorem gap8 (φ ψ z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hφC2 : ContDiffAt ℝ 2 (Function.uncurry φ) (x, y))
    (hψC2 : ContDiffAt ℝ 2 (Function.uncurry ψ) (x, y))
    (hzC2 : ContDiffAt ℝ 2 (Function.uncurry z) (x, y))
    (hSin : Real.sin (φ x y) ≠ 0)
    (hZx : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialX z p.1 p.2 = parametricZx (φ p.1 p.2) (ψ p.1 p.2)) :
    partialXX z x y =
      parametricZxPhi (φ x y) (ψ x y) * partialX φ x y +
      parametricZxPsi (φ x y) (ψ x y) * partialX ψ x y := by
  have hφDiff : DifferentiableAt ℝ (Function.uncurry φ) (x, y) :=
    hφC2.differentiableAt (by decide)
  have hψDiff : DifferentiableAt ℝ (Function.uncurry ψ) (x, y) :=
    hψC2.differentiableAt (by decide)
  have hφx := differentiableAt_fst_slice φ x y hφDiff
  have hψx := differentiableAt_fst_slice ψ x y hψDiff
  have hφderiv : HasDerivAt (fun t => φ t y) (partialX φ x y) x := by
    simpa [partialX] using hφx.hasDerivAt
  have hψderiv : HasDerivAt (fun t => ψ t y) (partialX ψ x y) x := by
    simpa [partialX] using hψx.hasDerivAt
  have hcosφ : HasDerivAt (fun t => Real.cos (φ t y))
      (-Real.sin (φ x y) * partialX φ x y) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_cos (φ x y)).comp x hφderiv
  have hsinφ : HasDerivAt (fun t => Real.sin (φ t y))
      (Real.cos (φ x y) * partialX φ x y) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sin (φ x y)).comp x hφderiv
  have hcosψ : HasDerivAt (fun t => Real.cos (ψ t y))
      (-Real.sin (ψ x y) * partialX ψ x y) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_cos (ψ x y)).comp x hψderiv
  have hcot : HasDerivAt (fun t => cot (φ t y))
      (-(1 / Real.sin (φ x y) ^ 2) * partialX φ x y) x := by
    change HasDerivAt
      (fun t => Real.cos (φ t y) / Real.sin (φ t y))
      (-(1 / Real.sin (φ x y) ^ 2) * partialX φ x y) x
    convert hcosφ.div hsinφ hSin using 1
    field_simp [hSin]
    linear_combination
      partialX φ x y * Real.sin_sq_add_cos_sq (φ x y)
  have hparam : HasDerivAt
      (fun t => parametricZx (φ t y) (ψ t y))
      (parametricZxPhi (φ x y) (ψ x y) * partialX φ x y +
        parametricZxPsi (φ x y) (ψ x y) * partialX ψ x y) x := by
    change HasDerivAt
      (fun t => -cot (φ t y) * Real.cos (ψ t y)) _ x
    convert hcot.neg.mul hcosψ using 1 <;>
      simp [parametricZxPhi, parametricZxPsi] <;> ring
  have hZx' : (fun t => partialX z t y) =ᶠ[nhds x]
      (fun t => parametricZx (φ t y) (ψ t y)) := by
    simpa using eventually_fst_slice x y hZx
  calc
    partialXX z x y = deriv (fun t => partialX z t y) x := rfl
    _ = deriv (fun t => parametricZx (φ t y) (ψ t y)) x := hZx'.deriv_eq
    _ = _ := hparam.deriv

theorem gap9 (φ ψ : ℝ → ℝ → ℝ) (x y : ℝ)
    (hSin : Real.sin (φ x y) ≠ 0)
    (hCos : Real.cos (φ x y) ≠ 0)
    (hφ : partialX φ x y = -Real.cos (ψ x y) / Real.sin (φ x y))
    (hψ : partialX ψ x y = -Real.sin (ψ x y) / Real.cos (φ x y)) :
    parametricZxPhi (φ x y) (ψ x y) * partialX φ x y +
        parametricZxPsi (φ x y) (ψ x y) * partialX ψ x y =
      (Real.cos (ψ x y) / Real.sin (φ x y) ^ 2) *
          (-Real.cos (ψ x y) / Real.sin (φ x y)) +
        cot (φ x y) * Real.sin (ψ x y) *
          (-Real.sin (ψ x y) / Real.cos (φ x y)) := by
  simp only [parametricZxPhi, parametricZxPsi, hφ, hψ]

theorem gap10 (φ ψ z : ℝ → ℝ → ℝ) (x y : ℝ)
    (h1 : partialXX z x y =
      parametricZxPhi (φ x y) (ψ x y) * partialX φ x y +
      parametricZxPsi (φ x y) (ψ x y) * partialX ψ x y)
    (h2 : parametricZxPhi (φ x y) (ψ x y) * partialX φ x y +
        parametricZxPsi (φ x y) (ψ x y) * partialX ψ x y =
      (Real.cos (ψ x y) / Real.sin (φ x y) ^ 2) *
          (-Real.cos (ψ x y) / Real.sin (φ x y)) +
        cot (φ x y) * Real.sin (ψ x y) *
          (-Real.sin (ψ x y) / Real.cos (φ x y))) :
    partialXX z x y =
      (Real.cos (ψ x y) / Real.sin (φ x y) ^ 2) *
          (-Real.cos (ψ x y) / Real.sin (φ x y)) +
        cot (φ x y) * Real.sin (ψ x y) *
          (-Real.sin (ψ x y) / Real.cos (φ x y)) := by
  exact h1.trans h2

theorem gap11 (φ ψ z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hSin : Real.sin (φ x y) ≠ 0) (hCos : Real.cos (φ x y) ≠ 0)
    (hExpanded : partialXX z x y =
      (Real.cos (ψ x y) / Real.sin (φ x y) ^ 2) *
          (-Real.cos (ψ x y) / Real.sin (φ x y)) +
        cot (φ x y) * Real.sin (ψ x y) *
          (-Real.sin (ψ x y) / Real.cos (φ x y))) :
    partialXX z x y = firstSecondForm (φ x y) (ψ x y) := by
  rw [hExpanded]
  unfold cot firstSecondForm
  field_simp [hSin, hCos]
  ring

theorem gap12 (φ ψ : ℝ → ℝ → ℝ) (x y : ℝ)
    (hSin : Real.sin (φ x y) ≠ 0) :
    firstSecondForm (φ x y) (ψ x y) =
      finalSecondForm (φ x y) (ψ x y) := by
  have ha : Real.cos (φ x y) ^ 2 = 1 - Real.sin (φ x y) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (φ x y)]
  have hb : Real.sin (ψ x y) ^ 2 = 1 - Real.cos (ψ x y) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (ψ x y)]
  unfold firstSecondForm finalSecondForm
  rw [ha, hb]
  ring

theorem gap13 (φ ψ z : ℝ → ℝ → ℝ) (x y : ℝ)
    (h1 : partialXX z x y = firstSecondForm (φ x y) (ψ x y))
    (h2 : firstSecondForm (φ x y) (ψ x y) =
      finalSecondForm (φ x y) (ψ x y)) :
    partialXX z x y = finalSecondForm (φ x y) (ψ x y) := by
  exact h1.trans h2

theorem gap14 (φ ψ z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hx : x = Real.cos (φ x y) * Real.cos (ψ x y))
    (hy : y = Real.cos (φ x y) * Real.sin (ψ x y))
    (hz : z x y = Real.sin (φ x y)) :
    x ^ 2 + y ^ 2 + (z x y) ^ 2 = 1 := by
  have hx2 : x ^ 2 =
      (Real.cos (φ x y) * Real.cos (ψ x y)) ^ 2 :=
    congrArg (fun t : ℝ => t ^ 2) hx
  have hy2 : y ^ 2 =
      (Real.cos (φ x y) * Real.sin (ψ x y)) ^ 2 :=
    congrArg (fun t : ℝ => t ^ 2) hy
  have hz2 : (z x y) ^ 2 = Real.sin (φ x y) ^ 2 :=
    congrArg (fun t : ℝ => t ^ 2) hz
  have ha : Real.cos (φ x y) ^ 2 + Real.sin (φ x y) ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (φ x y)]
  have hb : Real.cos (ψ x y) ^ 2 + Real.sin (ψ x y) ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (ψ x y)]
  rw [hx2, hy2, hz2]
  calc
    (Real.cos (φ x y) * Real.cos (ψ x y)) ^ 2 +
          (Real.cos (φ x y) * Real.sin (ψ x y)) ^ 2 +
          Real.sin (φ x y) ^ 2 =
        Real.cos (φ x y) ^ 2 *
            (Real.cos (ψ x y) ^ 2 + Real.sin (ψ x y) ^ 2) +
          Real.sin (φ x y) ^ 2 := by ring
    _ = Real.cos (φ x y) ^ 2 + Real.sin (φ x y) ^ 2 := by rw [hb]; ring
    _ = 1 := ha

theorem gap15 (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y))
    (hSphere : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      p.1 ^ 2 + p.2 ^ 2 + (z p.1 p.2) ^ 2 = 1) :
    2 * x + 2 * z x y * partialX z x y = 0 := by
  have hzSlice := differentiableAt_fst_slice z x y hzDiff
  have hzDeriv : HasDerivAt (fun t => z t y) (partialX z x y) x := by
    simpa [partialX] using hzSlice.hasDerivAt
  have hraw : HasDerivAt
      (fun t : ℝ => t ^ 2 + y ^ 2 + (z t y) ^ 2)
      (2 * x + 2 * z x y * partialX z x y) x := by
    convert (((hasDerivAt_id x).pow 2).add
      ((hasDerivAt_const (x := x) (c := y)).pow 2)).add
      (hzDeriv.pow 2) using 1 <;> norm_num <;> ring
  have hSphere' :
      (fun t : ℝ => t ^ 2 + y ^ 2 + (z t y) ^ 2) =ᶠ[nhds x]
        (fun _ : ℝ => 1) := by
    simpa using eventually_fst_slice x y hSphere
  calc
    2 * x + 2 * z x y * partialX z x y =
        deriv (fun t : ℝ => t ^ 2 + y ^ 2 + (z t y) ^ 2) x := hraw.deriv.symm
    _ = deriv (fun _ : ℝ => 1) x := hSphere'.deriv_eq
    _ = 0 := (hasDerivAt_const (x := x) (c := (1 : ℝ))).deriv

theorem gap16 (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hz : z x y ≠ 0)
    (hDerivative : 2 * x + 2 * z x y * partialX z x y = 0) :
    partialX z x y = -x / z x y := by
  field_simp [hz]
  nlinarith [hDerivative]

theorem gap17 (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hz : z x y ≠ 0)
    (hzC2 : ContDiffAt ℝ 2 (Function.uncurry z) (x, y))
    (hZx : ∀ᶠ p : ℝ × ℝ in nhds (x, y), partialX z p.1 p.2 = -p.1 / z p.1 p.2) :
    partialXX z x y =
      -(z x y - x * partialX z x y) / (z x y) ^ 2 := by
  have hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y) :=
    hzC2.differentiableAt (by decide)
  have hzSlice := differentiableAt_fst_slice z x y hzDiff
  have hzDeriv : HasDerivAt (fun t => z t y) (partialX z x y) x := by
    simpa [partialX] using hzSlice.hasDerivAt
  have hnegid : HasDerivAt (fun t : ℝ => -t) (-1) x := by
    simpa using (hasDerivAt_id x).neg
  have hquot : HasDerivAt (fun t : ℝ => -t / z t y)
      (-(z x y - x * partialX z x y) / (z x y) ^ 2) x := by
    convert hnegid.div hzDeriv hz using 1 <;> ring
  have hZx' : (fun t => partialX z t y) =ᶠ[nhds x]
      (fun t => -t / z t y) := by
    simpa using eventually_fst_slice x y hZx
  calc
    partialXX z x y = deriv (fun t => partialX z t y) x := rfl
    _ = deriv (fun t => -t / z t y) x := hZx'.deriv_eq
    _ = _ := hquot.deriv

theorem gap18 (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hz : z x y ≠ 0)
    (hZx : partialX z x y = -x / z x y) :
    -(z x y - x * partialX z x y) / (z x y) ^ 2 =
      -((z x y) ^ 2 + x ^ 2) / (z x y) ^ 3 := by
  rw [hZx]
  field_simp [hz]
  ring

theorem gap19 (φ ψ z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hz : z x y = Real.sin (φ x y))
    (hx : x = Real.cos (φ x y) * Real.cos (ψ x y))
    (hSin : Real.sin (φ x y) ≠ 0) :
    -((z x y) ^ 2 + x ^ 2) / (z x y) ^ 3 =
      finalSecondForm (φ x y) (ψ x y) := by
  have hz2 : (z x y) ^ 2 = Real.sin (φ x y) ^ 2 :=
    congrArg (fun t : ℝ => t ^ 2) hz
  have hz3 : (z x y) ^ 3 = Real.sin (φ x y) ^ 3 :=
    congrArg (fun t : ℝ => t ^ 3) hz
  have hx2 : x ^ 2 =
      (Real.cos (φ x y) * Real.cos (ψ x y)) ^ 2 :=
    congrArg (fun t : ℝ => t ^ 2) hx
  rw [hz2, hz3, hx2]
  unfold finalSecondForm
  ring

theorem gap20 (φ ψ z : ℝ → ℝ → ℝ) (x y : ℝ)
    (h1 : partialXX z x y = -((z x y) ^ 2 + x ^ 2) / (z x y) ^ 3)
    (h2 : -((z x y) ^ 2 + x ^ 2) / (z x y) ^ 3 =
      finalSecondForm (φ x y) (ψ x y)) :
    partialXX z x y = finalSecondForm (φ x y) (ψ x y) := by
  exact h1.trans h2

end

end ProofGap.Exercise3408
