import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1096

noncomputable section

def paramDeriv (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv f x / deriv g x

def expanded (x : ℝ) : ℝ := x ^ 3 - 2 * x ^ 6 - x ^ 9
def inCube (u : ℝ) : ℝ := u - 2 * u ^ 2 - u ^ 3
def cube (x : ℝ) : ℝ := x ^ 3

def sinc (x : ℝ) : ℝ := Real.sin x / x
def square (x : ℝ) : ℝ := x ^ 2
def sincOfSquare (u : ℝ) : ℝ := Real.sin (Real.sqrt u) / Real.sqrt u

def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x

private theorem hasDerivAt_inCube_cube (x : ℝ) :
    HasDerivAt inCube (1 - 4 * x ^ 3 - 3 * x ^ 6) (cube x) := by
  convert (((hasDerivAt_id (cube x)).sub
      (((hasDerivAt_id (cube x)).pow 2).const_mul 2)).sub
      ((hasDerivAt_id (cube x)).pow 3)) using 1 <;>
    simp [inCube, cube] <;> ring

private theorem hasDerivAt_expanded (x : ℝ) :
    HasDerivAt expanded (3 * x ^ 2 - 12 * x ^ 5 - 9 * x ^ 8) x := by
  convert ((((hasDerivAt_id x).pow 3).sub
      (((hasDerivAt_id x).pow 6).const_mul 2)).sub
      ((hasDerivAt_id x).pow 9)) using 1 <;>
    simp [expanded] <;> ring

private theorem hasDerivAt_cube (x : ℝ) :
    HasDerivAt cube (3 * x ^ 2) x := by
  convert (hasDerivAt_id x).pow 3 using 1 <;>
    simp [cube] <;> ring

private theorem hasDerivAt_sinc (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt sinc ((x * Real.cos x - Real.sin x) / x ^ 2) x := by
  convert (Real.hasDerivAt_sin x).div (hasDerivAt_id x) hx using 1 <;>
    simp [sinc] <;> ring

private theorem hasDerivAt_square (x : ℝ) :
    HasDerivAt square (2 * x) x := by
  convert (hasDerivAt_id x).pow 2 using 1 <;>
    simp [square] <;> ring

private theorem hasDerivAt_sincOfSquare_square (x : ℝ) (hx : 0 < x) :
    HasDerivAt sincOfSquare
      (((1 / 2 : ℝ) * Real.cos x -
        (1 / (2 * x)) * Real.sin x) / x ^ 2) (square x) := by
  have hsq_ne : square x ≠ 0 := by
    simp [square, hx.ne']
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * x)) (square x) := by
    convert Real.hasDerivAt_sqrt hsq_ne using 1 <;>
      simp [square, Real.sqrt_sq_eq_abs, abs_of_pos hx, one_div] <;>
      field_simp [hx.ne'] <;> ring
  have hsqrt_val : Real.sqrt (square x) = x := by
    simp [square, Real.sqrt_sq_eq_abs, abs_of_pos hx]
  have hnum : HasDerivAt (fun u : ℝ => Real.sin (Real.sqrt u))
      (Real.cos x * (1 / (2 * x))) (square x) := by
    convert (Real.hasDerivAt_sin (Real.sqrt (square x))).comp
      (square x) hsqrt using 1 <;> simp [hsqrt_val]
  have hquot := hnum.div hsqrt (by simpa [hsqrt_val] using hx.ne')
  convert hquot using 1 <;>
    simp [sincOfSquare, hsqrt_val] <;>
    field_simp [hx.ne'] <;> ring

private theorem hasDerivAt_cot (x : ℝ) (hs : Real.sin x ≠ 0) :
    HasDerivAt cot (-(1 / Real.sin x ^ 2)) x := by
  have hraw : HasDerivAt cot
      (((-Real.sin x) * Real.sin x - Real.cos x * Real.cos x) /
        Real.sin x ^ 2) x := by
    simpa only [cot] using
      (Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hs
  convert hraw using 1
  field_simp [hs]
  nlinarith [Real.sin_sq_add_cos_sq x]

private theorem hasDerivAt_reciprocal (u : ℝ) (hu : u ≠ 0) :
    HasDerivAt (fun v : ℝ => 1 / v) (-(1 / u ^ 2)) u := by
  convert (hasDerivAt_id u).inv hu using 1 <;>
    first
    | (funext v; simp [one_div])
    | (simp [one_div] <;> field_simp [hu] <;> ring)

private theorem hasDerivAt_tan_from_quotient (x : ℝ)
    (hc : Real.cos x ≠ 0) :
    HasDerivAt Real.tan (1 / Real.cos x ^ 2) x := by
  have hraw : HasDerivAt (fun y : ℝ => Real.sin y / Real.cos y)
      ((Real.cos x * Real.cos x - Real.sin x * (-Real.sin x)) /
        Real.cos x ^ 2) x :=
    (Real.hasDerivAt_sin x).div (Real.hasDerivAt_cos x) hc
  have hcoeff :
      (Real.cos x * Real.cos x - Real.sin x * (-Real.sin x)) /
          Real.cos x ^ 2 =
        1 / Real.cos x ^ 2 := by
    field_simp [hc]
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [hcoeff] at hraw
  have hfun : (fun y : ℝ => Real.sin y / Real.cos y) = Real.tan := by
    funext y
    rw [Real.tan_eq_sin_div_cos]
  rw [← hfun]
  exact hraw

theorem gap1 (x : ℝ) (hx : x ≠ 0) :
    paramDeriv expanded cube x = deriv inCube (cube x) := by
  rw [paramDeriv, (hasDerivAt_expanded x).deriv,
    (hasDerivAt_cube x).deriv, (hasDerivAt_inCube_cube x).deriv]
  field_simp [hx] <;> ring

theorem gap2 (x : ℝ) :
    HasDerivAt inCube (1 - 4 * x ^ 3 - 3 * x ^ 6) (cube x) := by
  exact hasDerivAt_inCube_cube x

theorem gap3 (x : ℝ) (hx : x ≠ 0) :
    paramDeriv expanded cube x = 1 - 4 * x ^ 3 - 3 * x ^ 6 := by
  calc
    paramDeriv expanded cube x = deriv inCube (cube x) := gap1 x hx
    _ = 1 - 4 * x ^ 3 - 3 * x ^ 6 := (gap2 x).deriv

theorem gap4 : Function.Even sinc := by
  intro x
  simp [sinc]

theorem gap5 (x : ℝ) (hx : 0 < x) :
    paramDeriv sinc square x = deriv sincOfSquare (square x) := by
  rw [paramDeriv, (hasDerivAt_sinc x hx.ne').deriv,
    (hasDerivAt_square x).deriv,
    (hasDerivAt_sincOfSquare_square x hx).deriv]
  field_simp [hx.ne'] <;> ring

theorem gap6 (x : ℝ) (hx : 0 < x) :
    deriv sincOfSquare (square x) =
      ((1 / 2 : ℝ) * Real.cos x -
        (1 / (2 * x)) * Real.sin x) / x ^ 2 := by
  exact (hasDerivAt_sincOfSquare_square x hx).deriv

theorem gap7 (x : ℝ) (hx : 0 < x) :
    ((1 / 2 : ℝ) * Real.cos x -
        (1 / (2 * x)) * Real.sin x) / x ^ 2 =
      (x * Real.cos x - Real.sin x) / (2 * x ^ 3) := by
  field_simp [hx.ne'] <;> ring

theorem gap8 (x : ℝ) (hx : 0 < x) :
    paramDeriv sinc square x =
      (x * Real.cos x - Real.sin x) / (2 * x ^ 3) := by
  calc
    paramDeriv sinc square x = deriv sincOfSquare (square x) := gap5 x hx
    _ = ((1 / 2 : ℝ) * Real.cos x -
          (1 / (2 * x)) * Real.sin x) / x ^ 2 := gap6 x hx
    _ = (x * Real.cos x - Real.sin x) / (2 * x ^ 3) := gap7 x hx

theorem gap9 (x : ℝ) (hx : x ≠ 0) :
    paramDeriv sinc square x =
      (x * Real.cos x - Real.sin x) / (2 * x ^ 3) := by
  rw [paramDeriv, (hasDerivAt_sinc x hx).deriv,
    (hasDerivAt_square x).deriv]
  field_simp [hx] <;> ring

theorem gap10 (x : ℝ) (hx : Real.sin x ≠ 0) :
    paramDeriv Real.sin Real.cos x =
      Real.cos x / (-Real.sin x) := by
  rw [paramDeriv, (Real.hasDerivAt_sin x).deriv,
    (Real.hasDerivAt_cos x).deriv]

theorem gap11 (x : ℝ) (hx : Real.sin x ≠ 0) :
    Real.cos x / (-Real.sin x) = -cot x := by
  unfold cot
  field_simp [hx] <;> ring

theorem gap12 (x : ℝ) (hx : Real.sin x ≠ 0) :
    paramDeriv Real.sin Real.cos x = -cot x := by
  calc
    paramDeriv Real.sin Real.cos x =
        Real.cos x / (-Real.sin x) := gap10 x hx
    _ = -cot x := gap11 x hx

theorem gap13 (x : ℝ)
    (hs : Real.sin x ≠ 0) (hc : Real.cos x ≠ 0) :
    paramDeriv Real.tan cot x =
      deriv (fun u : ℝ => 1 / u) (cot x) := by
  have hcot_ne : cot x ≠ 0 := by
    simpa [cot] using div_ne_zero hc hs
  rw [paramDeriv, (hasDerivAt_tan_from_quotient x hc).deriv,
    (hasDerivAt_cot x hs).deriv,
    (hasDerivAt_reciprocal (cot x) hcot_ne).deriv]
  rw [cot]
  field_simp [hs, hc] <;> ring

theorem gap14 (x : ℝ)
    (hs : Real.sin x ≠ 0) (hc : Real.cos x ≠ 0) :
    deriv (fun u : ℝ => 1 / u) (cot x) = -(1 / cot x ^ 2) := by
  have hcot_ne : cot x ≠ 0 := by
    simpa [cot] using div_ne_zero hc hs
  exact (hasDerivAt_reciprocal (cot x) hcot_ne).deriv

theorem gap15 (x : ℝ)
    (hs : Real.sin x ≠ 0) (hc : Real.cos x ≠ 0) :
    -(1 / cot x ^ 2) = -Real.tan x ^ 2 := by
  rw [Real.tan_eq_sin_div_cos]
  rw [cot]
  field_simp [hs, hc] <;> ring

theorem gap16 (x : ℝ)
    (hs : Real.sin x ≠ 0) (hc : Real.cos x ≠ 0) :
    paramDeriv Real.tan cot x = -Real.tan x ^ 2 := by
  calc
    paramDeriv Real.tan cot x =
        deriv (fun u : ℝ => 1 / u) (cot x) := gap13 x hs hc
    _ = -(1 / cot x ^ 2) := gap14 x hs hc
    _ = -Real.tan x ^ 2 := gap15 x hs hc

theorem gap17 (x : ℝ) (hx : |x| < 1) :
    paramDeriv Real.arcsin Real.arccos x =
      (1 / Real.sqrt (1 - x ^ 2)) /
        (-(1 / Real.sqrt (1 - x ^ 2))) := by
  have hxi : x ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp hx
  have hneg : x ≠ (-1 : ℝ) := by
    linarith [hxi.1]
  have hone : x ≠ (1 : ℝ) := by
    linarith [hxi.2]
  rw [paramDeriv, (Real.hasDerivAt_arcsin hneg hone).deriv,
    (Real.hasDerivAt_arccos hneg hone).deriv]

theorem gap18 (x : ℝ) (hx : |x| < 1) :
    (1 / Real.sqrt (1 - x ^ 2)) /
        (-(1 / Real.sqrt (1 - x ^ 2))) = -1 := by
  rcases abs_lt.mp hx with ⟨hl, hu⟩
  have hp : 0 < (1 - x) * (1 + x) :=
    mul_pos (sub_pos.mpr hu) (by linarith)
  have harg : 0 < 1 - x ^ 2 := by
    nlinarith [hp]
  have hsqrt : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 harg)
  field_simp [hsqrt] <;> ring

theorem gap19 (x : ℝ) (hx : |x| < 1) :
    paramDeriv Real.arcsin Real.arccos x = -1 := by
  calc
    paramDeriv Real.arcsin Real.arccos x =
        (1 / Real.sqrt (1 - x ^ 2)) /
          (-(1 / Real.sqrt (1 - x ^ 2))) := gap17 x hx
    _ = -1 := gap18 x hx

end

end ProofGap.Exercise1096
