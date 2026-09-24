import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise975

noncomputable section

def u (x : ℝ) : ℝ := Real.exp (-x ^ 2)

def outer (t : ℝ) : ℝ :=
  t * Real.arcsin t / Real.sqrt (1 - t ^ 2) +
    (1 / 2 : ℝ) * Real.log (1 - t ^ 2)

def y (x : ℝ) : ℝ := outer (u x)

def expandedOuterDerivative (t : ℝ) : ℝ :=
  ((Real.arcsin t + t / Real.sqrt (1 - t ^ 2)) *
        Real.sqrt (1 - t ^ 2) +
      t ^ 2 * Real.arcsin t / Real.sqrt (1 - t ^ 2)) /
      (1 - t ^ 2) -
    t / (1 - t ^ 2)

def finalOuterDerivative (t : ℝ) : ℝ :=
  Real.arcsin t / Real.sqrt (1 - t ^ 2) ^ 3

def substitutedOuterDerivative (x : ℝ) : ℝ :=
  Real.arcsin (Real.exp (-x ^ 2)) /
    Real.sqrt (1 - Real.exp (-2 * x ^ 2)) ^ 3

def finalDerivative (x : ℝ) : ℝ :=
  (-2 * x * Real.exp (-x ^ 2) * Real.arcsin (Real.exp (-x ^ 2))) /
    Real.sqrt (1 - Real.exp (-2 * x ^ 2)) ^ 3

private theorem expandedOuterDerivative_eq_finalOuterDerivative
    (t : ℝ) (hz : 0 < 1 - t ^ 2) :
    expandedOuterDerivative t = finalOuterDerivative t := by
  unfold expandedOuterDerivative finalOuterDerivative
  let z : ℝ := 1 - t ^ 2
  let s : ℝ := Real.sqrt z
  let A : ℝ := Real.arcsin t
  have hzpos : 0 < z := by
    simpa [z] using hz
  have hspos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 hzpos
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hzne : z ≠ 0 := ne_of_gt hzpos
  have hsq : s ^ 2 = z := by
    dsimp [s]
    exact Real.sq_sqrt (le_of_lt hzpos)
  have hone : s ^ 2 + t ^ 2 = 1 := by
    rw [hsq]
    dsimp [z]
    ring
  change
    (((A + t / s) * s + t ^ 2 * A / s) / z - t / z) =
      A / s ^ 3
  calc
    (((A + t / s) * s + t ^ 2 * A / s) / z - t / z) =
        (A * s + t ^ 2 * A / s) / z := by
      field_simp [hsne, hzne]
      ring
    _ = A * (s ^ 2 + t ^ 2) / (s * z) := by
      field_simp [hsne, hzne]
    _ = A / (s * z) := by
      rw [hone]
      ring
    _ = A / s ^ 3 := by
      rw [← hsq]
      ring

theorem gap1 (x : ℝ) (hx : x ≠ 0) :
    y x = outer (u x) := by
  rfl

theorem gap2 (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt outer (expandedOuterDerivative (u x)) (u x) := by
  let t : ℝ := u x
  change HasDerivAt outer (expandedOuterDerivative t) t
  have htpos : 0 < t := by
    change 0 < Real.exp (-x ^ 2)
    exact Real.exp_pos _
  have htlt : t < 1 := by
    change Real.exp (-x ^ 2) < 1
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (neg_lt_zero.mpr (sq_pos_of_ne_zero hx))
  have honeplus : 0 < 1 + t := by
    linarith
  have hprod : 0 < (1 - t) * (1 + t) :=
    mul_pos (sub_pos.mpr htlt) honeplus
  have hzpos : 0 < 1 - t ^ 2 := by
    nlinarith [hprod]
  have hzderiv :
      HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-2 * t) t := by
    convert (hasDerivAt_const (x := t) (c := (1 : ℝ))).sub
      ((hasDerivAt_id t).pow 2) using 1 <;>
      simp [id_eq] <;> ring
  have hasin :
      HasDerivAt Real.arcsin (1 / Real.sqrt (1 - t ^ 2)) t :=
    Real.hasDerivAt_arcsin (by nlinarith) (ne_of_lt htlt)
  have hnum :
      HasDerivAt (fun z : ℝ => z * Real.arcsin z)
        (Real.arcsin t + t / Real.sqrt (1 - t ^ 2)) t := by
    convert (hasDerivAt_id t).mul hasin using 1 <;>
      simp [id_eq, div_eq_mul_inv] <;> ring
  have hspos : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.2 hzpos
  have hsne : Real.sqrt (1 - t ^ 2) ≠ 0 := ne_of_gt hspos
  have hzne : 1 - t ^ 2 ≠ 0 := ne_of_gt hzpos
  have hsq : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 :=
    Real.sq_sqrt (le_of_lt hzpos)
  have hsinasin : Real.sin (Real.arcsin t) = t :=
    Real.sin_arcsin (by linarith) (le_of_lt htlt)
  have hcoscomp :=
    (Real.hasDerivAt_cos (Real.arcsin t)).comp t hasin
  have hroot :
      HasDerivAt (fun z : ℝ => Real.sqrt (1 - z ^ 2))
        (-t / Real.sqrt (1 - t ^ 2)) t := by
    simpa only [Function.comp_def, Real.cos_arcsin, hsinasin,
      div_eq_mul_inv, one_mul] using hcoscomp
  have hquot0 :
      HasDerivAt
        (fun z : ℝ => z * Real.arcsin z / Real.sqrt (1 - z ^ 2))
        (((Real.arcsin t + t / Real.sqrt (1 - t ^ 2)) *
              Real.sqrt (1 - t ^ 2) -
            (t * Real.arcsin t) *
              (-t / Real.sqrt (1 - t ^ 2))) /
          Real.sqrt (1 - t ^ 2) ^ 2) t :=
    hnum.div hroot hsne
  have hquotCoeff :
      (((Real.arcsin t + t / Real.sqrt (1 - t ^ 2)) *
              Real.sqrt (1 - t ^ 2) -
            (t * Real.arcsin t) *
              (-t / Real.sqrt (1 - t ^ 2))) /
          Real.sqrt (1 - t ^ 2) ^ 2) =
        (((Real.arcsin t + t / Real.sqrt (1 - t ^ 2)) *
              Real.sqrt (1 - t ^ 2) +
            t ^ 2 * Real.arcsin t / Real.sqrt (1 - t ^ 2)) /
          (1 - t ^ 2)) := by
    rw [hsq]
    field_simp [hsne, hzne]
    ring
  have hquot :
      HasDerivAt
        (fun z : ℝ => z * Real.arcsin z / Real.sqrt (1 - z ^ 2))
        (((Real.arcsin t + t / Real.sqrt (1 - t ^ 2)) *
              Real.sqrt (1 - t ^ 2) +
            t ^ 2 * Real.arcsin t / Real.sqrt (1 - t ^ 2)) /
          (1 - t ^ 2)) t := by
    rw [← hquotCoeff]
    exact hquot0
  have hlog :=
    (Real.hasDerivAt_log hzne).comp t hzderiv
  have hhalfLog :
      HasDerivAt
        (fun z : ℝ => (1 / 2 : ℝ) * Real.log (1 - z ^ 2))
        (-(t / (1 - t ^ 2))) t := by
    convert
      (hasDerivAt_const (x := t) (c := (1 / 2 : ℝ))).mul hlog
      using 1 <;>
      simp <;>
      field_simp [hzne] <;> ring
  unfold outer expandedOuterDerivative
  exact hquot.add hhalfLog

theorem gap3 (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt outer (finalOuterDerivative (u x)) (u x) := by
  have hupos : 0 < u x := Real.exp_pos _
  have hult : u x < 1 := by
    change Real.exp (-x ^ 2) < 1
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (neg_lt_zero.mpr (sq_pos_of_ne_zero hx))
  have honeplus : 0 < 1 + u x := by
    linarith
  have hprod : 0 < (1 - u x) * (1 + u x) :=
    mul_pos (sub_pos.mpr hult) honeplus
  have hzpos : 0 < 1 - (u x) ^ 2 := by
    nlinarith [hprod]
  rw [← expandedOuterDerivative_eq_finalOuterDerivative (u x) hzpos]
  exact gap2 x hx

theorem gap4 (x : ℝ) (hx : x ≠ 0) :
    finalOuterDerivative (u x) = substitutedOuterDerivative x := by
  unfold finalOuterDerivative substitutedOuterDerivative u
  have hexp :
      Real.exp (-x ^ 2) ^ 2 = Real.exp (-2 * x ^ 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]

theorem gap5 (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt outer (substitutedOuterDerivative x) (u x) := by
  rw [← gap4 x hx]
  exact gap3 x hx

theorem gap6 (x : ℝ) :
    HasDerivAt u (-2 * x * Real.exp (-x ^ 2)) x := by
  unfold u
  have hinner :
      HasDerivAt (fun z : ℝ => -z ^ 2) (-2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).neg using 1 <;>
      simp [id_eq] <;> ring
  convert (Real.hasDerivAt_exp (-x ^ 2)).comp x hinner using 1 <;>
    simp [id_eq] <;> ring

theorem gap7 (x : ℝ) (hx : x ≠ 0) :
    deriv y x = deriv outer (u x) * deriv u x := by
  have hcomp := (gap5 x hx).comp x (gap6 x)
  change deriv (outer ∘ u) x = deriv outer (u x) * deriv u x
  rw [hcomp.deriv, (gap5 x hx).deriv, (gap6 x).deriv]

theorem gap8 (x : ℝ) (hx : x ≠ 0) :
    deriv outer (u x) * deriv u x = finalDerivative x := by
  rw [(gap5 x hx).deriv, (gap6 x).deriv]
  unfold substitutedOuterDerivative finalDerivative
  ring

theorem gap9 (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt y (finalDerivative x) x := by
  have hcomp :
      HasDerivAt (outer ∘ u)
        (substitutedOuterDerivative x *
          (-2 * x * Real.exp (-x ^ 2))) x :=
    (gap5 x hx).comp x (gap6 x)
  have hcoeff :
      substitutedOuterDerivative x *
          (-2 * x * Real.exp (-x ^ 2)) =
        finalDerivative x := by
    calc
      substitutedOuterDerivative x *
          (-2 * x * Real.exp (-x ^ 2)) =
          deriv outer (u x) * deriv u x := by
        rw [(gap5 x hx).deriv, (gap6 x).deriv]
      _ = finalDerivative x := gap8 x hx
  rw [← hcoeff]
  simpa [y, Function.comp_def] using hcomp

end

end ProofGap.Exercise975
