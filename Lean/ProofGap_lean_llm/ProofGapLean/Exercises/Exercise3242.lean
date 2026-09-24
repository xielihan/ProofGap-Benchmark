import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3242

noncomputable section

def f (x y z : ℝ) : ℝ :=
  Real.exp (Real.log (x / y) / z)

def partialX (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => g t y z) x

def partialY (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => g x t z) y

def partialZ (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => g x y t) z

def partialXX (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialX g t y z) x

def partialXY (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialX g x t z) y

def partialXZ (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialX g x y t) z

def partialYY (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialY g x t z) y

def partialYZ (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialY g x y t) z

def partialZZ (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialZ g x y t) z

def differential (g : ℝ → ℝ → ℝ → ℝ)
    (x y z dx dy dz : ℝ) : ℝ :=
  partialX g x y z * dx + partialY g x y z * dy + partialZ g x y z * dz

def secondDifferential (g : ℝ → ℝ → ℝ → ℝ)
    (x y z dx dy dz : ℝ) : ℝ :=
  partialXX g x y z * dx ^ 2 +
    partialYY g x y z * dy ^ 2 +
    partialZZ g x y z * dz ^ 2 +
    2 * partialXY g x y z * dx * dy +
    2 * partialYZ g x y z * dy * dz +
    2 * partialXZ g x y z * dz * dx

def expandedSecond (dx dy dz : ℝ) : ℝ :=
  2 * dy ^ 2 - 2 * dx * dy + 2 * dy * dz - 2 * dx * dz

def factoredSecond (dx dy dz : ℝ) : ℝ :=
  2 * (dy - dx) * (dy + dz)

private theorem partial_formulas (x y z : ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    partialX f x y z = f x y z / (x * z) ∧
      partialY f x y z = -f x y z / (y * z) ∧
      partialZ f x y z = -f x y z * Real.log (x / y) / z ^ 2 := by
  have hxy : x / y ≠ 0 := div_ne_zero hx hy
  have hdx : HasDerivAt (fun t : ℝ => t / y) (1 / y) x := by
    simpa using (hasDerivAt_id x).div_const y
  have hdy : HasDerivAt (fun t : ℝ => x / t) (-x / y ^ 2) y := by
    simpa using
      (hasDerivAt_const y x).div (hasDerivAt_id y) hy
  have hdz :
      HasDerivAt (fun t : ℝ => Real.log (x / y) / t)
        (-Real.log (x / y) / z ^ 2) z := by
    simpa using
      (hasDerivAt_const z (Real.log (x / y))).div (hasDerivAt_id z) hz
  have hlogx :
      HasDerivAt (fun t : ℝ => Real.log (t / y))
        ((x / y)⁻¹ * (1 / y)) x := by
    simpa only [Function.comp_apply] using
      ((Real.hasDerivAt_log hxy).comp x hdx)
  have hquotx :
      HasDerivAt (fun t : ℝ => Real.log (t / y) / z)
        ((x / y)⁻¹ * (1 / y) / z) x := by
    simpa using hlogx.div_const z
  have hex :
      HasDerivAt (fun t : ℝ => Real.exp (Real.log (t / y) / z))
        (Real.exp (Real.log (x / y) / z) *
          ((x / y)⁻¹ * (1 / y) / z)) x := by
    simpa only [Function.comp_apply] using
      ((Real.hasDerivAt_exp (Real.log (x / y) / z)).comp x hquotx)
  have hlogy :
      HasDerivAt (fun t : ℝ => Real.log (x / t))
        ((x / y)⁻¹ * (-x / y ^ 2)) y := by
    simpa only [Function.comp_apply] using
      ((Real.hasDerivAt_log hxy).comp y hdy)
  have hquoty :
      HasDerivAt (fun t : ℝ => Real.log (x / t) / z)
        ((x / y)⁻¹ * (-x / y ^ 2) / z) y := by
    simpa using hlogy.div_const z
  have hey :
      HasDerivAt (fun t : ℝ => Real.exp (Real.log (x / t) / z))
        (Real.exp (Real.log (x / y) / z) *
          ((x / y)⁻¹ * (-x / y ^ 2) / z)) y := by
    simpa only [Function.comp_apply] using
      ((Real.hasDerivAt_exp (Real.log (x / y) / z)).comp y hquoty)
  have hez :
      HasDerivAt (fun t : ℝ => Real.exp (Real.log (x / y) / t))
        (Real.exp (Real.log (x / y) / z) *
          (-Real.log (x / y) / z ^ 2)) z := by
    simpa only [Function.comp_apply] using
      ((Real.hasDerivAt_exp (Real.log (x / y) / z)).comp z hdz)
  constructor
  · change deriv (fun t : ℝ => Real.exp (Real.log (t / y) / z)) x =
      f x y z / (x * z)
    rw [hex.deriv]
    simp only [f]
    field_simp [hx, hy, hz, hxy] <;> ring
  constructor
  · change deriv (fun t : ℝ => Real.exp (Real.log (x / t) / z)) y =
      -f x y z / (y * z)
    rw [hey.deriv]
    simp only [f]
    field_simp [hx, hy, hz, hxy] <;> ring
  · change deriv (fun t : ℝ => Real.exp (Real.log (x / y) / t)) z =
      -f x y z * Real.log (x / y) / z ^ 2
    rw [hez.deriv]
    simp only [f]
    field_simp [hx, hy, hz, hxy] <;> ring

theorem gap1 (x : ℝ) (hx : 0 < x) :
    partialX f x 1 1 = 1 := by
  have h :=
    (partial_formulas x 1 1 hx.ne' one_ne_zero one_ne_zero).1
  simpa [f, Real.exp_log hx, hx.ne'] using h

theorem gap2 :
    partialX f 1 1 1 = 1 := by
  simpa using gap1 (1 : ℝ) (by norm_num)

theorem gap3 (y : ℝ) (hy : 0 < y) :
    partialY f 1 y 1 = -(1 / y ^ 2) := by
  have h :=
    (partial_formulas 1 y 1 one_ne_zero hy.ne' one_ne_zero).2.1
  have hpos : 0 < 1 / y := one_div_pos.mpr hy
  have hf : f 1 y 1 = 1 / y := by
    change Real.exp (Real.log (1 / y) / 1) = 1 / y
    simpa using Real.exp_log hpos
  rw [h, hf]
  field_simp [hy.ne'] <;> ring

theorem gap4 :
    partialY f 1 1 1 = -1 := by
  simpa using gap3 (1 : ℝ) (by norm_num)

theorem gap5 (z : ℝ) (hz : z ≠ 0) :
    partialZ f 1 1 z = 0 := by
  have h :=
    (partial_formulas 1 1 z one_ne_zero one_ne_zero hz).2.2
  simpa [f] using h

theorem gap6 :
    partialZ f 1 1 1 = 0 := by
  simpa using gap5 (1 : ℝ) (by norm_num)

theorem gap7 (dx dy dz : ℝ) :
    differential f 1 1 1 dx dy dz =
      partialX f 1 1 1 * dx +
        partialY f 1 1 1 * dy +
        partialZ f 1 1 1 * dz := by
  rfl

theorem gap8 (dx dy dz : ℝ) :
    partialX f 1 1 1 * dx +
        partialY f 1 1 1 * dy +
        partialZ f 1 1 1 * dz =
      dx - dy := by
  rw [gap2, gap4, gap6]
  ring

theorem gap9 (dx dy dz : ℝ) :
    differential f 1 1 1 dx dy dz = dx - dy := by
  calc
    differential f 1 1 1 dx dy dz =
        partialX f 1 1 1 * dx + partialY f 1 1 1 * dy +
          partialZ f 1 1 1 * dz := gap7 dx dy dz
    _ = dx - dy := gap8 dx dy dz

theorem gap10 :
    partialXX f 1 1 1 = 0 := by
  have hlocal :
      (fun t : ℝ => partialX f t 1 1) =ᶠ[nhds (1 : ℝ)]
        (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact gap1 t ht
  unfold partialXX
  calc
    deriv (fun t : ℝ => partialX f t 1 1) 1 =
        deriv (fun _ : ℝ => (1 : ℝ)) 1 := hlocal.deriv_eq
    _ = 0 := (hasDerivAt_const (1 : ℝ) (1 : ℝ)).deriv

theorem gap11 :
    partialXY f 1 1 1 = -1 := by
  have hlocal :
      (fun t : ℝ => partialX f 1 t 1) =ᶠ[nhds (1 : ℝ)]
        (fun t : ℝ => 1 / t) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    have h :=
      (partial_formulas 1 t 1 one_ne_zero ht.ne' one_ne_zero).1
    have hpos : 0 < 1 / t := one_div_pos.mpr ht
    have hf : f 1 t 1 = 1 / t := by
      change Real.exp (Real.log (1 / t) / 1) = 1 / t
      simpa using Real.exp_log hpos
    rw [h, hf]
    ring
  have hd : HasDerivAt (fun t : ℝ => 1 / t) (-1) 1 := by
    convert
      (hasDerivAt_const (1 : ℝ) (1 : ℝ)).div
        (hasDerivAt_id (1 : ℝ)) (by norm_num)
      using 1 <;> norm_num
  unfold partialXY
  calc
    deriv (fun t : ℝ => partialX f 1 t 1) 1 =
        deriv (fun t : ℝ => 1 / t) 1 := hlocal.deriv_eq
    _ = -1 := hd.deriv

theorem gap12 :
    partialXZ f 1 1 1 = -1 := by
  have hlocal :
      (fun t : ℝ => partialX f 1 1 t) =ᶠ[nhds (1 : ℝ)]
        (fun t : ℝ => 1 / t) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    have h :=
      (partial_formulas 1 1 t one_ne_zero one_ne_zero ht.ne').1
    simpa [f] using h
  have hd : HasDerivAt (fun t : ℝ => 1 / t) (-1) 1 := by
    convert
      (hasDerivAt_const (1 : ℝ) (1 : ℝ)).div
        (hasDerivAt_id (1 : ℝ)) (by norm_num)
      using 1 <;> norm_num
  unfold partialXZ
  calc
    deriv (fun t : ℝ => partialX f 1 1 t) 1 =
        deriv (fun t : ℝ => 1 / t) 1 := hlocal.deriv_eq
    _ = -1 := hd.deriv

theorem gap13 :
    partialYY f 1 1 1 = 2 := by
  have hlocal :
      (fun t : ℝ => partialY f 1 t 1) =ᶠ[nhds (1 : ℝ)]
        (fun t : ℝ => -(1 / t ^ 2)) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact gap3 t ht
  have hd : HasDerivAt (fun t : ℝ => -(1 / t ^ 2)) 2 1 := by
    convert
      ((hasDerivAt_const (1 : ℝ) (1 : ℝ)).div
          ((hasDerivAt_id (1 : ℝ)).pow 2) (by norm_num)).neg
      using 1 <;> norm_num
  unfold partialYY
  calc
    deriv (fun t : ℝ => partialY f 1 t 1) 1 =
        deriv (fun t : ℝ => -(1 / t ^ 2)) 1 := hlocal.deriv_eq
    _ = 2 := hd.deriv

theorem gap14 :
    partialYZ f 1 1 1 = 1 := by
  have hlocal :
      (fun t : ℝ => partialY f 1 1 t) =ᶠ[nhds (1 : ℝ)]
        (fun t : ℝ => -(1 / t)) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    have h :=
      (partial_formulas 1 1 t one_ne_zero one_ne_zero ht.ne').2.1
    rw [h]
    simp [f, div_eq_mul_inv]
  have hd : HasDerivAt (fun t : ℝ => -(1 / t)) 1 1 := by
    convert
      ((hasDerivAt_const (1 : ℝ) (1 : ℝ)).div
          (hasDerivAt_id (1 : ℝ)) (by norm_num)).neg
      using 1 <;> norm_num
  unfold partialYZ
  calc
    deriv (fun t : ℝ => partialY f 1 1 t) 1 =
        deriv (fun t : ℝ => -(1 / t)) 1 := hlocal.deriv_eq
    _ = 1 := hd.deriv

theorem gap15 :
    partialZZ f 1 1 1 = 0 := by
  have hlocal :
      (fun t : ℝ => partialZ f 1 1 t) =ᶠ[nhds (1 : ℝ)]
        (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact gap5 t ht.ne'
  unfold partialZZ
  calc
    deriv (fun t : ℝ => partialZ f 1 1 t) 1 =
        deriv (fun _ : ℝ => (0 : ℝ)) 1 := hlocal.deriv_eq
    _ = 0 := (hasDerivAt_const (1 : ℝ) (0 : ℝ)).deriv

theorem gap16 (dx dy dz : ℝ) :
    secondDifferential f 1 1 1 dx dy dz = expandedSecond dx dy dz := by
  unfold secondDifferential expandedSecond
  rw [gap10, gap13, gap15, gap11, gap14, gap12]
  ring

theorem gap17 (dx dy dz : ℝ) :
    expandedSecond dx dy dz = factoredSecond dx dy dz := by
  unfold expandedSecond factoredSecond
  ring

theorem gap18 (dx dy dz : ℝ) :
    secondDifferential f 1 1 1 dx dy dz = factoredSecond dx dy dz := by
  calc
    secondDifferential f 1 1 1 dx dy dz = expandedSecond dx dy dz :=
      gap16 dx dy dz
    _ = factoredSecond dx dy dz := gap17 dx dy dz

end

end ProofGap.Exercise3242
