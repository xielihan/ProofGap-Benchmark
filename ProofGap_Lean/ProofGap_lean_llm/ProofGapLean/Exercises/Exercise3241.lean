import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3241

noncomputable section

def u (x y z : ℝ) : ℝ := z / (x ^ 2 + y ^ 2)

def partialX (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f t y z) x

def partialY (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f x t z) y

def partialZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f x y t) z

def partialXX (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialX f t y z) x

def partialXY (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialX f x t z) y

def partialXZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialX f x y t) z

def partialYY (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialY f x t z) y

def partialYZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialY f x y t) z

def partialZZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialZ f x y t) z

def differential (f : ℝ → ℝ → ℝ → ℝ)
    (x y z dx dy dz : ℝ) : ℝ :=
  partialX f x y z * dx + partialY f x y z * dy + partialZ f x y z * dz

def secondDifferential (f : ℝ → ℝ → ℝ → ℝ)
    (x y z dx dy dz : ℝ) : ℝ :=
  partialXX f x y z * dx ^ 2 +
    partialYY f x y z * dy ^ 2 +
    partialZZ f x y z * dz ^ 2 +
    2 * partialXY f x y z * dx * dy +
    2 * partialYZ f x y z * dy * dz +
    2 * partialXZ f x y z * dz * dx

def radiusSquared (x y : ℝ) : ℝ := x ^ 2 + y ^ 2

def radialDifferential (x y dx dy : ℝ) : ℝ := x * dx + y * dy

def firstExpanded (x y z dx dy dz : ℝ) : ℝ :=
  -(2 * z / radiusSquared x y ^ 2) * radialDifferential x y dx dy +
    dz / radiusSquared x y

def firstCombined (x y z dx dy dz : ℝ) : ℝ :=
  (radiusSquared x y * dz -
      2 * z * radialDifferential x y dx dy) /
    radiusSquared x y ^ 2

def secondRaw (x y z dx dy dz : ℝ) : ℝ :=
  let r := radiusSquared x y
  let q := radialDifferential x y dx dy
  (r ^ 2 *
        (2 * q * dz - 2 * q * dz - 2 * z * (dx ^ 2 + dy ^ 2)) -
      4 * r * q * (r * dz - 2 * z * q)) /
    r ^ 4

def secondSimplified (x y z dx dy dz : ℝ) : ℝ :=
  let r := radiusSquared x y
  (2 * z * (3 * x ^ 2 - y ^ 2) * dx ^ 2 +
      16 * z * x * y * dx * dy +
      2 * z * (3 * y ^ 2 - x ^ 2) * dy ^ 2 -
      4 * r * radialDifferential x y dx dy * dz) /
    r ^ 3

private theorem eventually_sq_add_sq_ne (a b : ℝ)
    (h : a ^ 2 + b ^ 2 ≠ 0) :
    ∀ᶠ t in nhds a, t ^ 2 + b ^ 2 ≠ 0 := by
  by_cases hb : b = 0
  · subst b
    have ha : a ≠ 0 := by
      intro ha
      apply h
      simp [ha]
    filter_upwards [eventually_ne_nhds ha] with t ht
    simp [ht]
  · apply Filter.Eventually.of_forall
    intro t ht
    nlinarith [sq_nonneg t, sq_pos_of_ne_zero hb]

private theorem partialX_u_formula (x y z : ℝ)
    (h : x ^ 2 + y ^ 2 ≠ 0) :
    partialX u x y z = -(2 * z * x / (x ^ 2 + y ^ 2) ^ 2) := by
  unfold partialX u
  have hden : HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * x) x := by
    convert (((hasDerivAt_id x).mul (hasDerivAt_id x)).add
      (hasDerivAt_const x (y ^ 2))) using 1
    · funext t
      simp [pow_two]
    · simp [two_mul, mul_two]
  have hd := (hasDerivAt_const x z).div hden h
  convert hd.deriv using 1 <;> field_simp [h] <;> ring

private theorem partialY_u_formula (x y z : ℝ)
    (h : x ^ 2 + y ^ 2 ≠ 0) :
    partialY u x y z = -(2 * z * y / (x ^ 2 + y ^ 2) ^ 2) := by
  unfold partialY u
  have hden : HasDerivAt (fun t : ℝ => x ^ 2 + t ^ 2) (2 * y) y := by
    convert ((hasDerivAt_const y (x ^ 2)).add
      ((hasDerivAt_id y).mul (hasDerivAt_id y))) using 1
    · funext t
      simp [pow_two]
    · simp [two_mul, mul_two]
  have hd := (hasDerivAt_const y z).div hden h
  convert hd.deriv using 1 <;> field_simp [h] <;> ring

private theorem partialZ_u_formula (x y z : ℝ)
    (h : x ^ 2 + y ^ 2 ≠ 0) :
    partialZ u x y z = 1 / (x ^ 2 + y ^ 2) := by
  unfold partialZ u
  have hd :=
    (hasDerivAt_id z).div
      (hasDerivAt_const z (x ^ 2 + y ^ 2)) h
  convert hd.deriv using 1 <;> field_simp [h] <;> ring

private theorem partialXX_u_formula (x y z : ℝ)
    (h : x ^ 2 + y ^ 2 ≠ 0) :
    partialXX u x y z =
      2 * z * (3 * x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2) ^ 3 := by
  unfold partialXX
  have he :
      (fun t => partialX u t y z) =ᶠ[nhds x]
        (fun t => -(2 * z * t / (t ^ 2 + y ^ 2) ^ 2)) := by
    filter_upwards [eventually_sq_add_sq_ne x y h] with t ht
    exact partialX_u_formula t y z ht
  rw [Filter.EventuallyEq.deriv_eq he]
  have hbase : HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * x) x := by
    convert (((hasDerivAt_id x).mul (hasDerivAt_id x)).add
      (hasDerivAt_const x (y ^ 2))) using 1
    · funext t
      simp [pow_two]
    · simp [two_mul, mul_two]
  have hden : HasDerivAt (fun t : ℝ => (t ^ 2 + y ^ 2) ^ 2)
      (4 * x * (x ^ 2 + y ^ 2)) x := by
    convert hbase.mul hbase using 1
    · funext t
      simp [pow_two]
    · ring
  have hnum : HasDerivAt (fun t : ℝ => 2 * z * t) (2 * z) x := by
    convert (hasDerivAt_const x (2 * z)).mul (hasDerivAt_id x) using 1 <;> ring
  have hd := (hnum.div hden (pow_ne_zero 2 h)).neg
  convert hd.deriv using 1 <;> field_simp [h] <;> ring

private theorem partialXY_u_formula (x y z : ℝ)
    (h : x ^ 2 + y ^ 2 ≠ 0) :
    partialXY u x y z =
      8 * z * x * y / (x ^ 2 + y ^ 2) ^ 3 := by
  unfold partialXY
  have h' : y ^ 2 + x ^ 2 ≠ 0 := by
    simpa [add_comm] using h
  have he :
      (fun t => partialX u x t z) =ᶠ[nhds y]
        (fun t => -(2 * z * x / (x ^ 2 + t ^ 2) ^ 2)) := by
    filter_upwards [eventually_sq_add_sq_ne y x h'] with t ht
    exact partialX_u_formula x t z (by simpa [add_comm] using ht)
  rw [Filter.EventuallyEq.deriv_eq he]
  have hbase : HasDerivAt (fun t : ℝ => x ^ 2 + t ^ 2) (2 * y) y := by
    convert ((hasDerivAt_const y (x ^ 2)).add
      ((hasDerivAt_id y).mul (hasDerivAt_id y))) using 1
    · funext t
      simp [pow_two]
    · simp [two_mul, mul_two]
  have hden : HasDerivAt (fun t : ℝ => (x ^ 2 + t ^ 2) ^ 2)
      (4 * y * (x ^ 2 + y ^ 2)) y := by
    convert hbase.mul hbase using 1
    · funext t
      simp [pow_two]
    · ring
  have hd := ((hasDerivAt_const y (2 * z * x)).div
    hden (pow_ne_zero 2 h)).neg
  convert hd.deriv using 1 <;> field_simp [h] <;> ring

private theorem partialXZ_u_formula (x y z : ℝ)
    (h : x ^ 2 + y ^ 2 ≠ 0) :
    partialXZ u x y z = -(2 * x / (x ^ 2 + y ^ 2) ^ 2) := by
  unfold partialXZ
  have he :
      (fun t => partialX u x y t) =
        (fun t => -(2 * t * x / (x ^ 2 + y ^ 2) ^ 2)) := by
    funext t
    exact partialX_u_formula x y t h
  rw [he]
  have hd :=
    ((((hasDerivAt_const z 2).mul (hasDerivAt_id z)).mul
      (hasDerivAt_const z x)).div
      (hasDerivAt_const z ((x ^ 2 + y ^ 2) ^ 2))
      (pow_ne_zero 2 h)).neg
  convert hd.deriv using 1 <;> field_simp [h] <;> ring

private theorem partialYY_u_formula (x y z : ℝ)
    (h : x ^ 2 + y ^ 2 ≠ 0) :
    partialYY u x y z =
      2 * z * (3 * y ^ 2 - x ^ 2) / (x ^ 2 + y ^ 2) ^ 3 := by
  unfold partialYY
  have h' : y ^ 2 + x ^ 2 ≠ 0 := by
    simpa [add_comm] using h
  have he :
      (fun t => partialY u x t z) =ᶠ[nhds y]
        (fun t => -(2 * z * t / (x ^ 2 + t ^ 2) ^ 2)) := by
    filter_upwards [eventually_sq_add_sq_ne y x h'] with t ht
    exact partialY_u_formula x t z (by simpa [add_comm] using ht)
  rw [Filter.EventuallyEq.deriv_eq he]
  have hbase : HasDerivAt (fun t : ℝ => x ^ 2 + t ^ 2) (2 * y) y := by
    convert ((hasDerivAt_const y (x ^ 2)).add
      ((hasDerivAt_id y).mul (hasDerivAt_id y))) using 1
    · funext t
      simp [pow_two]
    · simp [two_mul, mul_two]
  have hden : HasDerivAt (fun t : ℝ => (x ^ 2 + t ^ 2) ^ 2)
      (4 * y * (x ^ 2 + y ^ 2)) y := by
    convert hbase.mul hbase using 1
    · funext t
      simp [pow_two]
    · ring
  have hnum : HasDerivAt (fun t : ℝ => 2 * z * t) (2 * z) y := by
    convert (hasDerivAt_const y (2 * z)).mul (hasDerivAt_id y) using 1 <;> ring
  have hd := (hnum.div hden (pow_ne_zero 2 h)).neg
  convert hd.deriv using 1 <;> field_simp [h] <;> ring

private theorem partialYZ_u_formula (x y z : ℝ)
    (h : x ^ 2 + y ^ 2 ≠ 0) :
    partialYZ u x y z = -(2 * y / (x ^ 2 + y ^ 2) ^ 2) := by
  unfold partialYZ
  have he :
      (fun t => partialY u x y t) =
        (fun t => -(2 * t * y / (x ^ 2 + y ^ 2) ^ 2)) := by
    funext t
    exact partialY_u_formula x y t h
  rw [he]
  have hd :=
    ((((hasDerivAt_const z 2).mul (hasDerivAt_id z)).mul
      (hasDerivAt_const z y)).div
      (hasDerivAt_const z ((x ^ 2 + y ^ 2) ^ 2))
      (pow_ne_zero 2 h)).neg
  convert hd.deriv using 1 <;> field_simp [h] <;> ring

private theorem partialZZ_u_formula (x y z : ℝ)
    (h : x ^ 2 + y ^ 2 ≠ 0) :
    partialZZ u x y z = 0 := by
  unfold partialZZ
  rw [show (fun t => partialZ u x y t) =
      (fun _ => 1 / (x ^ 2 + y ^ 2)) by
    funext t
    exact partialZ_u_formula x y t h]
  simpa using (hasDerivAt_const z (1 / (x ^ 2 + y ^ 2))).deriv

theorem gap1 (x y z dx dy dz : ℝ) (hr : radiusSquared x y ≠ 0) :
    differential u x y z dx dy dz = firstExpanded x y z dx dy dz := by
  have h : x ^ 2 + y ^ 2 ≠ 0 := by
    simpa [radiusSquared] using hr
  unfold differential
  rw [partialX_u_formula x y z h, partialY_u_formula x y z h,
    partialZ_u_formula x y z h]
  simp only [firstExpanded, radiusSquared, radialDifferential]
  field_simp [h]
  ring

theorem gap2 (x y z dx dy dz : ℝ) (hr : radiusSquared x y ≠ 0) :
    firstExpanded x y z dx dy dz = firstCombined x y z dx dy dz := by
  have h : x ^ 2 + y ^ 2 ≠ 0 := by
    simpa [radiusSquared] using hr
  simp only [firstExpanded, firstCombined, radiusSquared, radialDifferential]
  field_simp [h]
  ring

theorem gap3 (x y z dx dy dz : ℝ) (hr : radiusSquared x y ≠ 0) :
    differential u x y z dx dy dz = firstCombined x y z dx dy dz := by
  exact (gap1 x y z dx dy dz hr).trans (gap2 x y z dx dy dz hr)

theorem gap4 (x y z dx dy dz : ℝ) (hr : radiusSquared x y ≠ 0) :
    secondDifferential u x y z dx dy dz = secondRaw x y z dx dy dz := by
  have h : x ^ 2 + y ^ 2 ≠ 0 := by
    simpa [radiusSquared] using hr
  unfold secondDifferential
  rw [partialXX_u_formula x y z h, partialYY_u_formula x y z h,
    partialZZ_u_formula x y z h, partialXY_u_formula x y z h,
    partialYZ_u_formula x y z h, partialXZ_u_formula x y z h]
  simp only [secondRaw, radiusSquared, radialDifferential]
  field_simp [h]
  ring

theorem gap5 (x y z dx dy dz : ℝ) (hr : radiusSquared x y ≠ 0) :
    secondRaw x y z dx dy dz = secondSimplified x y z dx dy dz := by
  have h : x ^ 2 + y ^ 2 ≠ 0 := by
    simpa [radiusSquared] using hr
  simp only [secondRaw, secondSimplified, radiusSquared, radialDifferential]
  field_simp [h]
  ring

theorem gap6 (x y z dx dy dz : ℝ) (hr : radiusSquared x y ≠ 0) :
    secondDifferential u x y z dx dy dz =
      secondSimplified x y z dx dy dz := by
  exact (gap4 x y z dx dy dz hr).trans (gap5 x y z dx dy dz hr)

end

end ProofGap.Exercise3241
