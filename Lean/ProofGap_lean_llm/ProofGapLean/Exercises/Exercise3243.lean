import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3243

noncomputable section

def u (x y z : ℝ) : ℝ :=
  Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)

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

def radialDifferential (x y z dx dy dz : ℝ) : ℝ :=
  x * dx + y * dy + z * dz

def firstForm (x y z dx dy dz : ℝ) : ℝ :=
  radialDifferential x y z dx dy dz / u x y z

def secondRaw (x y z dx dy dz : ℝ) : ℝ :=
  (1 / u x y z ^ 2) *
    (u x y z * (dx ^ 2 + dy ^ 2 + dz ^ 2) -
      radialDifferential x y z dx dy dz *
        differential u x y z dx dy dz)

def crossSquareSum (x y z dx dy dz : ℝ) : ℝ :=
  (x * dy - y * dx) ^ 2 +
    (y * dz - z * dy) ^ 2 +
    (z * dx - x * dz) ^ 2

def secondSimplified (x y z dx dy dz : ℝ) : ℝ :=
  crossSquareSum x y z dx dy dz / u x y z ^ 3

private theorem radialDerivatives (x y z : ℝ) (hu : 0 < u x y z) :
    partialX u x y z = x / u x y z ∧
    partialY u x y z = y / u x y z ∧
    partialZ u x y z = z / u x y z ∧
    partialXX u x y z = (u x y z ^ 2 - x ^ 2) / u x y z ^ 3 ∧
    partialXY u x y z = -(x * y) / u x y z ^ 3 ∧
    partialXZ u x y z = -(x * z) / u x y z ^ 3 ∧
    partialYY u x y z = (u x y z ^ 2 - y ^ 2) / u x y z ^ 3 ∧
    partialYZ u x y z = -(y * z) / u x y z ^ 3 ∧
    partialZZ u x y z = (u x y z ^ 2 - z ^ 2) / u x y z ^ 3 := by
  have derivX : ∀ (a b c : ℝ), 0 < u a b c →
      HasDerivAt (fun t => u t b c) (a / u a b c) a := by
    intro a b c h
    have hq : a ^ 2 + b ^ 2 + c ^ 2 ≠ 0 := by
      intro hzero
      apply h.ne'
      simp [u, hzero]
    have hpoly :
        HasDerivAt (fun t : ℝ => t ^ 2 + b ^ 2 + c ^ 2) (2 * a) a := by
      convert
        ((((hasDerivAt_id a).pow 2).add (hasDerivAt_const a (b ^ 2))).add
          (hasDerivAt_const a (c ^ 2))) using 1 <;> simp [id_eq] <;> ring_nf
    have hcomp := (Real.hasDerivAt_sqrt hq).comp a hpoly
    convert hcomp using 1
    change a / u a b c = 1 / (2 * u a b c) * (2 * a)
    field_simp [h.ne']
  have derivY : ∀ (a b c : ℝ), 0 < u a b c →
      HasDerivAt (fun t => u a t c) (b / u a b c) b := by
    intro a b c h
    have hq : a ^ 2 + b ^ 2 + c ^ 2 ≠ 0 := by
      intro hzero
      apply h.ne'
      simp [u, hzero]
    have hpoly :
        HasDerivAt (fun t : ℝ => a ^ 2 + t ^ 2 + c ^ 2) (2 * b) b := by
      convert
        (((hasDerivAt_const b (a ^ 2)).add ((hasDerivAt_id b).pow 2)).add
          (hasDerivAt_const b (c ^ 2))) using 1 <;> simp [id_eq] <;> ring_nf
    have hcomp := (Real.hasDerivAt_sqrt hq).comp b hpoly
    convert hcomp using 1
    change b / u a b c = 1 / (2 * u a b c) * (2 * b)
    field_simp [h.ne']
  have derivZ : ∀ (a b c : ℝ), 0 < u a b c →
      HasDerivAt (fun t => u a b t) (c / u a b c) c := by
    intro a b c h
    have hq : a ^ 2 + b ^ 2 + c ^ 2 ≠ 0 := by
      intro hzero
      apply h.ne'
      simp [u, hzero]
    have hpoly :
        HasDerivAt (fun t : ℝ => a ^ 2 + b ^ 2 + t ^ 2) (2 * c) c := by
      convert
        (((hasDerivAt_const c (a ^ 2)).add (hasDerivAt_const c (b ^ 2))).add
          ((hasDerivAt_id c).pow 2)) using 1 <;> simp [id_eq] <;> ring_nf
    have hcomp := (Real.hasDerivAt_sqrt hq).comp c hpoly
    convert hcomp using 1
    change c / u a b c = 1 / (2 * u a b c) * (2 * c)
    field_simp [h.ne']
  have hUx := derivX x y z hu
  have hUy := derivY x y z hu
  have hUz := derivZ x y z hu
  have hX : partialX u x y z = x / u x y z := by
    simpa [partialX] using hUx.deriv
  have hY : partialY u x y z = y / u x y z := by
    simpa [partialY] using hUy.deriv
  have hZ : partialZ u x y z = z / u x y z := by
    simpa [partialZ] using hUz.deriv
  have hevX : ∀ᶠ t in nhds x, 0 < u t y z :=
    hUx.continuousAt.eventually (isOpen_Ioi.mem_nhds hu)
  have hevY : ∀ᶠ t in nhds y, 0 < u x t z :=
    hUy.continuousAt.eventually (isOpen_Ioi.mem_nhds hu)
  have hevZ : ∀ᶠ t in nhds z, 0 < u x y t :=
    hUz.continuousAt.eventually (isOpen_Ioi.mem_nhds hu)
  have heqXX :
      (fun t => partialX u t y z) =ᶠ[nhds x] (fun t => t / u t y z) := by
    filter_upwards [hevX] with t ht
    simpa [partialX] using (derivX t y z ht).deriv
  have heqXY :
      (fun t => partialX u x t z) =ᶠ[nhds y] (fun t => x / u x t z) := by
    filter_upwards [hevY] with t ht
    simpa [partialX] using (derivX x t z ht).deriv
  have heqXZ :
      (fun t => partialX u x y t) =ᶠ[nhds z] (fun t => x / u x y t) := by
    filter_upwards [hevZ] with t ht
    simpa [partialX] using (derivX x y t ht).deriv
  have heqYY :
      (fun t => partialY u x t z) =ᶠ[nhds y] (fun t => t / u x t z) := by
    filter_upwards [hevY] with t ht
    simpa [partialY] using (derivY x t z ht).deriv
  have heqYZ :
      (fun t => partialY u x y t) =ᶠ[nhds z] (fun t => y / u x y t) := by
    filter_upwards [hevZ] with t ht
    simpa [partialY] using (derivY x y t ht).deriv
  have heqZZ :
      (fun t => partialZ u x y t) =ᶠ[nhds z] (fun t => t / u x y t) := by
    filter_upwards [hevZ] with t ht
    simpa [partialZ] using (derivZ x y t ht).deriv
  have hdXX : HasDerivAt (fun t => t / u t y z)
      ((u x y z ^ 2 - x ^ 2) / u x y z ^ 3) x := by
    convert (hasDerivAt_id x).div hUx hu.ne' using 1 <;>
      simp [id_eq] <;> field_simp [hu.ne'] <;> ring
  have hdXY : HasDerivAt (fun t => x / u x t z)
      (-(x * y) / u x y z ^ 3) y := by
    convert (hasDerivAt_const y x).div hUy hu.ne' using 1 <;>
      simp [id_eq] <;> field_simp [hu.ne'] <;> ring
  have hdXZ : HasDerivAt (fun t => x / u x y t)
      (-(x * z) / u x y z ^ 3) z := by
    convert (hasDerivAt_const z x).div hUz hu.ne' using 1 <;>
      simp [id_eq] <;> field_simp [hu.ne'] <;> ring
  have hdYY : HasDerivAt (fun t => t / u x t z)
      ((u x y z ^ 2 - y ^ 2) / u x y z ^ 3) y := by
    convert (hasDerivAt_id y).div hUy hu.ne' using 1 <;>
      simp [id_eq] <;> field_simp [hu.ne'] <;> ring
  have hdYZ : HasDerivAt (fun t => y / u x y t)
      (-(y * z) / u x y z ^ 3) z := by
    convert (hasDerivAt_const z y).div hUz hu.ne' using 1 <;>
      simp [id_eq] <;> field_simp [hu.ne'] <;> ring
  have hdZZ : HasDerivAt (fun t => t / u x y t)
      ((u x y z ^ 2 - z ^ 2) / u x y z ^ 3) z := by
    convert (hasDerivAt_id z).div hUz hu.ne' using 1 <;>
      simp [id_eq] <;> field_simp [hu.ne'] <;> ring
  have hXX : partialXX u x y z = (u x y z ^ 2 - x ^ 2) / u x y z ^ 3 := by
    change deriv (fun t => partialX u t y z) x = _
    rw [heqXX.deriv_eq]
    exact hdXX.deriv
  have hXY : partialXY u x y z = -(x * y) / u x y z ^ 3 := by
    change deriv (fun t => partialX u x t z) y = _
    rw [heqXY.deriv_eq]
    exact hdXY.deriv
  have hXZ : partialXZ u x y z = -(x * z) / u x y z ^ 3 := by
    change deriv (fun t => partialX u x y t) z = _
    rw [heqXZ.deriv_eq]
    exact hdXZ.deriv
  have hYY : partialYY u x y z = (u x y z ^ 2 - y ^ 2) / u x y z ^ 3 := by
    change deriv (fun t => partialY u x t z) y = _
    rw [heqYY.deriv_eq]
    exact hdYY.deriv
  have hYZ : partialYZ u x y z = -(y * z) / u x y z ^ 3 := by
    change deriv (fun t => partialY u x y t) z = _
    rw [heqYZ.deriv_eq]
    exact hdYZ.deriv
  have hZZ : partialZZ u x y z = (u x y z ^ 2 - z ^ 2) / u x y z ^ 3 := by
    change deriv (fun t => partialZ u x y t) z = _
    rw [heqZZ.deriv_eq]
    exact hdZZ.deriv
  exact ⟨hX, hY, hZ, hXX, hXY, hXZ, hYY, hYZ, hZZ⟩

theorem gap1 (x y z dx dy dz : ℝ) (hu : 0 < u x y z) :
    differential u x y z dx dy dz = firstForm x y z dx dy dz := by
  rcases radialDerivatives x y z hu with
    ⟨hX, hY, hZ, hXX, hXY, hXZ, hYY, hYZ, hZZ⟩
  unfold differential firstForm radialDifferential
  rw [hX, hY, hZ]
  field_simp [hu.ne']

theorem gap2 (x y z dx dy dz : ℝ) (hu : 0 < u x y z) :
    secondDifferential u x y z dx dy dz = secondRaw x y z dx dy dz := by
  rcases radialDerivatives x y z hu with
    ⟨hX, hY, hZ, hXX, hXY, hXZ, hYY, hYZ, hZZ⟩
  unfold secondDifferential secondRaw
  rw [hXX, hYY, hZZ, hXY, hYZ, hXZ, gap1 x y z dx dy dz hu]
  unfold firstForm radialDifferential
  field_simp [hu.ne'] <;> ring

theorem gap3 (x y z dx dy dz : ℝ) (hu : 0 < u x y z) :
    secondRaw x y z dx dy dz = secondSimplified x y z dx dy dz := by
  unfold secondRaw
  rw [gap1 x y z dx dy dz hu]
  have hq : 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 := by positivity
  have hu_sq : u x y z ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := by
    unfold u
    exact Real.sq_sqrt hq
  have hcross :
      crossSquareSum x y z dx dy dz =
        u x y z ^ 2 * (dx ^ 2 + dy ^ 2 + dz ^ 2) -
          radialDifferential x y z dx dy dz ^ 2 := by
    rw [hu_sq]
    unfold crossSquareSum radialDifferential
    ring
  unfold secondSimplified firstForm
  rw [hcross]
  unfold radialDifferential
  field_simp [hu.ne'] <;> ring

theorem gap4 (x y z dx dy dz : ℝ) (hu : 0 < u x y z) :
    secondDifferential u x y z dx dy dz =
      secondSimplified x y z dx dy dz := by
  exact (gap2 x y z dx dy dz hu).trans (gap3 x y z dx dy dz hu)

theorem gap5 (x y z dx dy dz : ℝ) (hu : 0 < u x y z) :
    0 ≤ secondDifferential u x y z dx dy dz := by
  rw [gap4 x y z dx dy dz hu]
  unfold secondSimplified crossSquareSum
  apply div_nonneg
  · positivity
  · positivity

theorem gap6 (x y z dx dy dz : ℝ) (hu : 0 < u x y z) :
    0 ≤ secondDifferential u x y z dx dy dz := by
  exact gap5 x y z dx dy dz hu

end

end ProofGap.Exercise3243
