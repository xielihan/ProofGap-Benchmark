import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3237

noncomputable section

def radialSq (x y : ℝ) : ℝ :=
  x ^ 2 + y ^ 2

def u (x y : ℝ) : ℝ :=
  Real.sqrt (radialSq x y)

def admissible (x y : ℝ) : Prop :=
  0 < radialSq x y

def radialThreeHalves (x y : ℝ) : ℝ :=
  Real.rpow (radialSq x y) (3 / 2 : ℝ)

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f t y) x

def partialXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f x t) y

def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY f x t) y

def differential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialX f x y * dx + partialY f x y * dy

def secondDifferential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialXX f x y * dx ^ 2 +
    2 * partialXY f x y * dx * dy +
    partialYY f x y * dy ^ 2

def firstForm (x y dx dy : ℝ) : ℝ :=
  (x * dx + y * dy) / Real.sqrt (radialSq x y)

def secondRaw (x y dx dy : ℝ) : ℝ :=
  (dx ^ 2 + dy ^ 2) / Real.sqrt (radialSq x y) -
    (x * dx + y * dy) ^ 2 / radialThreeHalves x y

def secondSimplified (x y dx dy : ℝ) : ℝ :=
  (y * dx - x * dy) ^ 2 / radialThreeHalves x y

private theorem radialThreeHalves_eq_mul_sqrt
    (x y : ℝ) (h : admissible x y) :
    radialThreeHalves x y = radialSq x y * Real.sqrt (radialSq x y) := by
  have hr : 0 < radialSq x y := h
  unfold radialThreeHalves
  calc
    Real.rpow (radialSq x y) (3 / 2 : ℝ) =
        Real.exp (Real.log (radialSq x y) * (3 / 2 : ℝ)) := by
      exact Real.rpow_def_of_pos hr (3 / 2 : ℝ)
    _ = Real.exp (Real.log (radialSq x y)) *
        Real.exp (Real.log (radialSq x y) * (1 / 2 : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = radialSq x y * Real.rpow (radialSq x y) (1 / 2 : ℝ) := by
      rw [Real.exp_log hr]
      congr 1
      exact (Real.rpow_def_of_pos hr (1 / 2 : ℝ)).symm
    _ = radialSq x y * Real.sqrt (radialSq x y) := by
      congr 1
      exact (Real.sqrt_eq_rpow (radialSq x y)).symm

private theorem hasDerivAt_u_x_of_pos
    (x y : ℝ) (h : admissible x y) :
    HasDerivAt (fun t => u t y)
      (x / Real.sqrt (radialSq x y)) x := by
  have hr : 0 < x ^ 2 + y ^ 2 := by
    simpa [admissible, radialSq] using h
  unfold u radialSq
  convert (Real.hasDerivAt_sqrt (ne_of_gt hr)).comp x
      (((hasDerivAt_id x).pow 2).add_const (y ^ 2)) using 1 <;>
    simp only [id_eq, Nat.cast_ofNat, pow_one, mul_one, add_zero] <;>
    field_simp [Real.sqrt_ne_zero'.mpr hr] <;>
    ring

private theorem hasDerivAt_u_y_of_pos
    (x y : ℝ) (h : admissible x y) :
    HasDerivAt (fun t => u x t)
      (y / Real.sqrt (radialSq x y)) y := by
  have hr : 0 < x ^ 2 + y ^ 2 := by
    simpa [admissible, radialSq] using h
  unfold u radialSq
  convert (Real.hasDerivAt_sqrt (ne_of_gt hr)).comp y
      ((hasDerivAt_const y (x ^ 2)).add ((hasDerivAt_id y).pow 2)) using 1 <;>
    simp only [id_eq, Nat.cast_ofNat, pow_one, mul_one, zero_add] <;>
    field_simp [Real.sqrt_ne_zero'.mpr hr] <;>
    ring

private theorem partialX_u_of_pos
    (x y : ℝ) (h : admissible x y) :
    partialX u x y = x / Real.sqrt (radialSq x y) := by
  exact (hasDerivAt_u_x_of_pos x y h).deriv

private theorem partialY_u_of_pos
    (x y : ℝ) (h : admissible x y) :
    partialY u x y = y / Real.sqrt (radialSq x y) := by
  exact (hasDerivAt_u_y_of_pos x y h).deriv

private theorem partialXX_u_of_pos
    (x y : ℝ) (h : admissible x y) :
    partialXX u x y =
      1 / Real.sqrt (radialSq x y) -
        x ^ 2 / radialThreeHalves x y := by
  have hr : 0 < radialSq x y := h
  have hc : ContinuousAt (fun t : ℝ => radialSq t y) x := by
    unfold radialSq
    exact (continuousAt_id.pow 2).add continuousAt_const
  have hev : ∀ᶠ t in nhds x, 0 < radialSq t y := by
    have hm := hc.eventually (isOpen_Ioi.mem_nhds hr)
    simpa only [Set.mem_Ioi] using hm
  have heq :
      (fun t => partialX u t y) =ᶠ[nhds x] (fun t => t / u t y) :=
    hev.mono (fun t ht => by
      simpa only [u] using partialX_u_of_pos t y ht)
  have hs := hasDerivAt_u_x_of_pos x y h
  have hg := (hasDerivAt_id x).div hs
    (by simpa only [u] using Real.sqrt_ne_zero'.mpr hr)
  unfold partialXX
  rw [heq.deriv_eq]
  change deriv ((id : ℝ → ℝ) / (fun t => u t y)) x =
    1 / Real.sqrt (radialSq x y) -
      x ^ 2 / radialThreeHalves x y
  rw [hg.deriv]
  simp only [id_eq]
  rw [radialThreeHalves_eq_mul_sqrt x y h]
  unfold u
  field_simp [Real.sqrt_ne_zero'.mpr hr, ne_of_gt hr,
    Real.sq_sqrt (le_of_lt hr)]
  rw [Real.sq_sqrt (le_of_lt hr)]
  ring

private theorem partialXY_u_of_pos
    (x y : ℝ) (h : admissible x y) :
    partialXY u x y =
      -(x * y) / radialThreeHalves x y := by
  have hr : 0 < radialSq x y := h
  have hc : ContinuousAt (fun t : ℝ => radialSq x t) y := by
    unfold radialSq
    exact continuousAt_const.add (continuousAt_id.pow 2)
  have hev : ∀ᶠ t in nhds y, 0 < radialSq x t := by
    have hm := hc.eventually (isOpen_Ioi.mem_nhds hr)
    simpa only [Set.mem_Ioi] using hm
  have heq :
      (fun t => partialX u x t) =ᶠ[nhds y] (fun t => x / u x t) :=
    hev.mono (fun t ht => by
      simpa only [u] using partialX_u_of_pos x t ht)
  have hs := hasDerivAt_u_y_of_pos x y h
  have hg := (hasDerivAt_const y x).div hs
    (by simpa only [u] using Real.sqrt_ne_zero'.mpr hr)
  unfold partialXY
  rw [heq.deriv_eq]
  change deriv ((fun _ : ℝ => x) / (fun t => u x t)) y =
    -(x * y) / radialThreeHalves x y
  rw [hg.deriv]
  rw [radialThreeHalves_eq_mul_sqrt x y h]
  unfold u
  field_simp [Real.sqrt_ne_zero'.mpr hr, ne_of_gt hr,
    Real.sq_sqrt (le_of_lt hr)]
  rw [Real.sq_sqrt (le_of_lt hr)]
  ring

private theorem partialYY_u_of_pos
    (x y : ℝ) (h : admissible x y) :
    partialYY u x y =
      1 / Real.sqrt (radialSq x y) -
        y ^ 2 / radialThreeHalves x y := by
  have hr : 0 < radialSq x y := h
  have hc : ContinuousAt (fun t : ℝ => radialSq x t) y := by
    unfold radialSq
    exact continuousAt_const.add (continuousAt_id.pow 2)
  have hev : ∀ᶠ t in nhds y, 0 < radialSq x t := by
    have hm := hc.eventually (isOpen_Ioi.mem_nhds hr)
    simpa only [Set.mem_Ioi] using hm
  have heq :
      (fun t => partialY u x t) =ᶠ[nhds y] (fun t => t / u x t) :=
    hev.mono (fun t ht => by
      simpa only [u] using partialY_u_of_pos x t ht)
  have hs := hasDerivAt_u_y_of_pos x y h
  have hg := (hasDerivAt_id y).div hs
    (by simpa only [u] using Real.sqrt_ne_zero'.mpr hr)
  unfold partialYY
  rw [heq.deriv_eq]
  change deriv ((id : ℝ → ℝ) / (fun t => u x t)) y =
    1 / Real.sqrt (radialSq x y) -
      y ^ 2 / radialThreeHalves x y
  rw [hg.deriv]
  simp only [id_eq]
  rw [radialThreeHalves_eq_mul_sqrt x y h]
  unfold u
  field_simp [Real.sqrt_ne_zero'.mpr hr, ne_of_gt hr,
    Real.sq_sqrt (le_of_lt hr)]
  rw [Real.sq_sqrt (le_of_lt hr)]
  ring

theorem gap1 :
    ∀ x y dx dy : ℝ, admissible x y →
      differential u x y dx dy = firstForm x y dx dy := by
  intro x y dx dy h
  have hr : 0 < radialSq x y := h
  unfold differential firstForm
  rw [partialX_u_of_pos x y h, partialY_u_of_pos x y h]
  field_simp [Real.sqrt_ne_zero'.mpr hr] <;> ring

theorem gap2 :
    ∀ x y dx dy : ℝ, admissible x y →
      secondDifferential u x y dx dy = secondRaw x y dx dy := by
  intro x y dx dy h
  have hr : 0 < radialSq x y := h
  unfold secondDifferential secondRaw
  rw [partialXX_u_of_pos x y h, partialXY_u_of_pos x y h,
    partialYY_u_of_pos x y h]
  rw [radialThreeHalves_eq_mul_sqrt x y h]
  field_simp [Real.sqrt_ne_zero'.mpr hr, ne_of_gt hr,
    Real.sq_sqrt (le_of_lt hr)] <;> ring

theorem gap3 :
    ∀ x y dx dy : ℝ, admissible x y →
      secondRaw x y dx dy = secondSimplified x y dx dy := by
  intro x y dx dy h
  have hr : 0 < radialSq x y := h
  unfold secondRaw secondSimplified
  rw [radialThreeHalves_eq_mul_sqrt x y h]
  field_simp [Real.sqrt_ne_zero'.mpr hr, ne_of_gt hr,
    Real.sq_sqrt (le_of_lt hr)] <;>
    unfold radialSq <;>
    ring

theorem gap4 :
    ∀ x y dx dy : ℝ, admissible x y →
      secondDifferential u x y dx dy =
        secondSimplified x y dx dy := by
  intro x y dx dy h
  calc
    secondDifferential u x y dx dy = secondRaw x y dx dy :=
      gap2 x y dx dy h
    _ = secondSimplified x y dx dy := gap3 x y dx dy h

end

end ProofGap.Exercise3237
