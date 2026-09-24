import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1172

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def y (x : ℝ) : ℝ := 1 / Real.sqrt x
def differential (n : ℕ) (f : ℝ → ℝ) (x dx : ℝ) : ℝ :=
  nthDeriv n f x * dx ^ n
def rawCoeff (x : ℝ) : ℝ :=
  (-1 / 2 : ℝ) * (-3 / 2 : ℝ) * (-5 / 2 : ℝ) *
    Real.rpow x (-7 / 2 : ℝ)

private theorem third_deriv_y_of_pos (x : ℝ) (hx : 0 < x) :
    nthDeriv 3 y x =
      (-15 / 8 : ℝ) * Real.rpow x (-7 / 2 : ℝ) := by
  let g0 : ℝ → ℝ := fun t => Real.rpow t (-1 / 2 : ℝ)
  let g1 : ℝ → ℝ := fun t => (-1 / 2 : ℝ) * Real.rpow t (-3 / 2 : ℝ)
  let g2 : ℝ → ℝ := fun t => (3 / 4 : ℝ) * Real.rpow t (-5 / 2 : ℝ)
  let g3 : ℝ → ℝ := fun t => (-15 / 8 : ℝ) * Real.rpow t (-7 / 2 : ℝ)
  have hy0 : ∀ z : ℝ, 0 < z → y z = g0 z := by
    intro z hz
    calc
      y z = (Real.sqrt z)⁻¹ := by simp [y, one_div]
      _ = (Real.rpow z (1 / 2 : ℝ))⁻¹ := by
        congr 1
        exact Real.sqrt_eq_rpow z
      _ = Real.rpow z (-(1 / 2 : ℝ)) :=
        (Real.rpow_neg hz.le (1 / 2 : ℝ)).symm
      _ = g0 z := by
        dsimp [g0]
        congr 1
        ring
  have hg0 : ∀ z : ℝ, 0 < z → HasDerivAt g0 (g1 z) z := by
    intro z hz
    have h : HasDerivAt
        (fun t : ℝ => Real.rpow t (-1 / 2 : ℝ))
        ((-1 / 2 : ℝ) * Real.rpow z ((-1 / 2 : ℝ) - 1)) z :=
      Real.hasDerivAt_rpow_const (p := (-1 / 2 : ℝ))
        (Or.inl (ne_of_gt hz))
    convert h using 1 <;> norm_num [g0, g1]
  have hg1 : ∀ z : ℝ, 0 < z → HasDerivAt g1 (g2 z) z := by
    intro z hz
    have hp : HasDerivAt
        (fun t : ℝ => Real.rpow t (-3 / 2 : ℝ))
        ((-3 / 2 : ℝ) * Real.rpow z ((-3 / 2 : ℝ) - 1)) z :=
      Real.hasDerivAt_rpow_const (p := (-3 / 2 : ℝ))
        (Or.inl (ne_of_gt hz))
    have h := (hasDerivAt_const z (-1 / 2 : ℝ)).mul hp
    convert h using 1 <;> norm_num [g1, g2] <;> ring
  have hg2 : ∀ z : ℝ, 0 < z → HasDerivAt g2 (g3 z) z := by
    intro z hz
    have hp : HasDerivAt
        (fun t : ℝ => Real.rpow t (-5 / 2 : ℝ))
        ((-5 / 2 : ℝ) * Real.rpow z ((-5 / 2 : ℝ) - 1)) z :=
      Real.hasDerivAt_rpow_const (p := (-5 / 2 : ℝ))
        (Or.inl (ne_of_gt hz))
    have h := (hasDerivAt_const z (3 / 4 : ℝ)).mul hp
    convert h using 1 <;> norm_num [g2, g3] <;> ring
  have hfirst : ∀ z : ℝ, 0 < z → deriv y z = g1 z := by
    intro z hz
    have hlocal : y =ᶠ[nhds z] g0 := by
      filter_upwards [eventually_gt_nhds hz] with w hw
      exact hy0 w hw
    calc
      deriv y z = deriv g0 z := hlocal.deriv_eq
      _ = g1 z := (hg0 z hz).deriv
  have hsecond : ∀ z : ℝ, 0 < z → deriv (deriv y) z = g2 z := by
    intro z hz
    have hlocal : deriv y =ᶠ[nhds z] g1 := by
      filter_upwards [eventually_gt_nhds hz] with w hw
      exact hfirst w hw
    calc
      deriv (deriv y) z = deriv g1 z := hlocal.deriv_eq
      _ = g2 z := (hg1 z hz).deriv
  have hlocal2 : deriv (deriv y) =ᶠ[nhds x] g2 := by
    filter_upwards [eventually_gt_nhds hx] with z hz
    exact hsecond z hz
  change deriv (deriv (deriv y)) x =
    (-15 / 8 : ℝ) * Real.rpow x (-7 / 2 : ℝ)
  calc
    deriv (deriv (deriv y)) x = deriv g2 x := hlocal2.deriv_eq
    _ = g3 x := (hg2 x hx).deriv
    _ = (-15 / 8 : ℝ) * Real.rpow x (-7 / 2 : ℝ) := rfl

private theorem rpow_neg_seven_halves (x : ℝ) (hx : 0 < x) :
    Real.rpow x (-7 / 2 : ℝ) = (x ^ 3 * Real.sqrt x)⁻¹ := by
  have hneg :
      Real.rpow x (-(7 / 2 : ℝ)) = (Real.rpow x (7 / 2 : ℝ))⁻¹ := by
    exact Real.rpow_neg hx.le (7 / 2 : ℝ)
  have hadd :
      Real.rpow x ((3 : ℝ) + 1 / 2) =
        Real.rpow x (3 : ℝ) * Real.rpow x (1 / 2 : ℝ) := by
    exact Real.rpow_add hx (3 : ℝ) (1 / 2 : ℝ)
  have hnat : Real.rpow x (3 : ℝ) = x ^ 3 := by
    exact Real.rpow_natCast x 3
  have hsqrt : Real.rpow x (1 / 2 : ℝ) = Real.sqrt x := by
    exact (Real.sqrt_eq_rpow x).symm
  calc
    Real.rpow x (-7 / 2 : ℝ) = Real.rpow x (-(7 / 2 : ℝ)) := by
      congr 1
      ring
    _ = (Real.rpow x (7 / 2 : ℝ))⁻¹ := hneg
    _ = (Real.rpow x ((3 : ℝ) + 1 / 2))⁻¹ := by norm_num
    _ = (Real.rpow x (3 : ℝ) * Real.rpow x (1 / 2 : ℝ))⁻¹ := by rw [hadd]
    _ = (x ^ 3 * Real.rpow x (1 / 2 : ℝ))⁻¹ := by rw [hnat]
    _ = (x ^ 3 * Real.sqrt x)⁻¹ := by rw [hsqrt]

theorem gap1 (x dx : ℝ) (hx : 0 < x) :
    differential 3 y x dx = rawCoeff x * dx ^ 3 := by
  unfold differential
  rw [third_deriv_y_of_pos x hx]
  unfold rawCoeff
  ring

theorem gap2 (x dx : ℝ) (hx : 0 < x) :
    rawCoeff x * dx ^ 3 =
      (-15 / (8 * x ^ 3 * Real.sqrt x)) * dx ^ 3 := by
  unfold rawCoeff
  rw [rpow_neg_seven_halves x hx]
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hs0 : Real.sqrt x ≠ 0 := Real.sqrt_ne_zero'.mpr hx
  field_simp [hx0, hs0] <;> ring

theorem gap3 (x dx : ℝ) (hx : 0 < x) :
    differential 3 y x dx =
      (-15 / (8 * x ^ 3 * Real.sqrt x)) * dx ^ 3 := by
  calc
    differential 3 y x dx = rawCoeff x * dx ^ 3 := gap1 x dx hx
    _ = (-15 / (8 * x ^ 3 * Real.sqrt x)) * dx ^ 3 := gap2 x dx hx

end

end ProofGap.Exercise1172
