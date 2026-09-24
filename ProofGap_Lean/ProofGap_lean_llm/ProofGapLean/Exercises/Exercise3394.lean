import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3394

noncomputable section

def uncurry3 (u : ℝ → ℝ → ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  u p.1 p.2.1 p.2.2

def partialX (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => u t y z) x

def partialY (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => u x t z) y

def partialZ (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => u x y t) z

def differential (u : ℝ → ℝ → ℝ → ℝ)
    (x y z dx dy dz : ℝ) : ℝ :=
  partialX u x y z * dx +
    partialY u x y z * dy +
    partialZ u x y z * dz

def solvedDifferential (u : ℝ → ℝ → ℝ → ℝ)
    (x y z dx dy dz : ℝ) : ℝ :=
  ((u x y z) ^ 2 * (dx + dy) - z ^ 2 * dz) /
    (u x y z * (u x y z - 2 * (x + y)))

theorem gap1 (x y z dx dy dz : ℝ) (u : ℝ → ℝ → ℝ → ℝ)
    (huDiff : DifferentiableAt ℝ (uncurry3 u) (x, y, z))
    (hImplicit :
      ∀ᶠ p : ℝ × ℝ × ℝ in nhds (x, y, z),
        (u p.1 p.2.1 p.2.2) ^ 3 -
            3 * (p.1 + p.2.1) * (u p.1 p.2.1 p.2.2) ^ 2 +
            p.2.2 ^ 3 = 0) :
    3 * (u x y z) ^ 2 * differential u x y z dx dy dz -
        3 * (u x y z) ^ 2 * (dx + dy) -
        6 * u x y z * (x + y) * differential u x y z dx dy dz +
        3 * z ^ 2 * dz = 0 := by
  have huX : DifferentiableAt ℝ (fun t : ℝ => u t y z) x := by
    simpa [uncurry3] using
      huDiff.comp x
        (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => (t, y, z)) x)
  have huY : DifferentiableAt ℝ (fun t : ℝ => u x t z) y := by
    simpa [uncurry3] using
      huDiff.comp y
        (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => (x, t, z)) y)
  have huZ : DifferentiableAt ℝ (fun t : ℝ => u x y t) z := by
    simpa [uncurry3] using
      huDiff.comp z
        (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => (x, y, t)) z)

  have hLineX : ContinuousAt (fun t : ℝ => (t, y, z)) x := by
    fun_prop
  have hEqX :
      (fun t : ℝ =>
          (u t y z) ^ 3 - 3 * (t + y) * (u t y z) ^ 2 + z ^ 3) =ᶠ[nhds x]
        (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [hLineX.eventually hImplicit] with t ht
    simpa using ht
  have hPolyX :
      HasDerivAt
        (fun t : ℝ =>
          (u t y z) ^ 3 - 3 * (t + y) * (u t y z) ^ 2 + z ^ 3)
        (3 * (u x y z) ^ 2 * partialX u x y z -
          3 * (u x y z) ^ 2 -
          6 * u x y z * (x + y) * partialX u x y z) x := by
    convert
      ((((huX.hasDerivAt.mul huX.hasDerivAt).mul huX.hasDerivAt).sub
          ((((hasDerivAt_const x (3 : ℝ)).mul
                ((hasDerivAt_id x).add (hasDerivAt_const x y))).mul
            (huX.hasDerivAt.mul huX.hasDerivAt)))).add
        (hasDerivAt_const x (z ^ 3))) using 1 <;>
      (try simp [partialX]) <;> ring_nf
    funext t
    simp <;> ring
  have hx :
      3 * (u x y z) ^ 2 * partialX u x y z -
          3 * (u x y z) ^ 2 -
          6 * u x y z * (x + y) * partialX u x y z = 0 := by
    rw [← hPolyX.deriv, hEqX.deriv_eq]
    simp

  have hLineY : ContinuousAt (fun t : ℝ => (x, t, z)) y := by
    fun_prop
  have hEqY :
      (fun t : ℝ =>
          (u x t z) ^ 3 - 3 * (x + t) * (u x t z) ^ 2 + z ^ 3) =ᶠ[nhds y]
        (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [hLineY.eventually hImplicit] with t ht
    simpa using ht
  have hPolyY :
      HasDerivAt
        (fun t : ℝ =>
          (u x t z) ^ 3 - 3 * (x + t) * (u x t z) ^ 2 + z ^ 3)
        (3 * (u x y z) ^ 2 * partialY u x y z -
          3 * (u x y z) ^ 2 -
          6 * u x y z * (x + y) * partialY u x y z) y := by
    convert
      ((((huY.hasDerivAt.mul huY.hasDerivAt).mul huY.hasDerivAt).sub
          ((((hasDerivAt_const y (3 : ℝ)).mul
                ((hasDerivAt_const y x).add (hasDerivAt_id y))).mul
            (huY.hasDerivAt.mul huY.hasDerivAt)))).add
        (hasDerivAt_const y (z ^ 3))) using 1 <;>
      (try simp [partialY]) <;> ring_nf
    funext t
    simp <;> ring
  have hy :
      3 * (u x y z) ^ 2 * partialY u x y z -
          3 * (u x y z) ^ 2 -
          6 * u x y z * (x + y) * partialY u x y z = 0 := by
    rw [← hPolyY.deriv, hEqY.deriv_eq]
    simp

  have hLineZ : ContinuousAt (fun t : ℝ => (x, y, t)) z := by
    fun_prop
  have hEqZ :
      (fun t : ℝ =>
          (u x y t) ^ 3 - 3 * (x + y) * (u x y t) ^ 2 + t ^ 3) =ᶠ[nhds z]
        (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [hLineZ.eventually hImplicit] with t ht
    simpa using ht
  have hPolyZ :
      HasDerivAt
        (fun t : ℝ =>
          (u x y t) ^ 3 - 3 * (x + y) * (u x y t) ^ 2 + t ^ 3)
        (3 * (u x y z) ^ 2 * partialZ u x y z -
          6 * u x y z * (x + y) * partialZ u x y z + 3 * z ^ 2) z := by
    convert
      ((((huZ.hasDerivAt.mul huZ.hasDerivAt).mul huZ.hasDerivAt).sub
          ((hasDerivAt_const z (3 * (x + y))).mul
            (huZ.hasDerivAt.mul huZ.hasDerivAt))).add
        (((hasDerivAt_id z).mul (hasDerivAt_id z)).mul (hasDerivAt_id z))) using 1 <;>
      (try simp [partialZ]) <;> ring_nf
    funext t
    simp <;> ring
  have hz :
      3 * (u x y z) ^ 2 * partialZ u x y z -
          6 * u x y z * (x + y) * partialZ u x y z + 3 * z ^ 2 = 0 := by
    rw [← hPolyZ.deriv, hEqZ.deriv_eq]
    simp

  unfold differential
  calc
    3 * (u x y z) ^ 2 *
          (partialX u x y z * dx + partialY u x y z * dy +
            partialZ u x y z * dz) -
        3 * (u x y z) ^ 2 * (dx + dy) -
        6 * u x y z * (x + y) *
          (partialX u x y z * dx + partialY u x y z * dy +
            partialZ u x y z * dz) +
        3 * z ^ 2 * dz =
      dx *
          (3 * (u x y z) ^ 2 * partialX u x y z -
            3 * (u x y z) ^ 2 -
            6 * u x y z * (x + y) * partialX u x y z) +
        dy *
          (3 * (u x y z) ^ 2 * partialY u x y z -
            3 * (u x y z) ^ 2 -
            6 * u x y z * (x + y) * partialY u x y z) +
        dz *
          (3 * (u x y z) ^ 2 * partialZ u x y z -
            6 * u x y z * (x + y) * partialZ u x y z + 3 * z ^ 2) := by
        ring
    _ = 0 := by rw [hx, hy, hz]; ring

theorem gap2 (x y z dx dy dz : ℝ) (u : ℝ → ℝ → ℝ → ℝ)
    (hDenominator :
      u x y z * (u x y z - 2 * (x + y)) ≠ 0)
    (hDifferentialIdentity :
      3 * (u x y z) ^ 2 * differential u x y z dx dy dz -
          3 * (u x y z) ^ 2 * (dx + dy) -
          6 * u x y z * (x + y) * differential u x y z dx dy dz +
          3 * z ^ 2 * dz = 0) :
    differential u x y z dx dy dz =
      solvedDifferential u x y z dx dy dz := by
  unfold solvedDifferential
  apply (eq_div_iff hDenominator).2
  nlinarith [hDifferentialIdentity]

end

end ProofGap.Exercise3394
