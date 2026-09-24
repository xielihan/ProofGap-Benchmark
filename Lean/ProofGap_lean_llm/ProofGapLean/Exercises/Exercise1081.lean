import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1081

noncomputable section

def ellipseEquation (y : ℝ → ℝ) (x : ℝ) : Prop :=
  x ^ 2 / 100 + y x ^ 2 / 64 = 1

def tangent : Set (ℝ × ℝ) := {p | 3 * p.1 + 5 * p.2 - 50 = 0}
def normal : Set (ℝ × ℝ) := {p | 5 * p.1 - 3 * p.2 - (54 / 5 : ℝ) = 0}

theorem gap1 (y : ℝ → ℝ) (x : ℝ)
    (hcurve : ∀ z ∈ Set.Ioo (-10 : ℝ) 10, ellipseEquation y z)
    (hx : x ∈ Set.Ioo (-10 : ℝ) 10)
    (hy : y x ≠ 0) (hd : DifferentiableAt ℝ y x) :
    HasDerivAt y (-(64 * x / (100 * y x))) x := by
  have hdy : HasDerivAt y (deriv y x) x := hd.hasDerivAt
  have hid : HasDerivAt (fun z : ℝ => z) 1 x := hasDerivAt_id x
  have hpoly :
      HasDerivAt
        (fun z : ℝ => z * z / 100 + (y z * y z) / 64)
        ((1 * x + x * 1) / 100 +
          (deriv y x * y x + y x * deriv y x) / 64) x := by
    simpa using
      HasDerivAt.add
        ((hid.mul hid).div_const 100)
        ((hdy.mul hdy).div_const 64)
  have hlocal :
      (fun _ : ℝ => (1 : ℝ)) =ᶠ[nhds x]
        (fun z : ℝ => z * z / 100 + (y z * y z) / 64) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with z hz
    simpa [ellipseEquation, pow_two] using (hcurve z hz).symm
  have hconst :
      HasDerivAt (fun _ : ℝ => (1 : ℝ))
        ((1 * x + x * 1) / 100 +
          (deriv y x * y x + y x * deriv y x) / 64) x :=
    hpoly.congr_of_eventuallyEq hlocal
  have hslope :
      (1 * x + x * 1) / 100 +
          (deriv y x * y x + y x * deriv y x) / 64 = 0 :=
    hconst.unique (hasDerivAt_const (x := x) (c := (1 : ℝ)))
  have hderiv : deriv y x = -(64 * x / (100 * y x)) := by
    field_simp [hy] at hslope ⊢
    nlinarith
  rw [hderiv] at hdy
  exact hdy

theorem gap2 (y : ℝ → ℝ) (x : ℝ) (hy : y x ≠ 0) :
    -(64 * x / (100 * y x)) = -(16 * x / (25 * y x)) := by
  field_simp [hy]
  ring

theorem gap3 (y : ℝ → ℝ) (x : ℝ)
    (hcurve : ∀ z ∈ Set.Ioo (-10 : ℝ) 10, ellipseEquation y z)
    (hx : x ∈ Set.Ioo (-10 : ℝ) 10)
    (hy : y x ≠ 0) (hd : DifferentiableAt ℝ y x) :
    HasDerivAt y (-(16 * x / (25 * y x))) x := by
  simpa only [gap2 y x hy] using gap1 y x hcurve hx hy hd

theorem gap4 (y : ℝ → ℝ)
    (hcurve : ∀ z ∈ Set.Ioo (-10 : ℝ) 10, ellipseEquation y z)
    (hy : y 6 = (32 / 5 : ℝ)) (hd : DifferentiableAt ℝ y 6) :
    HasDerivAt y (-(16 * 6 / (25 * (32 / 5 : ℝ)))) 6 := by
  have hx : (6 : ℝ) ∈ Set.Ioo (-10 : ℝ) 10 := by
    norm_num
  have hne : y 6 ≠ 0 := by
    rw [hy]
    norm_num
  simpa only [hy] using gap3 y 6 hcurve hx hne hd

theorem gap5 :
    (-(16 * 6 / (25 * (32 / 5 : ℝ))) : ℝ) = -(3 / 5 : ℝ) := by
  norm_num

theorem gap6 (y : ℝ → ℝ)
    (hcurve : ∀ z ∈ Set.Ioo (-10 : ℝ) 10, ellipseEquation y z)
    (hy : y 6 = (32 / 5 : ℝ)) (hd : DifferentiableAt ℝ y 6) :
    HasDerivAt y (-(3 / 5 : ℝ)) 6 := by
  have h := gap4 y hcurve hy hd
  rw [gap5] at h
  exact h

theorem gap7 :
    tangent = {p : ℝ × ℝ | 3 * p.1 + 5 * p.2 - 50 = 0} := by
  rfl

theorem gap8 :
    normal = {p : ℝ × ℝ | 5 * p.1 - 3 * p.2 - (54 / 5 : ℝ) = 0} := by
  rfl

end

end ProofGap.Exercise1081
