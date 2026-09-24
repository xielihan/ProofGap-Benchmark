import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed

namespace ProofGap.Exercise4251

noncomputable section

open scoped Interval

def roof (x : ℝ) : ℝ :=
  1 - |1 - x|

def lineIntegral : ℝ :=
  (∫ x in (0 : ℝ)..1, 2 * x ^ 2) +
    ∫ x in (1 : ℝ)..2, 2 * (2 - x) ^ 2

theorem gap1 (x : ℝ) (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    roof x = 1 - (1 - x) := by
  unfold roof
  rw [abs_of_nonneg (by linarith)]

theorem gap2 (x : ℝ) (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    1 - (1 - x) = x := by
  ring

theorem gap3 (x : ℝ) (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    roof x = x := by
  rw [gap1 x hx₀ hx₁, gap2 x hx₀ hx₁]

theorem gap4 (x : ℝ) (hx₀ : 0 < x) (hx₁ : x < 1) :
    deriv roof x = 1 := by
  have hlocal : roof =ᶠ[nhds x] (fun y : ℝ => y) := by
    filter_upwards [Ioo_mem_nhds hx₀ hx₁] with y hy
    exact gap3 y (le_of_lt hy.1) (le_of_lt hy.2)
  calc
    deriv roof x = deriv (fun y : ℝ => y) x := hlocal.deriv_eq
    _ = 1 := (hasDerivAt_id x).deriv

theorem gap5 (x : ℝ) (hx₁ : 1 ≤ x) (hx₂ : x ≤ 2) :
    roof x = 1 - (x - 1) := by
  unfold roof
  rw [abs_of_nonpos (by linarith)]
  ring

theorem gap6 (x : ℝ) (hx₁ : 1 ≤ x) (hx₂ : x ≤ 2) :
    1 - (x - 1) = 2 - x := by
  ring

theorem gap7 (x : ℝ) (hx₁ : 1 ≤ x) (hx₂ : x ≤ 2) :
    roof x = 2 - x := by
  rw [gap5 x hx₁ hx₂, gap6 x hx₁ hx₂]

theorem gap8 (x : ℝ) (hx₁ : 1 < x) (hx₂ : x < 2) :
    deriv roof x = -1 := by
  have hlocal : roof =ᶠ[nhds x] (fun y : ℝ => 2 - y) := by
    filter_upwards [Ioo_mem_nhds hx₁ hx₂] with y hy
    exact gap7 y (le_of_lt hy.1) (le_of_lt hy.2)
  calc
    deriv roof x = deriv (fun y : ℝ => 2 - y) x := hlocal.deriv_eq
    _ = -1 := ((hasDerivAt_id x).const_sub 2).deriv

theorem gap9 :
    lineIntegral =
      (∫ x in (0 : ℝ)..1, 2 * x ^ 2) +
        ∫ x in (1 : ℝ)..2,
          x ^ 2 + (2 - x) ^ 2 - x ^ 2 + (2 - x) ^ 2 := by
  unfold lineIntegral
  have h :
      (fun x : ℝ => 2 * (2 - x) ^ 2) =
        (fun x : ℝ => x ^ 2 + (2 - x) ^ 2 - x ^ 2 + (2 - x) ^ 2) := by
    funext x
    ring
  rw [h]

theorem gap10 :
    (∫ x in (0 : ℝ)..1, 2 * x ^ 2) +
        (∫ x in (1 : ℝ)..2,
          x ^ 2 + (2 - x) ^ 2 - x ^ 2 + (2 - x) ^ 2) =
      4 / 3 := by
  have hfirst :
      (∫ x in (0 : ℝ)..1, 2 * x ^ 2) = 2 / 3 := by
    calc
      (∫ x in (0 : ℝ)..1, 2 * x ^ 2) =
          (2 / 3 : ℝ) * 1 ^ 3 - (2 / 3 : ℝ) * 0 ^ 3 := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt
          (a := (0 : ℝ)) (b := 1)
          (f := fun x : ℝ => (2 / 3 : ℝ) * x ^ 3)
          (f' := fun x : ℝ => 2 * x ^ 2) ?_ ?_
        · intro x hx
          have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
          convert (((hid.mul hid).mul hid).const_mul (2 / 3 : ℝ)) using 1
          · funext y
            change (2 / 3 : ℝ) * y ^ 3 =
              (2 / 3 : ℝ) * ((y * y) * y)
            ring
          · change 2 * x ^ 2 =
              (2 / 3 : ℝ) *
                ((1 * x + x * 1) * x + (x * x) * 1)
            ring
        · have hcont : Continuous (fun x : ℝ => 2 * x ^ 2) :=
            continuous_const.mul (continuous_id.pow 2)
          exact hcont.intervalIntegrable (0 : ℝ) 1
      _ = 2 / 3 := by norm_num
  have hsecond :
      (∫ x in (1 : ℝ)..2,
        x ^ 2 + (2 - x) ^ 2 - x ^ 2 + (2 - x) ^ 2) = 2 / 3 := by
    have hpoly :
        (fun x : ℝ => x ^ 2 + (2 - x) ^ 2 - x ^ 2 + (2 - x) ^ 2) =
          (fun x : ℝ => 2 * x ^ 2 - 8 * x + 8) := by
      funext x
      ring
    rw [hpoly]
    calc
      (∫ x in (1 : ℝ)..2, 2 * x ^ 2 - 8 * x + 8) =
          ((2 / 3 : ℝ) * 2 ^ 3 - 4 * 2 ^ 2 + 8 * 2) -
            ((2 / 3 : ℝ) * 1 ^ 3 - 4 * 1 ^ 2 + 8 * 1) := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt
          (a := (1 : ℝ)) (b := 2)
          (f := fun x : ℝ => (2 / 3 : ℝ) * x ^ 3 - 4 * x ^ 2 + 8 * x)
          (f' := fun x : ℝ => 2 * x ^ 2 - 8 * x + 8) ?_ ?_
        · intro x hx
          have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
          have h3 := ((hid.mul hid).mul hid).const_mul (2 / 3 : ℝ)
          have h2 := (hid.mul hid).const_mul (4 : ℝ)
          have h1 := hid.const_mul (8 : ℝ)
          convert (h3.sub h2).add h1 using 1
          · funext y
            change
              (2 / 3 : ℝ) * y ^ 3 - 4 * y ^ 2 + 8 * y =
                ((2 / 3 : ℝ) * ((y * y) * y) - 4 * (y * y)) + 8 * y
            ring
          · change
              2 * x ^ 2 - 8 * x + 8 =
                ((2 / 3 : ℝ) *
                    ((1 * x + x * 1) * x + (x * x) * 1) -
                  4 * (1 * x + x * 1)) + 8 * 1
            ring
        · have hcont : Continuous (fun x : ℝ => 2 * x ^ 2 - 8 * x + 8) :=
            ((continuous_const.mul (continuous_id.pow 2)).sub
              (continuous_const.mul continuous_id)).add continuous_const
          exact hcont.intervalIntegrable (1 : ℝ) 2
      _ = 2 / 3 := by norm_num
  rw [hfirst, hsecond]
  norm_num

theorem gap11 :
    lineIntegral = 4 / 3 := by
  rw [gap9]
  exact gap10

end

end ProofGap.Exercise4251
