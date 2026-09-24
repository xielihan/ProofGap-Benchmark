import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1779_2

noncomputable section

def integrand (x : ℝ) : ℝ := x ^ 2 / Real.sqrt (x ^ 2 - 2)
def primitive (x : ℝ) : ℝ :=
  x / 2 * Real.sqrt (x ^ 2 - 2) +
    Real.log |x + Real.sqrt (x ^ 2 - 2)|
def domain : Set ℝ := Set.Iio (-Real.sqrt 2)
def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

private theorem constantOn_Iio_of_hasDerivAt_zero
    (f : ℝ → ℝ) (a : ℝ)
    (hf : ∀ x ∈ Set.Iio a, HasDerivAt f 0 x) :
    ∀ x ∈ Set.Iio a, ∀ y ∈ Set.Iio a, f x = f y := by
  intro x hx y hy
  apply isOpen_Iio.is_const_of_deriv_eq_zero isPreconnected_Iio
  · intro z hz
    exact (hf z hz).differentiableAt.differentiableWithinAt
  · intro z hz
    exact (hf z hz).deriv
  · exact hx
  · exact hy

private theorem primitive_hasDerivAt
    (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  change x < -Real.sqrt 2 at hx
  have hsqrt2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt2_sq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hrad : 0 < x ^ 2 - 2 := by
    nlinarith
  have hspos : 0 < Real.sqrt (x ^ 2 - 2) := Real.sqrt_pos.2 hrad
  have hssq : (Real.sqrt (x ^ 2 - 2)) ^ 2 = x ^ 2 - 2 :=
    Real.sq_sqrt hrad.le
  have harg : x + Real.sqrt (x ^ 2 - 2) < 0 := by
    have hxneg : x < 0 := by nlinarith
    have hsnonneg := Real.sqrt_nonneg (x ^ 2 - 2)
    nlinarith
  have hid : HasDerivAt (fun z : ℝ => z) 1 x := by
    simpa only [id_eq] using hasDerivAt_id x
  have hinner : HasDerivAt (fun z : ℝ => z ^ 2 - 2) (2 * x) x := by
    convert (hid.pow 2).sub_const 2 using 1 <;> ring
  have hsqrt : HasDerivAt
      (fun z : ℝ => Real.sqrt (z ^ 2 - 2))
      (x / Real.sqrt (x ^ 2 - 2)) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hrad)).comp x hinner using 1 <;>
      field_simp [ne_of_gt hspos] <;> ring
  have hfirst := (hid.div_const 2).mul hsqrt
  have hsum := hid.add hsqrt
  have hlog0 : HasDerivAt
      (fun z : ℝ => Real.log (z + Real.sqrt (z ^ 2 - 2)))
      (1 / Real.sqrt (x ^ 2 - 2)) x := by
    convert (Real.hasDerivAt_log (ne_of_lt harg)).comp x hsum using 1 <;>
      field_simp [ne_of_gt hspos, ne_of_lt harg] <;> ring
  have hlog : HasDerivAt
      (fun z : ℝ => Real.log |z + Real.sqrt (z ^ 2 - 2)|)
      (1 / Real.sqrt (x ^ 2 - 2)) x := by
    simpa only [Real.log_abs] using hlog0
  change HasDerivAt
    (fun z : ℝ =>
      z / 2 * Real.sqrt (z ^ 2 - 2) +
        Real.log |z + Real.sqrt (z ^ 2 - 2)|)
    (x ^ 2 / Real.sqrt (x ^ 2 - 2)) x
  convert hfirst.add hlog using 1 <;>
    field_simp [ne_of_gt hspos] <;>
    nlinarith [hssq]

theorem gap1 :
    Family integrand domain = Translates primitive domain := by
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand domain at hF
    change ∃ C, ∀ x ∈ domain, F x = primitive x + C
    let x₀ : ℝ := -Real.sqrt 2 - 1
    have hx₀ : x₀ ∈ domain := by
      change -Real.sqrt 2 - 1 < -Real.sqrt 2
      linarith
    have hzero : ∀ x ∈ domain,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      convert (hF x hx).sub (primitive_hasDerivAt x hx) using 1 <;> ring
    refine ⟨F x₀ - primitive x₀, ?_⟩
    intro x hx
    have hc := constantOn_Iio_of_hasDerivAt_zero
      (fun y => F y - primitive y) (-Real.sqrt 2) hzero
      x hx x₀ hx₀
    linarith
  · rintro ⟨C, hC⟩
    change IsAntiderivativeOn F integrand domain
    intro x hx
    have heq : F =ᶠ[nhds x] fun y => primitive y + C := by
      filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
      exact hC y hy
    exact ((primitive_hasDerivAt x hx).add_const C).congr_of_eventuallyEq heq

end

end ProofGap.Exercise1779_2
