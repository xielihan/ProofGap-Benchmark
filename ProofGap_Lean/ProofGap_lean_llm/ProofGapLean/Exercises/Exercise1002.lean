import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1002

open Filter

noncomputable section

def f (x : ℝ) : ℝ :=
  if x = 0 then 0 else x * |Real.cos (Real.pi / x)|

def dq (g : ℝ → ℝ) (a h : ℝ) : ℝ := (g (a + h) - g a) / h
def HasLeftDerivAt (g : ℝ → ℝ) (g' a : ℝ) : Prop :=
  Tendsto (dq g a) (nhdsWithin 0 (Set.Iio 0)) (nhds g')
def HasRightDerivAt (g : ℝ → ℝ) (g' a : ℝ) : Prop :=
  Tendsto (dq g a) (nhdsWithin 0 (Set.Ioi 0)) (nhds g')

def rawDerivative (x : ℝ) : ℝ :=
  |Real.cos (Real.pi / x)| +
    Real.pi / x *
      (|Real.cos (Real.pi / x)| / Real.cos (Real.pi / x)) *
      Real.sin (Real.pi / x)

def finalDerivative (x : ℝ) : ℝ :=
  (Real.cos (Real.pi / x) + Real.pi / x * Real.sin (Real.pi / x)) *
    Real.sign (Real.cos (Real.pi / x))

def cusp (k : ℤ) : ℝ := 2 / (2 * (k : ℝ) + 1)

private theorem leftWithin_le_punctured :
    nhdsWithin (0 : ℝ) (Set.Iio 0) ≤
      nhdsWithin (0 : ℝ) (({0} : Set ℝ)ᶜ) := by
  refine nhdsWithin_mono 0 ?_
  intro y hy
  simp only [Set.mem_Iio] at hy
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  exact ne_of_lt hy

private theorem rightWithin_le_punctured :
    nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤
      nhdsWithin (0 : ℝ) (({0} : Set ℝ)ᶜ) := by
  refine nhdsWithin_mono 0 ?_
  intro y hy
  simp only [Set.mem_Ioi] at hy
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  exact ne_of_gt hy

private theorem tendsto_add_within (a : ℝ) (s : Set ℝ) :
    Tendsto (fun h : ℝ => a + h) (nhdsWithin 0 s) (nhds a) := by
  have hid : Tendsto (fun h : ℝ => h) (nhdsWithin 0 s) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  simpa using tendsto_const_nhds.add hid

private theorem hasDerivAt_cos_pi_div (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.cos (Real.pi / y))
      (Real.pi / x ^ 2 * Real.sin (Real.pi / x)) x := by
  convert (Real.hasDerivAt_cos (Real.pi / x)).comp x
      ((hasDerivAt_const x Real.pi).div (hasDerivAt_id x) hx) using 1
  field_simp [hx]
  ring

private theorem rawDerivative_eq_finalDerivative (x : ℝ) (hx0 : x ≠ 0)
    (hcos : Real.cos (Real.pi / x) ≠ 0) :
    rawDerivative x = finalDerivative x := by
  rcases lt_or_gt_of_ne hcos with hneg | hpos
  · simp [rawDerivative, finalDerivative, Real.sign_of_neg hneg,
      abs_of_neg hneg, hcos] <;> ring
  · simp [rawDerivative, finalDerivative, Real.sign_of_pos hpos,
      abs_of_pos hpos, hcos] <;> ring

private theorem hasDerivAt_f_regular (x : ℝ) (hx0 : x ≠ 0)
    (hcos : Real.cos (Real.pi / x) ≠ 0) :
    HasDerivAt f (finalDerivative x) x := by
  have hu := hasDerivAt_cos_pi_div x hx0
  have habs := (hasDerivAt_abs hcos).comp x hu
  have hp := (hasDerivAt_id x).mul habs
  have hcoef :
      1 * |Real.cos (Real.pi / x)| +
          x * ((SignType.sign (Real.cos (Real.pi / x)) : ℝ) *
            (Real.pi / x ^ 2 * Real.sin (Real.pi / x))) =
        finalDerivative x := by
    rcases lt_or_gt_of_ne hcos with hneg | hpos
    · simp [finalDerivative, Real.sign_of_neg hneg, abs_of_neg hneg, hneg]
      field_simp [hx0] <;> ring
    · simp [finalDerivative, Real.sign_of_pos hpos, abs_of_pos hpos, hpos]
      field_simp [hx0] <;> ring
  have hmodel :
      HasDerivAt (fun y : ℝ => y * |Real.cos (Real.pi / y)|)
        (finalDerivative x) x := by
    rw [← hcoef]
    simpa only [Pi.mul_apply, id_eq, Function.comp_apply] using hp
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx0] with y hy
  simp [f, hy]

private theorem hasLeftDerivAt_of_hasDerivAt {g : ℝ → ℝ} {g' a : ℝ}
    (h : HasDerivAt g g' a) : HasLeftDerivAt g g' a := by
  unfold HasLeftDerivAt
  have hs := h.tendsto_slope_zero.mono_left leftWithin_le_punctured
  simpa only [dq, div_eq_mul_inv, smul_eq_mul, mul_comm] using hs

private theorem hasRightDerivAt_of_hasDerivAt {g : ℝ → ℝ} {g' a : ℝ}
    (h : HasDerivAt g g' a) : HasRightDerivAt g g' a := by
  unfold HasRightDerivAt
  have hs := h.tendsto_slope_zero.mono_left rightWithin_le_punctured
  simpa only [dq, div_eq_mul_inv, smul_eq_mul, mul_comm] using hs

private theorem hasRightDerivAt_mul_abs_of_hasDerivAt
    (u : ℝ → ℝ) (u' a : ℝ) (hu0 : u a = 0)
    (hdu : HasDerivAt u u' a) :
    HasRightDerivAt (fun y : ℝ => y * |u y|) (a * |u'|) a := by
  have hslope :
      Tendsto (fun h : ℝ => (u (a + h) - u a) / h)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds u') := by
    simpa only [div_eq_mul_inv, smul_eq_mul, mul_comm] using
      hdu.tendsto_slope_zero.mono_left rightWithin_le_punctured
  have habs :
      Tendsto (fun h : ℝ => |(u (a + h) - u a) / h|)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds |u'|) :=
    (continuous_abs.tendsto u').comp hslope
  have hshift := tendsto_add_within a (Set.Ioi 0)
  have hprod :
      Tendsto
        (fun h : ℝ => (a + h) * |(u (a + h) - u a) / h|)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (a * |u'|)) :=
    hshift.mul habs
  unfold HasRightDerivAt
  apply hprod.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  change 0 < h at hh
  simp only [dq, hu0, abs_zero, mul_zero, sub_zero]
  rw [abs_div, abs_of_pos hh]
  field_simp [ne_of_gt hh] <;> ring

private theorem hasLeftDerivAt_mul_abs_of_hasDerivAt
    (u : ℝ → ℝ) (u' a : ℝ) (hu0 : u a = 0)
    (hdu : HasDerivAt u u' a) :
    HasLeftDerivAt (fun y : ℝ => y * |u y|) (-(a * |u'|)) a := by
  have hslope :
      Tendsto (fun h : ℝ => (u (a + h) - u a) / h)
        (nhdsWithin 0 (Set.Iio 0)) (nhds u') := by
    simpa only [div_eq_mul_inv, smul_eq_mul, mul_comm] using
      hdu.tendsto_slope_zero.mono_left leftWithin_le_punctured
  have habs :
      Tendsto (fun h : ℝ => |(u (a + h) - u a) / h|)
        (nhdsWithin 0 (Set.Iio 0)) (nhds |u'|) :=
    (continuous_abs.tendsto u').comp hslope
  have hshift := tendsto_add_within a (Set.Iio 0)
  have hprod :
      Tendsto
        (fun h : ℝ => (a + h) * (-|(u (a + h) - u a) / h|))
        (nhdsWithin 0 (Set.Iio 0)) (nhds (-(a * |u'|))) := by
    simpa only [mul_neg] using hshift.mul habs.neg
  unfold HasLeftDerivAt
  apply hprod.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  change h < 0 at hh
  simp only [dq, hu0, abs_zero, mul_zero, sub_zero]
  rw [abs_div, abs_of_neg hh]
  field_simp [ne_of_lt hh] <;> ring

private theorem cusp_oneSidedDerivatives (k : ℤ) :
    HasLeftDerivAt f (-((2 * (k : ℝ) + 1) * Real.pi / 2)) (cusp k) ∧
      HasRightDerivAt f (((2 * (k : ℝ) + 1) * Real.pi / 2)) (cusp k) := by
  have hodd : (2 * k + 1 : ℤ) ≠ 0 := by omega
  have hq : (2 * (k : ℝ) + 1) ≠ 0 := by
    exact_mod_cast hodd
  have hcusp0 : cusp k ≠ 0 := by
    unfold cusp
    exact div_ne_zero (by norm_num) hq
  have harg :
      Real.pi / cusp k = (k : ℝ) * Real.pi + Real.pi / 2 := by
    unfold cusp
    field_simp [hq] <;> ring
  have hroot : Real.cos (Real.pi / cusp k) = 0 := by
    rw [harg, Real.cos_add]
    simp
  have hdu := hasDerivAt_cos_pi_div (cusp k) hcusp0
  have hsin_sq : Real.sin (Real.pi / cusp k) ^ 2 = 1 := by
    have htrig := Real.sin_sq_add_cos_sq (Real.pi / cusp k)
    rw [hroot] at htrig
    norm_num at htrig ⊢
    exact htrig
  have hsinabs : |Real.sin (Real.pi / cusp k)| = 1 := by
    nlinarith [sq_abs (Real.sin (Real.pi / cusp k)),
      abs_nonneg (Real.sin (Real.pi / cusp k))]
  have hpositive : 0 < Real.pi / cusp k ^ 2 := by positivity
  have huabs :
      |Real.pi / cusp k ^ 2 * Real.sin (Real.pi / cusp k)| =
        Real.pi / cusp k ^ 2 := by
    rw [abs_mul, abs_of_pos hpositive, hsinabs, mul_one]
  have hscale :
      cusp k * (Real.pi / cusp k ^ 2) =
        (2 * (k : ℝ) + 1) * Real.pi / 2 := by
    unfold cusp
    field_simp [hq] <;> ring
  let model : ℝ → ℝ := fun y => y * |Real.cos (Real.pi / y)|
  have hLmodel :
      HasLeftDerivAt model (-((2 * (k : ℝ) + 1) * Real.pi / 2)) (cusp k) := by
    rw [← hscale, ← huabs]
    exact hasLeftDerivAt_mul_abs_of_hasDerivAt
      (fun y : ℝ => Real.cos (Real.pi / y))
      (Real.pi / cusp k ^ 2 * Real.sin (Real.pi / cusp k))
      (cusp k) hroot hdu
  have hRmodel :
      HasRightDerivAt model (((2 * (k : ℝ) + 1) * Real.pi / 2)) (cusp k) := by
    rw [← hscale, ← huabs]
    exact hasRightDerivAt_mul_abs_of_hasDerivAt
      (fun y : ℝ => Real.cos (Real.pi / y))
      (Real.pi / cusp k ^ 2 * Real.sin (Real.pi / cusp k))
      (cusp k) hroot hdu
  have hlocal : f =ᶠ[nhds (cusp k)] model := by
    filter_upwards [eventually_ne_nhds hcusp0] with y hy
    simp [f, model, hy]
  have hpoint : f (cusp k) = model (cusp k) := by
    simp [f, model, hcusp0]
  constructor
  · unfold HasLeftDerivAt at hLmodel ⊢
    apply hLmodel.congr'
    have heq := (tendsto_add_within (cusp k) (Set.Iio 0)).eventually hlocal
    filter_upwards [heq] with h hh
    simp only [dq]
    rw [hh, hpoint]
  · unfold HasRightDerivAt at hRmodel ⊢
    apply hRmodel.congr'
    have heq := (tendsto_add_within (cusp k) (Set.Ioi 0)).eventually hlocal
    filter_upwards [heq] with h hh
    simp only [dq]
    rw [hh, hpoint]

theorem gap1 (x : ℝ) (hx0 : x ≠ 0)
    (hcos : Real.cos (Real.pi / x) ≠ 0) :
    HasLeftDerivAt f (finalDerivative x) x ∧
      HasRightDerivAt f (finalDerivative x) x := by
  have hd := hasDerivAt_f_regular x hx0 hcos
  exact ⟨hasLeftDerivAt_of_hasDerivAt hd, hasRightDerivAt_of_hasDerivAt hd⟩

theorem gap2 (x : ℝ) (hx0 : x ≠ 0)
    (hcos : Real.cos (Real.pi / x) ≠ 0) :
    HasRightDerivAt f (rawDerivative x) x := by
  rw [rawDerivative_eq_finalDerivative x hx0 hcos]
  exact (gap1 x hx0 hcos).2

theorem gap3 (x : ℝ) (hx0 : x ≠ 0)
    (hcos : Real.cos (Real.pi / x) ≠ 0) :
    rawDerivative x = finalDerivative x := by
  exact rawDerivative_eq_finalDerivative x hx0 hcos

theorem gap4 (x : ℝ) (hx0 : x ≠ 0)
    (hcos : Real.cos (Real.pi / x) ≠ 0) :
    HasLeftDerivAt f (finalDerivative x) x := by
  exact (gap1 x hx0 hcos).1

theorem gap5 (k : ℤ) :
    HasLeftDerivAt f (-((2 * (k : ℝ) + 1) * Real.pi / 2)) (cusp k) := by
  exact (cusp_oneSidedDerivatives k).1

theorem gap6 (k : ℤ) :
    HasRightDerivAt f (((2 * (k : ℝ) + 1) * Real.pi / 2)) (cusp k) := by
  exact (cusp_oneSidedDerivatives k).2

end

end ProofGap.Exercise1002
