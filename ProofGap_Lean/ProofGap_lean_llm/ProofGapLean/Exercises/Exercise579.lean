import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise579

noncomputable section

def original (x : ℝ) : ℝ :=
  (Real.exp (Real.sin (2 * x)) - Real.exp (Real.sin x)) / Real.tanh x
def tanhExpanded (x : ℝ) : ℝ :=
  ((Real.exp (Real.sin (2 * x)) - Real.exp (Real.sin x)) *
    (Real.exp (2 * x) + 1)) / (Real.exp (2 * x) - 1)
def normalized (x : ℝ) : ℝ :=
  ((((Real.exp (Real.sin (2 * x)) - 1) / Real.sin (2 * x)) *
      (Real.sin (2 * x) / (2 * x)) -
    ((Real.exp (Real.sin x) - 1) / Real.sin x) *
      (Real.sin x / x) * (1 / 2 : ℝ)) *
    (Real.exp (2 * x) + 1)) /
      ((Real.exp (2 * x) - 1) / (2 * x))
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 579, gap 1. -/
private theorem local_sin_ne_zero {x : ℝ} (hx : x ≠ 0)
    (hxpi : |x| < Real.pi) : Real.sin x ≠ 0 := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hlt : -x < Real.pi := by
      simpa [abs_of_neg hneg] using hxpi
    have hs : 0 < Real.sin (-x) :=
      Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hneg) hlt
    rw [Real.sin_neg] at hs
    intro hzero
    rw [hzero] at hs
    norm_num at hs
  · have hlt : x < Real.pi := lt_of_le_of_lt (le_abs_self x) hxpi
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos hlt)

private theorem punctured_sine_nonzero :
    ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      x ≠ 0 ∧ Real.sin x ≠ 0 ∧ Real.sin (2 * x) ≠ 0 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hI :
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) ∈ nhds (0 : ℝ) :=
    Ioo_mem_nhds (by nlinarith) (by nlinarith)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hI]
    with x hxmem hxI
  have hx : x ≠ 0 := by simpa using hxmem
  have hxabs : |x| < Real.pi := by
    apply (abs_lt).2
    constructor <;> nlinarith [hxI.1, hxI.2]
  have h2xabs : |(2 : ℝ) * x| < Real.pi := by
    apply (abs_lt).2
    constructor <;> nlinarith [hxI.1, hxI.2]
  exact ⟨hx, local_sin_ne_zero hx hxabs,
    local_sin_ne_zero (mul_ne_zero (by norm_num) hx) h2xabs⟩

private theorem tanhExpanded_limit_one :
    HasLimitAtZero tanhExpanded 1 := by
  have hlin : HasDerivAt (fun x : ℝ => 2 * x) 2 0 := by
    convert (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).const_mul 2 using 1 <;>
      norm_num
  have hs2 : HasDerivAt (fun x : ℝ => Real.sin (2 * x)) 2 0 := by
    convert (Real.hasDerivAt_sin (2 * 0)).comp 0 hlin using 1 <;>
      norm_num
  have he2 :
      HasDerivAt (fun x : ℝ => Real.exp (Real.sin (2 * x))) 2 0 := by
    convert
      (Real.hasDerivAt_exp (Real.sin (2 * 0))).comp 0 hs2 using 1 <;>
      norm_num
  have hs1 : HasDerivAt (fun x : ℝ => Real.sin x) 1 0 := by
    simpa using Real.hasDerivAt_sin 0
  have he1 :
      HasDerivAt (fun x : ℝ => Real.exp (Real.sin x)) 1 0 := by
    convert (Real.hasDerivAt_exp (Real.sin 0)).comp 0 hs1 using 1 <;>
      norm_num
  have hf :
      HasDerivAt
        (fun x : ℝ =>
          Real.exp (Real.sin (2 * x)) - Real.exp (Real.sin x)) 1 0 := by
    convert he2.sub he1 using 1 <;>
      norm_num
  have heg : HasDerivAt (fun x : ℝ => Real.exp (2 * x)) 2 0 := by
    convert (Real.hasDerivAt_exp (2 * 0)).comp 0 hlin using 1 <;>
      norm_num
  have hflim :
      Filter.Tendsto
        (fun x : ℝ =>
          (Real.exp (Real.sin (2 * x)) - Real.exp (Real.sin x)) / x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [div_eq_mul_inv, mul_comm] using hf.tendsto_slope_zero
  have hglim :
      Filter.Tendsto
        (fun x : ℝ => (Real.exp (2 * x) - 1) / x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 2) := by
    simpa [div_eq_mul_inv, mul_comm] using heg.tendsto_slope_zero
  have hone : ContinuousAt (fun _ : ℝ => (1 : ℝ)) 0 :=
    continuousAt_const
  have hfacFull :
      Filter.Tendsto (fun x : ℝ => Real.exp (2 * x) + 1)
        (nhds 0) (nhds 2) := by
    convert (heg.continuousAt.add hone).tendsto using 1 <;>
      norm_num
  have hfac :
      Filter.Tendsto (fun x : ℝ => Real.exp (2 * x) + 1)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 2) :=
    hfacFull.mono_left inf_le_left
  have hlim :
      Filter.Tendsto
        (fun x : ℝ =>
          (((Real.exp (Real.sin (2 * x)) - Real.exp (Real.sin x)) / x) *
            (Real.exp (2 * x) + 1)) /
            ((Real.exp (2 * x) - 1) / x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using (hflim.mul hfac).div hglim (by norm_num : (2 : ℝ) ≠ 0)
  unfold HasLimitAtZero
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hxmem
  have hx : x ≠ 0 := by simpa using hxmem
  have h2x : (2 : ℝ) * x ≠ 0 := mul_ne_zero (by norm_num) hx
  have heexp : Real.exp (2 * x) ≠ 1 := by
    simpa using Real.exp_injective.ne h2x
  have hden : Real.exp (2 * x) - 1 ≠ 0 := sub_ne_zero.mpr heexp
  unfold tanhExpanded
  field_simp [hx, hden]
  <;> ring_nf

theorem gap1 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero tanhExpanded L := by
  have heq :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        original x = tanhExpanded x := by
    filter_upwards [self_mem_nhdsWithin] with x hxmem
    have hx : x ≠ 0 := by simpa using hxmem
    have h2x : (2 : ℝ) * x ≠ 0 := mul_ne_zero (by norm_num) hx
    have heexp : Real.exp (2 * x) ≠ 1 := by
      simpa using Real.exp_injective.ne h2x
    have hden : Real.exp (2 * x) - 1 ≠ 0 := sub_ne_zero.mpr heexp
    have hplus : Real.exp (2 * x) + 1 ≠ 0 := by positivity
    have hex : Real.exp x ≠ 0 := Real.exp_ne_zero x
    have hsqplus : Real.exp x * Real.exp x + 1 ≠ 0 := by positivity
    have htwo : Real.exp (2 * x) = Real.exp x * Real.exp x := by
      rw [two_mul, Real.exp_add]
    have htanh :
        Real.tanh x =
          (Real.exp (2 * x) - 1) / (Real.exp (2 * x) + 1) := by
      rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq,
        Real.exp_neg, htwo]
      field_simp [hex, hsqplus, pow_two]
      <;> ring
    unfold original tanhExpanded
    rw [htanh]
    field_simp [hden, hplus]
    <;> ring
  have heq_rev :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        tanhExpanded x = original x := by
    filter_upwards [heq] with x hx
    exact hx.symm
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq_rev

/-- Exercise 579, gap 2. -/
theorem gap2 (L : ℝ) :
    HasLimitAtZero tanhExpanded L ↔ HasLimitAtZero normalized L := by
  have heq :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        tanhExpanded x = normalized x := by
    filter_upwards [punctured_sine_nonzero] with x hx
    rcases hx with ⟨hx0, hsx, hs2x⟩
    have h2x : (2 : ℝ) * x ≠ 0 := mul_ne_zero (by norm_num) hx0
    have heexp : Real.exp (2 * x) ≠ 1 := by
      simpa using Real.exp_injective.ne h2x
    have hden : Real.exp (2 * x) - 1 ≠ 0 := sub_ne_zero.mpr heexp
    unfold tanhExpanded normalized
    field_simp [hx0, h2x, hsx, hs2x, hden]
    <;> ring
  have heq_rev :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        normalized x = tanhExpanded x := by
    filter_upwards [heq] with x hx
    exact hx.symm
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq_rev

/-- Exercise 579, gap 3. -/
theorem gap3 : HasLimitAtZero normalized (2 * (1 - 1 / 2) / 1) := by
  norm_num
  exact (gap2 1).mp tanhExpanded_limit_one

/-- Exercise 579, gap 4. -/
theorem gap4 : (2 : ℝ) * (1 - 1 / 2) / 1 = 1 := by
  norm_num

/-- Exercise 579, gap 5. -/
theorem gap5 : HasLimitAtZero tanhExpanded 1 := by
  have hn := gap3
  rw [gap4] at hn
  exact (gap2 1).mpr hn

end

end ProofGap.Exercise579
