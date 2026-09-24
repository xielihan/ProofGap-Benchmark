import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1064_2

noncomputable section

open Filter
open scoped Topology

def y (x : ℝ) : ℝ := Real.arcsin (2 * x / (1 + x ^ 2))
def slopeQuotient (x : ℝ) : ℝ := (y x - Real.arcsin 1) / (x - 1)
def leftTransform (x : ℝ) : ℝ :=
  -Real.arcsin ((1 - x ^ 2) / (1 + x ^ 2)) / (x - 1)
def rationalTransform (x : ℝ) : ℝ :=
  ((1 - x ^ 2) / (1 + x ^ 2)) / (1 - x)
def kLeft : ℝ := 1
def kRight : ℝ := -1
def θ : ℝ := Real.pi / 2

private theorem eventually_pos_left :
    ∀ᶠ x : ℝ in nhdsWithin 1 (Set.Iio 1), 0 < x := by
  apply Filter.Eventually.filter_mono inf_le_left
  exact Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)

private theorem rationalTransform_eventuallyEq :
    rationalTransform =ᶠ[nhdsWithin 1 (Set.Iio 1)]
      (fun x : ℝ => (1 + x) / (1 + x ^ 2)) := by
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxne : x ≠ 1 := ne_of_lt hx
  have hone : 1 - x ≠ 0 := sub_ne_zero.mpr hxne.symm
  have hden : 1 + x ^ 2 ≠ 0 := by nlinarith [sq_nonneg x]
  simp only [rationalTransform]
  rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring]
  field_simp [hone, hden] <;> ring

private theorem rationalTransform_tendsto_one :
    Tendsto rationalTransform (nhdsWithin 1 (Set.Iio 1)) (𝓝 1) := by
  have hcont : ContinuousAt (fun x : ℝ => (1 + x) / (1 + x ^ 2)) 1 := by
    exact (continuousAt_const.add continuousAt_id).div
      (continuousAt_const.add (continuousAt_id.pow 2)) (by norm_num)
  have ht : Tendsto (fun x : ℝ => (1 + x) / (1 + x ^ 2))
      (nhdsWithin 1 (Set.Iio 1)) (𝓝 1) := by
    simpa using hcont.tendsto.mono_left inf_le_left
  exact (tendsto_congr' rationalTransform_eventuallyEq).2 ht

private theorem leftTransform_tendsto_one :
    Tendsto leftTransform (nhdsWithin 1 (Set.Iio 1)) (𝓝 1) := by
  let u : ℝ → ℝ := fun x => (1 - x ^ 2) / (1 + x ^ 2)
  have hu : Tendsto u (nhdsWithin 1 (Set.Iio 1)) (𝓝 0) := by
    have hcont : ContinuousAt u 1 := by
      dsimp [u]
      exact (continuousAt_const.sub (continuousAt_id.pow 2)).div
        (continuousAt_const.add (continuousAt_id.pow 2)) (by norm_num)
    simpa [u] using hcont.tendsto.mono_left inf_le_left
  have hu_ne : ∀ᶠ x in nhdsWithin 1 (Set.Iio 1), u x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin, eventually_pos_left] with x hxlt hxpos
    have hnumpos : 0 < 1 - x ^ 2 := by
      have hp : 0 < (1 - x) * (1 + x) :=
        mul_pos (sub_pos.mpr hxlt) (by linarith)
      nlinarith
    have hdenpos : 0 < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
    dsimp [u]
    exact div_ne_zero (ne_of_gt hnumpos) (ne_of_gt hdenpos)
  have hu_punct : Tendsto u (nhdsWithin 1 (Set.Iio 1)) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hu, ?_⟩
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hu_ne
  have harc : Tendsto (fun x => Real.arcsin (u x) / u x)
      (nhdsWithin 1 (Set.Iio 1)) (𝓝 1) := by
    have hd : HasDerivAt Real.arcsin 1 0 := by
      simpa using Real.hasDerivAt_arcsin (x := (0 : ℝ)) (by norm_num) (by norm_num)
    simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using
      hd.tendsto_slope_zero.comp hu_punct
  have hprod := harc.mul rationalTransform_tendsto_one
  have heq : leftTransform =ᶠ[nhdsWithin 1 (Set.Iio 1)]
      (fun x => Real.arcsin (u x) / u x * rationalTransform x) := by
    filter_upwards [self_mem_nhdsWithin, eventually_pos_left] with x hxlt hxpos
    have hxne : x ≠ 1 := ne_of_lt hxlt
    have hxsub : x - 1 ≠ 0 := sub_ne_zero.mpr hxne
    have hone : 1 - x ≠ 0 := sub_ne_zero.mpr hxne.symm
    have hnumpos : 0 < 1 - x ^ 2 := by
      have hp : 0 < (1 - x) * (1 + x) :=
        mul_pos (sub_pos.mpr hxlt) (by linarith)
      nlinarith
    have hdenpos : 0 < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
    have hu0 : u x ≠ 0 := by
      dsimp [u]
      exact div_ne_zero (ne_of_gt hnumpos) (ne_of_gt hdenpos)
    simp only [leftTransform, rationalTransform]
    change -Real.arcsin (u x) / (x - 1) =
      Real.arcsin (u x) / u x * (u x / (1 - x))
    field_simp [hxsub, hone, hu0] <;> ring
  have ht : Tendsto (fun x => Real.arcsin (u x) / u x * rationalTransform x)
      (nhdsWithin 1 (Set.Iio 1)) (𝓝 1) := by
    simpa using hprod
  exact (tendsto_congr' heq).2 ht

private theorem slope_left_eventuallyEq :
    slopeQuotient =ᶠ[nhdsWithin 1 (Set.Iio 1)] leftTransform := by
  filter_upwards [self_mem_nhdsWithin, eventually_pos_left] with x hxlt hxpos
  have hdenpos : 0 < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  let u : ℝ := (1 - x ^ 2) / (1 + x ^ 2)
  let v : ℝ := 2 * x / (1 + x ^ 2)
  have hnumpos : 0 < 1 - x ^ 2 := by
    have hp : 0 < (1 - x) * (1 + x) :=
      mul_pos (sub_pos.mpr hxlt) (by linarith)
    nlinarith
  have hu0 : 0 < u := by
    dsimp [u]
    exact div_pos hnumpos hdenpos
  have hv0 : 0 < v := by
    dsimp [v]
    exact div_pos (mul_pos (by norm_num) hxpos) hdenpos
  have huv : u ^ 2 + v ^ 2 = 1 := by
    dsimp [u, v]
    field_simp [ne_of_gt hdenpos] <;> ring
  have hrad : 0 ≤ 1 - u ^ 2 := by
    nlinarith [sq_nonneg v]
  have hsqrt : Real.sqrt (1 - u ^ 2) = v := by
    have hsquare := Real.sq_sqrt hrad
    have hsnonneg := Real.sqrt_nonneg (1 - u ^ 2)
    nlinarith
  have hsin : Real.sin (Real.pi / 2 - Real.arcsin u) = v := by
    rw [Real.sin_pi_div_two_sub]
    rw [Real.cos_arcsin]
    exact hsqrt
  have hang_low : -(Real.pi / 2) ≤ Real.pi / 2 - Real.arcsin u := by
    have ha := Real.arcsin_le_pi_div_two u
    have hpi : 0 ≤ Real.pi := le_of_lt Real.pi_pos
    linarith
  have hang_high : Real.pi / 2 - Real.arcsin u ≤ Real.pi / 2 := by
    have ha : 0 ≤ Real.arcsin u := Real.arcsin_nonneg.mpr (le_of_lt hu0)
    linarith
  have harc : Real.arcsin v = Real.pi / 2 - Real.arcsin u := by
    rw [← hsin]
    exact Real.arcsin_sin hang_low hang_high
  have harcsin_one : Real.arcsin 1 = Real.pi / 2 := Real.arcsin_one
  simp only [slopeQuotient, leftTransform, y]
  change (Real.arcsin v - Real.arcsin 1) / (x - 1) =
    -Real.arcsin u / (x - 1)
  rw [harc, harcsin_one]
  ring

private theorem slopeQuotient_tendsto_one :
    Tendsto slopeQuotient (nhdsWithin 1 (Set.Iio 1)) (𝓝 1) := by
  exact (tendsto_congr' slope_left_eventuallyEq).2 leftTransform_tendsto_one

theorem gap1 :
    Tendsto slopeQuotient (nhdsWithin 1 (Set.Iio 1)) (𝓝 kLeft) := by
  simpa [kLeft] using slopeQuotient_tendsto_one

theorem gap2 (L : ℝ) :
    Tendsto slopeQuotient (nhdsWithin 1 (Set.Iio 1)) (𝓝 L) ↔
      Tendsto leftTransform (nhdsWithin 1 (Set.Iio 1)) (𝓝 L) := by
  exact tendsto_congr' slope_left_eventuallyEq

theorem gap3 (L : ℝ) :
    Tendsto leftTransform (nhdsWithin 1 (Set.Iio 1)) (𝓝 L) ↔
      Tendsto rationalTransform (nhdsWithin 1 (Set.Iio 1)) (𝓝 L) := by
  constructor
  · intro h
    have hL : L = 1 := tendsto_nhds_unique h leftTransform_tendsto_one
    simpa [hL] using rationalTransform_tendsto_one
  · intro h
    have hL : L = 1 := tendsto_nhds_unique h rationalTransform_tendsto_one
    simpa [hL] using leftTransform_tendsto_one

theorem gap4 :
    Tendsto rationalTransform (nhdsWithin 1 (Set.Iio 1)) (𝓝 1) := by
  exact rationalTransform_tendsto_one

theorem gap5 : kLeft = 1 := by
  rfl
theorem gap6 : kRight = -1 := by
  rfl
theorem gap7 : kLeft * kRight = -1 := by
  norm_num [kLeft, kRight]
theorem gap8 : θ = Real.pi / 2 := by
  rfl

end

end ProofGap.Exercise1064_2
