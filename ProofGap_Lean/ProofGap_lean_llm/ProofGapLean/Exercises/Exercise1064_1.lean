import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1064_1

noncomputable section

open Filter
open scoped Topology

def y (a x : ℝ) : ℝ :=
  Real.sqrt (1 - Real.exp (-(a ^ 2 * x ^ 2)))

def slopeQuotient (a x : ℝ) : ℝ := y a x / x

def core (a x : ℝ) : ℝ :=
  ((Real.exp (-(a ^ 2 * x ^ 2)) - 1) / (-(a ^ 2 * x ^ 2))) * a ^ 2

def leftTransform (a x : ℝ) : ℝ := -Real.sqrt (core a x)
def rightTransform (a x : ℝ) : ℝ := Real.sqrt (core a x)
def kLeft (a : ℝ) : ℝ := -|a|
def kRight (a : ℝ) : ℝ := |a|
def θ (a : ℝ) : ℝ := 2 * Real.arctan (1 / |a|)

private theorem auxCoreTendsto
    (a : ℝ) (ha : a ≠ 0) (l : Filter ℝ)
    (hx : Tendsto (fun x : ℝ => x) l (𝓝 0))
    (hx_ne : ∀ᶠ x in l, x ≠ 0) :
    Tendsto (core a) l (𝓝 (a ^ 2)) := by
  have hexp :
      Tendsto (fun t : ℝ => (Real.exp t - 1) / t) (𝓝[≠] 0) (𝓝 1) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_exp 0).tendsto_slope_zero
  have ha_const :
      Tendsto (fun _ : ℝ => a ^ 2) l (𝓝 (a ^ 2)) := tendsto_const_nhds
  have ht :
      Tendsto (fun x : ℝ => -(a ^ 2 * x ^ 2)) l (𝓝 0) := by
    simpa using (ha_const.mul (hx.pow 2)).neg
  have ht_ne : ∀ᶠ x in l, -(a ^ 2 * x ^ 2) ≠ 0 := by
    filter_upwards [hx_ne] with x hx0
    exact neg_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 2 hx0))
  have ht_punct :
      Tendsto (fun x : ℝ => -(a ^ 2 * x ^ 2)) l (𝓝[≠] 0) := by
    rw [show 𝓝[≠] (0 : ℝ) = 𝓝 0 ⊓ 𝓟 ({0}ᶜ) by rfl]
    refine tendsto_inf.2 ⟨ht, ?_⟩
    exact tendsto_principal.2
      (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht_ne)
  have hratio := hexp.comp ht_punct
  simpa only [core, one_mul] using hratio.mul ha_const

private theorem auxLeftLimit (a : ℝ) (ha : a ≠ 0) :
    Tendsto (leftTransform a) (nhdsWithin 0 (Set.Iio 0)) (𝓝 (-|a|)) := by
  have hx :
      Tendsto (fun x : ℝ => x)
        (nhdsWithin (0 : ℝ) (Set.Iio 0)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hx_ne :
      ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) (Set.Iio 0), x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hxlt
    have hxlt' : x < (0 : ℝ) := by
      simpa only [Set.mem_Iio] using hxlt
    exact ne_of_lt hxlt'
  have hc := auxCoreTendsto a ha (nhdsWithin (0 : ℝ) (Set.Iio 0)) hx hx_ne
  have hsqrt :
      Tendsto Real.sqrt (𝓝 (a ^ 2)) (𝓝 (Real.sqrt (a ^ 2))) :=
    Real.continuous_sqrt.continuousAt
  have hs := hsqrt.comp hc
  simpa only [leftTransform, Real.sqrt_sq_eq_abs] using hs.neg

private theorem auxRightLimit (a : ℝ) (ha : a ≠ 0) :
    Tendsto (rightTransform a) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 |a|) := by
  have hx :
      Tendsto (fun x : ℝ => x)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hx_ne :
      ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hxgt
    have hxgt' : (0 : ℝ) < x := by
      simpa only [Set.mem_Ioi] using hxgt
    exact ne_of_gt hxgt'
  have hc := auxCoreTendsto a ha (nhdsWithin (0 : ℝ) (Set.Ioi 0)) hx hx_ne
  have hsqrt :
      Tendsto Real.sqrt (𝓝 (a ^ 2)) (𝓝 (Real.sqrt (a ^ 2))) :=
    Real.continuous_sqrt.continuousAt
  have hs := hsqrt.comp hc
  simpa only [rightTransform, Real.sqrt_sq_eq_abs] using hs

private theorem auxSlopeEqLeft (a x : ℝ) (ha : a ≠ 0) (hx : x < 0) :
    slopeQuotient a x = leftTransform a x := by
  have hn : 0 ≤ 1 - Real.exp (-(a ^ 2 * x ^ 2)) := by
    apply sub_nonneg.mpr
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr
      (neg_nonpos.mpr (mul_nonneg (sq_nonneg a) (sq_nonneg x)))
  have hcore :
      core a x = (1 - Real.exp (-(a ^ 2 * x ^ 2))) / x ^ 2 := by
    unfold core
    field_simp [ha, ne_of_lt hx]
    <;> ring
  unfold slopeQuotient y leftTransform
  rw [hcore, Real.sqrt_div hn, Real.sqrt_sq_eq_abs, abs_of_neg hx]
  field_simp [ne_of_lt hx]
  <;> ring

private theorem auxSlopeEqRight (a x : ℝ) (ha : a ≠ 0) (hx : 0 < x) :
    slopeQuotient a x = rightTransform a x := by
  have hn : 0 ≤ 1 - Real.exp (-(a ^ 2 * x ^ 2)) := by
    apply sub_nonneg.mpr
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr
      (neg_nonpos.mpr (mul_nonneg (sq_nonneg a) (sq_nonneg x)))
  have hcore :
      core a x = (1 - Real.exp (-(a ^ 2 * x ^ 2))) / x ^ 2 := by
    unfold core
    field_simp [ha, ne_of_gt hx]
    <;> ring
  unfold slopeQuotient y rightTransform
  rw [hcore, Real.sqrt_div hn, Real.sqrt_sq_eq_abs, abs_of_pos hx]

theorem gap1 (a : ℝ) :
    Tendsto (slopeQuotient a) (nhdsWithin 0 (Set.Iio 0)) (𝓝 (kLeft a)) := by
  by_cases ha : a = 0
  · subst a
    have heq :
        slopeQuotient 0 =ᶠ[nhdsWithin (0 : ℝ) (Set.Iio 0)]
          (fun _ : ℝ => 0) := by
      apply Filter.Eventually.of_forall
      intro x
      simp [slopeQuotient, y]
    have hz :
        Tendsto (slopeQuotient 0) (nhdsWithin (0 : ℝ) (Set.Iio 0)) (𝓝 0) :=
      (tendsto_congr' heq).mpr tendsto_const_nhds
    simpa only [kLeft, abs_zero, neg_zero] using hz
  · have heq :
        slopeQuotient a =ᶠ[nhdsWithin 0 (Set.Iio 0)] leftTransform a := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact auxSlopeEqLeft a x ha (by simpa only [Set.mem_Iio] using hx)
    exact (tendsto_congr' heq).mpr (auxLeftLimit a ha)

theorem gap2 (a L : ℝ) (ha : a ≠ 0) :
    Tendsto (slopeQuotient a) (nhdsWithin 0 (Set.Iio 0)) (𝓝 L) ↔
      Tendsto (leftTransform a) (nhdsWithin 0 (Set.Iio 0)) (𝓝 L) := by
  have heq :
      slopeQuotient a =ᶠ[nhdsWithin 0 (Set.Iio 0)] leftTransform a := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact auxSlopeEqLeft a x ha (by simpa only [Set.mem_Iio] using hx)
  exact tendsto_congr' heq

theorem gap3 (a : ℝ) (ha : a ≠ 0) :
    Tendsto (leftTransform a) (nhdsWithin 0 (Set.Iio 0)) (𝓝 (-|a|)) := by
  exact auxLeftLimit a ha

theorem gap4 (a : ℝ) : kLeft a = -|a| := by
  rfl

theorem gap5 (a : ℝ) :
    Tendsto (slopeQuotient a) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (kRight a)) := by
  by_cases ha : a = 0
  · subst a
    have heq :
        slopeQuotient 0 =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
          (fun _ : ℝ => 0) := by
      apply Filter.Eventually.of_forall
      intro x
      simp [slopeQuotient, y]
    have hz :
        Tendsto (slopeQuotient 0) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) :=
      (tendsto_congr' heq).mpr tendsto_const_nhds
    simpa only [kRight, abs_zero] using hz
  · have heq :
        slopeQuotient a =ᶠ[nhdsWithin 0 (Set.Ioi 0)] rightTransform a := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact auxSlopeEqRight a x ha (by simpa only [Set.mem_Ioi] using hx)
    exact (tendsto_congr' heq).mpr (auxRightLimit a ha)

theorem gap6 (a L : ℝ) (ha : a ≠ 0) :
    Tendsto (slopeQuotient a) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L) ↔
      Tendsto (rightTransform a) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L) := by
  have heq :
      slopeQuotient a =ᶠ[nhdsWithin 0 (Set.Ioi 0)] rightTransform a := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact auxSlopeEqRight a x ha (by simpa only [Set.mem_Ioi] using hx)
  exact tendsto_congr' heq

theorem gap7 (a : ℝ) (ha : a ≠ 0) :
    Tendsto (rightTransform a) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 |a|) := by
  exact auxRightLimit a ha

theorem gap8 (a : ℝ) : kRight a = |a| := by
  rfl

theorem gap9 (a : ℝ) (ha : a ≠ 0) (hunit : |a| ≠ 1) :
    Real.tan (θ a) = 2 * |a| / (|a| ^ 2 - 1) := by
  have habs : |a| ≠ 0 := abs_ne_zero.mpr ha
  have habs_pos : 0 < |a| := abs_pos.mpr ha
  have hden : |a| ^ 2 - 1 ≠ 0 := by
    intro h
    apply hunit
    nlinarith [sq_nonneg (|a| - 1)]
  unfold θ
  rw [Real.tan_two_mul, Real.tan_arctan]
  field_simp [habs, hden]
  <;> ring

theorem gap10 (a : ℝ) :
    θ a = 2 * Real.arctan (1 / |a|) := by
  rfl

end

end ProofGap.Exercise1064_1
