import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.Tendsto

namespace ProofGap.Exercise1005

open Filter

noncomputable section

def f (x : ℝ) : ℝ := Real.sqrt (1 - Real.exp (-(x ^ 2)))
def dq (g : ℝ → ℝ) (a h : ℝ) : ℝ := (g (a + h) - g a) / h
def HasLeftDerivAt (g : ℝ → ℝ) (g' a : ℝ) : Prop :=
  Tendsto (dq g a) (nhdsWithin 0 (Set.Iio 0)) (nhds g')
def HasRightDerivAt (g : ℝ → ℝ) (g' a : ℝ) : Prop :=
  Tendsto (dq g a) (nhdsWithin 0 (Set.Ioi 0)) (nhds g')

def derivativeValue (x : ℝ) : ℝ :=
  x * Real.exp (-(x ^ 2)) / Real.sqrt (1 - Real.exp (-(x ^ 2)))

def leftRootQuotient (h : ℝ) : ℝ :=
  Real.sqrt (1 - Real.exp (-(h ^ 2))) / h

def normalizedRoot (h : ℝ) : ℝ :=
  Real.sqrt ((1 - Real.exp (-(h ^ 2))) / h ^ 2)

private theorem normalizedRoot_tendsto_punctured :
    Tendsto normalizedRoot (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 1) := by
  have hexp :
      Tendsto (fun t : ℝ => (Real.exp t - 1) / t)
        (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 1) := by
    simpa only [zero_add, Real.exp_zero, div_eq_mul_inv, smul_eq_mul, mul_comm] using
      (Real.hasDerivAt_exp 0).tendsto_slope_zero
  have ht0_full :
      Tendsto (fun h : ℝ => -(h ^ 2)) (nhds 0) (nhds 0) := by
    simpa using
      (((tendsto_id : Tendsto (fun h : ℝ => h) (nhds 0) (nhds 0)).pow 2).neg)
  have ht0 :
      Tendsto (fun h : ℝ => -(h ^ 2))
        (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 0) :=
    ht0_full.mono_left inf_le_left
  have ht :
      Tendsto (fun h : ℝ => -(h ^ 2))
        (nhdsWithin 0 ({0}ᶜ : Set ℝ))
        (nhdsWithin 0 ({0}ᶜ : Set ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨ht0, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : h ≠ 0 := by simpa using hh
    have ht_ne : -(h ^ 2) ≠ 0 :=
      neg_ne_zero.mpr (pow_ne_zero 2 hh0)
    simpa using ht_ne
  have hratio :
      Tendsto
        (fun h : ℝ => (Real.exp (-(h ^ 2)) - 1) / (-(h ^ 2)))
        (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 1) :=
    hexp.comp ht
  have hinner :
      Tendsto
        (fun h : ℝ => (1 - Real.exp (-(h ^ 2))) / h ^ 2)
        (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 1) := by
    apply hratio.congr'
    exact Filter.Eventually.of_forall (fun h => by ring)
  have hsqrt :
      Tendsto Real.sqrt (nhds 1) (nhds 1) := by
    simpa using (Real.continuous_sqrt.tendsto 1)
  simpa only [normalizedRoot] using hsqrt.comp hinner

theorem gap1 (x : ℝ) (hx : x ≠ 0) :
    HasLeftDerivAt f (derivativeValue x) x ∧
      HasRightDerivAt f (derivativeValue x) x := by
  have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;> simp [id] <;> ring
  have hneg : HasDerivAt (fun y : ℝ => -(y ^ 2)) (-2 * x) x := by
    convert hpow.neg using 1 <;> ring
  have hexp :
      HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2)))
        ((-2 * x) * Real.exp (-(x ^ 2))) x := by
    convert (Real.hasDerivAt_exp (-(x ^ 2))).comp x hneg using 1 <;> ring
  have hinner :
      HasDerivAt (fun y : ℝ => 1 - Real.exp (-(y ^ 2)))
        (2 * x * Real.exp (-(x ^ 2))) x := by
    convert hexp.const_sub 1 using 1 <;> ring
  have hx_sq : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hexp_lt : Real.exp (-(x ^ 2)) < 1 := by
    calc
      Real.exp (-(x ^ 2)) < Real.exp 0 :=
        Real.exp_lt_exp.mpr (neg_lt_zero.mpr hx_sq)
      _ = 1 := Real.exp_zero
  have harg : 1 - Real.exp (-(x ^ 2)) ≠ 0 :=
    ne_of_gt (sub_pos.mpr hexp_lt)
  have hroot_ne : Real.sqrt (1 - Real.exp (-(x ^ 2))) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (sub_pos.mpr hexp_lt))
  have hsqrt := (Real.hasDerivAt_sqrt harg).comp x hinner
  have hfderiv : HasDerivAt f (derivativeValue x) x := by
    convert hsqrt using 1 <;>
      simp only [derivativeValue] <;>
      field_simp [hroot_ne] <;> ring
  have hslope :
      Tendsto (dq f x) (nhdsWithin 0 ({0}ᶜ : Set ℝ))
        (nhds (derivativeValue x)) := by
    apply hfderiv.tendsto_slope_zero.congr'
    exact Filter.Eventually.of_forall (fun h => by
      simp only [dq, smul_eq_mul, div_eq_mul_inv]
      ring)
  constructor
  · unfold HasLeftDerivAt
    apply hslope.mono_left
    apply nhdsWithin_mono
    intro h hh
    have hh0 : h ≠ 0 := ne_of_lt hh
    simpa using hh0
  · unfold HasRightDerivAt
    apply hslope.mono_left
    apply nhdsWithin_mono
    intro h hh
    have hh0 : h ≠ 0 := ne_of_gt hh
    simpa using hh0

theorem gap2 (x : ℝ) (hx : x ≠ 0) :
    HasRightDerivAt f (derivativeValue x) x := by
  exact (gap1 x hx).2

theorem gap3 (x : ℝ) (hx : x ≠ 0) :
    HasLeftDerivAt f (derivativeValue x) x := by
  exact (gap1 x hx).1

theorem gap4 (L : ℝ) :
    Tendsto (dq f 0) (nhdsWithin 0 (Set.Iio 0)) (nhds L) ↔
      Tendsto leftRootQuotient (nhdsWithin 0 (Set.Iio 0)) (nhds L) := by
  have hf0 : f 0 = 0 := by
    simp [f]
  have hdq : dq f 0 = leftRootQuotient := by
    funext h
    unfold dq leftRootQuotient
    rw [zero_add, hf0, sub_zero]
    rfl
  rw [hdq]

theorem gap5 (L : ℝ) :
    Tendsto leftRootQuotient (nhdsWithin 0 (Set.Iio 0)) (nhds (-L)) ↔
      Tendsto normalizedRoot (nhdsWithin 0 (Set.Iio 0)) (nhds L) := by
  let l : Filter ℝ := nhdsWithin 0 (Set.Iio 0)
  have heq :
      leftRootQuotient =ᶠ[l] (fun h => -normalizedRoot h) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hneg : h < 0 := hh
    have hexp_le : Real.exp (-(h ^ 2)) ≤ 1 := by
      calc
        Real.exp (-(h ^ 2)) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (neg_nonpos.mpr (sq_nonneg h))
        _ = 1 := Real.exp_zero
    have harg : 0 ≤ 1 - Real.exp (-(h ^ 2)) :=
      sub_nonneg.mpr hexp_le
    simp only [leftRootQuotient, normalizedRoot]
    rw [Real.sqrt_div harg, Real.sqrt_sq_eq_abs, abs_of_neg hneg]
    ring
  constructor
  · intro hleft
    have hneg :
        Tendsto (fun h => -leftRootQuotient h) l (nhds (-(-L))) :=
      hleft.neg
    have hnorm : Tendsto normalizedRoot l (nhds (-(-L))) := by
      apply hneg.congr'
      filter_upwards [heq] with h hh
      simp [hh]
    simpa using hnorm
  · intro hnorm
    have hneg :
        Tendsto (fun h => -normalizedRoot h) l (nhds (-L)) :=
      hnorm.neg
    apply hneg.congr'
    filter_upwards [heq] with h hh
    simp [hh]

theorem gap6 :
    Tendsto normalizedRoot (nhdsWithin 0 (Set.Iio 0)) (nhds 1) := by
  apply normalizedRoot_tendsto_punctured.mono_left
  apply nhdsWithin_mono
  intro h hh
  have hh0 : h ≠ 0 := ne_of_lt hh
  simpa using hh0

theorem gap7 :
    HasLeftDerivAt f (-1) 0 := by
  unfold HasLeftDerivAt
  exact (gap4 (-1)).2 ((gap5 1).2 gap6)

theorem gap8 :
    HasRightDerivAt f 1 0 := by
  let l : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
  have hnorm : Tendsto normalizedRoot l (nhds 1) := by
    apply normalizedRoot_tendsto_punctured.mono_left
    apply nhdsWithin_mono
    intro h hh
    have hh0 : h ≠ 0 := ne_of_gt hh
    simpa using hh0
  have hf0 : f 0 = 0 := by
    simp [f]
  have heq : dq f 0 =ᶠ[l] normalizedRoot := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hpos : 0 < h := hh
    have hexp_le : Real.exp (-(h ^ 2)) ≤ 1 := by
      calc
        Real.exp (-(h ^ 2)) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (neg_nonpos.mpr (sq_nonneg h))
        _ = 1 := Real.exp_zero
    have harg : 0 ≤ 1 - Real.exp (-(h ^ 2)) :=
      sub_nonneg.mpr hexp_le
    unfold dq
    rw [zero_add, hf0, sub_zero]
    unfold f normalizedRoot
    rw [Real.sqrt_div harg, Real.sqrt_sq_eq_abs, abs_of_pos hpos]
  unfold HasRightDerivAt
  exact (tendsto_congr' heq).2 hnorm

end

end ProofGap.Exercise1005
