import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open Filter Topology
open scoped Interval

namespace ProofGap.Exercise2233

noncomputable section

def puncturedZero := nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ

def cosineQuotient (x : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..x, Real.cos (t ^ 2)) / x

def cosineDerivativeRatio (x : ℝ) : ℝ := Real.cos (x ^ 2)

def arctanQuotient (x : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..x, Real.arctan t ^ 2) / Real.sqrt (x ^ 2 + 1)

def arctanDerivativeRatio (x : ℝ) : ℝ :=
  Real.arctan x ^ 2 / (x / Real.sqrt (1 + x ^ 2))

def expIntegral (c x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, Real.exp (c * t ^ 2)

def expOriginalRatio (x : ℝ) : ℝ :=
  expIntegral 1 x ^ 2 / expIntegral 2 x

def expFirstRatio (x : ℝ) : ℝ :=
  (2 * Real.exp (x ^ 2) * expIntegral 1 x) / Real.exp (2 * x ^ 2)

def expSecondRatio (x : ℝ) : ℝ :=
  (2 * expIntegral 1 x) / Real.exp (x ^ 2)

def expThirdRatio (x : ℝ) : ℝ :=
  (2 * Real.exp (x ^ 2)) / (2 * x * Real.exp (x ^ 2))

private theorem reciprocal_tendsto_zero :
    Tendsto (fun x : ℝ => 1 / x) atTop (nhds 0) := by
  simpa [one_div] using
    (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0))

private theorem continuous_intervalIntegral_hasDerivAt
    {f : ℝ → ℝ} (hf : Continuous f) (a x : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ t in a..y, f t) (f x) x := by
  have hi : IntervalIntegrable f MeasureTheory.volume a x :=
    hf.intervalIntegrable a x
  have hsm : StronglyMeasurableAtFilter f (nhds x) MeasureTheory.volume :=
    hf.stronglyMeasurable.stronglyMeasurableAtFilter
  have ht : Tendsto f (nhds x) (nhds (f x)) := hf.continuousAt
  exact intervalIntegral.integral_hasDerivAt_right hi hsm ht

private theorem nondecreasing_of_nonnegative_derivative
    {f f' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ∀ x : ℝ, HasDerivAt f (f' x) x)
    (hnonneg : ∀ x ∈ Set.Ioo a b, 0 ≤ f' x) :
    f a ≤ f b := by
  rcases eq_or_lt_of_le hab with hab_eq | hab_lt
  · subst b
    exact le_rfl
  · have hdiff : Differentiable ℝ f := fun x => (hf x).differentiableAt
    obtain ⟨c, hc, hcs⟩ :=
      exists_hasDerivAt_eq_slope f f' hab_lt
        hdiff.continuous.continuousOn (fun x _ => hf x)
    have hquot : 0 ≤ (f b - f a) / (b - a) := by
      rw [← hcs]
      exact hnonneg c hc
    have hba : 0 < b - a := sub_pos.mpr hab_lt
    have hsub : 0 ≤ f b - f a := by
      rw [show f b - f a =
          ((f b - f a) / (b - a)) * (b - a) by
            field_simp [ne_of_gt hba] <;> ring]
      exact mul_nonneg hquot (le_of_lt hba)
    linarith

private theorem tendsto_div_atTop_of_deriv_div
    {f g f' g' : ℝ → ℝ} {L : ℝ}
    (hf : ∀ x : ℝ, HasDerivAt f (f' x) x)
    (hg : ∀ x : ℝ, HasDerivAt g (g' x) x)
    (hgpos : ∀ᶠ x in atTop, 0 < g' x)
    (hginfty : Tendsto g atTop atTop)
    (hquot : Tendsto (fun x => f' x / g' x) atTop (nhds L)) :
    Tendsto (fun x => f x / g x) atTop (nhds L) := by
  have hginv : Tendsto (fun x => 1 / g x) atTop (nhds 0) := by
    simpa only [Function.comp_apply] using
      reciprocal_tendsto_zero.comp hginfty
  have hgpositive : ∀ᶠ x in atTop, 0 < g x :=
    hginfty.eventually (eventually_gt_atTop (0 : ℝ))
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    let q : ℝ := (a + L) / 2
    have haq : a < q := by
      dsimp [q]
      linarith
    have hqL : q < L := by
      dsimp [q]
      linarith
    have hstart : ∀ᶠ y in atTop,
        q < f' y / g' y ∧ 0 < g' y :=
      ((tendsto_order.1 hquot).1 q hqL).and hgpos
    rcases eventually_atTop.1 hstart with ⟨A, hA⟩
    have hconstant :
        Tendsto (fun _ : ℝ => f A - q * g A) atTop
          (nhds (f A - q * g A)) := tendsto_const_nhds
    have hzero :
        Tendsto (fun x => (f A - q * g A) * (1 / g x)) atTop
          (nhds 0) := by
      simpa using hconstant.mul hginv
    have hqconstant : Tendsto (fun _ : ℝ => q) atTop (nhds q) :=
      tendsto_const_nhds
    have hbound :
        Tendsto (fun x => q + (f A - q * g A) * (1 / g x)) atTop
          (nhds q) := by
      simpa using hqconstant.add hzero
    have hbound_event : ∀ᶠ x in atTop,
        a < q + (f A - q * g A) * (1 / g x) :=
      (tendsto_order.1 hbound).1 a haq
    filter_upwards [eventually_ge_atTop A, hgpositive, hbound_event] with x hx hgx hbx
    have hdifference : ∀ y : ℝ,
        HasDerivAt (fun z => f z - q * g z)
          (f' y - q * g' y) y := by
      intro y
      exact (hf y).sub ((hg y).const_mul q)
    have hmono : f A - q * g A ≤ f x - q * g x :=
      nondecreasing_of_nonnegative_derivative hx hdifference (by
        intro y hy
        have hydata := hA y (le_of_lt hy.1)
        have hymul : q * g' y < f' y :=
          (lt_div_iff₀ hydata.2).mp hydata.1
        linarith)
    have halgebra :
        q + (f A - q * g A) * (1 / g x) ≤ f x / g x := by
      apply (le_div_iff₀ hgx).2
      field_simp [ne_of_gt hgx] <;> linarith [hmono]
    exact lt_of_lt_of_le hbx halgebra
  · intro b hb
    let q : ℝ := (L + b) / 2
    have hLq : L < q := by
      dsimp [q]
      linarith
    have hqb : q < b := by
      dsimp [q]
      linarith
    have hstart : ∀ᶠ y in atTop,
        f' y / g' y < q ∧ 0 < g' y :=
      ((tendsto_order.1 hquot).2 q hLq).and hgpos
    rcases eventually_atTop.1 hstart with ⟨A, hA⟩
    have hconstant :
        Tendsto (fun _ : ℝ => f A - q * g A) atTop
          (nhds (f A - q * g A)) := tendsto_const_nhds
    have hzero :
        Tendsto (fun x => (f A - q * g A) * (1 / g x)) atTop
          (nhds 0) := by
      simpa using hconstant.mul hginv
    have hqconstant : Tendsto (fun _ : ℝ => q) atTop (nhds q) :=
      tendsto_const_nhds
    have hbound :
        Tendsto (fun x => q + (f A - q * g A) * (1 / g x)) atTop
          (nhds q) := by
      simpa using hqconstant.add hzero
    have hbound_event : ∀ᶠ x in atTop,
        q + (f A - q * g A) * (1 / g x) < b :=
      (tendsto_order.1 hbound).2 b hqb
    filter_upwards [eventually_ge_atTop A, hgpositive, hbound_event] with x hx hgx hbx
    have hdifference : ∀ y : ℝ,
        HasDerivAt (fun z => q * g z - f z)
          (q * g' y - f' y) y := by
      intro y
      exact ((hg y).const_mul q).sub (hf y)
    have hmono : q * g A - f A ≤ q * g x - f x :=
      nondecreasing_of_nonnegative_derivative hx hdifference (by
        intro y hy
        have hydata := hA y (le_of_lt hy.1)
        have hymul : f' y < q * g' y :=
          (div_lt_iff₀ hydata.2).mp hydata.1
        linarith)
    have halgebra :
        f x / g x ≤ q + (f A - q * g A) * (1 / g x) := by
      apply (div_le_iff₀ hgx).2
      field_simp [ne_of_gt hgx] <;> linarith [hmono]
    exact lt_of_le_of_lt halgebra hbx

private theorem cosineDerivativeRatio_tendsto_one :
    Tendsto cosineDerivativeRatio puncturedZero (nhds 1) := by
  have hc : Continuous (fun x : ℝ => Real.cos (x ^ 2)) := by
    simpa only [Function.comp_apply, id_eq] using
      Real.continuous_cos.comp (continuous_id.pow 2)
  have h : Tendsto (fun x : ℝ => Real.cos (x ^ 2)) (nhds 0)
      (nhds ((fun x : ℝ => Real.cos (x ^ 2)) 0)) :=
    hc.continuousAt
  have h1 : Tendsto (fun x : ℝ => Real.cos (x ^ 2)) (nhds 0) (nhds 1) := by
    convert h using 1 <;> norm_num
  unfold cosineDerivativeRatio puncturedZero
  exact h1.mono_left inf_le_left

private theorem cosineQuotient_tendsto_one :
    Tendsto cosineQuotient puncturedZero (nhds 1) := by
  let F : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, Real.cos (t ^ 2)
  have hc : Continuous (fun t : ℝ => Real.cos (t ^ 2)) := by
    simpa only [Function.comp_apply, id_eq] using
      Real.continuous_cos.comp (continuous_id.pow 2)
  have hd : HasDerivAt F 1 0 := by
    dsimp [F]
    simpa using continuous_intervalIntegral_hasDerivAt hc 0 0
  have hs : Tendsto (slope F 0) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    hasDerivAt_iff_tendsto_slope.mp hd
  have heq : slope F 0 = cosineQuotient := by
    funext x
    simp [F, slope, cosineQuotient, div_eq_mul_inv, mul_comm]
  unfold puncturedZero
  rw [← heq]
  exact hs

private theorem arctanDenominator_tendsto_one :
    Tendsto (fun x : ℝ => x / Real.sqrt (1 + x ^ 2)) atTop (nhds 1) := by
  have hbase :
      Tendsto (fun x : ℝ => 1 + (1 / x) ^ 2) atTop (nhds (1 + 0 ^ 2)) :=
    tendsto_const_nhds.add (reciprocal_tendsto_zero.pow 2)
  have hsqrt :
      Tendsto (fun x : ℝ => Real.sqrt (1 + (1 / x) ^ 2)) atTop (nhds 1) := by
    convert (Real.continuous_sqrt.tendsto (1 + 0 ^ 2)).comp hbase using 1 <;>
      norm_num
  have hinv :
      Tendsto (fun x : ℝ => 1 / Real.sqrt (1 + (1 / x) ^ 2)) atTop (nhds 1) := by
    convert tendsto_const_nhds.div hsqrt (by norm_num : (1 : ℝ) ≠ 0) using 1 <;>
      norm_num
  have heq :
      (fun x : ℝ => 1 / Real.sqrt (1 + (1 / x) ^ 2)) =ᶠ[atTop]
        (fun x : ℝ => x / Real.sqrt (1 + x ^ 2)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hfac : 1 + x ^ 2 = x ^ 2 * (1 + (1 / x) ^ 2) := by
      field_simp [ne_of_gt hx]
      <;> ring
    rw [hfac, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq_eq_abs, abs_of_pos hx]
    field_simp [ne_of_gt hx, Real.sqrt_ne_zero'.mpr (by positivity)]
  exact hinv.congr' heq

private theorem arctanDerivativeRatio_tendsto :
    Tendsto arctanDerivativeRatio atTop (nhds (Real.pi ^ 2 / 4)) := by
  have hatan : Tendsto Real.arctan atTop (nhds (Real.pi / 2)) :=
    Real.tendsto_arctan_atTop.mono_right inf_le_left
  have ha : Tendsto (fun x : ℝ => Real.arctan x ^ 2) atTop
      (nhds ((Real.pi / 2) ^ 2)) := hatan.pow 2
  have h := ha.div arctanDenominator_tendsto_one (by norm_num : (1 : ℝ) ≠ 0)
  convert h using 1 <;>
    simp [arctanDerivativeRatio] <;> ring

private theorem sqrt_sq_add_one_atTop :
    Tendsto (fun x : ℝ => Real.sqrt (x ^ 2 + 1)) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop (max b 0)] with x hx
  have hx0 : 0 ≤ x := le_trans (le_max_right b 0) hx
  have hsqrtx : Real.sqrt (x ^ 2) = x := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hx0]
  have hs : x ≤ Real.sqrt (x ^ 2 + 1) := by
    calc
      x = Real.sqrt (x ^ 2) := hsqrtx.symm
      _ ≤ Real.sqrt (x ^ 2 + 1) := Real.sqrt_le_sqrt (by linarith)
  exact le_trans (le_trans (le_max_left b 0) hx) hs

private theorem arctanQuotient_tendsto :
    Tendsto arctanQuotient atTop (nhds (Real.pi ^ 2 / 4)) := by
  have hc : Continuous (fun t : ℝ => Real.arctan t ^ 2) :=
    Real.continuous_arctan.pow 2
  have hf : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => ∫ t in (0 : ℝ)..y, Real.arctan t ^ 2)
      (Real.arctan x ^ 2) x := by
    intro x
    exact continuous_intervalIntegral_hasDerivAt hc 0 x
  have hg : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => Real.sqrt (y ^ 2 + 1))
      (x / Real.sqrt (1 + x ^ 2)) x := by
    intro x
    have hi : HasDerivAt (fun y : ℝ => y ^ 2 + 1) (2 * x) x := by
      convert ((hasDerivAt_id x).pow 2).add_const 1 using 1 <;>
        simp only [id_eq] <;> ring
    have hs := (Real.hasDerivAt_sqrt
      (by positivity : x ^ 2 + 1 ≠ 0)).comp x hi
    convert hs using 1
    rw [show 1 + x ^ 2 = x ^ 2 + 1 by ring]
    field_simp [Real.sqrt_ne_zero'.mpr (by positivity : 0 < x ^ 2 + 1)] <;>
      ring
  have hpos : ∀ᶠ x : ℝ in atTop,
      0 < x / Real.sqrt (1 + x ^ 2) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_pos hx (Real.sqrt_pos.2 (by positivity))
  have hratio : Tendsto
      (fun x : ℝ => Real.arctan x ^ 2 /
        (x / Real.sqrt (1 + x ^ 2))) atTop
      (nhds (Real.pi ^ 2 / 4)) := by
    simpa [arctanDerivativeRatio] using arctanDerivativeRatio_tendsto
  simpa [arctanQuotient] using
    tendsto_div_atTop_of_deriv_div hf hg hpos sqrt_sq_add_one_atTop hratio

private theorem hasDerivAt_expIntegral (c x : ℝ) :
    HasDerivAt (expIntegral c) (Real.exp (c * x ^ 2)) x := by
  have hc : Continuous (fun t : ℝ => Real.exp (c * t ^ 2)) := by
    simpa only [Function.comp_apply, id_eq] using
      Real.continuous_exp.comp
        ((continuous_const : Continuous (fun _ : ℝ => c)).mul (continuous_id.pow 2))
  unfold expIntegral
  exact continuous_intervalIntegral_hasDerivAt hc 0 x

private theorem square_tendsto_atTop :
    Tendsto (fun x : ℝ => x ^ 2) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop (max 1 b)] with x hx
  have h1 : 1 ≤ x := le_trans (le_max_left 1 b) hx
  have hb : b ≤ x := le_trans (le_max_right 1 b) hx
  exact le_trans hb (by nlinarith)

private theorem exp_square_tendsto_atTop :
    Tendsto (fun x : ℝ => Real.exp (x ^ 2)) atTop atTop :=
  Real.tendsto_exp_atTop.comp square_tendsto_atTop

private theorem expIntegral_two_atTop :
    Tendsto (expIntegral 2) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop (max b 0)] with x hx
  have hx0 : 0 ≤ x := le_trans (le_max_right b 0) hx
  have hc : Continuous (fun t : ℝ => Real.exp ((2 : ℝ) * t ^ 2)) := by
    simpa only [Function.comp_apply, id_eq] using
      Real.continuous_exp.comp
        ((continuous_const : Continuous (fun _ : ℝ => (2 : ℝ))).mul
          (continuous_id.pow 2))
  have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ))
      MeasureTheory.volume 0 x := intervalIntegrable_const
  have hexp : IntervalIntegrable
      (fun t : ℝ => Real.exp ((2 : ℝ) * t ^ 2)) MeasureTheory.volume 0 x :=
    hc.intervalIntegrable 0 x
  have hmono : x ≤ expIntegral 2 x := by
    have h := intervalIntegral.integral_mono_on hx0 hconst hexp
      (fun t _ => Real.one_le_exp (by positivity : 0 ≤ (2 : ℝ) * t ^ 2))
    simpa [expIntegral] using h
  exact le_trans (le_trans (le_max_left b 0) hx) hmono

private theorem expThirdRatio_eq_reciprocal (x : ℝ) :
    expThirdRatio x = 1 / x := by
  by_cases hx : x = 0
  · subst x
    simp [expThirdRatio]
  · unfold expThirdRatio
    field_simp [hx, Real.exp_ne_zero]
    <;> ring

private theorem expThirdRatio_tendsto_zero :
    Tendsto expThirdRatio atTop (nhds 0) := by
  have heq : expThirdRatio = fun x : ℝ => 1 / x := by
    funext x
    exact expThirdRatio_eq_reciprocal x
  rw [heq]
  exact reciprocal_tendsto_zero

private theorem expSecondRatio_tendsto_zero :
    Tendsto expSecondRatio atTop (nhds 0) := by
  have hf : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => 2 * expIntegral 1 y)
      (2 * Real.exp (x ^ 2)) x := by
    intro x
    simpa only [one_mul] using (hasDerivAt_expIntegral 1 x).const_mul 2
  have hg : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => Real.exp (y ^ 2))
      (2 * x * Real.exp (x ^ 2)) x := by
    intro x
    convert (Real.hasDerivAt_exp (x ^ 2)).comp x ((hasDerivAt_id x).pow 2) using 1 <;>
      simp only [id_eq] <;> ring
  have hpos : ∀ᶠ x : ℝ in atTop,
      0 < 2 * x * Real.exp (x ^ 2) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    positivity
  have hratio : Tendsto
      (fun x : ℝ => (2 * Real.exp (x ^ 2)) /
        (2 * x * Real.exp (x ^ 2))) atTop (nhds 0) := by
    simpa [expThirdRatio] using expThirdRatio_tendsto_zero
  simpa [expSecondRatio] using
    tendsto_div_atTop_of_deriv_div hf hg hpos exp_square_tendsto_atTop hratio

private theorem expFirstRatio_eq_expSecondRatio (x : ℝ) :
    expFirstRatio x = expSecondRatio x := by
  unfold expFirstRatio expSecondRatio
  rw [show 2 * x ^ 2 = x ^ 2 + x ^ 2 by ring, Real.exp_add]
  field_simp [Real.exp_ne_zero]

private theorem expFirstRatio_tendsto_zero :
    Tendsto expFirstRatio atTop (nhds 0) := by
  have heq : expFirstRatio = expSecondRatio := by
    funext x
    exact expFirstRatio_eq_expSecondRatio x
  rw [heq]
  exact expSecondRatio_tendsto_zero

private theorem expOriginalRatio_tendsto_zero :
    Tendsto expOriginalRatio atTop (nhds 0) := by
  have hf : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => expIntegral 1 y ^ 2)
      (2 * Real.exp (x ^ 2) * expIntegral 1 x) x := by
    intro x
    convert (hasDerivAt_expIntegral 1 x).pow 2 using 1 <;>
      simp only [one_mul] <;> ring
  have hg : ∀ x : ℝ, HasDerivAt (expIntegral 2)
      (Real.exp (2 * x ^ 2)) x := hasDerivAt_expIntegral 2
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < Real.exp (2 * x ^ 2) :=
    Filter.Eventually.of_forall (fun x => Real.exp_pos (2 * x ^ 2))
  have hratio : Tendsto
      (fun x : ℝ => (2 * Real.exp (x ^ 2) * expIntegral 1 x) /
        Real.exp (2 * x ^ 2)) atTop (nhds 0) := by
    simpa [expFirstRatio] using expFirstRatio_tendsto_zero
  simpa [expOriginalRatio] using
    tendsto_div_atTop_of_deriv_div hf hg hpos expIntegral_two_atTop hratio

theorem gap1 :
    ∀ L : ℝ, Tendsto cosineQuotient puncturedZero (𝓝 L) ↔
      Tendsto cosineDerivativeRatio puncturedZero (𝓝 L) := by
  intro L
  haveI : NeBot puncturedZero := by
    unfold puncturedZero
    infer_instance
  constructor
  · intro h
    have hL : L = 1 := tendsto_nhds_unique h cosineQuotient_tendsto_one
    simpa [hL] using cosineDerivativeRatio_tendsto_one
  · intro h
    have hL : L = 1 := tendsto_nhds_unique h cosineDerivativeRatio_tendsto_one
    simpa [hL] using cosineQuotient_tendsto_one

theorem gap2 :
    Tendsto cosineDerivativeRatio puncturedZero (𝓝 1) := by
  exact cosineDerivativeRatio_tendsto_one

theorem gap3 :
    Tendsto cosineQuotient puncturedZero (𝓝 1) := by
  exact (gap1 1).2 gap2

theorem gap4 :
    ∀ L : ℝ, Tendsto arctanQuotient atTop (𝓝 L) ↔
      Tendsto arctanDerivativeRatio atTop (𝓝 L) := by
  intro L
  constructor
  · intro h
    have hL : L = Real.pi ^ 2 / 4 :=
      tendsto_nhds_unique h arctanQuotient_tendsto
    simpa [hL] using arctanDerivativeRatio_tendsto
  · intro h
    have hL : L = Real.pi ^ 2 / 4 :=
      tendsto_nhds_unique h arctanDerivativeRatio_tendsto
    simpa [hL] using arctanQuotient_tendsto

theorem gap5 :
    Tendsto arctanDerivativeRatio atTop (𝓝 (Real.pi ^ 2 / 4)) := by
  exact arctanDerivativeRatio_tendsto

theorem gap6 :
    Tendsto arctanQuotient atTop (𝓝 (Real.pi ^ 2 / 4)) := by
  exact (gap4 (Real.pi ^ 2 / 4)).2 gap5

theorem gap7 :
    ∀ L : ℝ, Tendsto expOriginalRatio atTop (𝓝 L) ↔
      Tendsto expFirstRatio atTop (𝓝 L) := by
  intro L
  constructor
  · intro h
    have hL : L = 0 := tendsto_nhds_unique h expOriginalRatio_tendsto_zero
    simpa [hL] using expFirstRatio_tendsto_zero
  · intro h
    have hL : L = 0 := tendsto_nhds_unique h expFirstRatio_tendsto_zero
    simpa [hL] using expOriginalRatio_tendsto_zero

theorem gap8 :
    ∀ L : ℝ, Tendsto expFirstRatio atTop (𝓝 L) ↔
      Tendsto expSecondRatio atTop (𝓝 L) := by
  intro L
  have heq : expFirstRatio = expSecondRatio := by
    funext x
    exact expFirstRatio_eq_expSecondRatio x
  rw [heq]

theorem gap9 :
    ∀ L : ℝ, Tendsto expSecondRatio atTop (𝓝 L) ↔
      Tendsto expThirdRatio atTop (𝓝 L) := by
  intro L
  constructor
  · intro h
    have hL : L = 0 := tendsto_nhds_unique h expSecondRatio_tendsto_zero
    simpa [hL] using expThirdRatio_tendsto_zero
  · intro h
    have hL : L = 0 := tendsto_nhds_unique h expThirdRatio_tendsto_zero
    simpa [hL] using expSecondRatio_tendsto_zero

theorem gap10 :
    ∀ L : ℝ, Tendsto expThirdRatio atTop (𝓝 L) ↔
      Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 L) := by
  intro L
  have heq : expThirdRatio = fun x : ℝ => 1 / x := by
    funext x
    exact expThirdRatio_eq_reciprocal x
  rw [heq]

theorem gap11 :
    Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
  exact reciprocal_tendsto_zero

theorem gap12 :
    Tendsto expOriginalRatio atTop (𝓝 0) := by
  exact (gap7 0).2 ((gap8 0).2 ((gap9 0).2 ((gap10 0).2 gap11)))

end

end ProofGap.Exercise2233
