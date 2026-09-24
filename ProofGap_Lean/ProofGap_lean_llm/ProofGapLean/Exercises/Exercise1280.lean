import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1280

noncomputable section

open Filter

def y (x : ℝ) : ℝ := Real.rpow (1 + 1 / x) x
def z (x : ℝ) : ℝ := Real.log (1 + 1 / x) - 1 / (1 + x)
def domain (x : ℝ) : Prop := x < -1 ∨ 0 < x

private theorem baseEqDiv (x : ℝ) (hx : x ≠ 0) :
    1 + 1 / x = (x + 1) / x := by
  field_simp [hx]
  <;> ring

private theorem rpowBasePos (x : ℝ) (hx : domain x) : 0 < 1 + 1 / x := by
  rcases hx with hx | hx
  · have hx0 : x < 0 := by linarith
    have hxne : x ≠ 0 := ne_of_lt hx0
    have hnum : x + 1 < 0 := by linarith
    rw [baseEqDiv x hxne]
    exact div_pos_of_neg_of_neg hnum hx0
  · have hxne : x ≠ 0 := ne_of_gt hx
    have hnum : 0 < x + 1 := by linarith
    rw [baseEqDiv x hxne]
    exact div_pos hnum hx

private theorem logCorrectionPos (x : ℝ) (hx : domain x) :
    0 < Real.log (1 + 1 / x) - 1 / (1 + x) := by
  have hx0 : x ≠ 0 := by
    rcases hx with hx | hx
    · linarith
    · linarith
  have hx1 : 1 + x ≠ 0 := by
    rcases hx with hx | hx
    · linarith
    · linarith
  have hx1' : x + 1 ≠ 0 := by simpa [add_comm] using hx1
  have hb : 0 < 1 + 1 / x := rpowBasePos x hx
  have hb1 : 1 + 1 / x ≠ 1 := by
    intro h
    have hzero : 1 / x = 0 := by linarith
    exact (one_div_ne_zero hx0) hzero
  have hbinv1 : (1 + 1 / x)⁻¹ ≠ 1 := by
    intro h
    apply hb1
    calc
      1 + 1 / x = ((1 + 1 / x)⁻¹)⁻¹ := by simp
      _ = (1 : ℝ)⁻¹ := by rw [h]
      _ = 1 := by norm_num
  have hlog := Real.log_lt_sub_one_of_pos (inv_pos.mpr hb) hbinv1
  rw [Real.log_inv] at hlog
  have heq : 1 - (1 + 1 / x)⁻¹ = 1 / (1 + x) := by
    rw [baseEqDiv x hx0, inv_div]
    field_simp [hx1, hx1']
    <;> ring
  rw [← heq]
  linarith

private theorem hasDerivAtBase (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => 1 + 1 / t) (-1 / x ^ 2) x := by
  have hinv := (hasDerivAt_id x).inv hx
  have hsum := (hasDerivAt_const (x := x) (c := (1 : ℝ))).add hinv
  simpa only [Pi.add_apply, id_eq, one_div, zero_add] using hsum

private theorem hasDerivAtYOnDomain (x : ℝ) (hx : domain x) :
    HasDerivAt y
      (y x * (Real.log (1 + 1 / x) - 1 / (1 + x))) x := by
  have hx0 : x ≠ 0 := by
    rcases hx with hx | hx
    · linarith
    · linarith
  have hx1 : 1 + x ≠ 0 := by
    rcases hx with hx | hx
    · linarith
    · linarith
  have hx1' : x + 1 ≠ 0 := by simpa [add_comm] using hx1
  have hb : 0 < 1 + 1 / x := rpowBasePos x hx
  have hbase := hasDerivAtBase x hx0
  have hcalc := ((hbase.log hb.ne').mul (hasDerivAt_id x)).exp
  have hevent : ∀ᶠ t : ℝ in nhds x, 0 < 1 + 1 / t :=
    hbase.continuousAt (Ioi_mem_nhds hb)
  have heq :
      y =ᶠ[nhds x]
        (fun t : ℝ => Real.exp (Real.log (1 + 1 / t) * t)) := by
    filter_upwards [hevent] with t ht
    simpa only [y] using (Real.rpow_def_of_pos ht t)
  have hpoint :
      y x = Real.exp (Real.log (1 + 1 / x) * x) := by
    simpa only [y] using (Real.rpow_def_of_pos hb x)
  have hy := hcalc.congr_of_eventuallyEq heq
  simp only [Pi.mul_apply, id_eq, mul_one] at hy
  have hcoef :
      (-1 / x ^ 2) / (1 + 1 / x) * x + Real.log (1 + 1 / x) =
        Real.log (1 + 1 / x) - 1 / (1 + x) := by
    rw [baseEqDiv x hx0]
    field_simp [hx0, hx1, hx1']
    <;> ring
  rw [← hpoint, hcoef] at hy
  exact hy

private theorem hasDerivAtZOnNegativeBranch (x : ℝ) (hx : x < -1) :
    HasDerivAt z (-(1 / (x * (1 + x) ^ 2))) x := by
  have hx0 : x ≠ 0 := by linarith
  have hx1 : 1 + x ≠ 0 := by linarith
  have hx1' : x + 1 ≠ 0 := by simpa [add_comm] using hx1
  have hb : 0 < 1 + 1 / x := rpowBasePos x (Or.inl hx)
  have hbase := hasDerivAtBase x hx0
  have hlinear : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
    simpa using (hasDerivAt_const (x := x) (c := (1 : ℝ))).add (hasDerivAt_id x)
  have hrecip :
      HasDerivAt (fun t : ℝ => 1 / (1 + t)) (-1 / (1 + x) ^ 2) x := by
    simpa [one_div, inv_pow] using hlinear.inv hx1
  have hz :
      HasDerivAt z
        ((-1 / x ^ 2) / (1 + 1 / x) - (-1 / (1 + x) ^ 2)) x := by
    simpa only [z] using (hbase.log hb.ne').sub hrecip
  have halg :
      (-1 / x ^ 2) / (1 + 1 / x) - (-1 / (1 + x) ^ 2) =
        -(1 / (x * (1 + x) ^ 2)) := by
    rw [baseEqDiv x hx0]
    field_simp [hx0, hx1, hx1']
    <;> ring
  rw [halg] at hz
  exact hz

private theorem strictMonoOnOfHasDerivAtPos
    (f : ℝ → ℝ) (s : Set ℝ)
    (hsegment : ∀ ⦃a b : ℝ⦄, a ∈ s → b ∈ s → a < b → Set.Icc a b ⊆ s)
    (hderiv : ∀ x ∈ s, ∃ d : ℝ, HasDerivAt f d x ∧ 0 < d) :
    StrictMonoOn f s := by
  intro a ha b hb hab
  have hsub : Set.Icc a b ⊆ s := hsegment ha hb hab
  have hcont : ContinuousOn f (Set.Icc a b) := by
    intro t ht
    obtain ⟨d, hd, hdpos⟩ := hderiv t (hsub ht)
    exact hd.continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (Set.Ioo a b) := by
    intro t ht
    obtain ⟨d, hd, hdpos⟩ := hderiv t
      (hsub ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
    exact hd.differentiableAt.differentiableWithinAt
  obtain ⟨t, ht, hderivEq⟩ :=
    exists_deriv_eq_slope f hab hcont hdiff
  obtain ⟨d, hd, hdpos⟩ := hderiv t
    (hsub ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
  have hdEq : deriv f t = d := hd.deriv
  have hslope : 0 < (f b - f a) / (b - a) := by
    linarith
  rcases (div_pos_iff.mp hslope) with h | h <;> linarith

theorem gap1 (x : ℝ) (hx : domain x) :
    deriv y x = y x * (Real.log (1 + 1 / x) - 1 / (1 + x)) := by
  exact (hasDerivAtYOnDomain x hx).deriv

theorem gap2 (x : ℝ) (hx : x < -1) :
    0 < y x := by
  simpa only [y] using
    (Real.rpow_pos_of_pos (rpowBasePos x (Or.inl hx)) x)

theorem gap3 :
    StrictMonoOn y (Set.Iio (-1 : ℝ)) ∧
      StrictMonoOn y (Set.Ioi (0 : ℝ)) := by
  constructor
  · refine strictMonoOnOfHasDerivAtPos y (Set.Iio (-1 : ℝ)) ?_ ?_
    · intro a b ha hb hab t ht
      exact lt_of_le_of_lt ht.2 hb
    · intro x hx
      have hdom : domain x := Or.inl hx
      have hypos : 0 < y x := by
        simpa only [y] using
          (Real.rpow_pos_of_pos (rpowBasePos x hdom) x)
      refine ⟨y x * (Real.log (1 + 1 / x) - 1 / (1 + x)),
        hasDerivAtYOnDomain x hdom, ?_⟩
      exact mul_pos hypos (logCorrectionPos x hdom)
  · refine strictMonoOnOfHasDerivAtPos y (Set.Ioi (0 : ℝ)) ?_ ?_
    · intro a b ha hb hab t ht
      exact lt_of_lt_of_le ha ht.1
    · intro x hx
      have hdom : domain x := Or.inr hx
      have hypos : 0 < y x := by
        simpa only [y] using
          (Real.rpow_pos_of_pos (rpowBasePos x hdom) x)
      refine ⟨y x * (Real.log (1 + 1 / x) - 1 / (1 + x)),
        hasDerivAtYOnDomain x hdom, ?_⟩
      exact mul_pos hypos (logCorrectionPos x hdom)

theorem gap4 (x : ℝ) (hx : x < -1) :
    deriv z x = -(1 / (x * (1 + x) ^ 2)) := by
  exact (hasDerivAtZOnNegativeBranch x hx).deriv

theorem gap5 (x : ℝ) (hx : x < -1) :
    -(1 / (x * (1 + x) ^ 2)) > 0 := by
  have hx0 : x < 0 := by linarith
  have hx1 : 1 + x ≠ 0 := by linarith
  have hsquare : 0 < (1 + x) ^ 2 := sq_pos_of_ne_zero hx1
  have hden : x * (1 + x) ^ 2 < 0 := mul_neg_of_neg_of_pos hx0 hsquare
  exact neg_pos.mpr (one_div_neg.mpr hden)

theorem gap6 (x : ℝ) (hx : x < -1) :
    deriv z x > 0 := by
  rw [gap4 x hx]
  exact gap5 x hx

theorem gap7 :
    StrictMonoOn z (Set.Iio (-1 : ℝ)) := by
  refine strictMonoOnOfHasDerivAtPos z (Set.Iio (-1 : ℝ)) ?_ ?_
  · intro a b ha hb hab t ht
    exact lt_of_le_of_lt ht.2 hb
  · intro x hx
    exact ⟨-(1 / (x * (1 + x) ^ 2)),
      hasDerivAtZOnNegativeBranch x hx, gap5 x hx⟩

theorem gap8 :
    Tendsto z atBot (nhds 0) := by
  have hinv : Tendsto (fun x : ℝ => 1 / x) atBot (nhds 0) := by
    simpa only [one_div] using
      (tendsto_inv_atBot_zero : Tendsto (fun x : ℝ => x⁻¹) atBot (nhds 0))
  have hbase : Tendsto (fun x : ℝ => 1 + 1 / x) atBot (nhds 1) := by
    simpa using (tendsto_const_nhds.add hinv)
  have hlogAtOne :
      Tendsto Real.log (nhds (1 : ℝ)) (nhds (Real.log (1 : ℝ))) :=
    (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).continuousAt
  rw [Real.log_one] at hlogAtOne
  have hlog : Tendsto (fun x : ℝ => Real.log (1 + 1 / x)) atBot (nhds 0) := by
    simpa only [Function.comp_apply] using hlogAtOne.comp hbase
  have hratio :
      Tendsto (fun x : ℝ => (1 / x) / (1 + 1 / x)) atBot (nhds 0) := by
    simpa using hinv.div hbase (by norm_num : (1 : ℝ) ≠ 0)
  have heq :
      (fun x : ℝ => 1 / (1 + x)) =ᶠ[atBot]
        (fun x : ℝ => (1 / x) / (1 + 1 / x)) := by
    filter_upwards [eventually_lt_atBot (-1 : ℝ)] with x hx
    have hx0 : x ≠ 0 := by linarith
    have hx1 : 1 + x ≠ 0 := by linarith
    have hx1' : x + 1 ≠ 0 := by simpa [add_comm] using hx1
    rw [baseEqDiv x hx0]
    field_simp [hx0, hx1, hx1']
    <;> ring
  have hsecond : Tendsto (fun x : ℝ => 1 / (1 + x)) atBot (nhds 0) :=
    hratio.congr' heq.symm
  simpa only [z, sub_zero] using hlog.sub hsecond

theorem gap9 (x : ℝ) (hx : x < -1) :
    z x > 0 := by
  simpa only [z] using logCorrectionPos x (Or.inl hx)

theorem gap10 (x : ℝ) (hx : x < -1) :
    deriv y x > 0 := by
  rw [gap1 x (Or.inl hx)]
  exact mul_pos (gap2 x hx) (logCorrectionPos x (Or.inl hx))

theorem gap11 :
    StrictMonoOn y (Set.Iio (-1 : ℝ)) := by
  exact gap3.1

theorem gap12 :
    StrictMonoOn y (Set.Ioi (0 : ℝ)) := by
  exact gap3.2

theorem gap13 (x : ℝ) (hx : x < -1) :
    Real.log (1 + 1 / x) - 1 / (1 + x) > 0 := by
  exact logCorrectionPos x (Or.inl hx)

end

end ProofGap.Exercise1280
