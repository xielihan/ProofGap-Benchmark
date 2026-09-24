import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2364
noncomputable section

open Filter MeasureTheory

def integrand (a n x : ℝ) : ℝ :=
  Real.arctan (a * x) / Real.rpow x n
def zeroNormalized (a n x : ℝ) : ℝ :=
  Real.rpow x (n - 1) * integrand a n x
def infinityNormalized (a n x : ℝ) : ℝ :=
  Real.rpow x n * integrand a n x
def NearZeroIntegrable (a n : ℝ) : Prop :=
  IntegrableOn (integrand a n) (Set.Ioc (0 : ℝ) 1)
def TailIntegrable (a n : ℝ) : Prop :=
  IntegrableOn (integrand a n) (Set.Ioi (1 : ℝ))
def FullIntegrable (a n : ℝ) : Prop :=
  IntegrableOn (integrand a n) (Set.Ioi (0 : ℝ))

private theorem continuousOn_integrand_positive (a n : ℝ) :
    ContinuousOn (integrand a n) (Set.Ioi (0 : ℝ)) := by
  intro x hx
  unfold integrand
  have hx0 : x ≠ 0 := ne_of_gt hx
  exact ((Real.continuous_arctan.continuousAt.comp
      (continuousAt_const.mul continuousAt_id)).continuousWithinAt).div
    (continuousAt_id.rpow_const (Or.inl hx0)).continuousWithinAt
    (Real.rpow_pos_of_pos hx n).ne'

private theorem locallyIntegrableOn_integrand_positive (a n : ℝ) :
    LocallyIntegrableOn (integrand a n) (Set.Ioi (0 : ℝ)) :=
  (continuousOn_integrand_positive a n).locallyIntegrableOn measurableSet_Ioi

private theorem continuousOn_rpow_positive (s : ℝ) :
    ContinuousOn (fun x : ℝ => x ^ s) (Set.Ioi (0 : ℝ)) :=
  continuous_id.continuousOn.rpow_const
    (fun x hx => Or.inl (ne_of_gt hx))

private theorem integrableAtFilter_rpow_nhdsGT_zero_iff (s : ℝ) :
    IntegrableAtFilter (fun x : ℝ => x ^ s) (nhdsWithin 0 (Set.Ioi 0)) ↔
      -1 < s := by
  constructor
  · rintro ⟨u, hu, hint⟩
    obtain ⟨b, hb, hsub⟩ :=
      mem_nhdsGT_iff_exists_Ioo_subset.mp hu
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff hb).mp
      (hint.mono_set hsub)
  · intro hs
    exact ⟨Set.Ioo 0 1, Ioo_mem_nhdsGT zero_lt_one,
      (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr hs⟩

private theorem integrableOn_Ioc_zero_one_iff_integrableAtFilter
    {f : ℝ → ℝ}
    (hlocal : LocallyIntegrableOn f (Set.Ioi (0 : ℝ))) :
    IntegrableOn f (Set.Ioc 0 1) ↔
      IntegrableAtFilter f (nhdsWithin 0 (Set.Ioi 0)) := by
  constructor
  · intro h
    exact ⟨Set.Ioc 0 1, Ioc_mem_nhdsGT zero_lt_one, h⟩
  · rintro ⟨u, hu, hint⟩
    obtain ⟨b, hb, hsub⟩ :=
      mem_nhdsGT_iff_exists_Ioc_subset.mp hu
    have hsmall : IntegrableOn f (Set.Ioc 0 b) :=
      hint.mono_set hsub
    by_cases hb1 : 1 ≤ b
    · exact hsmall.mono_set (Set.Ioc_subset_Ioc_right hb1)
    · have hb1' : b ≤ 1 := le_of_not_ge hb1
      have hrest : IntegrableOn f (Set.Icc b 1) :=
        hlocal.integrableOn_compact_subset
          (fun x hx => hb.trans_le hx.1) isCompact_Icc
      rw [← Set.Ioc_union_Icc_eq_Ioc hb hb1', integrableOn_union]
      exact ⟨hsmall, hrest⟩

private theorem integrableOn_Ioi_one_iff_integrableAtFilter_atTop
    {f : ℝ → ℝ}
    (hlocal : LocallyIntegrableOn f (Set.Ioi (0 : ℝ))) :
    IntegrableOn f (Set.Ioi 1) ↔ IntegrableAtFilter f atTop := by
  have hlocalIci : LocallyIntegrableOn f (Set.Ici (1 : ℝ)) :=
    hlocal.mono_set (Set.Ici_subset_Ioi.mpr zero_lt_one)
  constructor
  · intro h
    have hIci : IntegrableOn f (Set.Ici 1) :=
      (integrableOn_Ici_iff_integrableOn_Ioi).2 h
    exact (integrableOn_Ici_iff_integrableAtFilter_atTop.mp hIci).1
  · intro h
    have hIci : IntegrableOn f (Set.Ici 1) :=
      integrableOn_Ici_iff_integrableAtFilter_atTop.mpr ⟨h, hlocalIci⟩
    exact (integrableOn_Ici_iff_integrableOn_Ioi).1 hIci

private theorem integrableAtFilter_iff_of_isTheta
    {f g : ℝ → ℝ} {l : Filter ℝ} [l.IsMeasurablyGenerated]
    (hθ : f =Θ[l] g)
    (hfm : StronglyMeasurableAtFilter f l)
    (hgm : StronglyMeasurableAtFilter g l) :
    IntegrableAtFilter f l ↔ IntegrableAtFilter g l := by
  constructor
  · exact fun hf => hθ.2.integrableAtFilter hgm hf
  · exact fun hg => hθ.1.integrableAtFilter hfm hg

theorem gap1 (a x : ℝ) :
    Real.arctan (a * x) = -Real.arctan (-a * x) := by
  rw [show -a * x = -(a * x) by ring, Real.arctan_neg]
  ring

theorem gap2 (a n : ℝ) (ha : 0 < a) :
    Tendsto (zeroNormalized a n) (nhdsWithin 0 (Set.Ioi 0)) (nhds a) ↔
      Tendsto (fun x => Real.arctan (a * x) / x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds a) := by
  have heq :
      zeroNormalized a n =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        fun x => Real.arctan (a * x) / x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : 0 < x := hx
    unfold zeroNormalized integrand
    simp only [div_eq_mul_inv]
    have hneg :
        (Real.rpow x n)⁻¹ = Real.rpow x (-n) :=
      (Real.rpow_neg hx0.le n).symm
    rw [hneg]
    have hmul :
        Real.rpow x (n - 1) * Real.rpow x (-n) = x⁻¹ := by
      calc
        Real.rpow x (n - 1) * Real.rpow x (-n) =
            Real.rpow x ((n - 1) + -n) :=
          (Real.rpow_add hx0 (n - 1) (-n)).symm
        _ = Real.rpow x (-1) := by congr 1 <;> ring
        _ = x⁻¹ := Real.rpow_neg_one x
    calc
      Real.rpow x (n - 1) *
          (Real.arctan (a * x) * Real.rpow x (-n)) =
          Real.arctan (a * x) *
            (Real.rpow x (n - 1) * Real.rpow x (-n)) := by ring
      _ = Real.arctan (a * x) * x⁻¹ := by rw [hmul]
  constructor
  · exact fun h => h.congr' heq
  · exact fun h => h.congr' heq.symm

theorem gap3 (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x => Real.arctan (a * x) / x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds a) := by
  have hinner : HasDerivAt (fun x : ℝ => a * x) a 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul a
  have hderiv :
      HasDerivAt (fun x : ℝ => Real.arctan (a * x)) a 0 := by
    convert (Real.hasDerivAt_arctan (a * 0)).comp 0 hinner using 1 <;>
      norm_num
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using
    hderiv.tendsto_slope_zero_right

theorem gap4 (a n : ℝ) (ha : 0 < a) :
    Tendsto (zeroNormalized a n)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds a) := by
  exact (gap2 a n ha).2 (gap3 a ha)

theorem gap5 (a n : ℝ) (ha : 0 < a) :
    NearZeroIntegrable a n ↔ n < 2 := by
  let p : ℝ → ℝ := fun x => Real.rpow x (1 - n)
  have heq :
      (fun x => integrand a n x / p x) =ᶠ[
        nhdsWithin 0 (Set.Ioi 0)] zeroNormalized a n := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : 0 < x := hx
    have hneg :
        (Real.rpow x (1 - n))⁻¹ = Real.rpow x (-(1 - n)) :=
      (Real.rpow_neg hx0.le (1 - n)).symm
    unfold p zeroNormalized
    simp only [div_eq_mul_inv]
    rw [hneg]
    rw [show -(1 - n) = n - 1 by ring]
    ring
  have hratio :
      Tendsto (fun x => integrand a n x / p x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds a) :=
    (gap4 a n ha).congr' heq.symm
  have hθ :
      p =Θ[nhdsWithin 0 (Set.Ioi 0)] integrand a n :=
    Asymptotics.isTheta_of_div_tendsto_nhds_ne_zero hratio ha.ne'
  have hpm :
      StronglyMeasurableAtFilter p (nhdsWithin 0 (Set.Ioi 0)) :=
    (continuousOn_rpow_positive (1 - n)).stronglyMeasurableAtFilter_nhdsWithin
      measurableSet_Ioi 0
  have him :
      StronglyMeasurableAtFilter (integrand a n)
        (nhdsWithin 0 (Set.Ioi 0)) :=
    (continuousOn_integrand_positive a n).stronglyMeasurableAtFilter_nhdsWithin
      measurableSet_Ioi 0
  have hiff :=
    integrableAtFilter_iff_of_isTheta hθ hpm him
  unfold NearZeroIntegrable
  rw [integrableOn_Ioc_zero_one_iff_integrableAtFilter
    (locallyIntegrableOn_integrand_positive a n)]
  rw [← hiff]
  change IntegrableAtFilter (fun x : ℝ => x ^ (1 - n))
      (nhdsWithin 0 (Set.Ioi 0)) ↔ n < 2
  rw [integrableAtFilter_rpow_nhdsGT_zero_iff]
  constructor <;> intro h <;> linarith

theorem gap6 (a n : ℝ) (ha : 0 < a) :
    Tendsto (infinityNormalized a n) atTop (nhds (Real.pi / 2)) := by
  have hax : Tendsto (fun x : ℝ => a * x) atTop atTop :=
    Tendsto.const_mul_atTop ha tendsto_id
  have hatan :
      Tendsto (fun x : ℝ => Real.arctan (a * x)) atTop
        (nhds (Real.pi / 2)) :=
    by
      simpa only [Function.comp_apply] using
        tendsto_nhds_of_tendsto_nhdsWithin
          (Real.tendsto_arctan_atTop.comp hax)
  apply hatan.congr'
  filter_upwards [Filter.eventually_gt_atTop 0] with x hx
  unfold infinityNormalized integrand
  have hxn : x ^ n ≠ 0 := (Real.rpow_pos_of_pos hx n).ne'
  field_simp [hxn]

theorem gap7 (a n : ℝ) (ha : 0 < a) :
    TailIntegrable a n ↔ 1 < n := by
  let p : ℝ → ℝ := fun x => Real.rpow x (-n)
  have heq :
      (fun x => integrand a n x / p x) =ᶠ[atTop]
        infinityNormalized a n := by
    filter_upwards [Filter.eventually_gt_atTop 0] with x hx
    have hneg := Real.rpow_neg hx.le n
    have hinv :
        (Real.rpow x (-n))⁻¹ = Real.rpow x n := by
      calc
        (Real.rpow x (-n))⁻¹ = ((Real.rpow x n)⁻¹)⁻¹ :=
          congrArg Inv.inv hneg
        _ = Real.rpow x n := inv_inv _
    unfold p infinityNormalized
    simp only [div_eq_mul_inv]
    rw [hinv]
    ring
  have hratio :
      Tendsto (fun x => integrand a n x / p x) atTop
        (nhds (Real.pi / 2)) :=
    (gap6 a n ha).congr' heq.symm
  have hpi : Real.pi / 2 ≠ 0 :=
    div_ne_zero (ne_of_gt Real.pi_pos) (by norm_num)
  have hθ : p =Θ[atTop] integrand a n :=
    Asymptotics.isTheta_of_div_tendsto_nhds_ne_zero hratio hpi
  have hpm : StronglyMeasurableAtFilter p atTop :=
    AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
      ((continuousOn_rpow_positive (-n)).aestronglyMeasurable measurableSet_Ioi)
      (Ioi_mem_atTop 0)
  have him : StronglyMeasurableAtFilter (integrand a n) atTop :=
    AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
      ((continuousOn_integrand_positive a n).aestronglyMeasurable measurableSet_Ioi)
      (Ioi_mem_atTop 0)
  have hiff :=
    integrableAtFilter_iff_of_isTheta hθ hpm him
  unfold TailIntegrable
  rw [integrableOn_Ioi_one_iff_integrableAtFilter_atTop
    (locallyIntegrableOn_integrand_positive a n)]
  rw [← hiff]
  change IntegrableAtFilter (fun x : ℝ => x ^ (-n)) atTop ↔ 1 < n
  rw [integrableAtFilter_rpow_atTop_iff]
  constructor <;> intro h <;> linarith

theorem gap8 (a n : ℝ) (ha : 0 < a) :
    (1 < n ∧ n < 2) ↔ FullIntegrable a n := by
  unfold FullIntegrable
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
    integrableOn_union]
  change (1 < n ∧ n < 2) ↔
    (NearZeroIntegrable a n ∧ TailIntegrable a n)
  rw [gap5 a n ha, gap7 a n ha]
  tauto

end
end ProofGap.Exercise2364
