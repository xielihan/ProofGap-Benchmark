import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2365
noncomputable section

open Filter MeasureTheory

def integrand (n x : ℝ) : ℝ :=
  Real.log (1 + x) / Real.rpow x n
def alpha (n : ℝ) : ℝ := (n - 1) / 2
def tailNormalized (n α x : ℝ) : ℝ :=
  Real.rpow x (n - α) * integrand n x
def zeroNormalized (n x : ℝ) : ℝ :=
  Real.rpow x (n - 1) * integrand n x
def NearZeroIntegrable (n : ℝ) : Prop :=
  IntegrableOn (integrand n) (Set.Ioc (0 : ℝ) 1)
def TailIntegrable (n : ℝ) : Prop :=
  IntegrableOn (integrand n) (Set.Ioi (1 : ℝ))
def FullIntegrable (n : ℝ) : Prop :=
  IntegrableOn (integrand n) (Set.Ioi (0 : ℝ))

private theorem continuousOn_integrand_positive (n : ℝ) :
    ContinuousOn (integrand n) (Set.Ioi (0 : ℝ)) := by
  intro x hx
  unfold integrand
  have hx0 : 0 < x := hx
  have h1x : 1 + x ≠ 0 := ne_of_gt (by linarith)
  exact
    (((Real.continuousAt_log h1x).comp
      (continuousAt_const.add continuousAt_id)).continuousWithinAt).div
      (continuousAt_id.rpow_const (Or.inl (ne_of_gt hx))).continuousWithinAt
      (Real.rpow_pos_of_pos hx n).ne'

private theorem locallyIntegrableOn_integrand_positive (n : ℝ) :
    LocallyIntegrableOn (integrand n) (Set.Ioi (0 : ℝ)) :=
  (continuousOn_integrand_positive n).locallyIntegrableOn measurableSet_Ioi

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

theorem gap1 (n : ℝ) (hn : 1 < n) :
    0 < alpha n := by
  unfold alpha
  linarith

theorem gap2 (n : ℝ) (hn : 1 < n) :
    1 < n - alpha n := by
  unfold alpha
  linarith

theorem gap3 (n : ℝ) (hn : 1 < n) :
    Tendsto (tailNormalized n (alpha n)) atTop (nhds 0) ↔
      Tendsto (fun x => Real.log (1 + x) / Real.rpow x (alpha n))
        atTop (nhds 0) := by
  have heq :
      tailNormalized n (alpha n) =ᶠ[atTop]
        fun x => Real.log (1 + x) / Real.rpow x (alpha n) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hneg :
        (Real.rpow x n)⁻¹ = Real.rpow x (-n) :=
      (Real.rpow_neg hx.le n).symm
    have hmul :
        Real.rpow x (n - alpha n) * Real.rpow x (-n) =
          (Real.rpow x (alpha n))⁻¹ := by
      calc
        Real.rpow x (n - alpha n) * Real.rpow x (-n) =
            Real.rpow x ((n - alpha n) + -n) :=
          (Real.rpow_add hx (n - alpha n) (-n)).symm
        _ = Real.rpow x (-(alpha n)) := by congr 1 <;> ring
        _ = (Real.rpow x (alpha n))⁻¹ :=
          Real.rpow_neg hx.le (alpha n)
    unfold tailNormalized integrand
    simp only [div_eq_mul_inv]
    rw [hneg]
    calc
      Real.rpow x (n - alpha n) *
          (Real.log (1 + x) * Real.rpow x (-n)) =
          Real.log (1 + x) *
            (Real.rpow x (n - alpha n) * Real.rpow x (-n)) := by ring
      _ = Real.log (1 + x) * (Real.rpow x (alpha n))⁻¹ := by rw [hmul]
  constructor
  · exact fun h => h.congr' heq
  · exact fun h => h.congr' heq.symm

theorem gap4 (n : ℝ) (hn : 1 < n) :
    Tendsto (fun x => Real.log (1 + x) / Real.rpow x (alpha n))
      atTop (nhds 0) := by
  have hα : 0 < alpha n := gap1 n hn
  have hmain :
      Tendsto (fun x : ℝ => Real.log x / Real.rpow x (alpha n))
        atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop hα).tendsto_div_nhds_zero
  have hdiff :
      Tendsto (fun x : ℝ => Real.log (x + 1) - Real.log x)
        atTop (nhds 0) :=
    Real.tendsto_log_comp_add_sub_log 1
  have hinv :
      Tendsto (fun x : ℝ => (Real.rpow x (alpha n))⁻¹)
        atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop hα)
  have hcorr :
      Tendsto
        (fun x : ℝ =>
          (Real.log (x + 1) - Real.log x) *
            (Real.rpow x (alpha n))⁻¹)
        atTop (nhds 0) := by
    simpa using hdiff.mul hinv
  convert hmain.add hcorr using 1
  · funext x
    simp only [div_eq_mul_inv]
    rw [add_comm 1 x]
    ring
  · ring

theorem gap5 (n : ℝ) (hn : 1 < n) :
    Tendsto (tailNormalized n (alpha n)) atTop (nhds 0) := by
  exact (gap3 n hn).2 (gap4 n hn)

theorem gap6 (n : ℝ) (hn : 1 < n) :
    TailIntegrable n := by
  have hq : 1 < n - alpha n := gap2 n hn
  have htend :
      Tendsto (tailNormalized n (alpha n)) atTop (nhds 0) :=
    gap5 n hn
  have hbound :
      ∀ᶠ x in atTop, ‖tailNormalized n (alpha n) x‖ ≤ 1 := by
    filter_upwards [
      htend.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)] with x hx
    have hx' : ‖tailNormalized n (alpha n) x‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hx
    exact hx'.le
  have hO :
      integrand n =O[atTop]
        fun x : ℝ => Real.rpow x (-(n - alpha n)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [hbound, eventually_gt_atTop (0 : ℝ)] with x hb hx
    have hprod :
        Real.rpow x (n - alpha n) *
            Real.rpow x (-(n - alpha n)) = 1 := by
      calc
        Real.rpow x (n - alpha n) *
            Real.rpow x (-(n - alpha n)) =
            Real.rpow x ((n - alpha n) + -(n - alpha n)) :=
          (Real.rpow_add hx (n - alpha n) (-(n - alpha n))).symm
        _ = Real.rpow x 0 := by congr 1 <;> ring
        _ = 1 := Real.rpow_zero x
    have heq :
        integrand n x =
          tailNormalized n (alpha n) x *
            Real.rpow x (-(n - alpha n)) := by
      unfold tailNormalized
      calc
        integrand n x =
            (Real.rpow x (n - alpha n) *
              Real.rpow x (-(n - alpha n))) * integrand n x := by
                rw [hprod]
                ring
        _ = (Real.rpow x (n - alpha n) * integrand n x) *
              Real.rpow x (-(n - alpha n)) := by ring
    rw [heq, norm_mul, one_mul]
    nlinarith [norm_nonneg (Real.rpow x (-(n - alpha n)))]
  have hp :
      IntegrableAtFilter
        (fun x : ℝ => Real.rpow x (-(n - alpha n))) atTop := by
    change IntegrableAtFilter
      (fun x : ℝ => x ^ (-(n - alpha n))) atTop
    rw [integrableAtFilter_rpow_atTop_iff]
    linarith
  have hlocalIci :
      LocallyIntegrableOn (integrand n) (Set.Ici (1 : ℝ)) :=
    (locallyIntegrableOn_integrand_positive n).mono_set
      (Set.Ici_subset_Ioi.mpr zero_lt_one)
  have hIci : IntegrableOn (integrand n) (Set.Ici (1 : ℝ)) :=
    hlocalIci.integrableOn_of_isBigO_atTop hO hp
  unfold TailIntegrable
  exact (integrableOn_Ici_iff_integrableOn_Ioi).1 hIci

theorem gap7 (n : ℝ) (hn : n ≤ 1) :
    ¬ TailIntegrable n := by
  intro htail
  have hf :
      IntegrableAtFilter (integrand n) atTop :=
    (integrableOn_Ioi_one_iff_integrableAtFilter_atTop
      (locallyIntegrableOn_integrand_positive n)).1 htail
  have hO :
      (fun x : ℝ => Real.rpow x (-n)) =O[atTop] integrand n := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [
      eventually_ge_atTop (Real.exp 1),
      eventually_gt_atTop (0 : ℝ)] with x hxexp hx
    have h1x : 0 < 1 + x := by linarith
    have hlog : 1 ≤ Real.log (1 + x) :=
      (Real.le_log_iff_exp_le h1x).2 (by linarith)
    have hp : 0 < Real.rpow x (-n) :=
      Real.rpow_pos_of_pos hx (-n)
    have hneg :
        (Real.rpow x n)⁻¹ = Real.rpow x (-n) :=
      (Real.rpow_neg hx.le n).symm
    have heq :
        integrand n x =
          Real.log (1 + x) * Real.rpow x (-n) := by
      unfold integrand
      rw [div_eq_mul_inv, hneg]
    rw [heq, norm_mul, one_mul, Real.norm_of_nonneg hp.le,
      Real.norm_of_nonneg (le_trans zero_le_one hlog)]
    nlinarith
  have hpm :
      StronglyMeasurableAtFilter
        (fun x : ℝ => Real.rpow x (-n)) atTop :=
    AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
      ((continuousOn_rpow_positive (-n)).aestronglyMeasurable
        measurableSet_Ioi)
      (Ioi_mem_atTop 0)
  have hp :
      IntegrableAtFilter (fun x : ℝ => Real.rpow x (-n)) atTop :=
    hO.integrableAtFilter hpm hf
  have hp' :
      IntegrableAtFilter (fun x : ℝ => x ^ (-n)) atTop := by
    exact hp
  have hexp : -n < -1 :=
    (integrableAtFilter_rpow_atTop_iff).1 hp'
  linarith

theorem gap8 (n : ℝ) (hn : n ≤ 1) :
    ¬ TailIntegrable n := by
  exact gap7 n hn

theorem gap9 (n : ℝ) :
    Tendsto (zeroNormalized n) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) ↔
      Tendsto (fun x => Real.log (1 + x) / x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have heq :
      zeroNormalized n =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        fun x => Real.log (1 + x) / x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : 0 < x := hx
    have hneg :
        (Real.rpow x n)⁻¹ = Real.rpow x (-n) :=
      (Real.rpow_neg hx0.le n).symm
    have hmul :
        Real.rpow x (n - 1) * Real.rpow x (-n) = x⁻¹ := by
      calc
        Real.rpow x (n - 1) * Real.rpow x (-n) =
            Real.rpow x ((n - 1) + -n) :=
          (Real.rpow_add hx0 (n - 1) (-n)).symm
        _ = Real.rpow x (-1) := by congr 1 <;> ring
        _ = x⁻¹ := Real.rpow_neg_one x
    unfold zeroNormalized integrand
    simp only [div_eq_mul_inv]
    rw [hneg]
    calc
      Real.rpow x (n - 1) *
          (Real.log (1 + x) * Real.rpow x (-n)) =
          Real.log (1 + x) *
            (Real.rpow x (n - 1) * Real.rpow x (-n)) := by ring
      _ = Real.log (1 + x) * x⁻¹ := by rw [hmul]
  constructor
  · exact fun h => h.congr' heq
  · exact fun h => h.congr' heq.symm

theorem gap10 :
    Tendsto (fun x : ℝ => Real.log (1 + x) / x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hinner :
      HasDerivAt (fun x : ℝ => 1 + x) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add 1
  have hlog :
      HasDerivAt Real.log 1 (1 + (0 : ℝ)) := by
    convert Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0) using 1 <;>
      norm_num
  have hderiv :
      HasDerivAt (fun x : ℝ => Real.log (1 + x)) 1 0 := by
    simpa [Function.comp_def] using hlog.comp 0 hinner
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using
    hderiv.tendsto_slope_zero_right

theorem gap11 (n : ℝ) :
    Tendsto (zeroNormalized n)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  exact (gap9 n).2 gap10

theorem gap12 (n : ℝ) :
    NearZeroIntegrable n ↔ n < 2 := by
  let p : ℝ → ℝ := fun x => Real.rpow x (1 - n)
  have heq :
      (fun x => integrand n x / p x) =ᶠ[
        nhdsWithin 0 (Set.Ioi 0)] zeroNormalized n := by
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
      Tendsto (fun x => integrand n x / p x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
    (gap11 n).congr' heq.symm
  have hθ :
      p =Θ[nhdsWithin 0 (Set.Ioi 0)] integrand n :=
    Asymptotics.isTheta_of_div_tendsto_nhds_ne_zero hratio one_ne_zero
  have hpm :
      StronglyMeasurableAtFilter p (nhdsWithin 0 (Set.Ioi 0)) :=
    (continuousOn_rpow_positive (1 - n)).stronglyMeasurableAtFilter_nhdsWithin
      measurableSet_Ioi 0
  have him :
      StronglyMeasurableAtFilter (integrand n)
        (nhdsWithin 0 (Set.Ioi 0)) :=
    (continuousOn_integrand_positive n).stronglyMeasurableAtFilter_nhdsWithin
      measurableSet_Ioi 0
  have hiff :=
    integrableAtFilter_iff_of_isTheta hθ hpm him
  unfold NearZeroIntegrable
  rw [integrableOn_Ioc_zero_one_iff_integrableAtFilter
    (locallyIntegrableOn_integrand_positive n)]
  rw [← hiff]
  change IntegrableAtFilter (fun x : ℝ => x ^ (1 - n))
      (nhdsWithin 0 (Set.Ioi 0)) ↔ n < 2
  rw [integrableAtFilter_rpow_nhdsGT_zero_iff]
  constructor <;> intro h <;> linarith

theorem gap13 (n : ℝ) :
    (1 < n ∧ n < 2) ↔ FullIntegrable n := by
  have htail : TailIntegrable n ↔ 1 < n := by
    constructor
    · intro h
      by_contra hn
      exact gap7 n (le_of_not_gt hn) h
    · exact gap6 n
  unfold FullIntegrable
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
    integrableOn_union]
  change (1 < n ∧ n < 2) ↔
    (NearZeroIntegrable n ∧ TailIntegrable n)
  rw [gap12 n, htail]
  tauto

end
end ProofGap.Exercise2365
