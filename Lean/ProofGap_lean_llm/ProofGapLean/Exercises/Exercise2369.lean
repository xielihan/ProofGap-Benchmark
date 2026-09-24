import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2369
noncomputable section

open Filter MeasureTheory

def integrand (p q x : ℝ) : ℝ :=
  1 / (Real.rpow (Real.sin x) p * Real.rpow (Real.cos x) q)
def NearZeroIntegrable (p q : ℝ) : Prop :=
  IntegrableOn (integrand p q) (Set.Ioc (0 : ℝ) (Real.pi / 4))
def NearUpperIntegrable (p q : ℝ) : Prop :=
  IntegrableOn (integrand p q) (Set.Ioo (Real.pi / 4) (Real.pi / 2))
def FullIntegrable (p q : ℝ) : Prop :=
  IntegrableOn (integrand p q) (Set.Ioo (0 : ℝ) (Real.pi / 2))

def zeroNormalized (p q x : ℝ) : ℝ :=
  Real.rpow x p * integrand p q x
def zeroModel (p q x : ℝ) : ℝ :=
  Real.rpow (x / Real.sin x) p / Real.rpow (Real.cos x) q
def upperNormalized (p q x : ℝ) : ℝ :=
  Real.rpow (Real.pi / 2 - x) q * integrand p q x
def upperModel (q t : ℝ) : ℝ :=
  Real.rpow (t / Real.sin t) q

private theorem continuousOn_integrand_middle (p q : ℝ) :
    ContinuousOn (integrand p q)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  intro x hx
  have hx0 : 0 < x := hx.1
  have hxhalf : x < Real.pi / 2 := hx.2
  have hxpi : x < Real.pi := by
    linarith [Real.pi_pos]
  have hsin : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx.1 hxpi
  have hcos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hxhalf⟩
  unfold integrand
  exact continuousAt_const.continuousWithinAt.div
    ((Real.continuous_sin.continuousAt.rpow_const
      (Or.inl hsin.ne')).mul
      (Real.continuous_cos.continuousAt.rpow_const
        (Or.inl hcos.ne'))).continuousWithinAt
    (mul_ne_zero (Real.rpow_pos_of_pos hsin p).ne'
      (Real.rpow_pos_of_pos hcos q).ne')

private theorem locallyIntegrableOn_integrand_middle (p q : ℝ) :
    LocallyIntegrableOn (integrand p q)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (continuousOn_integrand_middle p q).locallyIntegrableOn measurableSet_Ioo

private theorem continuousOn_rpow_positive (s : ℝ) :
    ContinuousOn (fun x : ℝ => x ^ s) (Set.Ioi (0 : ℝ)) :=
  continuous_id.continuousOn.rpow_const
    (fun x hx => Or.inl (ne_of_gt hx))

private theorem integrableAtFilter_rpow_nhdsGT_zero_iff (s : ℝ) :
    IntegrableAtFilter (fun x : ℝ => x ^ s)
        (nhdsWithin 0 (Set.Ioi 0)) ↔ -1 < s := by
  constructor
  · rintro ⟨u, hu, hint⟩
    obtain ⟨b, hb, hsub⟩ :=
      mem_nhdsGT_iff_exists_Ioo_subset.mp hu
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff hb).mp
      (hint.mono_set hsub)
  · intro hs
    exact ⟨Set.Ioo 0 1, Ioo_mem_nhdsGT zero_lt_one,
      (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr hs⟩

private theorem nearZeroIntegrable_iff_integrableAtFilter (p q : ℝ) :
    NearZeroIntegrable p q ↔
      IntegrableAtFilter (integrand p q)
        (nhdsWithin 0 (Set.Ioi 0)) := by
  have hquarter : 0 < Real.pi / 4 := by positivity
  have hquarter_half : Real.pi / 4 < Real.pi / 2 := by
    linarith [Real.pi_pos]
  constructor
  · intro h
    exact ⟨Set.Ioc 0 (Real.pi / 4),
      Ioc_mem_nhdsGT hquarter, h⟩
  · rintro ⟨u, hu, hint⟩
    obtain ⟨b, hb, hsub⟩ :=
      mem_nhdsGT_iff_exists_Ioc_subset.mp hu
    have hsmall :
        IntegrableOn (integrand p q) (Set.Ioc 0 b) :=
      hint.mono_set hsub
    unfold NearZeroIntegrable
    by_cases hbq : Real.pi / 4 ≤ b
    · exact hsmall.mono_set (Set.Ioc_subset_Ioc_right hbq)
    · have hbq' : b ≤ Real.pi / 4 := le_of_not_ge hbq
      have hrest :
          IntegrableOn (integrand p q) (Set.Icc b (Real.pi / 4)) :=
        (locallyIntegrableOn_integrand_middle p q).integrableOn_compact_subset
          (fun x hx =>
            ⟨hb.trans_le hx.1, lt_of_le_of_lt hx.2 hquarter_half⟩)
          isCompact_Icc
      rw [← Set.Ioc_union_Icc_eq_Ioc hb hbq', integrableOn_union]
      exact ⟨hsmall, hrest⟩

private theorem stronglyMeasurableAtFilter_integrand_zero (p q : ℝ) :
    StronglyMeasurableAtFilter (integrand p q)
      (nhdsWithin 0 (Set.Ioi 0)) := by
  have hmem :
      Set.Ioo (0 : ℝ) (Real.pi / 2) ∈
        nhdsWithin 0 (Set.Ioi 0) := by
    change Set.Ioi 0 ∩ Set.Iio (Real.pi / 2) ∈
      nhdsWithin 0 (Set.Ioi 0)
    exact inter_mem self_mem_nhdsWithin
      (nhdsWithin_le_nhds (Iio_mem_nhds (by positivity)))
  exact AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
    ((continuousOn_integrand_middle p q).aestronglyMeasurable
      measurableSet_Ioo)
    hmem

private theorem integrableAtFilter_iff_of_isTheta
    {f g : ℝ → ℝ} {l : Filter ℝ} [l.IsMeasurablyGenerated]
    (hθ : f =Θ[l] g)
    (hfm : StronglyMeasurableAtFilter f l)
    (hgm : StronglyMeasurableAtFilter g l) :
    IntegrableAtFilter f l ↔ IntegrableAtFilter g l := by
  constructor
  · exact fun hf => hθ.2.integrableAtFilter hgm hf
  · exact fun hg => hθ.1.integrableAtFilter hfm hg

theorem gap1 (p q : ℝ) :
    FullIntegrable p q ↔
      NearZeroIntegrable p q ∧ NearUpperIntegrable p q := by
  unfold FullIntegrable NearZeroIntegrable NearUpperIntegrable
  rw [← Set.Ioc_union_Ioo_eq_Ioo
      (by positivity : (0 : ℝ) ≤ Real.pi / 4)
      (by linarith [Real.pi_pos] : Real.pi / 4 < Real.pi / 2),
    integrableOn_union]

theorem gap2 (p q : ℝ) :
    Tendsto (zeroNormalized p q) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) ↔
      Tendsto (zeroModel p q) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have heq :
      zeroNormalized p q =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        zeroModel p q := by
    have hlt :
        ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0), x < Real.pi / 2 :=
      (eventually_lt_nhds (by positivity : (0 : ℝ) < Real.pi / 2)).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hlt] with x hx hxhalf
    have hsin : 0 < Real.sin x :=
      Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_pos])
    have hdiv :
        Real.rpow (x / Real.sin x) p =
          Real.rpow x p / Real.rpow (Real.sin x) p :=
      Real.div_rpow hx.le hsin.le p
    unfold zeroNormalized zeroModel integrand
    rw [hdiv]
    simp only [div_eq_mul_inv, one_mul]
    ring
  constructor
  · exact fun h => h.congr' heq
  · exact fun h => h.congr' heq.symm

theorem gap3 (p q : ℝ) :
    Tendsto (zeroModel p q) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hsinDiv :
      Tendsto (fun x : ℝ => Real.sin x / x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_sin 0).tendsto_slope_zero_right
  have hxDivSin :
      Tendsto (fun x : ℝ => x / Real.sin x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hinv :
        Tendsto (fun x : ℝ => (Real.sin x / x)⁻¹)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      simpa using hsinDiv.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    apply hinv.congr'
    have hlt :
        ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0), x < Real.pi / 2 :=
      (eventually_lt_nhds (by positivity : (0 : ℝ) < Real.pi / 2)).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hlt] with x hx hxhalf
    have hx0 : 0 < x := hx
    have hsin : Real.sin x ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi hx0
        (by linarith [Real.pi_pos])).ne'
    field_simp [hx0.ne', hsin]
  have hxpow :
      Tendsto (fun x : ℝ => Real.rpow (x / Real.sin x) p)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa using hxDivSin.rpow_const (Or.inl one_ne_zero)
  have hcos :
      Tendsto Real.cos (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hc0 : ContinuousAt Real.cos 0 :=
      Real.continuous_cos.continuousAt
    simpa using hc0.tendsto.mono_left
      (nhdsWithin_le_nhds :
        nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0)
  have hcospow :
      Tendsto (fun x : ℝ => Real.rpow (Real.cos x) q)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa using hcos.rpow_const (Or.inl one_ne_zero)
  simpa [zeroModel] using hxpow.div hcospow (by norm_num : (1 : ℝ) ≠ 0)

theorem gap4 (p q : ℝ) :
    Tendsto (zeroNormalized p q)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  exact (gap2 p q).2 (gap3 p q)

theorem gap5 (p q : ℝ) :
    NearZeroIntegrable p q ↔ p < 1 := by
  let m : ℝ → ℝ := fun x => Real.rpow x (-p)
  have heq :
      (fun x => integrand p q x / m x) =ᶠ[
        nhdsWithin 0 (Set.Ioi 0)] zeroNormalized p q := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : 0 < x := hx
    have hinv :
        (Real.rpow x (-p))⁻¹ = Real.rpow x p := by
      calc
        (Real.rpow x (-p))⁻¹ =
            ((Real.rpow x p)⁻¹)⁻¹ := by
          congr 1
          exact Real.rpow_neg hx0.le p
        _ = Real.rpow x p := inv_inv _
    unfold m zeroNormalized
    simp only [div_eq_mul_inv]
    rw [hinv]
    ring
  have hratio :
      Tendsto (fun x => integrand p q x / m x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
    (gap4 p q).congr' heq.symm
  have hθ :
      m =Θ[nhdsWithin 0 (Set.Ioi 0)] integrand p q :=
    Asymptotics.isTheta_of_div_tendsto_nhds_ne_zero hratio one_ne_zero
  have hmm :
      StronglyMeasurableAtFilter m (nhdsWithin 0 (Set.Ioi 0)) :=
    (continuousOn_rpow_positive (-p)).stronglyMeasurableAtFilter_nhdsWithin
      measurableSet_Ioi 0
  have him :
      StronglyMeasurableAtFilter (integrand p q)
        (nhdsWithin 0 (Set.Ioi 0)) :=
    stronglyMeasurableAtFilter_integrand_zero p q
  have hiff :=
    integrableAtFilter_iff_of_isTheta hθ hmm him
  rw [nearZeroIntegrable_iff_integrableAtFilter p q]
  rw [← hiff]
  change IntegrableAtFilter (fun x : ℝ => x ^ (-p))
      (nhdsWithin 0 (Set.Ioi 0)) ↔ p < 1
  rw [integrableAtFilter_rpow_nhdsGT_zero_iff]
  constructor <;> intro h <;> linarith

private theorem upperModel_tendsto (q : ℝ) :
    Tendsto (upperModel q)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  convert gap3 q 0 using 1
  funext x
  unfold zeroModel upperModel
  have hz : Real.rpow (Real.cos x) 0 = 1 :=
    Real.rpow_zero _
  rw [hz, div_one]

private theorem upperNormalized_tendsto (p q : ℝ) :
    Tendsto (upperNormalized p q)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds 1) := by
  let c : ℝ := Real.pi / 2
  have hc : 0 < c := by
    unfold c
    positivity
  have hsub :
      Tendsto (fun x : ℝ => c - x)
        (nhdsWithin c (Set.Iio c))
        (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · convert
        tendsto_const_nhds.sub
          (tendsto_id.mono_left
            (nhdsWithin_le_nhds :
              nhdsWithin c (Set.Iio c) ≤ nhds c))
        using 1 <;> ring
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hxlt : x < c := hx
      exact sub_pos.mpr hxlt
  have hcomp :
      Tendsto (fun x => zeroModel q p (c - x))
        (nhdsWithin c (Set.Iio c)) (nhds 1) :=
    (gap3 q p).comp hsub
  have heq :
      (fun x => zeroModel q p (c - x)) =ᶠ[
        nhdsWithin c (Set.Iio c)] upperNormalized p q := by
    have hxpos :
        ∀ᶠ x in nhdsWithin c (Set.Iio c), 0 < x :=
      (eventually_gt_nhds hc).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hxpos] with x hxc hx
    have ht : 0 < c - x := sub_pos.mpr hxc
    have htlt : c - x < Real.pi / 2 := by
      unfold c
      linarith
    have hsint : 0 < Real.sin (c - x) :=
      Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_pos])
    have hdiv :
        Real.rpow ((c - x) / Real.sin (c - x)) q =
          Real.rpow (c - x) q / Real.rpow (Real.sin (c - x)) q :=
      Real.div_rpow ht.le hsint.le q
    have hsinx : Real.sin x = Real.cos (c - x) := by
      unfold c
      rw [← Real.sin_pi_div_two_sub (Real.pi / 2 - x)]
      congr 1 <;> ring
    have hcosx : Real.cos x = Real.sin (c - x) := by
      unfold c
      rw [← Real.cos_pi_div_two_sub (Real.pi / 2 - x)]
      congr 1 <;> ring
    unfold c at hdiv hsinx hcosx ⊢
    unfold zeroModel upperNormalized integrand
    rw [hdiv, hsinx, hcosx]
    simp only [div_eq_mul_inv, one_mul]
    ring
  unfold c at hcomp heq
  exact hcomp.congr' heq

theorem gap6 (p q : ℝ) :
    Tendsto (upperNormalized p q)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 1) ↔
      Tendsto (upperModel q)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  constructor
  · intro _
    exact upperModel_tendsto q
  · intro _
    exact upperNormalized_tendsto p q

theorem gap7 (q : ℝ) :
    Tendsto (upperModel q)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  exact upperModel_tendsto q

theorem gap8 (p q : ℝ) :
    Tendsto (upperNormalized p q)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 1) := by
  exact upperNormalized_tendsto p q

theorem gap9 (p q : ℝ) :
    NearUpperIntegrable p q ↔ q < 1 := by
  have h0quarter : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have hquarterhalf : Real.pi / 4 ≤ Real.pi / 2 := by
    linarith [Real.pi_pos]
  have hquarter :
      Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring
  have hreflect :
      IntervalIntegrable (integrand p q) volume
          (Real.pi / 4) (Real.pi / 2) ↔
        IntervalIntegrable (integrand q p) volume
          0 (Real.pi / 4) := by
    have heq :
        (fun x => integrand p q (Real.pi / 2 - x)) =
          integrand q p := by
      funext x
      unfold integrand
      rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
      rw [mul_comm (Real.rpow (Real.cos x) p)
        (Real.rpow (Real.sin x) q)]
    constructor
    · intro h
      have ht :=
        (h.comp_sub_left (Real.pi / 2)).symm
      rw [heq] at ht
      simpa [hquarter] using ht
    · intro h
      have ht :
          IntervalIntegrable
            (fun x => integrand p q (Real.pi / 2 - x))
            volume 0 (Real.pi / 4) := by
        rw [heq]
        exact h
      have horig :=
        ht.symm.comp_sub_left (Real.pi / 2)
      simpa [hquarter] using horig
  calc
    NearUpperIntegrable p q ↔ NearZeroIntegrable q p := by
      unfold NearUpperIntegrable NearZeroIntegrable
      rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le
          hquarterhalf,
        ← intervalIntegrable_iff_integrableOn_Ioc_of_le h0quarter]
      exact hreflect
    _ ↔ q < 1 := gap5 q p

theorem gap10 (p q : ℝ) :
    (p < 1 ∧ q < 1) ↔ FullIntegrable p q := by
  rw [gap1 p q, gap5 p q, gap9 p q]

end
end ProofGap.Exercise2369
