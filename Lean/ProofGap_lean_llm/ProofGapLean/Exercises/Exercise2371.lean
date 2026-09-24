import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2371
noncomputable section

open Filter MeasureTheory

def integrand (p q x : ℝ) : ℝ :=
  1 / (Real.rpow x p + Real.rpow x q)
def NearZeroIntegrable (p q : ℝ) : Prop :=
  IntegrableOn (integrand p q) (Set.Ioc (0 : ℝ) 1)
def TailIntegrable (p q : ℝ) : Prop :=
  IntegrableOn (integrand p q) (Set.Ioi (1 : ℝ))
def FullIntegrable (p q : ℝ) : Prop :=
  IntegrableOn (integrand p q) (Set.Ioi (0 : ℝ))
def pNormalized (p q x : ℝ) : ℝ :=
  Real.rpow x p * integrand p q x
def pModel (p q x : ℝ) : ℝ :=
  1 / (1 + Real.rpow x (q - p))
def qNormalized (p q x : ℝ) : ℝ :=
  Real.rpow x q * integrand p q x
def qModel (p q x : ℝ) : ℝ :=
  1 / (Real.rpow x (-(q - p)) + 1)

private theorem integrand_swap (p q : ℝ) : integrand p q = integrand q p := by
  funext x
  unfold integrand
  ring

private theorem integrand_continuousOn_pos (p q : ℝ) :
    ContinuousOn (integrand p q) (Set.Ioi (0 : ℝ)) := by
  intro x hx
  have hp := continuousAt_id.rpow_const (Or.inl hx.ne') (p := p)
  have hq := continuousAt_id.rpow_const (Or.inl hx.ne') (p := q)
  unfold integrand
  exact (continuousAt_const.div (hp.add hq) (by
    change Real.rpow x p + Real.rpow x q ≠ 0
    have hpp : 0 < Real.rpow x p := Real.rpow_pos_of_pos hx p
    have hqp : 0 < Real.rpow x q := Real.rpow_pos_of_pos hx q
    exact ne_of_gt (by linarith))).continuousWithinAt

private theorem near_bounds_of_le {p q x : ℝ} (hpq : p ≤ q)
    (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    0 ≤ integrand p q x ∧
      integrand p q x ≤ Real.rpow x (-p) ∧
      Real.rpow x (-p) ≤ 2 * integrand p q x := by
  have hxp : 0 < x := hx.1
  let P := Real.rpow x p
  let Q := Real.rpow x q
  let R := Real.rpow x (-p)
  have hP : 0 < P := Real.rpow_pos_of_pos hxp p
  have hQ : 0 < Q := Real.rpow_pos_of_pos hxp q
  have hQP : Q ≤ P := Real.rpow_le_rpow_of_exponent_ge hxp hx.2 hpq
  have hD : 0 < P + Q := by positivity
  have hR : R = P⁻¹ := by
    exact Real.rpow_neg hxp.le p
  unfold integrand
  change 0 ≤ 1 / (P + Q) ∧ 1 / (P + Q) ≤ R ∧ R ≤ 2 * (1 / (P + Q))
  constructor
  · positivity
  constructor
  · rw [hR]
    rw [← one_div]
    exact div_le_div_of_nonneg_left zero_le_one hP (by linarith)
  · rw [hR]
    rw [← one_div]
    rw [show 2 * (1 / (P + Q)) = 2 / (P + Q) by ring]
    apply (div_le_div_iff₀ hP hD).2
    linarith

private theorem tail_bounds_of_le {p q x : ℝ} (hpq : p ≤ q)
    (hx : x ∈ Set.Ioi (1 : ℝ)) :
    0 ≤ integrand p q x ∧
      integrand p q x ≤ Real.rpow x (-q) ∧
      Real.rpow x (-q) ≤ 2 * integrand p q x := by
  have hxp : 0 < x := zero_lt_one.trans hx
  let P := Real.rpow x p
  let Q := Real.rpow x q
  let R := Real.rpow x (-q)
  have hP : 0 < P := Real.rpow_pos_of_pos hxp p
  have hQ : 0 < Q := Real.rpow_pos_of_pos hxp q
  have hPQ : P ≤ Q := Real.rpow_le_rpow_of_exponent_le hx.le hpq
  have hD : 0 < P + Q := by positivity
  have hR : R = Q⁻¹ := by
    exact Real.rpow_neg hxp.le q
  unfold integrand
  change 0 ≤ 1 / (P + Q) ∧ 1 / (P + Q) ≤ R ∧ R ≤ 2 * (1 / (P + Q))
  constructor
  · positivity
  constructor
  · rw [hR]
    rw [← one_div]
    exact div_le_div_of_nonneg_left zero_le_one hQ (by linarith)
  · rw [hR]
    rw [← one_div]
    rw [show 2 * (1 / (P + Q)) = 2 / (P + Q) by ring]
    apply (div_le_div_iff₀ hQ hD).2
    linarith

private theorem near_integrable_iff_of_le (p q : ℝ) (hpq : p ≤ q) :
    IntegrableOn (integrand p q) (Set.Ioc (0 : ℝ) 1) ↔ p < 1 := by
  have hpow_iff :
      IntegrableOn (fun x : ℝ => Real.rpow x (-p)) (Set.Ioc (0 : ℝ) 1) ↔
        p < 1 := by
    have hbase :
        IntegrableOn (fun x : ℝ => Real.rpow x (-p)) (Set.Ioc (0 : ℝ) 1) ↔
          -1 < -p := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo]
      exact intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one
    exact hbase.trans (by constructor <;> intro h <;> linarith)
  have hpow_meas : AEStronglyMeasurable (fun x : ℝ => Real.rpow x (-p))
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (continuousOn_id.rpow_const (fun x hx => Or.inl hx.1.ne')).aestronglyMeasurable
      measurableSet_Ioc
  have hint_meas : AEStronglyMeasurable (integrand p q)
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    ((integrand_continuousOn_pos p q).mono fun x hx => hx.1).aestronglyMeasurable
      measurableSet_Ioc
  constructor
  · intro hint
    have hscaled : IntegrableOn (fun x => 2 * integrand p q x)
        (Set.Ioc (0 : ℝ) 1) := hint.const_mul 2
    have hpow : IntegrableOn (fun x : ℝ => Real.rpow x (-p))
        (Set.Ioc (0 : ℝ) 1) := by
      apply hscaled.integrable.mono' hpow_meas
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hb := near_bounds_of_le hpq hx
      have hpow_nonneg : 0 ≤ Real.rpow x (-p) := Real.rpow_nonneg hx.1.le _
      rw [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg]
      exact hb.2.2
    exact hpow_iff.mp hpow
  · intro hp
    have hpow := hpow_iff.mpr hp
    apply hpow.integrable.mono' hint_meas
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hb := near_bounds_of_le hpq hx
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2.1

private theorem tail_integrable_iff_of_le (p q : ℝ) (hpq : p ≤ q) :
    IntegrableOn (integrand p q) (Set.Ioi (1 : ℝ)) ↔ 1 < q := by
  have hpow_iff :
      IntegrableOn (fun x : ℝ => Real.rpow x (-q)) (Set.Ioi (1 : ℝ)) ↔
        1 < q := by
    have hbase :
        IntegrableOn (fun x : ℝ => Real.rpow x (-q)) (Set.Ioi (1 : ℝ)) ↔
          -q < -1 := by
      exact integrableOn_Ioi_rpow_iff zero_lt_one
    exact hbase.trans (by constructor <;> intro h <;> linarith)
  have hpow_meas : AEStronglyMeasurable (fun x : ℝ => Real.rpow x (-q))
      (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) :=
    (continuousOn_id.rpow_const (fun x hx =>
      Or.inl (ne_of_gt (zero_lt_one.trans hx)))).aestronglyMeasurable measurableSet_Ioi
  have hint_meas : AEStronglyMeasurable (integrand p q)
      (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) :=
    ((integrand_continuousOn_pos p q).mono
      (show Set.Ioi (1 : ℝ) ⊆ Set.Ioi (0 : ℝ) by
        intro x hx
        exact zero_lt_one.trans (Set.mem_Ioi.mp hx))).aestronglyMeasurable measurableSet_Ioi
  constructor
  · intro hint
    have hscaled : IntegrableOn (fun x => 2 * integrand p q x)
        (Set.Ioi (1 : ℝ)) := hint.const_mul 2
    have hpow : IntegrableOn (fun x : ℝ => Real.rpow x (-q))
        (Set.Ioi (1 : ℝ)) := by
      apply hscaled.integrable.mono' hpow_meas
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hb := tail_bounds_of_le hpq hx
      have hpow_nonneg : 0 ≤ Real.rpow x (-q) :=
        Real.rpow_nonneg (zero_lt_one.trans hx).le _
      rw [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg]
      exact hb.2.2
    exact hpow_iff.mp hpow
  · intro hq
    have hpow := hpow_iff.mpr hq
    apply hpow.integrable.mono' hint_meas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hb := tail_bounds_of_le hpq hx
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2.1

private theorem pNormalized_eventuallyEq_pModel (p q : ℝ) :
    pNormalized p q =ᶠ[nhdsWithin 0 (Set.Ioi 0)] pModel p q := by
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hP0 : Real.rpow x p ≠ 0 := (Real.rpow_pos_of_pos hx p).ne'
  have hsub : Real.rpow x (q - p) = Real.rpow x q / Real.rpow x p :=
    Real.rpow_sub hx q p
  unfold pNormalized pModel integrand
  rw [hsub]
  field_simp [hP0]

private theorem pModel_tendsto (p q : ℝ) (hpq : p < q) :
    Tendsto (pModel p q) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hqp : 0 < q - p := sub_pos.mpr hpq
  have hr : Tendsto (fun x : ℝ => Real.rpow x (q - p))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hc := (Real.continuousAt_rpow_const 0 (q - p) (Or.inr hqp.le)).tendsto
    simpa [Real.zero_rpow hqp.ne'] using hc.mono_left inf_le_left
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := tendsto_const_nhds
  unfold pModel
  simpa only [Pi.div_apply, Pi.add_apply, Pi.one_apply, add_zero, div_one] using
    hone.div (hone.add hr) (by norm_num)

private theorem pNormalized_tendsto (p q : ℝ) (hpq : p < q) :
    Tendsto (pNormalized p q) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
  (pModel_tendsto p q hpq).congr' (pNormalized_eventuallyEq_pModel p q).symm

private theorem qNormalized_eventuallyEq_qModel (p q : ℝ) :
    qNormalized p q =ᶠ[atTop] qModel p q := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hQ0 : Real.rpow x q ≠ 0 := (Real.rpow_pos_of_pos hx q).ne'
  have hsub0 : Real.rpow x (p - q) = Real.rpow x p / Real.rpow x q :=
    Real.rpow_sub hx p q
  have hsub : Real.rpow x (-(q - p)) = Real.rpow x p / Real.rpow x q := by
    rw [show -(q - p) = p - q by ring]
    exact hsub0
  unfold qNormalized qModel integrand
  rw [hsub]
  field_simp [hQ0]

private theorem qModel_tendsto (p q : ℝ) (hpq : p < q) :
    Tendsto (qModel p q) atTop (nhds 1) := by
  have hqp : 0 < q - p := sub_pos.mpr hpq
  have hr : Tendsto (fun x : ℝ => Real.rpow x (-(q - p))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop hqp
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  unfold qModel
  simpa only [Pi.div_apply, Pi.add_apply, Pi.one_apply, zero_add, div_one] using
    hone.div (hr.add hone) (by norm_num)

private theorem qNormalized_tendsto (p q : ℝ) (hpq : p < q) :
    Tendsto (qNormalized p q) atTop (nhds 1) :=
  (qModel_tendsto p q hpq).congr' (qNormalized_eventuallyEq_qModel p q).symm

theorem gap1 (p q : ℝ) :
    FullIntegrable p q ↔
      NearZeroIntegrable p q ∧ TailIntegrable p q := by
  unfold FullIntegrable NearZeroIntegrable TailIntegrable
  have hset : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (hx | hx) <;> linarith
    · intro hx
      by_cases h : x ≤ 1
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (lt_of_not_ge h)
  rw [← hset, integrableOn_union]

theorem gap2 (p q : ℝ) (hpq : p < q) :
    Tendsto (pNormalized p q) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) ↔
      Tendsto (pModel p q) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  exact tendsto_congr' (pNormalized_eventuallyEq_pModel p q)

theorem gap3 (p q : ℝ) (hpq : p < q) :
    Tendsto (pModel p q)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  exact pModel_tendsto p q hpq

theorem gap4 (p q : ℝ) (hpq : p < q) :
    Tendsto (pNormalized p q)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  exact pNormalized_tendsto p q hpq

theorem gap5 (p q : ℝ) (hpq : p < q) :
    NearZeroIntegrable p q ↔ p < 1 := by
  unfold NearZeroIntegrable
  exact near_integrable_iff_of_le p q hpq.le

theorem gap6 (p q : ℝ) :
    NearZeroIntegrable p q ↔ min p q < 1 := by
  unfold NearZeroIntegrable
  rcases le_total p q with hpq | hqp
  · rw [min_eq_left hpq]
    exact near_integrable_iff_of_le p q hpq
  · rw [min_eq_right hqp, integrand_swap p q]
    exact near_integrable_iff_of_le q p hqp

theorem gap7 (p q : ℝ) (hpq : p < q) :
    Tendsto (qNormalized p q) atTop (nhds 1) ↔
      Tendsto (qModel p q) atTop (nhds 1) := by
  exact tendsto_congr' (qNormalized_eventuallyEq_qModel p q)

theorem gap8 (p q : ℝ) (hpq : p < q) :
    Tendsto (qModel p q) atTop (nhds 1) := by
  exact qModel_tendsto p q hpq

theorem gap9 (p q : ℝ) (hpq : p < q) :
    Tendsto (qNormalized p q) atTop (nhds 1) := by
  exact qNormalized_tendsto p q hpq

theorem gap10 (p q : ℝ) (hpq : p < q) :
    TailIntegrable p q ↔ 1 < q := by
  unfold TailIntegrable
  exact tail_integrable_iff_of_le p q hpq.le

theorem gap11 (p q : ℝ) :
    TailIntegrable p q ↔ 1 < max p q := by
  unfold TailIntegrable
  rcases le_total p q with hpq | hqp
  · rw [max_eq_right hpq]
    exact tail_integrable_iff_of_le p q hpq
  · rw [max_eq_left hqp, integrand_swap p q]
    exact tail_integrable_iff_of_le q p hqp

theorem gap12 (p q : ℝ) :
    (min p q < 1 ∧ 1 < max p q) ↔ FullIntegrable p q := by
  constructor
  · rintro ⟨hzero, htail⟩
    exact (gap1 p q).mpr ⟨(gap6 p q).mpr hzero, (gap11 p q).mpr htail⟩
  · intro hfull
    obtain ⟨hzero, htail⟩ := (gap1 p q).mp hfull
    exact ⟨(gap6 p q).mp hzero, (gap11 p q).mp htail⟩

end
end ProofGap.Exercise2371
