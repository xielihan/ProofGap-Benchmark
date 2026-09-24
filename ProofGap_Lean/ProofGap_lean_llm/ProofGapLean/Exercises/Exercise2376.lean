import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Asymptotics

namespace ProofGap.Exercise2376
noncomputable section

open Filter MeasureTheory
open scoped BigOperators

def denominator {n : ℕ} (a p : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∏ i, Real.rpow |x - a i| (p i)
def integrand {n : ℕ} (a p : Fin n → ℝ) (x : ℝ) : ℝ :=
  1 / denominator a p x
def totalExponent {n : ℕ} (p : Fin n → ℝ) : ℝ := ∑ i, p i
def normalizedAtInfinity {n : ℕ} (a p : Fin n → ℝ) (x : ℝ) : ℝ :=
  integrand a p x * Real.rpow |x| (totalExponent p)
def localCoefficient {n : ℕ} (a p : Fin n → ℝ) (i : Fin n) : ℝ :=
  1 / ∏ j ∈ Finset.univ.erase i, Real.rpow |a i - a j| (p j)
def normalizedAtCenter {n : ℕ} (a p : Fin n → ℝ) (i : Fin n) (x : ℝ) : ℝ :=
  Real.rpow |x - a i| (p i) * integrand a p x
def LocallyIntegrableAt {n : ℕ} (a p : Fin n → ℝ) (i : Fin n) : Prop :=
  ∃ ε > 0, IntegrableOn (integrand a p) (Set.Ioo (a i - ε) (a i + ε))
def FullIntegrable {n : ℕ} (a p : Fin n → ℝ) : Prop :=
  Integrable (integrand a p)

private theorem tendsto_abs_div_abs_sub_atTop (a : ℝ) :
    Tendsto (fun x : ℝ => |x| / |x - a|) atTop (nhds 1) := by
  have hid : Tendsto (fun x : ℝ => x) atTop atTop := by
    simpa only [id_eq] using
      (tendsto_id'.2 (show (atTop : Filter ℝ) ≤ atTop from le_rfl))
  have hzero : Tendsto (fun x : ℝ => a / x) atTop (nhds 0) :=
    hid.const_div_atTop a
  have h : Tendsto (fun x : ℝ => 1 / (1 - a / x)) atTop (nhds 1) := by
    simpa [one_div] using
      ((show Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) from
        tendsto_const_nhds).sub hzero).inv₀
        (by norm_num : (1 : ℝ) - 0 ≠ 0)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (max 0 a)] with x hx
  rw [abs_of_pos (lt_of_le_of_lt (le_max_left 0 a) hx),
    abs_of_pos (sub_pos.mpr (lt_of_le_of_lt (le_max_right 0 a) hx))]
  have hx0 : x ≠ 0 := ne_of_gt (lt_of_le_of_lt (le_max_left 0 a) hx)
  field_simp [hx0]

private theorem tendsto_abs_div_abs_sub_atBot (a : ℝ) :
    Tendsto (fun x : ℝ => |x| / |x - a|) atBot (nhds 1) := by
  have hid : Tendsto (fun x : ℝ => x) atBot atBot := by
    simpa only [id_eq] using
      (tendsto_id'.2 (show (atBot : Filter ℝ) ≤ atBot from le_rfl))
  have hzero : Tendsto (fun x : ℝ => a / x) atBot (nhds 0) :=
    hid.const_div_atBot a
  have h : Tendsto (fun x : ℝ => 1 / (1 - a / x)) atBot (nhds 1) := by
    simpa [one_div] using
      ((show Tendsto (fun _ : ℝ => (1 : ℝ)) atBot (nhds 1) from
        tendsto_const_nhds).sub hzero).inv₀
        (by norm_num : (1 : ℝ) - 0 ≠ 0)
  refine h.congr' ?_
  filter_upwards [eventually_lt_atBot (min 0 a)] with x hx
  rw [abs_of_neg (lt_of_lt_of_le hx (min_le_left 0 a)),
    abs_of_neg (sub_neg.mpr (lt_of_lt_of_le hx (min_le_right 0 a)))]
  have hx0 : x ≠ 0 := ne_of_lt (lt_of_lt_of_le hx (min_le_left 0 a))
  field_simp [hx0]

theorem gap1 {n : ℕ} (a p : Fin n → ℝ) :
    Tendsto (normalizedAtInfinity a p) atTop (nhds 1) := by
  have hprod :
      Tendsto (fun x : ℝ => ∏ i, (|x| / |x - a i|) ^ (p i)) atTop (nhds 1) := by
    simpa using tendsto_finset_prod Finset.univ fun i _ =>
      (tendsto_abs_div_abs_sub_atTop (a i)).rpow_const (Or.inl one_ne_zero)
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [normalizedAtInfinity, integrand, denominator, totalExponent]
  have hsum : Real.rpow |x| (∑ i, p i) = ∏ i, Real.rpow |x| (p i) := by
    simpa using Real.rpow_sum_of_pos (abs_pos.mpr hx.ne') p Finset.univ
  rw [hsum]
  simp_rw [Real.div_rpow (abs_nonneg x) (abs_nonneg (x - a _))]
  rw [Finset.prod_div_distrib]
  simp only [div_eq_mul_inv, one_div]
  ac_rfl

theorem gap2 {n : ℕ} (a p : Fin n → ℝ) :
    Tendsto (normalizedAtInfinity a p) atBot (nhds 1) := by
  have hprod :
      Tendsto (fun x : ℝ => ∏ i, (|x| / |x - a i|) ^ (p i)) atBot (nhds 1) := by
    simpa using tendsto_finset_prod Finset.univ fun i _ =>
      (tendsto_abs_div_abs_sub_atBot (a i)).rpow_const (Or.inl one_ne_zero)
  refine hprod.congr' ?_
  filter_upwards [eventually_lt_atBot 0] with x hx
  simp only [normalizedAtInfinity, integrand, denominator, totalExponent]
  have hsum : Real.rpow |x| (∑ i, p i) = ∏ i, Real.rpow |x| (p i) := by
    simpa using Real.rpow_sum_of_pos (abs_pos.mpr hx.ne) p Finset.univ
  rw [hsum]
  simp_rw [Real.div_rpow (abs_nonneg x) (abs_nonneg (x - a _))]
  rw [Finset.prod_div_distrib]
  simp only [div_eq_mul_inv, one_div]
  ac_rfl

private theorem tendsto_normalizedAtCenter {n : ℕ} (a p : Fin n → ℝ)
    (ha : Set.Pairwise Set.univ (fun i j => a i ≠ a j)) (i : Fin n) :
    Tendsto (normalizedAtCenter a p i)
      (nhdsWithin (a i) ({a i}ᶜ : Set ℝ))
      (nhds (localCoefficient a p i)) := by
  have hne : ∀ j ∈ Finset.univ.erase i, a i ≠ a j := by
    intro j hj
    exact ha (by simp) (by simp) (Finset.ne_of_mem_erase hj).symm
  have hprod :
      Tendsto
        (fun x : ℝ => ∏ j ∈ Finset.univ.erase i,
          Real.rpow |x - a j| (p j))
        (nhds (a i))
        (nhds (∏ j ∈ Finset.univ.erase i,
          Real.rpow |a i - a j| (p j))) := by
    apply tendsto_finset_prod
    intro j hj
    have hbase : ContinuousAt (fun x : ℝ => |x - a j|) (a i) := by
      simpa only [id_eq] using
        ((continuousAt_id.sub
          (continuousAt_const : ContinuousAt (fun _ : ℝ => a j) (a i))).abs)
    exact hbase.rpow_const
      (Or.inl (abs_ne_zero.mpr (sub_ne_zero.mpr (hne j hj))))
  have hpos : 0 < ∏ j ∈ Finset.univ.erase i,
      Real.rpow |a i - a j| (p j) := by
    apply Finset.prod_pos
    intro j hj
    exact Real.rpow_pos_of_pos
      (abs_pos.mpr (sub_ne_zero.mpr (hne j hj))) (p j)
  have hlim :
      Tendsto
        (fun x : ℝ => 1 / ∏ j ∈ Finset.univ.erase i,
          Real.rpow |x - a j| (p j))
        (nhds (a i)) (nhds (localCoefficient a p i)) := by
    simpa only [localCoefficient, one_div] using hprod.inv₀ hpos.ne'
  refine (hlim.mono_left inf_le_left).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxi : x ≠ a i := by simpa using hx
  have hpow : Real.rpow |x - a i| (p i) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (abs_pos.mpr (sub_ne_zero.mpr hxi)) (p i))
  have hden := Finset.mul_prod_erase Finset.univ
    (fun j => Real.rpow |x - a j| (p j)) (Finset.mem_univ i)
  simp only [normalizedAtCenter, integrand, denominator]
  rw [← hden]
  simp only [one_div, mul_inv_rev]
  calc
    (∏ j ∈ Finset.univ.erase i, Real.rpow |x - a j| (p j))⁻¹ =
        (Real.rpow |x - a i| (p i) *
          (Real.rpow |x - a i| (p i))⁻¹) *
          (∏ j ∈ Finset.univ.erase i, Real.rpow |x - a j| (p j))⁻¹ := by
            rw [mul_inv_cancel₀ hpow, one_mul]
    _ = Real.rpow |x - a i| (p i) *
        ((∏ j ∈ Finset.univ.erase i, Real.rpow |x - a j| (p j))⁻¹ *
          (Real.rpow |x - a i| (p i))⁻¹) := by ac_rfl

theorem gap3 {n : ℕ} (a p : Fin n → ℝ)
    (ha : Set.Pairwise Set.univ (fun i j => a i ≠ a j)) :
    ∃ c : Fin n → ℝ, ∀ i,
      Tendsto (normalizedAtCenter a p i)
        (nhdsWithin (a i) ({a i}ᶜ : Set ℝ)) (nhds (c i)) := by
  exact ⟨localCoefficient a p, tendsto_normalizedAtCenter a p ha⟩

theorem gap4 {n : ℕ} (a p : Fin n → ℝ)
    (ha : Set.Pairwise Set.univ (fun i j => a i ≠ a j)) :
    ∀ i, 0 < localCoefficient a p i := by
  intro i
  have hprod : 0 < ∏ j ∈ Finset.univ.erase i,
      Real.rpow |a i - a j| (p j) := by
    apply Finset.prod_pos
    intro j hj
    have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    exact Real.rpow_pos_of_pos
      (abs_pos.mpr (sub_ne_zero.mpr (ha (by simp) (by simp) hij))) (p j)
  exact one_div_pos.mpr hprod

theorem gap5 {n : ℕ} (a p : Fin n → ℝ)
    (ha : Set.Pairwise Set.univ (fun i j => a i ≠ a j)) :
    ∀ i, ∃ M : ℝ, |localCoefficient a p i| ≤ M := by
  intro i
  exact ⟨|localCoefficient a p i|, le_rfl⟩

private theorem measurable_abs_rpow (q : ℝ) :
    Measurable (fun x : ℝ => Real.rpow |x| q) := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro x hx
  have habs : ContinuousAt (fun y : ℝ => |y|) x := by
    simpa only [id_eq] using (continuousAt_id.abs : ContinuousAt (fun y : ℝ => |y|) x)
  exact (habs.rpow_const (Or.inl (abs_ne_zero.mpr (by simpa using hx)))).continuousWithinAt

private theorem measurable_abs_sub_rpow (a q : ℝ) :
    Measurable (fun x : ℝ => Real.rpow |x - a| q) := by
  simpa only [Function.comp_apply] using
    (measurable_abs_rpow q).comp (measurable_id.sub measurable_const)

private theorem measurable_integrand {n : ℕ} (a p : Fin n → ℝ) :
    Measurable (integrand a p) := by
  have hden : Measurable (denominator a p) := by
    apply Finset.measurable_prod
    intro i _
    exact measurable_abs_sub_rpow (a i) (p i)
  unfold integrand
  exact measurable_const.div hden

private theorem intervalIntegrable_abs_rpow_iff {q ε : ℝ} (hε : 0 < ε) :
    IntervalIntegrable (fun x : ℝ => Real.rpow |x| q) volume (-ε) ε ↔ -1 < q := by
  constructor
  · intro h
    have hall : IntegrableOn (fun x : ℝ => Real.rpow |x| q) (Set.Ioo (-ε) ε) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).mp h
    have hright : IntegrableOn (fun x : ℝ => Real.rpow |x| q) (Set.Ioo 0 ε) :=
      hall.mono_set (Set.Ioo_subset_Ioo (by linarith) le_rfl)
    have hrpow : IntegrableOn (fun x : ℝ => Real.rpow x q) (Set.Ioo 0 ε) :=
      hright.congr_fun (fun x hx => by rw [abs_of_pos hx.1]) measurableSet_Ioo
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff hε).mp hrpow
  · intro hq
    have hrpow : IntegrableOn (fun x : ℝ => Real.rpow x q) (Set.Ioo 0 ε) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hε).mpr hq
    have habs : IntegrableOn (fun x : ℝ => Real.rpow |x| q) (Set.Ioo 0 ε) :=
      hrpow.congr_fun (fun x hx => by rw [abs_of_pos hx.1]) measurableSet_Ioo
    have hright : IntervalIntegrable (fun x : ℝ => Real.rpow |x| q) volume 0 ε :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hε.le).mpr habs
    have hleft : IntervalIntegrable (fun x : ℝ => Real.rpow |x| q) volume (-ε) 0 := by
      have hneg := (IntervalIntegrable.iff_comp_neg (a := 0) (b := ε)
        (f := fun x : ℝ => Real.rpow |x| q)).mp hright
      simpa only [neg_zero, abs_neg] using hneg.symm
    exact hleft.trans hright

private theorem integrableOn_abs_sub_neg_rpow_iff {a p ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun x : ℝ => Real.rpow |x - a| (-p))
      (Set.Ioo (a - ε) (a + ε)) ↔ p < 1 := by
  rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)]
  have hshift :
      IntervalIntegrable (fun x : ℝ => Real.rpow |x - a| (-p)) volume
          (a - ε) (a + ε) ↔
        IntervalIntegrable (fun x : ℝ => Real.rpow |x| (-p)) volume (-ε) ε := by
    simpa only [neg_add_cancel_comm_assoc, add_comm, sub_eq_add_neg] using
      (IntervalIntegrable.comp_sub_right_iff
        (f := fun x : ℝ => Real.rpow |x| (-p)) (a := -ε) (b := ε) (c := a))
  rw [hshift, intervalIntegrable_abs_rpow_iff hε]
  constructor <;> intro h <;> linarith

private theorem integrableAtFilter_punctured_iff_exists_interval (f : ℝ → ℝ) (a : ℝ) :
    IntegrableAtFilter f (nhdsWithin a ({a}ᶜ : Set ℝ)) ↔
      ∃ ε > 0, IntegrableOn f (Set.Ioo (a - ε) (a + ε)) := by
  constructor
  · rintro ⟨s, hs, hint⟩
    obtain ⟨u, hu, hus⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hs
    obtain ⟨l, r, har, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp hu
    let ε := min (a - l) (r - a)
    have hε : 0 < ε := lt_min (sub_pos.mpr har.1) (sub_pos.mpr har.2)
    have hsub : Set.Ioo (a - ε) (a + ε) ⊆ Set.Ioo l r :=
      Set.Ioo_subset_Ioo (by
        dsimp only [ε]
        linarith [min_le_left (a - l) (r - a)]) (by
        dsimp only [ε]
        linarith [min_le_right (a - l) (r - a)])
    refine ⟨ε, hε, ?_⟩
    have hpunct : IntegrableOn f (Set.Ioo (a - ε) (a + ε) \ {a}) :=
      hint.mono_set fun _ hx => hus ⟨hlu (hsub hx.1), hx.2⟩
    refine (hpunct.union
      (integrableOn_singleton (f := f) (x := a) (hx := by simp))).mono_set ?_
    intro x hx
    by_cases hxa : x = a
    · exact Set.mem_union_right _ (by simpa [hxa])
    · exact Set.mem_union_left _ ⟨hx, by simpa [hxa]⟩
  · rintro ⟨ε, hε, hint⟩
    refine ⟨Set.Ioo (a - ε) (a + ε), ?_, hint⟩
    exact mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨Set.Ioo (a - ε) (a + ε), Ioo_mem_nhds (by linarith) (by linarith),
        Set.inter_subset_left⟩

theorem gap6 {n : ℕ} (a p : Fin n → ℝ)
    (ha : Set.Pairwise Set.univ (fun i j => a i ≠ a j)) :
    ∀ i, LocallyIntegrableAt a p i ↔ p i < 1 := by
  intro i
  let l := nhdsWithin (a i) ({a i}ᶜ : Set ℝ)
  let g : ℝ → ℝ := fun x => Real.rpow |x - a i| (-p i)
  haveI : IsMeasurablyGenerated l := by
    dsimp only [l]
    exact (measurableSet_singleton (a i)).compl.nhdsWithin_isMeasurablyGenerated _
  have hratio : Tendsto (fun x => integrand a p x / g x) l
      (nhds (localCoefficient a p i)) := by
    refine (tendsto_normalizedAtCenter a p ha i).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [g, normalizedAtCenter]
    have hneg : Real.rpow |x - a i| (-p i) =
        (Real.rpow |x - a i| (p i))⁻¹ :=
      Real.rpow_neg (abs_nonneg (x - a i)) (p i)
    rw [hneg]
    simp only [div_eq_mul_inv, inv_inv]
    ac_rfl
  have htheta : g =Θ[l] integrand a p :=
    Asymptotics.isTheta_of_div_tendsto_nhds_ne_zero hratio (gap4 a p ha i).ne'
  have hmeasG : StronglyMeasurableAtFilter g l :=
    (measurable_abs_sub_rpow (a i) (-p i)).stronglyMeasurable.stronglyMeasurableAtFilter
  have hmeasF : StronglyMeasurableAtFilter (integrand a p) l :=
    (measurable_integrand a p).stronglyMeasurable.stronglyMeasurableAtFilter
  have hfg : IntegrableAtFilter (integrand a p) l ↔ IntegrableAtFilter g l := by
    exact ⟨fun hf => htheta.1.integrableAtFilter hmeasG hf,
      fun hg => htheta.2.integrableAtFilter hmeasF hg⟩
  have hg : IntegrableAtFilter g l ↔ p i < 1 := by
    rw [integrableAtFilter_punctured_iff_exists_interval]
    constructor
    · rintro ⟨ε, hε, hint⟩
      exact (integrableOn_abs_sub_neg_rpow_iff hε).mp hint
    · intro hp
      exact ⟨1, zero_lt_one, (integrableOn_abs_sub_neg_rpow_iff zero_lt_one).mpr hp⟩
  simpa only [LocallyIntegrableAt, l] using
    (integrableAtFilter_punctured_iff_exists_interval (integrand a p) (a i)).symm.trans
      (hfg.trans hg)

private theorem measurable_rpow (q : ℝ) :
    Measurable (fun x : ℝ => Real.rpow x q) := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro x hx
  exact (Real.continuousAt_rpow_const x q
    (Or.inl (by simpa using hx))).continuousWithinAt

private theorem continuousAt_integrand_of_ne {n : ℕ} (a p : Fin n → ℝ) {x : ℝ}
    (hx : ∀ i, x ≠ a i) : ContinuousAt (integrand a p) x := by
  have hden : ContinuousAt (denominator a p) x := by
    apply tendsto_finset_prod
    intro i _
    have hbase : ContinuousAt (fun y : ℝ => |y - a i|) x := by
      simpa only [id_eq] using
        ((continuousAt_id.sub
          (continuousAt_const : ContinuousAt (fun _ : ℝ => a i) x)).abs)
    exact hbase.rpow_const
      (Or.inl (abs_ne_zero.mpr (sub_ne_zero.mpr (hx i))))
  have hpos : 0 < denominator a p x := by
    apply Finset.prod_pos
    intro i _
    exact Real.rpow_pos_of_pos
      (abs_pos.mpr (sub_ne_zero.mpr (hx i))) (p i)
  unfold integrand
  exact continuousAt_const.div hden hpos.ne'

private theorem integrableAtFilter_comp_neg_atBot_iff (f : ℝ → ℝ) :
    IntegrableAtFilter (fun x => f (-x)) atBot ↔ IntegrableAtFilter f atTop := by
  rw [integrableAtFilter_atBot_iff, integrableAtFilter_atTop_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    have hmap :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
        (Homeomorph.neg ℝ).measurableEmbedding (f := f) (s := Set.Ici (-a))
    apply hmap.mp
    have hset : Neg.neg ⁻¹' Set.Ici (-a) = Set.Iic a := by
      ext x
      simp
    rw [hset]
    simpa only [Function.comp_apply] using ha
  · rintro ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    have hmap :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
        (Homeomorph.neg ℝ).measurableEmbedding (f := f) (s := Set.Ici a)
    have := hmap.mpr ha
    have hset : Neg.neg ⁻¹' Set.Ici a = Set.Iic (-a) := by
      ext x
      simp
    rw [hset] at this
    simpa only [Function.comp_apply] using this

theorem gap7 {n : ℕ} (a p : Fin n → ℝ)
    (ha : Set.Pairwise Set.univ (fun i j => a i ≠ a j)) :
    FullIntegrable a p ↔
      1 < totalExponent p ∧ ∀ i, p i < 1 := by
  let f := integrand a p
  let q := totalExponent p
  let gTop : ℝ → ℝ := fun x => Real.rpow x (-q)
  let gBot : ℝ → ℝ := fun x => Real.rpow (-x) (-q)
  have hratioTop : Tendsto (fun x => f x / gTop x) atTop (nhds 1) := by
    refine (gap1 a p).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hneg : Real.rpow x (-q) = (Real.rpow x q)⁻¹ :=
      Real.rpow_neg hx.le q
    simp only [f, gTop, normalizedAtInfinity]
    rw [abs_of_pos hx, hneg]
    simp only [div_eq_mul_inv, inv_inv]
    rfl
  have hratioBot : Tendsto (fun x => f x / gBot x) atBot (nhds 1) := by
    refine (gap2 a p).congr' ?_
    filter_upwards [eventually_lt_atBot 0] with x hx
    have hneg : Real.rpow (-x) (-q) = (Real.rpow (-x) q)⁻¹ :=
      Real.rpow_neg (neg_nonneg.mpr hx.le) q
    simp only [f, gBot, normalizedAtInfinity]
    rw [abs_of_neg hx, hneg]
    simp only [div_eq_mul_inv, inv_inv]
    rfl
  have hthetaTop : gTop =Θ[atTop] f :=
    Asymptotics.isTheta_of_div_tendsto_nhds_ne_zero hratioTop one_ne_zero
  have hthetaBot : gBot =Θ[atBot] f :=
    Asymptotics.isTheta_of_div_tendsto_nhds_ne_zero hratioBot one_ne_zero
  have hmeasF : StronglyMeasurableAtFilter f atTop ∧
      StronglyMeasurableAtFilter f atBot := by
    constructor <;>
      exact (measurable_integrand a p).stronglyMeasurable.stronglyMeasurableAtFilter
  have hmeasTop : StronglyMeasurableAtFilter gTop atTop :=
    (measurable_rpow (-q)).stronglyMeasurable.stronglyMeasurableAtFilter
  have hmeasBot : StronglyMeasurableAtFilter gBot atBot := by
    have hm : Measurable gBot := by
      simpa only [gBot, Function.comp_apply] using
        (measurable_rpow (-q)).comp measurable_id.neg
    exact hm.stronglyMeasurable.stronglyMeasurableAtFilter
  have htop : IntegrableAtFilter f atTop ↔ 1 < q := by
    have hcomp : IntegrableAtFilter f atTop ↔ IntegrableAtFilter gTop atTop :=
      ⟨fun hf => hthetaTop.1.integrableAtFilter hmeasTop hf,
        fun hg => hthetaTop.2.integrableAtFilter hmeasF.1 hg⟩
    rw [hcomp]
    have hpow : IntegrableAtFilter (fun x : ℝ => Real.rpow x (-q)) atTop ↔
        -q < -1 := by
      simpa using (integrableAtFilter_rpow_atTop_iff (s := -q))
    rw [hpow]
    constructor <;> intro h <;> linarith
  have hbot : IntegrableAtFilter f atBot ↔ 1 < q := by
    have hcomp : IntegrableAtFilter f atBot ↔ IntegrableAtFilter gBot atBot :=
      ⟨fun hf => hthetaBot.1.integrableAtFilter hmeasBot hf,
        fun hg => hthetaBot.2.integrableAtFilter hmeasF.2 hg⟩
    rw [hcomp]
    have hneg : IntegrableAtFilter (fun x : ℝ => Real.rpow (-x) (-q)) atBot ↔
        IntegrableAtFilter (fun x : ℝ => Real.rpow x (-q)) atTop := by
      simpa using integrableAtFilter_comp_neg_atBot_iff
        (fun x : ℝ => Real.rpow x (-q))
    rw [hneg]
    have hpow : IntegrableAtFilter (fun x : ℝ => Real.rpow x (-q)) atTop ↔
        -q < -1 := by
      simpa using (integrableAtFilter_rpow_atTop_iff (s := -q))
    rw [hpow]
    constructor <;> intro h <;> linarith
  have hlocal : LocallyIntegrable f ↔ ∀ i, p i < 1 := by
    constructor
    · intro hloc i
      apply (gap6 a p ha i).mp
      exact (integrableAtFilter_punctured_iff_exists_interval (integrand a p) (a i)).mp
        (MeasureTheory.IntegrableAtFilter.filter_mono inf_le_left (hloc (a i)))
    · intro hp x
      by_cases hx : x ∈ Set.range a
      · rcases hx with ⟨i, rfl⟩
        rcases (gap6 a p ha i).mpr (hp i) with ⟨ε, hε, hint⟩
        exact ⟨Set.Ioo (a i - ε) (a i + ε),
          Ioo_mem_nhds (by linarith) (by linarith), hint⟩
      · let s : Set ℝ := (Set.range a)ᶜ
        have hsopen : IsOpen s := (Set.finite_range a).isClosed.isOpen_compl
        have hsmeas : MeasurableSet s := hsopen.measurableSet
        have hcont : ContinuousOn f s := by
          intro y hy
          exact (continuousAt_integrand_of_ne a p fun i hyi =>
            hy ⟨i, hyi.symm⟩).continuousWithinAt
        have hint := hcont.locallyIntegrableOn (μ := volume) hsmeas x hx
        rwa [hsopen.nhdsWithin_eq hx] at hint
  unfold FullIntegrable
  rw [integrable_iff_integrableAtFilter_atBot_atTop, hbot, htop, hlocal]
  simp only [f, q]
  tauto

theorem gap8 {n : ℕ} (a p : Fin n → ℝ)
    (ha : Set.Pairwise Set.univ (fun i j => a i ≠ a j)) :
    (1 < totalExponent p ∧ ∀ i, p i < 1) ↔ FullIntegrable a p := by
  exact (gap7 a p ha).symm

end
end ProofGap.Exercise2376
