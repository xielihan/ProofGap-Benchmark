import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise2370
noncomputable section

open Filter MeasureTheory

def integrand (n x : ℝ) : ℝ :=
  Real.rpow x n / Real.sqrt (1 - x ^ 2)
def NearZeroIntegrable (n : ℝ) : Prop :=
  IntegrableOn (integrand n) (Set.Ioc (0 : ℝ) (1 / 2))
def NearOneIntegrable (n : ℝ) : Prop :=
  IntegrableOn (integrand n) (Set.Ioo (1 / 2 : ℝ) 1)
def FullIntegrable (n : ℝ) : Prop :=
  IntegrableOn (integrand n) (Set.Ioo (0 : ℝ) 1)
def zeroNormalized (n x : ℝ) : ℝ :=
  Real.rpow x (-n) * integrand n x
def oneNormalized (n x : ℝ) : ℝ :=
  Real.sqrt (1 - x) * integrand n x
def oneModel (n x : ℝ) : ℝ :=
  Real.rpow x n / Real.sqrt (1 + x)

private theorem zeroNormalized_eq (n x : ℝ) (hx : 0 < x) :
    zeroNormalized n x = 1 / Real.sqrt (1 - x ^ 2) := by
  have hp : Real.rpow x (-n) * Real.rpow x n = 1 := by
    simp only [Real.rpow_eq_pow]
    rw [(Real.rpow_add hx _ _).symm]
    norm_num
  unfold zeroNormalized integrand
  rw [(mul_div_assoc _ _ _).symm, hp]

private theorem oneNormalized_eq_model (n x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    oneNormalized n x = oneModel n x := by
  have ha : 0 ≤ 1 - x := by linarith
  have hsa : Real.sqrt (1 - x) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  have hsb : Real.sqrt (1 + x) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  have hs : Real.sqrt (1 - x ^ 2) = Real.sqrt (1 - x) * Real.sqrt (1 + x) := by
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring, Real.sqrt_mul ha]
  unfold oneNormalized oneModel integrand
  rw [hs]
  field_simp [hsa, hsb]

private theorem endpointBase_mul_model (n x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    Real.rpow (1 - x) (-1 / 2 : ℝ) * oneModel n x = integrand n x := by
  have ha : 0 ≤ 1 - x := by linarith
  have hsa : Real.sqrt (1 - x) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  have hr : Real.rpow (1 - x) (-1 / 2 : ℝ) = (Real.sqrt (1 - x))⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring]
    rw [Real.rpow_eq_pow, Real.sqrt_eq_rpow]
    exact Real.rpow_neg ha (1 / 2 : ℝ)
  rw [hr, (oneNormalized_eq_model n x hx0 hx1).symm]
  unfold oneNormalized
  field_simp [hsa]

theorem gap1 (n : ℝ) :
    FullIntegrable n ↔ NearZeroIntegrable n ∧ NearOneIntegrable n := by
  unfold FullIntegrable NearZeroIntegrable NearOneIntegrable
  rw [(Set.Ioc_union_Ioo_eq_Ioo (a := (0 : ℝ)) (b := 1 / 2) (c := 1)
      (by norm_num) (by norm_num)).symm,
    MeasureTheory.integrableOn_union]

theorem gap2 (n : ℝ) :
    Tendsto (zeroNormalized n)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hrad : ContinuousAt (fun x : ℝ => 1 - x ^ 2) 0 := by fun_prop
  have hs0 := Real.continuous_sqrt.continuousAt.comp hrad
  have hs : ContinuousAt (fun x : ℝ => Real.sqrt (1 - x ^ 2)) 0 := by
    simpa [Function.comp_def] using hs0
  have hc : ContinuousAt (fun x : ℝ => 1 / Real.sqrt (1 - x ^ 2)) 0 :=
    continuousAt_const.div hs (by norm_num)
  have ht : Tendsto (fun x : ℝ => 1 / Real.sqrt (1 - x ^ 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa using hc.tendsto.mono_left inf_le_left
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (zeroNormalized_eq n x hx).symm

theorem gap3 (n : ℝ) :
    NearZeroIntegrable n ↔ -1 < n := by
  let den : ℝ → ℝ := fun x => Real.sqrt (1 - x ^ 2)
  have hden : ContinuousOn den (Set.Icc (0 : ℝ) (1 / 2)) := by
    unfold den
    exact (continuousOn_const.sub (continuousOn_id.pow 2)).sqrt
  have hden_ne : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2), den x ≠ 0 := by
    intro x hx
    apply Real.sqrt_ne_zero'.2
    have hx2 : x ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self hx.1 hx.2
    nlinarith
  have hinvden : ContinuousOn (fun x => 1 / den x) (Set.Icc (0 : ℝ) (1 / 2)) :=
    continuousOn_const.div hden hden_ne
  have hIcc : IntegrableOn (integrand n) (Set.Icc (0 : ℝ) (1 / 2)) ↔
      IntegrableOn (fun x : ℝ => x ^ n) (Set.Icc (0 : ℝ) (1 / 2)) := by
    constructor
    · intro h
      have hm := h.mul_continuousOn hden isCompact_Icc
      exact hm.congr_fun (fun x hx => by
        have hsne : Real.sqrt (1 - x ^ 2) ≠ 0 := by
          simpa [den] using hden_ne x hx
        unfold integrand den
        field_simp [hsne]
        exact Real.rpow_eq_pow _ _) measurableSet_Icc
    · intro h
      have hm := h.mul_continuousOn hinvden isCompact_Icc
      exact hm.congr_fun (fun x _ => by
        unfold integrand den
        simp [div_eq_mul_inv]) measurableSet_Icc
  unfold NearZeroIntegrable
  rw [(integrableOn_Icc_iff_integrableOn_Ioc (f := integrand n)).symm]
  rw [hIcc]
  rw [integrableOn_Icc_iff_integrableOn_Ioo]
  exact intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)

theorem gap4 (n : ℝ) :
    Tendsto (oneNormalized n)
        (nhdsWithin 1 (Set.Iio 1)) (nhds (1 / Real.sqrt 2)) ↔
      Tendsto (oneModel n)
        (nhdsWithin 1 (Set.Iio 1)) (nhds (1 / Real.sqrt 2)) := by
  have hx0 : ∀ᶠ x : ℝ in nhdsWithin 1 (Set.Iio 1), 0 < x :=
    Filter.Eventually.filter_mono inf_le_left (Ioi_mem_nhds one_pos)
  have heq : oneNormalized n =ᶠ[nhdsWithin 1 (Set.Iio 1)] oneModel n := by
    filter_upwards [self_mem_nhdsWithin, hx0] with x hx1 hx0
    exact oneNormalized_eq_model n x hx0 hx1
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

theorem gap5 (n : ℝ) :
    Tendsto (oneModel n)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (1 / Real.sqrt 2)) := by
  have hnum : ContinuousAt (fun x : ℝ => Real.rpow x n) 1 :=
    continuousAt_id.rpow_const (Or.inl one_ne_zero)
  have hden0 : ContinuousAt (fun x : ℝ => 1 + x) 1 := by fun_prop
  have hden : ContinuousAt (fun x : ℝ => Real.sqrt (1 + x)) 1 := by
    have h := Real.continuous_sqrt.continuousAt.comp hden0
    simpa [Function.comp_def] using h
  have hc : ContinuousAt (oneModel n) 1 := by
    unfold oneModel
    exact hnum.div hden (by norm_num)
  have ht : Tendsto (oneModel n) (nhdsWithin 1 (Set.Iio 1)) (nhds (oneModel n 1)) :=
    hc.tendsto.mono_left inf_le_left
  convert ht using 1
  norm_num [oneModel]

theorem gap6 (n : ℝ) :
    Tendsto (oneNormalized n)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (1 / Real.sqrt 2)) := by
  exact (gap4 n).2 (gap5 n)

theorem gap7 :
    ∀ n : ℝ, NearOneIntegrable n := by
  intro n
  let base : ℝ → ℝ := fun x => Real.rpow (1 - x) (-1 / 2 : ℝ)
  have h0 : IntervalIntegrable (fun x : ℝ => x ^ (-1 / 2 : ℝ)) volume 0 (1 / 2) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h1 := (h0.comp_sub_left 1).symm
  have hbint : IntervalIntegrable base volume (1 / 2) 1 := by
    simpa only [base, Real.rpow_eq_pow, sub_zero, sub_half] using h1
  have hbaseIoo : IntegrableOn base (Set.Ioo (1 / 2 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).1 hbint
  have hbase : IntegrableOn base (Set.Icc (1 / 2 : ℝ) 1) :=
    (integrableOn_Icc_iff_integrableOn_Ioo).2 hbaseIoo
  have hmodel : ContinuousOn (oneModel n) (Set.Icc (1 / 2 : ℝ) 1) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hnum : ContinuousAt (fun y : ℝ => Real.rpow y n) x :=
      continuousAt_id.rpow_const (Or.inl hx0.ne')
    have hden0 : ContinuousAt (fun y : ℝ => 1 + y) x := by fun_prop
    have hden : ContinuousAt (fun y : ℝ => Real.sqrt (1 + y)) x := by
      have h := Real.continuous_sqrt.continuousAt.comp hden0
      simpa [Function.comp_def] using h
    unfold oneModel
    exact hnum.div hden (Real.sqrt_ne_zero'.2 (by linarith))
  have hprod := hbase.mul_continuousOn hmodel isCompact_Icc
  have hprodIoo := hprod.mono Set.Ioo_subset_Icc_self le_rfl
  unfold NearOneIntegrable
  exact hprodIoo.congr_fun (fun x hx =>
    endpointBase_mul_model n x (by linarith [hx.1]) hx.2) measurableSet_Ioo

theorem gap8 (n : ℝ) :
    -1 < n ↔ FullIntegrable n := by
  constructor
  · intro hn
    exact (gap1 n).2 ⟨(gap3 n).2 hn, gap7 n⟩
  · intro hfull
    exact (gap3 n).1 ((gap1 n).1 hfull).1

end
end ProofGap.Exercise2370
