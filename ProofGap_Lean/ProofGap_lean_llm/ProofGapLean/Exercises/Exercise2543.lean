import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Ring

open scoped Interval

namespace ProofGap.Exercise2543

noncomputable section

def gaussian (x : ℝ) : ℝ := Real.exp (-x ^ 2)
def transformed (t : ℝ) : ℝ :=
  if t = 1 then 0
  else Real.exp (-(t / (1 - t)) ^ 2) / (1 - t) ^ 2
def mesh (i : ℕ) : ℝ := i / 18
def sample (i : ℕ) : ℝ := transformed (mesh i)
def gaussianHalfIntegral : ℝ := ∫ x in Set.Ioi (0 : ℝ), gaussian x
def transformedIntegral : ℝ := ∫ t in (0 : ℝ)..1, transformed t
def roundedSimpson : ℝ :=
  1 / 54 * (1 + 4.46894 + 2.49201 + 5.53415 + 3.04696 +
    6.61414 + 3.50460 + 7.14411 + 3.41685 + 5.88607 +
    2.12232 + 2.23855 + 0.32968 + 0.06009 + 0.00010)

private theorem gaussianHalfIntegral_eq :
    gaussianHalfIntegral = Real.sqrt Real.pi / 2 := by
  unfold gaussianHalfIntegral gaussian
  simpa using integral_gaussian_Ioi 1

private theorem gaussianHalfIntegral_bounds :
    (0.88618 : ℝ) < gaussianHalfIntegral ∧
      gaussianHalfIntegral < (0.88635 : ℝ) := by
  rw [gaussianHalfIntegral_eq]
  constructor
  · have hsq : (2 * (0.88618 : ℝ)) ^ 2 < Real.pi := by
      nlinarith [Real.pi_gt_d6]
    have hsqrt : 2 * (0.88618 : ℝ) < Real.sqrt Real.pi :=
      Real.lt_sqrt_of_sq_lt hsq
    nlinarith
  · have hsq : Real.pi < (2 * (0.88635 : ℝ)) ^ 2 := by
      nlinarith [Real.pi_lt_d6]
    have hsqrt : Real.sqrt Real.pi < 2 * (0.88635 : ℝ) :=
      (Real.sqrt_lt' (by norm_num : 0 < 2 * (0.88635 : ℝ))).2 hsq
    nlinarith

private theorem roundedSimpson_eq :
    roundedSimpson = 47.85857 / 54 := by
  norm_num [roundedSimpson]

private def expTaylor (n : ℕ) (x : ℝ) : ℝ :=
  ∑ m ∈ Finset.range n, x ^ m / m.factorial

private def expError (n : ℕ) (x : ℝ) : ℝ :=
  |x| ^ n * ((n.succ : ℝ) / (n.factorial * n))

private theorem exp_scaled_bounds (x : ℝ) (k n : ℕ)
    (hx : |x| ≤ 1) (hn : 0 < n)
    (hlow : 0 ≤ expTaylor n x - expError n x) :
    (expTaylor n x - expError n x) ^ k ≤
        Real.exp ((k : ℝ) * x) ∧
      Real.exp ((k : ℝ) * x) ≤
        (expTaylor n x + expError n x) ^ k := by
  have hb := Real.exp_bound (x := x) (n := n) hx hn
  change |Real.exp x - expTaylor n x| ≤ expError n x at hb
  rw [abs_le] at hb
  have hlo : expTaylor n x - expError n x ≤ Real.exp x := by
    linarith [hb.1]
  have hhi : Real.exp x ≤ expTaylor n x + expError n x := by
    linarith [hb.2]
  rw [Real.exp_nat_mul]
  exact ⟨pow_le_pow_left₀ hlow hlo k,
    pow_le_pow_left₀ (Real.exp_pos x).le hhi k⟩

private theorem exp_neg_nat_lt_inv_pow_two (n : ℕ) (hn : 0 < n) :
    Real.exp (-(n : ℝ)) < (1 / 2 : ℝ) ^ n := by
  rw [show -(n : ℝ) = (n : ℝ) * (-1 : ℝ) by ring,
    Real.exp_nat_mul]
  exact pow_lt_pow_left₀ Real.exp_neg_one_lt_half
    (Real.exp_pos (-1)).le hn.ne'

private theorem transformed_tendsto_at_one :
    Filter.Tendsto (fun t : ℝ =>
      Real.exp (-(t / (1 - t)) ^ 2) / (1 - t) ^ 2)
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
  have hAtTop : Filter.Tendsto
      (fun u : ℝ => Real.exp (-(u - 1) ^ 2) * u ^ 2)
      Filter.atTop (nhds 0) := by
    have hnonneg : ∀ᶠ u : ℝ in Filter.atTop,
        0 ≤ Real.exp (-(u - 1) ^ 2) * u ^ 2 :=
      Filter.Eventually.of_forall fun u =>
        mul_nonneg (Real.exp_pos _).le (sq_nonneg u)
    have hle : ∀ᶠ u : ℝ in Filter.atTop,
        Real.exp (-(u - 1) ^ 2) * u ^ 2 ≤
          u ^ 2 * Real.exp (-u) := by
      filter_upwards [Filter.eventually_ge_atTop (3 : ℝ)] with u hu
      have hsquare : u ≤ (u - 1) ^ 2 := by nlinarith
      have hexp : Real.exp (-(u - 1) ^ 2) ≤ Real.exp (-u) :=
        (Real.exp_le_exp).2 (neg_le_neg hsquare)
      calc
        Real.exp (-(u - 1) ^ 2) * u ^ 2 ≤
            Real.exp (-u) * u ^ 2 :=
          mul_le_mul_of_nonneg_right hexp (sq_nonneg u)
        _ = u ^ 2 * Real.exp (-u) := by ring
    exact squeeze_zero' hnonneg hle
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2)
  have hzero : Filter.Tendsto (fun t : ℝ => 1 - t)
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
    have hcont :=
      (by fun_prop : ContinuousAt (fun t : ℝ => 1 - t) 1).tendsto
    simpa using hcont.mono_left
      (show nhdsWithin (1 : ℝ) (Set.Iio 1) ≤ nhds 1 from inf_le_left)
  have hpos : ∀ᶠ t : ℝ in nhdsWithin 1 (Set.Iio 1),
      1 - t ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htt : t < 1 := by simpa only [Set.mem_Iio] using ht
    exact sub_pos.mpr htt
  have hden : Filter.Tendsto (fun t : ℝ => 1 - t)
      (nhdsWithin 1 (Set.Iio 1)) (nhdsWithin 0 (Set.Ioi 0)) :=
    Filter.tendsto_inf.2 ⟨hzero, Filter.tendsto_principal.2 hpos⟩
  have hinv : Filter.Tendsto (fun t : ℝ => (1 - t)⁻¹)
      (nhdsWithin 1 (Set.Iio 1)) Filter.atTop :=
    tendsto_inv_nhdsGT_zero.comp hden
  refine (hAtTop.comp hinv).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hne : 1 - t ≠ 0 := (sub_pos.mpr ht).ne'
  have hratio : (1 - t)⁻¹ - 1 = t / (1 - t) := by
    field_simp [hne]
    ring
  have hsquare : ((1 - t)⁻¹) ^ 2 = 1 / (1 - t) ^ 2 := by
    rw [inv_pow, one_div]
  change Real.exp (-((1 - t)⁻¹ - 1) ^ 2) * ((1 - t)⁻¹) ^ 2 =
    Real.exp (-(t / (1 - t)) ^ 2) / (1 - t) ^ 2
  rw [hratio, hsquare]
  ring

private def compactify (x : ℝ) : ℝ := x / (1 + x)

private def compactifyDeriv (x : ℝ) : ℝ := 1 / (1 + x) ^ 2

private theorem compactify_hasDerivAt (x : ℝ) (hx : -1 < x) :
    HasDerivAt compactify (compactifyDeriv x) x := by
  have hnum : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hden : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    convert (hasDerivAt_const x 1).add (hasDerivAt_id x) using 1 <;>
      norm_num
  have hquot := hnum.div hden (by dsimp; linarith)
  unfold compactify compactifyDeriv
  convert hquot using 1 <;> ring

private theorem transformed_compactify_mul (x : ℝ) (hx : 0 ≤ x) :
    transformed (compactify x) * compactifyDeriv x = gaussian x := by
  have hden : 1 + x ≠ 0 := by linarith
  have hnotone : x / (1 + x) ≠ 1 := by
    intro h
    field_simp [hden] at h
    linarith
  have hone : 1 - x / (1 + x) = 1 / (1 + x) := by
    field_simp [hden]
    ring
  have hratio : (x / (1 + x)) / (1 - x / (1 + x)) = x := by
    rw [hone]
    field_simp [hden]
  unfold transformed compactify compactifyDeriv gaussian
  rw [if_neg hnotone, hratio, hone]
  field_simp [hden]

private theorem continuousOn_transformed_Iio :
    ContinuousOn transformed (Set.Iio 1) := by
  have hratio : ContinuousOn (fun t : ℝ => t / (1 - t)) (Set.Iio 1) := by
    apply ContinuousOn.div continuousOn_id
      (continuousOn_const.sub continuousOn_id)
    intro t ht
    have : t < 1 := by simpa only [Set.mem_Iio] using ht
    simp only [id_eq]
    linarith
  have hnum : ContinuousOn
      (fun t : ℝ => Real.exp (-(t / (1 - t)) ^ 2)) (Set.Iio 1) :=
    Real.continuous_exp.comp_continuousOn (hratio.pow 2).neg
  have hden : ContinuousOn (fun t : ℝ => (1 - t) ^ 2) (Set.Iio 1) := by
    fun_prop
  have hraw : ContinuousOn (fun t : ℝ =>
      Real.exp (-(t / (1 - t)) ^ 2) / (1 - t) ^ 2) (Set.Iio 1) := by
    apply hnum.div hden
    intro t ht
    have : t < 1 := by simpa only [Set.mem_Iio] using ht
    exact pow_ne_zero _ (by linarith)
  apply hraw.congr
  intro t ht
  have htt : t < 1 := by simpa only [Set.mem_Iio] using ht
  simp [transformed, ne_of_lt htt]

private theorem transformed_continuousAt_of_lt {t : ℝ} (ht : t < 1) :
    ContinuousAt transformed t := by
  have hne : 1 - t ≠ 0 := by linarith
  have hdenAt : ContinuousAt (fun s : ℝ => 1 - s) t :=
    continuousAt_const.sub continuousAt_id
  have hratioAt : ContinuousAt (fun s : ℝ => s / (1 - s)) t :=
    continuousAt_id.div hdenAt hne
  have hnumAt : ContinuousAt
      (fun s : ℝ => Real.exp (-(s / (1 - s)) ^ 2)) t :=
    Real.continuous_exp.continuousAt.comp' (hratioAt.pow 2).neg
  have hraw : ContinuousAt (fun s : ℝ =>
      Real.exp (-(s / (1 - s)) ^ 2) / (1 - s) ^ 2) t := by
    exact hnumAt.div (hdenAt.pow 2) (pow_ne_zero _ hne)
  apply hraw.congr
  filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
  have hss : s < 1 := by simpa only [Set.mem_Iio] using hs
  simp [transformed, ne_of_lt hss]

private theorem transformed_continuousWithinAt_one :
    ContinuousWithinAt transformed (Set.Iic 1) 1 := by
  have hleft : Filter.Tendsto transformed
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
    refine transformed_tendsto_at_one.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htt : t < 1 := by simpa only [Set.mem_Iio] using ht
    simp [transformed, ne_of_lt htt]
  change Filter.Tendsto transformed (nhdsWithin 1 (Set.Iic 1))
    (nhds (transformed 1))
  have hone : transformed 1 = 0 := by simp [transformed]
  rw [hone]
  rw [← Set.Iio_insert, nhdsWithin_insert]
  apply Filter.tendsto_sup.2
  constructor
  · apply Filter.tendsto_pure_left.2
    intro s hs
    have h0 : (0 : ℝ) ∈ s := mem_of_mem_nhds hs
    simpa [transformed] using h0
  · exact hleft

private theorem continuousOn_transformed_Icc :
    ContinuousOn transformed (Set.Icc 0 1) := by
  intro t ht
  by_cases ht1 : t = 1
  · subst t
    exact transformed_continuousWithinAt_one.mono Set.Icc_subset_Iic_self
  · have hlt : t < 1 := lt_of_le_of_ne ht.2 ht1
    exact (transformed_continuousAt_of_lt hlt).continuousWithinAt

private theorem partial_integral_eq (u : ℝ) (hu : 0 ≤ u) :
    (∫ x in (0 : ℝ)..u, gaussian x) =
      ∫ t in (0 : ℝ)..compactify u, transformed t := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) u,
      HasDerivAt compactify (compactifyDeriv x) x := by
    intro x hx
    rw [Set.uIcc_of_le hu] at hx
    exact compactify_hasDerivAt x (by linarith [hx.1])
  have hderivCont : ContinuousOn compactifyDeriv (Set.uIcc (0 : ℝ) u) := by
    intro x hx
    rw [Set.uIcc_of_le hu] at hx
    have hne : 1 + x ≠ 0 := by linarith [hx.1]
    unfold compactifyDeriv
    have hbase : ContinuousAt (fun y : ℝ => 1 + y) x :=
      continuousAt_const.add continuousAt_id
    exact (continuousAt_const.div (hbase.pow 2)
      (pow_ne_zero _ hne)).continuousWithinAt
  have himage : compactify '' Set.uIcc (0 : ℝ) u ⊆ Set.Iio 1 := by
    rintro y ⟨x, hx, rfl⟩
    rw [Set.uIcc_of_le hu] at hx
    unfold compactify
    change x / (1 + x) < 1
    rw [div_lt_one (by linarith [hx.1])]
    linarith
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := (0 : ℝ)) (b := u) (f := compactify)
    (f' := compactifyDeriv) (g := transformed)
    hderiv hderivCont (continuousOn_transformed_Iio.mono himage)
  have hleft :
      (∫ x in (0 : ℝ)..u,
        (transformed ∘ compactify) x * compactifyDeriv x) =
        ∫ x in (0 : ℝ)..u, gaussian x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hu] at hx
    simpa [Function.comp_apply] using transformed_compactify_mul x hx.1
  calc
    (∫ x in (0 : ℝ)..u, gaussian x) =
        ∫ x in (0 : ℝ)..u,
          (transformed ∘ compactify) x * compactifyDeriv x := hleft.symm
    _ = ∫ t in compactify 0..compactify u, transformed t := hsub
    _ = ∫ t in (0 : ℝ)..compactify u, transformed t := by
      simp [compactify]

private theorem compactify_tendsto_atTop :
    Filter.Tendsto compactify Filter.atTop (nhds 1) := by
  have hplus : Filter.Tendsto (fun x : ℝ => 1 + x)
      Filter.atTop Filter.atTop := by
    simpa [add_comm] using
      (Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
        Filter.tendsto_id)
  have hinv : Filter.Tendsto (fun x : ℝ => (1 + x)⁻¹)
      Filter.atTop (nhds 0) := tendsto_inv_atTop_zero.comp hplus
  have hlim : Filter.Tendsto (fun x : ℝ => 1 - (1 + x)⁻¹)
      Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hinv
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (-1 : ℝ)] with x hx
  unfold compactify
  have hne : 1 + x ≠ 0 := by linarith
  field_simp [hne]
  ring

theorem gap1 : gaussianHalfIntegral = transformedIntegral := by
  have hgint : MeasureTheory.IntegrableOn gaussian (Set.Ioi (0 : ℝ)) := by
    simpa [gaussian] using
      (integrable_exp_neg_mul_sq (b := (1 : ℝ)) zero_lt_one).integrableOn
  have hleft : Filter.Tendsto
      (fun u : ℝ => ∫ x in (0 : ℝ)..u, gaussian x)
      Filter.atTop (nhds gaussianHalfIntegral) := by
    unfold gaussianHalfIntegral
    exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 hgint
      Filter.tendsto_id
  have htransOn : ContinuousOn transformed (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le zero_le_one] using continuousOn_transformed_Icc
  have htransInt : IntervalIntegrable transformed MeasureTheory.volume 0 1 :=
    htransOn.intervalIntegrable
  have hprimitive : ContinuousOn
      (fun b : ℝ => ∫ t in (0 : ℝ)..b, transformed t)
      (Set.uIcc (0 : ℝ) 1) :=
    intervalIntegral.continuousOn_primitive_interval' htransInt
      Set.left_mem_uIcc
  have hrange : ∀ᶠ u : ℝ in Filter.atTop,
      compactify u ∈ Set.uIcc (0 : ℝ) 1 := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with u hu
    rw [Set.uIcc_of_le zero_le_one]
    constructor
    · unfold compactify
      positivity
    · unfold compactify
      rw [div_le_one (by positivity)]
      linarith
  have hcompactWithin : Filter.Tendsto compactify Filter.atTop
      (nhdsWithin 1 (Set.uIcc (0 : ℝ) 1)) :=
    Filter.tendsto_inf.2 ⟨compactify_tendsto_atTop,
      Filter.tendsto_principal.2 hrange⟩
  have hright : Filter.Tendsto
      (fun u : ℝ => ∫ t in (0 : ℝ)..compactify u, transformed t)
      Filter.atTop (nhds transformedIntegral) := by
    unfold transformedIntegral
    exact Filter.Tendsto.comp (hprimitive 1 Set.right_mem_uIcc)
      hcompactWithin
  have heq : ∀ᶠ u : ℝ in Filter.atTop,
      (∫ x in (0 : ℝ)..u, gaussian x) =
        ∫ t in (0 : ℝ)..compactify u, transformed t := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with u hu
    exact partial_integral_eq u hu
  exact tendsto_nhds_unique hleft
    (hright.congr' (Filter.EventuallyEq.symm heq))
theorem gap2 : ∃ Δt : ℝ, Δt = 1 / 18 := by
  exact ⟨1 / 18, rfl⟩
theorem gap3 : mesh 0 = 0 := by
  norm_num [mesh]
theorem gap4 : sample 0 = 1 := by
  norm_num [sample, transformed, mesh]
theorem gap5 : mesh 1 = 1 / 18 := by
  norm_num [mesh]
theorem gap6 : |4 * sample 1 - 4.46894| < 0.00001 := by
  have h := Real.exp_bound (x := -(1 / 289 : ℝ)) (n := 6)
    (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  norm_num [sample, transformed, mesh]
  rw [abs_le] at h
  rw [abs_lt]
  constructor <;> nlinarith [h.1, h.2]
theorem gap7 : mesh 2 = 1 / 9 := by
  norm_num [mesh]
theorem gap8 : |2 * sample 2 - 2.49201| < 0.00001 := by
  have h := Real.exp_bound (x := -(1 / 64 : ℝ)) (n := 12)
    (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  norm_num [sample, transformed, mesh]
  rw [abs_le] at h
  rw [abs_lt]
  constructor <;> nlinarith [h.1, h.2]
theorem gap9 : mesh 3 = 1 / 6 := by
  norm_num [mesh]
theorem gap10 : |4 * sample 3 - 5.53415| < 0.00001 := by
  have h := Real.exp_bound (x := -(1 / 25 : ℝ)) (n := 12)
    (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  norm_num [sample, transformed, mesh]
  rw [abs_le] at h
  rw [abs_lt]
  constructor <;> nlinarith [h.1, h.2]
theorem gap11 : mesh 4 = 2 / 9 := by
  norm_num [mesh]
theorem gap12 : |2 * sample 4 - 3.04696| < 0.00001 := by
  have h := Real.exp_bound (x := -(4 / 49 : ℝ)) (n := 12)
    (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  norm_num [sample, transformed, mesh]
  rw [abs_le] at h
  rw [abs_lt]
  constructor <;> nlinarith [h.1, h.2]
theorem gap13 : mesh 5 = 5 / 18 := by
  norm_num [mesh]
theorem gap14 : |4 * sample 5 - 6.61414| < 0.00001 := by
  have h := Real.exp_bound (x := -(25 / 169 : ℝ)) (n := 12)
    (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  norm_num [sample, transformed, mesh]
  rw [abs_le] at h
  rw [abs_lt]
  constructor <;> nlinarith [h.1, h.2]
theorem gap15 : mesh 6 = 1 / 3 := by
  norm_num [mesh]
theorem gap16 : |2 * sample 6 - 3.50460| < 0.00001 := by
  have h := Real.exp_bound (x := -(1 / 4 : ℝ)) (n := 12)
    (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  norm_num [sample, transformed, mesh]
  rw [abs_le] at h
  rw [abs_lt]
  constructor <;> nlinarith [h.1, h.2]
theorem gap17 : mesh 7 = 7 / 18 := by
  norm_num [mesh]
theorem gap18 : |4 * sample 7 - 7.14411| < 0.00001 := by
  have h := Real.exp_bound (x := -(49 / 121 : ℝ)) (n := 12)
    (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  norm_num [sample, transformed, mesh]
  rw [abs_le] at h
  rw [abs_lt]
  constructor <;> nlinarith [h.1, h.2]
theorem gap19 : mesh 8 = 4 / 9 := by
  norm_num [mesh]
theorem gap20 : |2 * sample 8 - 3.41685| < 0.00001 := by
  have h := Real.exp_bound (x := -(16 / 25 : ℝ)) (n := 12)
    (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  norm_num [sample, transformed, mesh]
  rw [abs_le] at h
  rw [abs_lt]
  constructor <;> nlinarith [h.1, h.2]
theorem gap21 : mesh 9 = 1 / 2 := by
  norm_num [mesh]
theorem gap22 : |4 * sample 9 - 5.88607| < 0.00001 := by
  have h := Real.exp_bound (x := (-1 : ℝ)) (n := 12)
    (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  norm_num [sample, transformed, mesh]
  rw [abs_le] at h
  rw [abs_lt]
  constructor <;> nlinarith [h.1, h.2]
theorem gap23 : mesh 10 = 5 / 9 := by
  norm_num [mesh]
theorem gap24 : |2 * sample 10 - 2.12232| < 0.00001 := by
  have h := exp_scaled_bounds (-(25 / 32 : ℝ)) 2 12
    (by norm_num) (by norm_num)
    (by norm_num [expTaylor, expError, Finset.sum_range_succ, Nat.factorial])
  norm_num [expTaylor, expError, Finset.sum_range_succ, Nat.factorial] at h
  norm_num [sample, transformed, mesh]
  rw [abs_lt]
  constructor <;> nlinarith [h.1, h.2]
theorem gap25 : mesh 11 = 11 / 18 := by
  norm_num [mesh]
theorem gap26 : |4 * sample 11 - 2.23855| < 0.00001 := by
  have h := exp_scaled_bounds (-(121 / 147 : ℝ)) 3 12
    (by norm_num) (by norm_num)
    (by norm_num [expTaylor, expError, Finset.sum_range_succ, Nat.factorial])
  norm_num [expTaylor, expError, Finset.sum_range_succ, Nat.factorial] at h
  norm_num [sample, transformed, mesh]
  rw [abs_lt]
  constructor <;> nlinarith [h.1, h.2]
theorem gap27 : mesh 12 = 2 / 3 := by
  norm_num [mesh]
theorem gap28 : |2 * sample 12 - 0.32968| < 0.00001 := by
  have h := exp_scaled_bounds (-1 : ℝ) 4 12
    (by norm_num) (by norm_num)
    (by norm_num [expTaylor, expError, Finset.sum_range_succ, Nat.factorial])
  norm_num [expTaylor, expError, Finset.sum_range_succ, Nat.factorial] at h
  norm_num [sample, transformed, mesh]
  rw [abs_lt]
  constructor <;> nlinarith [h.1, h.2]
theorem gap29 : mesh 13 = 13 / 18 := by
  norm_num [mesh]
theorem gap30 : |4 * sample 13 - 0.06009| < 0.00001 := by
  have h := exp_scaled_bounds (-(169 / 175 : ℝ)) 7 12
    (by norm_num) (by norm_num)
    (by norm_num [expTaylor, expError, Finset.sum_range_succ, Nat.factorial])
  norm_num [expTaylor, expError, Finset.sum_range_succ, Nat.factorial] at h
  norm_num [sample, transformed, mesh]
  rw [abs_lt]
  constructor <;> nlinarith [h.1, h.2]
theorem gap31 : mesh 14 = 7 / 9 := by
  norm_num [mesh]
theorem gap32 : |2 * sample 14 - 0.00019| < 0.00001 := by
  have h := exp_scaled_bounds (-(49 / 52 : ℝ)) 13 12
    (by norm_num) (by norm_num)
    (by norm_num [expTaylor, expError, Finset.sum_range_succ, Nat.factorial])
  norm_num [expTaylor, expError, Finset.sum_range_succ, Nat.factorial] at h
  norm_num [sample, transformed, mesh]
  rw [abs_lt]
  constructor <;> nlinarith [h.1, h.2]
theorem gap33 : mesh 15 = 5 / 6 := by
  norm_num [mesh]
theorem gap34 : |4 * sample 15| < 0.00001 := by
  have h := exp_neg_nat_lt_inv_pow_two 25 (by norm_num)
  norm_num at h
  norm_num [sample, transformed, mesh]
  rw [abs_of_nonneg (by positivity)]
  nlinarith
theorem gap35 : mesh 16 = 8 / 9 := by
  norm_num [mesh]
theorem gap36 : |2 * sample 16| < 0.00001 := by
  have hpow := exp_neg_nat_lt_inv_pow_two 32 (by norm_num)
  have hmono : Real.exp (-64) < Real.exp (-32) :=
    (Real.exp_lt_exp).2 (by norm_num)
  norm_num at hpow
  norm_num [sample, transformed, mesh]
  rw [abs_of_nonneg (by positivity)]
  nlinarith
theorem gap37 : mesh 17 = 17 / 18 := by
  norm_num [mesh]
theorem gap38 : |4 * sample 17| < 0.00001 := by
  have hpow := exp_neg_nat_lt_inv_pow_two 32 (by norm_num)
  have hmono : Real.exp (-289) < Real.exp (-32) :=
    (Real.exp_lt_exp).2 (by norm_num)
  norm_num at hpow
  norm_num [sample, transformed, mesh]
  rw [abs_of_nonneg (by positivity)]
  nlinarith
theorem gap39 : mesh 18 = 1 := by
  norm_num [mesh]
theorem gap40 : sample 18 = 0 := by
  norm_num [sample, transformed, mesh]
theorem gap41 :
    Filter.Tendsto (fun t : ℝ =>
      Real.exp (-(t / (1 - t)) ^ 2) / (1 - t) ^ 2)
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
  exact transformed_tendsto_at_one
theorem gap42 : gaussianHalfIntegral = transformedIntegral := by
  exact gap1
theorem gap43 : |transformedIntegral - roundedSimpson| < 0.0001 := by
  rw [← gap1, roundedSimpson_eq, abs_lt]
  constructor <;> nlinarith [gaussianHalfIntegral_bounds.1,
    gaussianHalfIntegral_bounds.2]
theorem gap44 : |gaussianHalfIntegral - roundedSimpson| < 0.0001 := by
  rw [roundedSimpson_eq, abs_lt]
  constructor <;> nlinarith [gaussianHalfIntegral_bounds.1,
    gaussianHalfIntegral_bounds.2]
theorem gap45 : |gaussianHalfIntegral - 47.85857 / 54| < 0.0001 := by
  rw [abs_lt]
  constructor <;> nlinarith [gaussianHalfIntegral_bounds.1,
    gaussianHalfIntegral_bounds.2]
theorem gap46 : |(47.85857 / 54 : ℝ) - 0.88627| < 0.00001 := by
  norm_num [abs_lt]
theorem gap47 : |gaussianHalfIntegral - 0.88627| < 0.0001 := by
  rw [abs_lt]
  constructor <;> nlinarith [gaussianHalfIntegral_bounds.1,
    gaussianHalfIntegral_bounds.2]

end

end ProofGap.Exercise2543
