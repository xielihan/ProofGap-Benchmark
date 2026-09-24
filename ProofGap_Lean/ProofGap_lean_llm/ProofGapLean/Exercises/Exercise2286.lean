import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped Interval

namespace ProofGap.Exercise2286

noncomputable section

def I (n m : ℕ) : ℝ :=
  ∫ x in 0..1, x ^ m * Real.log x ^ n

def boundaryTerm (n m : ℕ) (x : ℝ) : ℝ :=
  x ^ (m + 1) * Real.log x ^ n / (m + 1 : ℝ)

def recurrenceProduct (n m : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (Nat.factorial n : ℝ) /
    (m + 1 : ℝ) ^ n * I 0 m

def closedForm (n m : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (Nat.factorial n : ℝ) /
    (m + 1 : ℝ) ^ (n + 1)

private def tailIntegral (n : ℕ) (c : ℝ) : ℝ :=
  ∫ y : ℝ in Set.Ioi 1, Real.log y ^ n * y ^ (-(c + 1) : ℝ)

private theorem integrableOn_log_pow_mul_rpow_Ici
    (n : ℕ) {a : ℝ} (ha : 1 < a) :
    MeasureTheory.IntegrableOn
      (fun y : ℝ => Real.log y ^ n * y ^ (-a : ℝ)) (Set.Ici 1) := by
  let b : ℝ := (a + 1) / 2
  have hb1 : 1 < b := by dsimp [b]; linarith
  have hba : b < a := by dsimp [b]; linarith
  have hlocal :
      MeasureTheory.LocallyIntegrableOn
        (fun y : ℝ => Real.log y ^ n * y ^ (-a : ℝ)) (Set.Ici 1) := by
    apply ContinuousOn.locallyIntegrableOn
    · have hne : ∀ y : ℝ, y ∈ Set.Ici 1 → y ≠ 0 := by
        intro y hy
        exact ne_of_gt (zero_lt_one.trans_le hy)
      exact ((continuous_id.continuousOn.log hne).pow n).mul
        (continuous_id.continuousOn.rpow_const
          (fun y hy => Or.inl (hne y hy)))
    · exact measurableSet_Ici
  have hlog :=
    (isLittleO_log_rpow_rpow_atTop (s := a - b) (n : ℝ)
      (sub_pos.mpr hba)).isBigO
  have hprod :=
    hlog.smul
      (Asymptotics.isBigO_refl (fun y : ℝ => y ^ (-a : ℝ)) Filter.atTop)
  have hbig :
      (fun y : ℝ => Real.log y ^ n * y ^ (-a : ℝ)) =O[Filter.atTop]
        (fun y : ℝ => y ^ (-b : ℝ)) := by
    refine hprod.congr' ?_ ?_
    · filter_upwards with y
      simp only [Real.rpow_natCast, smul_eq_mul]
    · filter_upwards [Filter.eventually_gt_atTop 0] with y hy
      simp only [smul_eq_mul]
      rw [← Real.rpow_add hy]
      congr 2
      ring
  exact hlocal.integrableOn_of_isBigO_atTop hbig
    (integrableAtFilter_rpow_atTop_iff.mpr (by linarith))

private theorem integrableOn_tail (n : ℕ) {c : ℝ} (hc : 0 < c) :
    MeasureTheory.IntegrableOn
      (fun y : ℝ => Real.log y ^ n * y ^ (-(c + 1) : ℝ)) (Set.Ioi 1) :=
  (integrableOn_log_pow_mul_rpow_Ici n (a := c + 1) (by linarith)).mono_set
    Set.Ioi_subset_Ici_self

private theorem tendsto_log_pow_mul_rpow_atTop
    (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun y : ℝ => Real.log y ^ n * y ^ (-c : ℝ))
      Filter.atTop (nhds 0) := by
  have h :=
    (isLittleO_log_rpow_rpow_atTop (s := c) (n : ℝ) hc).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [Filter.eventually_gt_atTop 0] with y hy
  rw [Real.rpow_natCast, Real.rpow_neg hy.le]
  simp only [div_eq_mul_inv]

private theorem tail_recurrence (n : ℕ) {c : ℝ}
    (hn : 0 < n) (hc : 0 < c) :
    tailIntegral n c = (n : ℝ) / c * tailIntegral (n - 1) c := by
  let u : ℝ → ℝ := fun y => Real.log y ^ n
  let u' : ℝ → ℝ := fun y => (n : ℝ) * Real.log y ^ (n - 1) / y
  let v : ℝ → ℝ := fun y => -(1 / c) * y ^ (-c : ℝ)
  let v' : ℝ → ℝ := fun y => y ^ (-(c + 1) : ℝ)
  have hu : ∀ y ∈ Set.Ioi (1 : ℝ), HasDerivAt u (u' y) y := by
    intro y hy
    have hy0 : y ≠ 0 := ne_of_gt (zero_lt_one.trans hy)
    simpa only [u, u', div_eq_mul_inv] using
      (Real.hasDerivAt_log hy0).pow n
  have hv : ∀ y ∈ Set.Ioi (1 : ℝ), HasDerivAt v (v' y) y := by
    intro y hy
    have hy0 : y ≠ 0 := ne_of_gt (zero_lt_one.trans hy)
    have hraw :=
      (Real.hasDerivAt_rpow_const (p := -c) (Or.inl hy0)).const_mul
        (-(1 / c))
    dsimp only [v, v']
    convert hraw using 1
    · field_simp [ne_of_gt hc]
      ring
  have huv' : MeasureTheory.IntegrableOn (u * v') (Set.Ioi 1) := by
    simpa only [u, v', Pi.mul_apply] using integrableOn_tail n hc
  have hu'v : MeasureTheory.IntegrableOn (u' * v) (Set.Ioi 1) := by
    have hbase := (integrableOn_tail (n - 1) hc).const_mul (-(n : ℝ) / c)
    refine MeasureTheory.IntegrableOn.congr_fun hbase ?_ measurableSet_Ioi
    intro y hy
    have hy0 : 0 < y := zero_lt_one.trans hy
    have hpow :
        y⁻¹ * y ^ (-c : ℝ) = y ^ (-(c + 1) : ℝ) := by
      rw [← Real.rpow_neg_one y, ← Real.rpow_add hy0]
      congr 1
      ring
    dsimp only [u', v, Pi.mul_apply]
    symm
    rw [div_eq_mul_inv]
    rw [show ((n : ℝ) * Real.log y ^ (n - 1) * y⁻¹) *
        (-(1 / c) * y ^ (-c : ℝ)) =
        (-(n : ℝ) / c) * Real.log y ^ (n - 1) *
          (y⁻¹ * y ^ (-c : ℝ)) by ring]
    rw [hpow]
    ring
  have hzero : Filter.Tendsto (u * v) (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    have hcont : ContinuousAt (u * v) 1 := by
      exact (Real.continuousAt_log one_ne_zero).pow n |>.mul
        (continuousAt_const.mul
          (continuousAt_id.rpow_const (Or.inl one_ne_zero)))
    have ht :
        Filter.Tendsto (u * v) (nhdsWithin 1 (Set.Ioi 1))
          (nhds ((u * v) 1)) :=
      hcont.continuousWithinAt
    convert ht using 1
    norm_num [u, v, Nat.ne_of_gt hn]
  have hinfty : Filter.Tendsto (u * v) Filter.atTop (nhds 0) := by
    have ht := Filter.Tendsto.const_mul (-(1 / c))
      (tendsto_log_pow_mul_rpow_atTop n hc)
    convert ht using 1
    · funext y
      simp only [u, v, Pi.mul_apply]
      ring
    · ring
  have hparts :=
    MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
      hu hv huv' hu'v hzero hinfty
  have hleft :
      (∫ y : ℝ in Set.Ioi 1, u y * v' y) = tailIntegral n c := by
    rfl
  have hright :
      (∫ y : ℝ in Set.Ioi 1, u' y * v y) =
        (-(n : ℝ) / c) * tailIntegral (n - 1) c := by
    unfold tailIntegral
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    have hy0 : 0 < y := zero_lt_one.trans hy
    have hpow :
        y⁻¹ * y ^ (-c : ℝ) = y ^ (-(c + 1) : ℝ) := by
      rw [← Real.rpow_neg_one y, ← Real.rpow_add hy0]
      congr 1
      ring
    dsimp only [u', v]
    rw [div_eq_mul_inv]
    rw [show ((n : ℝ) * Real.log y ^ (n - 1) * y⁻¹) *
        (-(1 / c) * y ^ (-c : ℝ)) =
        (-(n : ℝ) / c) * Real.log y ^ (n - 1) *
          (y⁻¹ * y ^ (-c : ℝ)) by ring]
    rw [hpow]
    ring
  rw [hleft, hright] at hparts
  calc
    tailIntegral n c =
        0 - 0 - (-(n : ℝ) / c) * tailIntegral (n - 1) c := hparts
    _ = (n : ℝ) / c * tailIntegral (n - 1) c := by ring

private theorem tailIntegral_zero {c : ℝ} (hc : 0 < c) :
    tailIntegral 0 c = 1 / c := by
  unfold tailIntegral
  simp only [pow_zero, one_mul]
  rw [integral_Ioi_rpow_of_lt (by linarith : -(c + 1) < (-1 : ℝ))
    zero_lt_one]
  rw [Real.one_rpow]
  field_simp [ne_of_gt hc]
  ring

private theorem tailIntegral_formula (n : ℕ) {c : ℝ} (hc : 0 < c) :
    tailIntegral n c = (Nat.factorial n : ℝ) / c ^ (n + 1) := by
  induction n with
  | zero =>
      simpa using tailIntegral_zero hc
  | succ n ih =>
      rw [tail_recurrence (n + 1) (by omega) hc]
      simp only [Nat.add_sub_cancel]
      rw [ih]
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp [ne_of_gt hc]
      ring

private def unitIntegral (n : ℕ) (r : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, x ^ r * Real.log x ^ n

private theorem unitIntegral_eq_tail (n : ℕ) {r : ℝ} (hr : -1 < r) :
    unitIntegral n r = (-1 : ℝ) ^ n * tailIntegral n (r + 1) := by
  let h : ℝ → ℝ := fun y => y ^ r * Real.log y ^ n
  let g : ℝ → ℝ := Set.Ioc (0 : ℝ) 1 |>.indicator h
  let k : ℝ → ℝ :=
    fun y => (-1 : ℝ) ^ n *
      (Real.log y ^ n * y ^ (-(r + 2) : ℝ))
  have hpoint : ∀ y ∈ Set.Ioi (0 : ℝ),
      (|(-1 : ℝ)| * y ^ ((-1 : ℝ) - 1)) • g (y ^ (-1 : ℝ)) =
        (Set.Ici (1 : ℝ)).indicator k y := by
    intro y hy
    have hy0 : 0 < y := hy
    by_cases hy1 : 1 ≤ y
    · have hinv : y⁻¹ ∈ Set.Ioc (0 : ℝ) 1 :=
        ⟨inv_pos.mpr hy0, (inv_le_one₀ hy0).2 hy1⟩
      have hyIci : y ∈ Set.Ici (1 : ℝ) := hy1
      have hg : g y⁻¹ = h y⁻¹ := by
        simp only [g, Set.indicator_of_mem hinv]
      rw [Set.indicator_of_mem hyIci, Real.rpow_neg_one, hg]
      simp only [abs_neg, abs_one, one_mul, smul_eq_mul, h, k]
      rw [Real.inv_rpow hy0.le, ← Real.rpow_neg hy0.le, Real.log_inv,
        neg_pow]
      have hpow :
          y ^ ((-1 : ℝ) - 1) * y ^ (-r : ℝ) =
            y ^ (-(r + 2) : ℝ) := by
        rw [← Real.rpow_add hy0]
        congr 1
        ring
      rw [show y ^ ((-1 : ℝ) - 1) *
          (y ^ (-r : ℝ) * ((-1 : ℝ) ^ n * Real.log y ^ n)) =
          (-1 : ℝ) ^ n * Real.log y ^ n *
            (y ^ ((-1 : ℝ) - 1) * y ^ (-r : ℝ)) by ring]
      rw [hpow]
      ring
    · have hylt : y < 1 := lt_of_not_ge hy1
      have hnotInv : y⁻¹ ∉ Set.Ioc (0 : ℝ) 1 := by
        intro hmem
        exact (not_le_of_gt ((one_lt_inv₀ hy0).2 hylt)) hmem.2
      have hnotIci : y ∉ Set.Ici (1 : ℝ) := hy1
      rw [Set.indicator_of_notMem hnotIci, Real.rpow_neg_one]
      simp only [g, Set.indicator_of_notMem hnotInv, smul_zero]
  have hsub :=
    MeasureTheory.integral_comp_rpow_Ioi g
      (p := (-1 : ℝ)) (by norm_num)
  have hrhs :
      (∫ y : ℝ in Set.Ioi 0, g y) =
        ∫ y : ℝ in Set.Ioc 0 1, h y := by
    dsimp only [g]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc]
    rw [show Set.Ioi (0 : ℝ) ∩ Set.Ioc 0 1 = Set.Ioc 0 1 by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]
      tauto]
  have hlhs :
      (∫ y : ℝ in Set.Ioi 0,
          (|(-1 : ℝ)| * y ^ ((-1 : ℝ) - 1)) • g (y ^ (-1 : ℝ))) =
        (-1 : ℝ) ^ n * tailIntegral n (r + 1) := by
    calc
      (∫ y : ℝ in Set.Ioi 0,
          (|(-1 : ℝ)| * y ^ ((-1 : ℝ) - 1)) • g (y ^ (-1 : ℝ))) =
          ∫ y : ℝ in Set.Ioi 0, (Set.Ici (1 : ℝ)).indicator k y := by
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
            exact hpoint
      _ = ∫ y : ℝ in Set.Ioi 0 ∩ Set.Ici 1, k y := by
            rw [MeasureTheory.setIntegral_indicator measurableSet_Ici]
      _ = ∫ y : ℝ in Set.Ici 1, k y := by
            rw [show Set.Ioi (0 : ℝ) ∩ Set.Ici 1 = Set.Ici 1 by
              ext y
              simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
              constructor
              · exact fun h => h.2
              · intro h
                exact ⟨zero_lt_one.trans_le h, h⟩]
      _ = ∫ y : ℝ in Set.Ioi 1, k y := by
            exact MeasureTheory.integral_Ici_eq_integral_Ioi
      _ = (-1 : ℝ) ^ n * tailIntegral n (r + 1) := by
            unfold tailIntegral
            dsimp only [k]
            rw [MeasureTheory.integral_const_mul]
            congr 1
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
            intro y hy
            congr 2
            ring
  unfold unitIntegral
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  change (∫ y : ℝ in Set.Ioc 0 1, h y) =
    (-1 : ℝ) ^ n * tailIntegral n (r + 1)
  rw [← hrhs, ← hlhs]
  exact hsub.symm

private theorem unitIntegral_formula (n : ℕ) {r : ℝ} (hr : -1 < r) :
    unitIntegral n r =
      (-1 : ℝ) ^ n * (Nat.factorial n : ℝ) / (r + 1) ^ (n + 1) := by
  rw [unitIntegral_eq_tail n hr, tailIntegral_formula n (by linarith : 0 < r + 1)]
  ring

private theorem I_eq_unitIntegral (n m : ℕ) :
    I n m = unitIntegral n (m : ℝ) := by
  simp only [I, unitIntegral, Real.rpow_natCast]

private theorem I_formula (n m : ℕ) :
    I n m = closedForm n m := by
  have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rw [I_eq_unitIntegral,
    unitIntegral_formula n (by linarith : (-1 : ℝ) < (m : ℝ))]
  unfold closedForm
  norm_cast

private theorem I_recurrence (n m : ℕ) (hn : 0 < n) :
    I n m = -(n : ℝ) / (m + 1 : ℝ) * I (n - 1) m := by
  rw [I_formula n m, I_formula (n - 1) m]
  unfold closedForm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [Nat.succ_sub_one, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, pow_succ]
  have hm : (m + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hm]
  rw [Nat.cast_succ]

theorem gap1 (n m : ℕ) (hn : 0 < n) :
    I n m =
      (boundaryTerm n m 1 - boundaryTerm n m 0) -
        (n : ℝ) / (m + 1 : ℝ) * I (n - 1) m := by
  rw [I_recurrence n m hn]
  simp [boundaryTerm, Nat.ne_of_gt hn]
  ring

theorem gap2 (n m : ℕ) (hn : 0 < n) :
    I n m = -(n : ℝ) / (m + 1 : ℝ) * I (n - 1) m := by
  exact I_recurrence n m hn

theorem gap3 (n m : ℕ) :
    recurrenceProduct n m =
      (-1 : ℝ) ^ n * (Nat.factorial n : ℝ) /
        (m + 1 : ℝ) ^ n * I 0 m := by
  rfl

theorem gap4 (n m : ℕ) :
    recurrenceProduct n m = closedForm n m := by
  have hzero := I_formula 0 m
  unfold closedForm at hzero
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul] at hzero
  unfold recurrenceProduct closedForm
  rw [hzero]
  have hm : (m + 1 : ℝ) ≠ 0 := by positivity
  rw [pow_succ]
  field_simp [hm]
  ring

theorem gap5 (n m : ℕ) :
    I n m = closedForm n m := by
  exact I_formula n m

end

end ProofGap.Exercise2286
