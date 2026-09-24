import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ProofGap.Exercise2388
noncomputable section

open Filter Set MeasureTheory
open scoped BigOperators Interval

def rightSum (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * ∑ k ∈ Finset.range n, f ((k + 1 : ℕ) / (n : ℝ))

def shifted (f : ℝ → ℝ) (x : ℝ) : ℝ := f x - f 1

def UnboundedAboveNearZero (f : ℝ → ℝ) : Prop :=
  ∀ M : ℝ, ∃ x ∈ Ioc (0 : ℝ) 1, M < f x

private def mesh (n k : ℕ) : ℝ := (k : ℝ) / (n : ℝ)

private theorem mesh_nonneg (n k : ℕ) : 0 ≤ mesh n k := by
  unfold mesh
  positivity

private theorem mesh_mono (n : ℕ) {k l : ℕ} (hkl : k ≤ l) : mesh n k ≤ mesh n l := by
  unfold mesh
  gcongr

private theorem mesh_le_one (n k : ℕ) (hn : 0 < n) (hkn : k ≤ n) : mesh n k ≤ 1 := by
  unfold mesh
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  exact (div_le_one hnR).2 (by exact_mod_cast hkn)

private theorem mesh_pos (n k : ℕ) (hn : 0 < n) (hk : 0 < k) : 0 < mesh n k := by
  unfold mesh
  exact div_pos (by exact_mod_cast hk) (by exact_mod_cast hn)

private theorem mesh_succ_sub (n k : ℕ) (hn : 0 < n) :
    mesh n (k + 1) - mesh n k = 1 / (n : ℝ) := by
  unfold mesh
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hn0]
  norm_num

private theorem mesh_interval_integrable (f : ℝ → ℝ) (n k : ℕ)
    (hn : 0 < n) (hk : k < n) (hInt : IntervalIntegrable f volume 0 1) :
    IntervalIntegrable f volume (mesh n k) (mesh n (k + 1)) := by
  apply hInt.mono_set
  apply Set.uIcc_subset_uIcc
  · rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨mesh_nonneg n k, mesh_le_one n k hn hk.le⟩
  · rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨mesh_nonneg n (k + 1), mesh_le_one n (k + 1) hn (Nat.succ_le_iff.2 hk)⟩

private theorem mesh_interval_upper_bound (f : ℝ → ℝ) (n k : ℕ)
    (hn : 0 < n) (hk1 : 1 ≤ k) (hkn : k < n)
    (hf : AntitoneOn f (Ioc (0 : ℝ) 1))
    (hInt : IntervalIntegrable f volume 0 1) :
    (∫ x in mesh n k..mesh n (k + 1), f x) ≤
      (1 / (n : ℝ)) * f (mesh n k) := by
  have hseg := mesh_interval_integrable f n k hn hkn hInt
  have hconst : IntervalIntegrable (fun _ : ℝ => f (mesh n k)) volume
      (mesh n k) (mesh n (k + 1)) := intervalIntegrable_const
  have hmono : (∫ x in mesh n k..mesh n (k + 1), f x) ≤
      ∫ _x in mesh n k..mesh n (k + 1), f (mesh n k) := by
    apply intervalIntegral.integral_mono_on (mesh_mono n (by omega : k ≤ k + 1)) hseg hconst
    intro x hx
    have hkmem : mesh n k ∈ Ioc (0 : ℝ) 1 :=
      ⟨mesh_pos n k hn (by omega), mesh_le_one n k hn hkn.le⟩
    have hxmem : x ∈ Ioc (0 : ℝ) 1 := by
      constructor
      · exact hkmem.1.trans_le hx.1
      · exact hx.2.trans (mesh_le_one n (k + 1) hn (Nat.succ_le_iff.2 hkn))
    exact hf hkmem hxmem hx.1
  calc
    (∫ x in mesh n k..mesh n (k + 1), f x) ≤
        ∫ _x in mesh n k..mesh n (k + 1), f (mesh n k) := hmono
    _ = (1 / (n : ℝ)) * f (mesh n k) := by
      rw [intervalIntegral.integral_const, mesh_succ_sub n k hn]
      simp [smul_eq_mul]

private theorem mesh_interval_lower_bound (f : ℝ → ℝ) (n k : ℕ)
    (hn : 0 < n) (hkn : k < n)
    (hf : AntitoneOn f (Ioc (0 : ℝ) 1))
    (hInt : IntervalIntegrable f volume 0 1) :
    (1 / (n : ℝ)) * f (mesh n (k + 1)) ≤
      ∫ x in mesh n k..mesh n (k + 1), f x := by
  have hseg := mesh_interval_integrable f n k hn hkn hInt
  have hconst : IntervalIntegrable (fun _ : ℝ => f (mesh n (k + 1))) volume
      (mesh n k) (mesh n (k + 1)) := intervalIntegrable_const
  have hmono : (∫ _x in mesh n k..mesh n (k + 1), f (mesh n (k + 1))) ≤
      ∫ x in mesh n k..mesh n (k + 1), f x := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (mesh_mono n (by omega : k ≤ k + 1)) hconst hseg
    intro x hx
    have hrmem : mesh n (k + 1) ∈ Ioc (0 : ℝ) 1 :=
      ⟨mesh_pos n (k + 1) hn (Nat.succ_pos k),
        mesh_le_one n (k + 1) hn (Nat.succ_le_iff.2 hkn)⟩
    have hxmem : x ∈ Ioc (0 : ℝ) 1 := by
      constructor
      · exact (mesh_nonneg n k).trans_lt hx.1
      · exact hx.2.le.trans hrmem.2
    exact hf hxmem hrmem hx.2.le
  calc
    (1 / (n : ℝ)) * f (mesh n (k + 1)) =
        ∫ _x in mesh n k..mesh n (k + 1), f (mesh n (k + 1)) := by
      rw [intervalIntegral.integral_const, mesh_succ_sub n k hn]
      simp [smul_eq_mul]
    _ ≤ ∫ x in mesh n k..mesh n (k + 1), f x := hmono

private theorem sum_range_split_zero {g : ℕ → ℝ} {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ Finset.range n, g k = g 0 + ∑ k ∈ Finset.Ico 1 n, g k := by
  rw [Finset.range_eq_Ico]
  exact Finset.sum_eq_sum_Ico_succ_bot hn g

private theorem sum_Icc_mesh_eq_rightSum_sum (f : ℝ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, f (mesh n k) =
      ∑ k ∈ Finset.range n, f ((k + 1 : ℕ) / (n : ℝ)) := by
  have hset : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext k
    simp [Nat.lt_succ_iff]
  rw [hset, Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  unfold mesh
  norm_num [Nat.add_comm]

private theorem shifted_interval_integrable (f : ℝ → ℝ)
    (hInt : IntervalIntegrable f volume 0 1) :
    IntervalIntegrable (shifted f) volume 0 1 := by
  unfold shifted
  exact hInt.sub intervalIntegrable_const

private theorem rightSum_shifted_eq (f : ℝ → ℝ) (n : ℕ) (hn : 0 < n) :
    rightSum (shifted f) n = rightSum f n - f 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold rightSum shifted
  rw [Finset.sum_sub_distrib]
  simp [Finset.card_range, hn0]
  field_simp [hn0]

theorem gap1 (f : ℝ → ℝ) (hf : AntitoneOn f (Ioc (0 : ℝ) 1))
    (hunb : UnboundedAboveNearZero f) :
    Tendsto f (nhdsWithin 0 (Ioi 0)) atTop := by
  apply tendsto_atTop.2
  intro M
  obtain ⟨y, hy, hMy⟩ := hunb M
  filter_upwards [Ioc_mem_nhdsGT hy.1] with x hx
  exact hMy.le.trans (hf ⟨hx.1, hx.2.trans hy.2⟩ hy hx.2)

theorem gap2 (f : ℝ → ℝ) (n : ℕ) (hn : 0 < n)
    (hInt : IntervalIntegrable f volume 0 1) :
    (∫ x in (0 : ℝ)..1, f x) =
      ∑ k ∈ Finset.range n,
        ∫ x in ((k : ℝ) / n)..(((k : ℝ) + 1) / n), f x := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := f) (μ := volume) (a := mesh n) (n := n)
    (fun k hk => mesh_interval_integrable f n k hn hk hInt)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simpa [mesh, Nat.cast_add, Nat.cast_one, hn0] using hsum.symm

theorem gap3 (f : ℝ → ℝ) (n : ℕ) (hn : 0 < n)
    (hf : AntitoneOn f (Ioc (0 : ℝ) 1))
    (hInt : IntervalIntegrable f volume 0 1) :
    (∫ x in (0 : ℝ)..1, f x) ≤
      (∫ x in (0 : ℝ)..(1 / (n : ℝ)), f x) +
        (1 / (n : ℝ)) *
          ∑ k ∈ Finset.Ico 1 n, f ((k : ℝ) / n) := by
  let I : ℕ → ℝ := fun k => ∫ x in mesh n k..mesh n (k + 1), f x
  have hsplit : ∑ k ∈ Finset.range n, I k =
      I 0 + ∑ k ∈ Finset.Ico 1 n, I k := sum_range_split_zero hn
  have hsum : (∑ k ∈ Finset.Ico 1 n, I k) ≤
      ∑ k ∈ Finset.Ico 1 n, (1 / (n : ℝ)) * f (mesh n k) := by
    apply Finset.sum_le_sum
    intro k hk
    have hk' := Finset.mem_Ico.mp hk
    exact mesh_interval_upper_bound f n k hn (by omega) hk'.2 hf hInt
  calc
    (∫ x in (0 : ℝ)..1, f x) = ∑ k ∈ Finset.range n, I k := by
      simpa [I, mesh, Nat.cast_add, Nat.cast_one] using gap2 f n hn hInt
    _ = I 0 + ∑ k ∈ Finset.Ico 1 n, I k := hsplit
    _ ≤ I 0 + ∑ k ∈ Finset.Ico 1 n, (1 / (n : ℝ)) * f (mesh n k) :=
      add_le_add_right hsum _
    _ = (∫ x in (0 : ℝ)..(1 / (n : ℝ)), f x) +
        (1 / (n : ℝ)) * ∑ k ∈ Finset.Ico 1 n, f ((k : ℝ) / n) := by
      unfold I mesh
      rw [Finset.mul_sum]
      norm_num

theorem gap4 (f : ℝ → ℝ) (n : ℕ) (hn : 0 < n)
    (hf0 : ∀ x ∈ Ioc (0 : ℝ) 1, 0 ≤ f x) :
    (∫ x in (0 : ℝ)..(1 / (n : ℝ)), f x) +
        (1 / (n : ℝ)) * ∑ k ∈ Finset.Ico 1 n, f ((k : ℝ) / n) ≤
      (∫ x in (0 : ℝ)..(1 / (n : ℝ)), f x) +
        (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 n, f ((k : ℝ) / n) := by
  have hn1 : 1 ≤ n := hn
  have hset : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext k
    simp [Nat.lt_succ_iff]
  have hfn : 0 ≤ f ((n : ℝ) / n) := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simpa [hn0] using hf0 1 ⟨zero_lt_one, le_rfl⟩
  have hsum : (∑ k ∈ Finset.Ico 1 n, f ((k : ℝ) / n)) ≤
      ∑ k ∈ Finset.Icc 1 n, f ((k : ℝ) / n) := by
    rw [hset, Finset.sum_Ico_succ_top hn1]
    exact le_add_of_nonneg_right hfn
  have hcoef : 0 ≤ 1 / (n : ℝ) := by positivity
  exact add_le_add_right (mul_le_mul_of_nonneg_left hsum hcoef) _

theorem gap5 (f : ℝ → ℝ) (n : ℕ) (hn : 0 < n)
    (hf : AntitoneOn f (Ioc (0 : ℝ) 1))
    (hf0 : ∀ x ∈ Ioc (0 : ℝ) 1, 0 ≤ f x)
    (hInt : IntervalIntegrable f volume 0 1) :
    (∫ x in (0 : ℝ)..1, f x) ≤
      (∫ x in (0 : ℝ)..(1 / (n : ℝ)), f x) +
        (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 n, f ((k : ℝ) / n) := by
  exact (gap3 f n hn hf hInt).trans (gap4 f n hn hf0)

theorem gap6 (f : ℝ → ℝ) (n : ℕ) (hn : 0 < n)
    (hf : AntitoneOn f (Ioc (0 : ℝ) 1))
    (hInt : IntervalIntegrable f volume 0 1) :
    rightSum f n ≤ ∫ x in (0 : ℝ)..1, f x := by
  have hsum : (∑ k ∈ Finset.range n, (1 / (n : ℝ)) * f (mesh n (k + 1))) ≤
      ∑ k ∈ Finset.range n, ∫ x in mesh n k..mesh n (k + 1), f x := by
    apply Finset.sum_le_sum
    intro k hk
    exact mesh_interval_lower_bound f n k hn (by simpa using hk) hf hInt
  calc
    rightSum f n = ∑ k ∈ Finset.range n, (1 / (n : ℝ)) * f (mesh n (k + 1)) := by
      unfold rightSum mesh
      rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range n, ∫ x in mesh n k..mesh n (k + 1), f x := hsum
    _ = ∫ x in (0 : ℝ)..1, f x := by
      symm
      simpa [mesh, Nat.cast_add, Nat.cast_one] using gap2 f n hn hInt

theorem gap7 (f : ℝ → ℝ) (n : ℕ) (hn : 0 < n)
    (hf : AntitoneOn f (Ioc (0 : ℝ) 1))
    (hInt : IntervalIntegrable f volume 0 1) :
    0 ≤ (∫ x in (0 : ℝ)..1, f x) - rightSum f n := by
  linarith [gap6 f n hn hf hInt]

theorem gap8 (f : ℝ → ℝ) (n : ℕ) (hn : 0 < n)
    (hf : AntitoneOn f (Ioc (0 : ℝ) 1))
    (hf0 : ∀ x ∈ Ioc (0 : ℝ) 1, 0 ≤ f x)
    (hInt : IntervalIntegrable f volume 0 1) :
    (∫ x in (0 : ℝ)..1, f x) - rightSum f n ≤
      ∫ x in (0 : ℝ)..(1 / (n : ℝ)), f x := by
  have hsum := sum_Icc_mesh_eq_rightSum_sum f n
  have hrs : (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 n, f ((k : ℝ) / n) =
      rightSum f n := by
    unfold rightSum
    simpa [mesh] using congrArg (fun z : ℝ => (1 / (n : ℝ)) * z) hsum
  linarith [gap5 f n hn hf hf0 hInt]

theorem gap9 (f : ℝ → ℝ) (n : ℕ) (hn : 0 < n)
    (hf0 : ∀ x ∈ Ioc (0 : ℝ) 1, 0 ≤ f x) :
    0 ≤ ∫ x in (0 : ℝ)..(1 / (n : ℝ)), f x := by
  by_cases hint : IntervalIntegrable f volume 0 (1 / (n : ℝ))
  · have hzero : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 (1 / (n : ℝ)) :=
      intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on_of_le_Ioo
      (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ)) hzero hint (by
        intro x hx
        exact hf0 x ⟨hx.1, hx.2.le.trans (by
          have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
          simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hnR)⟩)
    simpa using hmono
  · rw [intervalIntegral.integral_undef hint]

theorem gap10 (f : ℝ → ℝ) (hInt : IntervalIntegrable f volume 0 1) :
    Tendsto (fun n : ℕ => ∫ x in (0 : ℝ)..(1 / (n + 1 : ℕ)), f x)
      atTop (nhds 0) := by
  have hu : IntegrableOn f (Set.uIcc (0 : ℝ) 1) := (intervalIntegrable_iff').1 hInt
  have hc := (intervalIntegral.continuousOn_primitive_interval hu) 0
    (by rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact ⟨le_rfl, zero_le_one⟩)
  have hfilter : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhdsWithin 0 (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact le_inf inf_le_left (Filter.le_principal_iff.mpr (Icc_mem_nhdsGT zero_lt_one))
  have hprim : Tendsto (fun b => ∫ x in (0 : ℝ)..b, f x)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using hc.tendsto.mono_left hfilter
  have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hpos : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / ((n : ℝ) + 1) ∈ Ioi 0 :=
    Filter.Eventually.of_forall (fun n => show 0 < (1 : ℝ) / ((n : ℝ) + 1) by positivity)
  have hwithin : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      atTop (nhdsWithin 0 (Ioi 0)) := tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  have h := hprim.comp hwithin
  simpa only [Nat.cast_add, Nat.cast_one] using h

private theorem rightSum_neg_eq (f : ℝ → ℝ) (n : ℕ) :
    rightSum (fun x => -f x) n = -rightSum f n := by
  unfold rightSum
  rw [Finset.sum_neg_distrib]
  ring

private theorem integral_shifted_eq (f : ℝ → ℝ)
    (hInt : IntervalIntegrable f volume 0 1) :
    (∫ x in (0 : ℝ)..1, shifted f x) = (∫ x in (0 : ℝ)..1, f x) - f 1 := by
  unfold shifted
  rw [intervalIntegral.integral_sub hInt intervalIntegrable_const]
  simp

theorem gap11 (f : ℝ → ℝ) (hf : AntitoneOn f (Ioc (0 : ℝ) 1))
    (hInt : IntervalIntegrable f volume 0 1) :
    Tendsto (rightSum f) atTop (nhds (∫ x in (0 : ℝ)..1, f x)) := by
  have hganti : AntitoneOn (shifted f) (Ioc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    unfold shifted
    linarith [hf hx hy hxy]
  have hg0 : ∀ x ∈ Ioc (0 : ℝ) 1, 0 ≤ shifted f x := by
    intro x hx
    unfold shifted
    exact sub_nonneg.mpr (hf hx ⟨zero_lt_one, le_rfl⟩ hx.2)
  have hgInt := shifted_interval_integrable f hInt
  let J : ℝ := ∫ x in (0 : ℝ)..1, shifted f x
  have hlow : ∀ n : ℕ, 0 ≤ J - rightSum (shifted f) (n + 1) := by
    intro n
    exact gap7 (shifted f) (n + 1) (Nat.succ_pos n) hganti hgInt
  have hupp : ∀ n : ℕ, J - rightSum (shifted f) (n + 1) ≤
      ∫ x in (0 : ℝ)..(1 / (n + 1 : ℕ)), shifted f x := by
    intro n
    exact gap8 (shifted f) (n + 1) (Nat.succ_pos n) hganti hg0 hgInt
  have hdiff : Tendsto (fun n : ℕ => J - rightSum (shifted f) (n + 1))
      atTop (nhds 0) := squeeze_zero hlow hupp (gap10 (shifted f) hgInt)
  have htail : Tendsto (fun n : ℕ => rightSum (shifted f) (n + 1))
      atTop (nhds J) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => J) atTop (nhds J)).sub hdiff
    convert h using 1 <;> ring
  have hg : Tendsto (rightSum (shifted f)) atTop (nhds J) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mp htail
  have heq : rightSum (shifted f) =ᶠ[atTop] (fun n => rightSum f n - f 1) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact rightSum_shifted_eq f n hn
  have hsub : Tendsto (fun n => rightSum f n - f 1) atTop
      (nhds ((∫ x in (0 : ℝ)..1, f x) - f 1)) := by
    rw [← integral_shifted_eq f hInt]
    exact hg.congr' heq
  have hadd := hsub.add (tendsto_const_nhds : Tendsto (fun _ : ℕ => f 1) atTop (nhds (f 1)))
  simpa using hadd

theorem gap12 (f : ℝ → ℝ) (hf : AntitoneOn f (Ioc (0 : ℝ) 1)) :
    ∀ x ∈ Ioc (0 : ℝ) 1, 0 ≤ shifted f x := by
  intro x hx
  unfold shifted
  exact sub_nonneg.mpr (hf hx ⟨zero_lt_one, le_rfl⟩ hx.2)

theorem gap13 (f : ℝ → ℝ) (hf : AntitoneOn f (Ioc (0 : ℝ) 1)) :
    AntitoneOn (shifted f) (Ioc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  unfold shifted
  linarith [hf hx hy hxy]

theorem gap14 (f : ℝ → ℝ) (hf : AntitoneOn f (Ioc (0 : ℝ) 1))
    (hunb : UnboundedAboveNearZero f) :
    Tendsto (shifted f) (nhdsWithin 0 (Ioi 0)) atTop := by
  have h := (nhdsWithin (0 : ℝ) (Ioi 0)).tendsto_atTop_add_const_right
    (-f 1) (gap1 f hf hunb)
  simpa [shifted, sub_eq_add_neg] using h

theorem gap15 (f : ℝ → ℝ) (hf : AntitoneOn f (Ioc (0 : ℝ) 1))
    (hInt : IntervalIntegrable (shifted f) volume 0 1) :
    Tendsto (rightSum (shifted f)) atTop
      (nhds (∫ x in (0 : ℝ)..1, shifted f x)) := by
  exact gap11 (shifted f) (gap13 f hf) hInt

theorem gap16 (f : ℝ → ℝ) :
    ∀ n : ℕ, 0 < n → rightSum (shifted f) n = rightSum f n - f 1 := by
  intro n hn
  exact rightSum_shifted_eq f n hn

theorem gap17 (f : ℝ → ℝ) (hf : AntitoneOn f (Ioc (0 : ℝ) 1))
    (hInt : IntervalIntegrable f volume 0 1) :
    Tendsto (rightSum f) atTop (nhds (∫ x in (0 : ℝ)..1, f x)) := by
  exact gap11 f hf hInt

theorem gap18 (f g : ℝ → ℝ) (hf : MonotoneOn f (Ioc (0 : ℝ) 1))
    (hg : ∀ x, g x = -f x) (hInt : IntervalIntegrable g volume 0 1) :
    Tendsto (rightSum g) atTop (nhds (∫ x in (0 : ℝ)..1, g x)) := by
  apply gap17 g _ hInt
  intro x hx y hy hxy
  rw [hg x, hg y]
  exact neg_le_neg (hf hx hy hxy)

theorem gap19 (f : ℝ → ℝ) (hf : MonotoneOn f (Ioc (0 : ℝ) 1))
    (hInt : IntervalIntegrable f volume 0 1) :
    Tendsto (rightSum f) atTop (nhds (∫ x in (0 : ℝ)..1, f x)) := by
  have hneg := gap18 f (fun x => -f x) hf (fun _ => rfl) hInt.neg
  have hneg' : Tendsto (fun n => -rightSum (fun x => -f x) n) atTop
      (nhds (∫ x in (0 : ℝ)..1, f x)) := by
    simpa using hneg.neg
  apply hneg'.congr'
  exact Filter.Eventually.of_forall (fun n => by
    change -rightSum (fun x => -f x) n = rightSum f n
    rw [rightSum_neg_eq]
    simp)

theorem gap20 (f : ℝ → ℝ)
    (hf : AntitoneOn f (Ioc (0 : ℝ) 1) ∨ MonotoneOn f (Ioc (0 : ℝ) 1))
    (hInt : IntervalIntegrable f volume 0 1) :
    Tendsto (rightSum f) atTop (nhds (∫ x in (0 : ℝ)..1, f x)) := by
  rcases hf with hf | hf
  · exact gap17 f hf hInt
  · exact gap19 f hf hInt

end
end ProofGap.Exercise2388
