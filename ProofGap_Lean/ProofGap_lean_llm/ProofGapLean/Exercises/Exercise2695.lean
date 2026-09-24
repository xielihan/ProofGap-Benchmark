import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2695

noncomputable section

open Filter

def groupedTerm (p : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow (4 * n - 3) p +
    1 / Real.rpow (4 * n - 1) p -
    1 / Real.rpow (2 * n - 1) p

def leadingTerm (p : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow (2 * n) p * (1 / Real.rpow 2 (p - 1) - 1)

def correctionTerm (p : ℝ) (n : ℕ) : ℝ :=
  (1 / Real.rpow 2 p) * (p / Real.rpow 2 p - p / 2) /
    Real.rpow n (p + 1)

def expansionRemainder (p : ℝ) (n : ℕ) : ℝ :=
  groupedTerm p n - leadingTerm p n - correctionTerm p n

def ConditionallySummable (f : ℕ → ℝ) : Prop :=
  ProofGap.SeriesConverges f ∧
    ¬ ProofGap.SeriesConverges (fun n => |f n|)

private def rpowTaylorRemainder (p x : ℝ) : ℝ :=
  1 / Real.rpow (1 - x) p - (1 + p * x)

private theorem rpowTaylorRemainder_isBigO (p : ℝ) :
    Asymptotics.IsBigO (nhds 0) (rpowTaylorRemainder p)
      (fun x : ℝ => x ^ 2) := by
  have h :=
    (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero p).hasFPowerSeriesAt
      |>.isBigO_sub_partialSum_pow 2
  convert h using 1
  · funext x
    norm_num [rpowTaylorRemainder, FormalMultilinearSeries.partialSum,
      Finset.sum_range_succ]
    ring
  · funext x
    simp only [Real.norm_eq_abs, sq_abs]

private theorem sq_div_isBigO (k c : ℝ) (hk : 0 < k) :
    Asymptotics.IsBigO atTop (fun t : ℝ => (c / (k * t)) ^ 2)
      (fun t : ℝ => 1 / Real.rpow t 2) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨(|c| / k) ^ 2, ?_⟩
  filter_upwards [eventually_atTop.2 ⟨1, fun b hb => hb⟩] with t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  rw [show Real.rpow t 2 = t ^ (2 : ℕ) from Real.rpow_two t]
  simp only [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hk, abs_of_pos ht0,
    abs_pow, abs_of_nonneg (sq_nonneg t)]
  field_simp
  norm_num

private theorem inv_mul_rpow_isBigO (p k : ℝ) (hk : 0 < k) :
    Asymptotics.IsBigO atTop (fun t : ℝ => 1 / Real.rpow (k * t) p)
      (fun t : ℝ => 1 / Real.rpow t p) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1 / Real.rpow k p, ?_⟩
  filter_upwards [eventually_atTop.2 ⟨1, fun b hb => hb⟩] with t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hkp : 0 < Real.rpow k p := Real.rpow_pos_of_pos hk p
  have htp : 0 < Real.rpow t p := Real.rpow_pos_of_pos ht0 p
  rw [show Real.rpow (k * t) p = Real.rpow k p * Real.rpow t p from
    Real.mul_rpow hk.le ht0.le]
  simp only [Real.norm_eq_abs, abs_div, abs_one, abs_of_pos hkp, abs_of_pos htp,
    abs_mul]
  field_simp
  norm_num

private def shiftedRpowRemainder (p k c t : ℝ) : ℝ :=
  1 / Real.rpow (k * t - c) p -
    1 / Real.rpow (k * t) p * (1 + p * (c / (k * t)))

private theorem shiftedRpowRemainder_isBigO (p k c : ℝ) (hk : 0 < k) :
    Asymptotics.IsBigO atTop (shiftedRpowRemainder p k c)
      (fun t : ℝ => 1 / Real.rpow t (p + 2)) := by
  have hkt : Tendsto (fun t : ℝ => k * t) atTop atTop := by
    simpa only [id_eq] using
      (Filter.Tendsto.const_mul_atTop hk
        (Filter.tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop))
  have hsmall : Tendsto (fun t : ℝ => c / (k * t)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hkt
  have hrem :
      Asymptotics.IsBigO atTop
        (fun t : ℝ => rpowTaylorRemainder p (c / (k * t)))
        (fun t : ℝ => 1 / Real.rpow t 2) := by
    have hcomp := (rpowTaylorRemainder_isBigO p).comp_tendsto hsmall
    have hcomp' :
        Asymptotics.IsBigO atTop
          (fun t : ℝ => rpowTaylorRemainder p (c / (k * t)))
          (fun t : ℝ => (c / (k * t)) ^ 2) := by
      simpa only [Function.comp_apply] using hcomp
    exact hcomp'.trans (sq_div_isBigO k c hk)
  have hprod := (inv_mul_rpow_isBigO p k hk).mul hrem
  have hleft :
      shiftedRpowRemainder p k c =ᶠ[atTop]
        (fun t : ℝ =>
          1 / Real.rpow (k * t) p *
            rpowTaylorRemainder p (c / (k * t))) := by
    filter_upwards [eventually_atTop.2
      ⟨max 1 ((c + 1) / k), fun b hb => hb⟩] with t ht
    have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    have hct : c < k * t := by
      have hle : (c + 1) / k ≤ t := le_trans (le_max_right _ _) ht
      have := (div_le_iff₀ hk).mp hle
      linarith
    have hkt0 : 0 < k * t := mul_pos hk ht0
    have hfac0 : 0 < 1 - c / (k * t) := by
      exact sub_pos.mpr ((div_lt_one hkt0).mpr hct)
    have hbase : k * t - c = (k * t) * (1 - c / (k * t)) := by
      field_simp [ne_of_gt hkt0]
    simp only [shiftedRpowRemainder, rpowTaylorRemainder]
    rw [hbase, show
      Real.rpow ((k * t) * (1 - c / (k * t))) p =
        Real.rpow (k * t) p * Real.rpow (1 - c / (k * t)) p from
      Real.mul_rpow hkt0.le hfac0.le]
    ring
  have hright :
      (fun t : ℝ =>
        (1 / Real.rpow t p) * (1 / Real.rpow t 2)) =ᶠ[atTop]
      (fun t : ℝ => 1 / Real.rpow t (p + 2)) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun b hb => hb⟩] with t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    rw [show Real.rpow t (p + 2) = Real.rpow t p * Real.rpow t 2 from
      Real.rpow_add ht0 p 2]
    ring
  exact hprod.congr' hleft.symm hright

private theorem expansionRemainder_eq_shifted (p : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    expansionRemainder p n =
      shiftedRpowRemainder p 4 3 n +
        shiftedRpowRemainder p 4 1 n -
          shiftedRpowRemainder p 2 1 n := by
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  simp only [expansionRemainder, groupedTerm, leadingTerm, correctionTerm,
    shiftedRpowRemainder]
  have h2n : Real.rpow (2 * (n : ℝ)) p =
      Real.rpow 2 p * Real.rpow n p :=
    Real.mul_rpow (by norm_num) hnr.le
  have h4n : Real.rpow (4 * (n : ℝ)) p =
      (Real.rpow 2 p * Real.rpow 2 p) * Real.rpow n p := by
    calc
      Real.rpow (4 * (n : ℝ)) p =
          Real.rpow ((2 : ℝ) * 2 * (n : ℝ)) p := by norm_num
      _ = Real.rpow ((2 : ℝ) * 2) p * Real.rpow n p :=
        Real.mul_rpow (by positivity) hnr.le
      _ = (Real.rpow 2 p * Real.rpow 2 p) * Real.rpow n p := by
        rw [show Real.rpow ((2 : ℝ) * 2) p =
          Real.rpow 2 p * Real.rpow 2 p from
          Real.mul_rpow (by norm_num) (by norm_num)]
  have h2sub : Real.rpow 2 (p - 1) = Real.rpow 2 p / 2 := by
    rw [show Real.rpow 2 (p - 1) = Real.rpow 2 p / Real.rpow 2 1 from
      Real.rpow_sub (by norm_num) p 1]
    norm_num
  have hnadd : Real.rpow (n : ℝ) (p + 1) =
      Real.rpow n p * n := by
    rw [show Real.rpow (n : ℝ) (p + 1) =
      Real.rpow n p * Real.rpow n 1 from Real.rpow_add hnr p 1]
    norm_num
  rw [h2n, h4n, h2sub, hnadd]
  have hA : 0 < Real.rpow 2 p := Real.rpow_pos_of_pos (by norm_num) p
  have hN : 0 < Real.rpow (n : ℝ) p := Real.rpow_pos_of_pos hnr p
  field_simp [ne_of_gt hnr, ne_of_gt hA, ne_of_gt hN]
  ring

private theorem summable_inv_nat_affine_rpow (p a b : ℝ)
    (hp : 1 < p) (ha : 0 < a) (hb : 0 < b) :
    Summable (fun n : ℕ => 1 / Real.rpow (a * n + b) p) := by
  have hs : Summable (fun n : ℕ => 1 / |(n : ℝ) + b / a| ^ p) :=
    (Real.summable_one_div_nat_add_rpow (b / a) p).2 hp
  have hscaled := hs.mul_left (1 / Real.rpow a p)
  convert hscaled using 1
  funext n
  have hshift : 0 < (n : ℝ) + b / a := by positivity
  have hbase : a * n + b = a * ((n : ℝ) + b / a) := by
    field_simp [ne_of_gt ha]
  rw [abs_of_pos hshift, hbase, show
    Real.rpow (a * ((n : ℝ) + b / a)) p =
      Real.rpow a p * Real.rpow ((n : ℝ) + b / a) p from
    Real.mul_rpow ha.le hshift.le]
  change 1 / (Real.rpow a p * Real.rpow ((n : ℝ) + b / a) p) =
    1 / Real.rpow a p * (1 / Real.rpow ((n : ℝ) + b / a) p)
  ring

theorem gap1 (p : ℝ) :
    ∀ S₀ : ℕ → ℝ,
      (∀ n : ℕ, S₀ n = groupedTerm p (n + 1)) →
      (Summable S₀ ↔ Summable (fun n : ℕ => groupedTerm p (n + 1))) := by
  intro S₀ hS
  have hfun : S₀ = fun n : ℕ => groupedTerm p (n + 1) := funext hS
  subst S₀
  rfl

theorem gap2 (p : ℝ) :
    (∀ n : ℕ, 1 ≤ n →
      groupedTerm p n =
        leadingTerm p n + correctionTerm p n + expansionRemainder p n) ∧
    Asymptotics.IsBigO atTop (expansionRemainder p)
      (fun n : ℕ => 1 / Real.rpow n (p + 2)) := by
  constructor
  · intro n hn
    simp only [expansionRemainder]
    ring
  · have hA :=
      (shiftedRpowRemainder_isBigO p 4 3 (by norm_num)).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))
    have hB :=
      (shiftedRpowRemainder_isBigO p 4 1 (by norm_num)).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))
    have hC :=
      (shiftedRpowRemainder_isBigO p 2 1 (by norm_num)).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))
    have hsum := hA.add hB |>.sub hC
    apply hsum.congr'
    · filter_upwards [eventually_atTop.2 ⟨1, fun b hb => hb⟩] with n hn
      simpa only [Function.comp_apply] using
        (expansionRemainder_eq_shifted p n hn).symm
    · exact Eventually.of_forall fun n => by
        simp only [Function.comp_apply]

theorem gap3 (p : ℝ) (hp : 1 < p) :
    Summable (fun n : ℕ => |groupedTerm p (n + 1)|) := by
  have h1 := summable_inv_nat_affine_rpow p 4 1 hp (by norm_num) (by norm_num)
  have h2 := summable_inv_nat_affine_rpow p 4 3 hp (by norm_num) (by norm_num)
  have h3 := summable_inv_nat_affine_rpow p 2 1 hp (by norm_num) (by norm_num)
  have hg : Summable (fun n : ℕ => groupedTerm p (n + 1)) := by
    convert h1.add h2 |>.sub h3 using 1
    funext n
    simp only [groupedTerm]
    congr 3 <;> norm_num <;> ring
  exact hg.abs

theorem gap4 (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1) :
    ¬ Summable (fun n : ℕ => leadingTerm p (n + 1)) := by
  let C : ℝ :=
    1 / Real.rpow 2 p * (1 / Real.rpow 2 (p - 1) - 1)
  have hpowlt : Real.rpow 2 (p - 1) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hC : C ≠ 0 := by
    have hp2 : 0 < Real.rpow 2 p := Real.rpow_pos_of_pos (by norm_num) p
    have hp2sub : 0 < Real.rpow 2 (p - 1) :=
      Real.rpow_pos_of_pos (by norm_num) (p - 1)
    have hdiff : 0 < 1 / Real.rpow 2 (p - 1) - 1 :=
      sub_pos.mpr ((one_lt_div hp2sub).mpr hpowlt)
    dsimp [C]
    exact mul_ne_zero (div_ne_zero one_ne_zero hp2.ne') hdiff.ne'
  have hlead :
      (fun n : ℕ => leadingTerm p (n + 1)) =
        (fun n : ℕ => C * (1 / Real.rpow (n + 1) p)) := by
    funext n
    have hn : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
    simp only [leadingTerm, C]
    rw [show Real.rpow (2 * (((n + 1 : ℕ) : ℝ))) p =
      Real.rpow 2 p * Real.rpow (((n + 1 : ℕ) : ℝ)) p from
      Real.mul_rpow (by norm_num) hn]
    push_cast
    ring
  intro hs
  rw [hlead, summable_mul_left_iff hC] at hs
  have hsShift : Summable (fun n : ℕ => 1 / Real.rpow ((n + 1 : ℕ) : ℝ) p) := by
    convert hs using 1
    funext n
    norm_num
  have hsfull : Summable (fun n : ℕ => 1 / Real.rpow n p) :=
    (summable_nat_add_iff 1).mp hsShift
  have := Real.summable_one_div_nat_rpow.mp hsfull
  linarith

theorem gap5 (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1) :
    Summable (fun n : ℕ => correctionTerm p (n + 1)) := by
  have hbase : Summable (fun n : ℕ => 1 / Real.rpow n (p + 1)) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  have hshift : Summable (fun n : ℕ => 1 / Real.rpow (n + 1) (p + 1)) :=
    by
      have h := (summable_nat_add_iff 1).mpr hbase
      convert h using 1
      funext n
      norm_num
  have hscaled := hshift.mul_left
    ((1 / Real.rpow 2 p) * (p / Real.rpow 2 p - p / 2))
  convert hscaled using 1
  funext n
  simp only [correctionTerm]
  push_cast
  ring

theorem gap6 (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1) :
    Summable (fun n : ℕ => expansionRemainder p (n + 1)) := by
  have hbase : Summable (fun n : ℕ => 1 / Real.rpow n (p + 2)) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  have hrem : Summable (expansionRemainder p) :=
    summable_of_isBigO_nat hbase (gap2 p).2
  exact (summable_nat_add_iff 1).mpr hrem

theorem gap7 (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1) :
    ¬ Summable (fun n : ℕ => groupedTerm p (n + 1)) := by
  intro hg
  apply gap4 p hp₀ hp₁
  have hlead := hg.sub (gap5 p hp₀ hp₁) |>.sub (gap6 p hp₀ hp₁)
  convert hlead using 1
  funext n
  rw [(gap2 p).1 (n + 1) (by omega)]
  ring

theorem gap8 (p : ℝ) (hp : p = 1) :
    Summable (fun n : ℕ => groupedTerm p (n + 1)) := by
  subst p
  have hbase : Summable (fun n : ℕ => 1 / Real.rpow n (1 + 2)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have hrem : Summable (expansionRemainder 1) :=
    summable_of_isBigO_nat hbase (gap2 1).2
  have hshift : Summable (fun n : ℕ => expansionRemainder 1 (n + 1)) :=
    (summable_nat_add_iff 1).mpr hrem
  convert hshift using 1
  funext n
  have h := (gap2 1).1 (n + 1) (by omega)
  simpa [leadingTerm, correctionTerm] using h

theorem gap9 :
    ¬ Summable (fun n : ℕ =>
      1 / ((4 * (n + 1) - 3 : ℕ) : ℝ) +
      1 / ((4 * (n + 1) - 1 : ℕ) : ℝ) +
      1 / ((2 * (n + 1) - 1 : ℕ) : ℝ)) := by
  intro hs
  have hfirst : Summable (fun n : ℕ =>
      1 / ((4 * (n + 1) - 3 : ℕ) : ℝ)) :=
    hs.of_nonneg_of_le
      (fun n => by positivity)
      (fun n => by
        have h2 : 0 ≤ 1 / ((4 * (n + 1) - 1 : ℕ) : ℝ) := by positivity
        have h3 : 0 ≤ 1 / ((2 * (n + 1) - 1 : ℕ) : ℝ) := by positivity
        linarith)
  have hq : Summable (fun n : ℕ => 1 / (4 * (n : ℝ) + 1)) := by
    convert hfirst using 1
    funext n
    congr 2
    norm_cast
  have hscale :
      (fun n : ℕ => 1 / (4 * (n : ℝ) + 1)) =
        (fun n : ℕ => (1 / 4 : ℝ) *
          (1 / |(n : ℝ) + 1 / 4| ^ (1 : ℝ))) := by
    funext n
    have hn : 0 < (n : ℝ) + 1 / 4 := by positivity
    rw [abs_of_pos hn]
    change 1 / (4 * (n : ℝ) + 1) =
      (1 / 4 : ℝ) * (1 / Real.rpow ((n : ℝ) + 1 / 4) 1)
    rw [show Real.rpow ((n : ℝ) + 1 / 4) 1 = (n : ℝ) + 1 / 4 from
      Real.rpow_one _]
    field_simp
  rw [hscale, summable_mul_left_iff (by norm_num : (1 / 4 : ℝ) ≠ 0)] at hq
  have hbad := (Real.summable_one_div_nat_add_rpow (1 / 4) 1).mp hq
  norm_num at hbad

theorem gap10 (p : ℝ) (hp : p = 1) :
    Summable (fun n : ℕ => |groupedTerm p (n + 1)|) := by
  exact (gap8 p hp).abs

theorem gap11 (p : ℝ) (hp : p ≤ 0) :
    ¬ Summable (fun n : ℕ => groupedTerm p (n + 1)) := by
  have hlower : ∀ n : ℕ, 1 ≤ groupedTerm p (n + 1) := by
    intro n
    let x : ℝ := ((n + 1 : ℕ) : ℝ)
    have hx : 1 ≤ x := by
      dsimp [x]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hA : 0 < 4 * x - 3 := by linarith
    have hB : 0 < 4 * x - 1 := by linarith
    have hC : 0 < 2 * x - 1 := by linarith
    have hCA : 2 * x - 1 ≤ 4 * x - 3 := by linarith
    have hB1 : 1 ≤ 4 * x - 1 := by linarith
    have hACpow : Real.rpow (2 * x - 1) (-p) ≤
        Real.rpow (4 * x - 3) (-p) :=
      Real.rpow_le_rpow hC.le hCA (neg_nonneg.mpr hp)
    have hBpow : 1 ≤ Real.rpow (4 * x - 1) (-p) :=
      Real.one_le_rpow hB1 (neg_nonneg.mpr hp)
    have hArw : 1 / Real.rpow (4 * x - 3) p =
        Real.rpow (4 * x - 3) (-p) := by
      simpa only [one_div] using (Real.rpow_neg hA.le p).symm
    have hBrw : 1 / Real.rpow (4 * x - 1) p =
        Real.rpow (4 * x - 1) (-p) := by
      simpa only [one_div] using (Real.rpow_neg hB.le p).symm
    have hCrw : 1 / Real.rpow (2 * x - 1) p =
        Real.rpow (2 * x - 1) (-p) := by
      simpa only [one_div] using (Real.rpow_neg hC.le p).symm
    simp only [groupedTerm]
    change 1 / Real.rpow (4 * x - 3) p +
      1 / Real.rpow (4 * x - 1) p -
        1 / Real.rpow (2 * x - 1) p ≥ 1
    rw [hArw, hBrw, hCrw]
    linarith
  intro hs
  have hevent := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨n, hn⟩ := hevent.exists
  exact (not_lt_of_ge (hlower n)) hn

theorem gap12 (p : ℝ) :
    (Summable (fun n : ℕ => |groupedTerm p (n + 1)|) ↔ 1 ≤ p) ∧
    (¬ Summable (fun n : ℕ => groupedTerm p (n + 1)) ↔ p < 1) := by
  constructor
  · constructor
    · intro habs
      have hg : Summable (fun n : ℕ => groupedTerm p (n + 1)) :=
        Summable.of_norm (by simpa only [Real.norm_eq_abs] using habs)
      by_contra hp
      have hplt : p < 1 := lt_of_not_ge hp
      rcases le_or_gt p 0 with hp0 | hp0
      · exact (gap11 p hp0) hg
      · exact (gap7 p hp0 hplt) hg
    · intro hp
      rcases hp.eq_or_lt with hpEq | hpGt
      · exact gap10 p hpEq.symm
      · exact gap3 p hpGt
  · constructor
    · intro hnot
      by_contra hp
      have hpge : 1 ≤ p := le_of_not_gt hp
      rcases hpge.eq_or_lt with hpEq | hpGt
      · exact hnot (gap8 p hpEq.symm)
      · have habs := gap3 p hpGt
        exact hnot (Summable.of_norm (by
          simpa only [Real.norm_eq_abs] using habs))
    · intro hplt
      rcases le_or_gt p 0 with hp0 | hp0
      · exact gap11 p hp0
      · exact gap7 p hp0 hplt

end

end ProofGap.Exercise2695
