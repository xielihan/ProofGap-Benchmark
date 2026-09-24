import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise3934

noncomputable section

open MeasureTheory
open scoped Interval

def disk (a : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ a ^ 2}

def diskIntegral (a : ℝ) : ℝ :=
  ∫ p in disk a, |p.1 * p.2|

private theorem integral_id_zero_3934 (b : ℝ) :
    (∫ x in (0 : ℝ)..b, x) = b ^ 2 / 2 := by
  have hint :
      IntervalIntegrable (fun x : ℝ => (2 : ℝ) * x) volume 0 b :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hderiv (x : ℝ) :
      HasDerivAt (fun t : ℝ => t * t) (2 * x) x := by
    simpa [two_mul] using
      (hasDerivAt_id x).mul (hasDerivAt_id x)
  have hFTC :
      (∫ x in (0 : ℝ)..b, (2 : ℝ) * x) =
        b * b - (0 : ℝ) * 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hderiv x) hint
  rw [intervalIntegral.integral_const_mul] at hFTC
  nlinarith [hFTC]

theorem gap1 (a : ℝ) (ha : 0 ≤ a) :
    diskIntegral a =
      ∫ x in -a..a,
        ∫ y in -Real.sqrt (a ^ 2 - x ^ 2)..Real.sqrt (a ^ 2 - x ^ 2),
          |x * y| := by
  classical
  let f : ℝ × ℝ → ℝ := fun p => |p.1 * p.2|
  have hdisk : MeasurableSet (disk a) := by
    unfold disk
    exact measurableSet_le
      (((continuous_fst.pow 2).add (continuous_snd.pow 2)).measurable)
      continuous_const.measurable
  have hsubset : disk a ⊆ Set.Icc (-a) a ×ˢ Set.Icc (-a) a := by
    intro p hp
    change p.1 ^ 2 + p.2 ^ 2 ≤ a ^ 2 at hp
    have hx2 : p.1 ^ 2 ≤ a ^ 2 := by
      nlinarith [sq_nonneg p.2]
    have hy2 : p.2 ^ 2 ≤ a ^ 2 := by
      nlinarith [sq_nonneg p.1]
    have hxlo : -a ≤ p.1 := by
      by_contra h
      have hlt : p.1 < -a := lt_of_not_ge h
      have hmul : 0 < (p.1 + a) * (p.1 - a) :=
        mul_pos_of_neg_of_neg (by linarith) (by linarith)
      nlinarith [hmul]
    have hxhi : p.1 ≤ a := by
      by_contra h
      have hgt : a < p.1 := lt_of_not_ge h
      have hmul : 0 < (p.1 - a) * (p.1 + a) :=
        mul_pos (by linarith) (by linarith)
      nlinarith [hmul]
    have hylo : -a ≤ p.2 := by
      by_contra h
      have hlt : p.2 < -a := lt_of_not_ge h
      have hmul : 0 < (p.2 + a) * (p.2 - a) :=
        mul_pos_of_neg_of_neg (by linarith) (by linarith)
      nlinarith [hmul]
    have hyhi : p.2 ≤ a := by
      by_contra h
      have hgt : a < p.2 := lt_of_not_ge h
      have hmul : 0 < (p.2 - a) * (p.2 + a) :=
        mul_pos (by linarith) (by linarith)
      nlinarith [hmul]
    exact ⟨⟨hxlo, hxhi⟩, ⟨hylo, hyhi⟩⟩
  have hfcont : Continuous f := by
    exact (continuous_fst.mul continuous_snd).abs
  have hrect : IntegrableOn f (Set.Icc (-a) a ×ˢ Set.Icc (-a) a) := by
    exact hfcont.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hdiskInt : IntegrableOn f (disk a) := hrect.mono_set hsubset
  have hindInt : Integrable ((disk a).indicator f) :=
    (integrable_indicator_iff hdisk).2 hdiskInt
  have hae_ne (c : ℝ) : ∀ᵐ y : ℝ ∂volume, y ≠ c := by
    simp [ae_iff]
  unfold diskIntegral
  change (∫ p in disk a, f p) = _
  rw [← MeasureTheory.integral_indicator hdisk]
  have hprod :
      (∫ p : ℝ × ℝ, (disk a).indicator f p ∂volume) =
        ∫ x : ℝ, ∫ y : ℝ, (disk a).indicator f (x, y) := by
    change
      (∫ p : ℝ × ℝ, (disk a).indicator f p ∂(volume.prod volume)) =
        ∫ x : ℝ, ∫ y : ℝ, (disk a).indicator f (x, y)
    exact MeasureTheory.integral_prod ((disk a).indicator f) hindInt
  rw [hprod]
  have hout : -a ≤ a := by linarith
  rw [intervalIntegral.integral_of_le hout]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hae_ne (-a)] with x hxne
  by_cases hx : x ∈ Set.Ioc (-a) a
  · rw [Set.indicator_of_mem hx]
    have hxlo : -a < x := hx.1
    have hxhi : x ≤ a := hx.2
    have hxmul : (x + a) * (x - a) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have hq : 0 ≤ a ^ 2 - x ^ 2 := by
      nlinarith [hxmul]
    let s := Real.sqrt (a ^ 2 - x ^ 2)
    have hs : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = a ^ 2 - x ^ 2 := by
      dsimp [s]
      exact Real.sq_sqrt hq
    change (∫ y : ℝ, (disk a).indicator f (x, y)) =
      ∫ y in -s..s, |x * y|
    rw [intervalIntegral.integral_of_le (by linarith : -s ≤ s)]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hae_ne (-s)] with y hy
    have hmem : (x, y) ∈ disk a ↔ y ∈ Set.Ioc (-s) s := by
      change x ^ 2 + y ^ 2 ≤ a ^ 2 ↔ -s < y ∧ y ≤ s
      constructor
      · intro hxy
        have hysq : y ^ 2 ≤ s ^ 2 := by
          nlinarith
        have hylo : -s ≤ y := by
          by_contra h
          have hlt : y < -s := lt_of_not_ge h
          have hmul : 0 < (y + s) * (y - s) :=
            mul_pos_of_neg_of_neg (by linarith) (by linarith)
          nlinarith [hmul]
        have hyhi : y ≤ s := by
          by_contra h
          have hgt : s < y := lt_of_not_ge h
          have hmul : 0 < (y + s) * (y - s) :=
            mul_pos (by linarith) (by linarith)
          nlinarith [hmul]
        exact ⟨lt_of_le_of_ne hylo (Ne.symm hy), hyhi⟩
      · intro hy'
        have hmul : (y + s) * (y - s) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
        nlinarith [hmul]
    change (disk a).indicator f (x, y) =
      (Set.Ioc (-s) s).indicator (fun y => |x * y|) y
    simp [Set.indicator_apply, hmem, f]
  · have hcases : x < -a ∨ a < x := by
      by_cases hleft : x ≤ -a
      · exact Or.inl (lt_of_le_of_ne hleft hxne)
      · have hxlo : -a < x := lt_of_not_ge hleft
        have hright : ¬x ≤ a := by
          intro hxhi
          exact hx ⟨hxlo, hxhi⟩
        exact Or.inr (lt_of_not_ge hright)
    have hnot (y : ℝ) : (x, y) ∉ disk a := by
      intro hxy
      change x ^ 2 + y ^ 2 ≤ a ^ 2 at hxy
      rcases hcases with hleft | hright
      · have hmul : 0 < (x + a) * (x - a) :=
          mul_pos_of_neg_of_neg (by linarith) (by linarith)
        nlinarith [hmul, sq_nonneg y]
      · have hmul : 0 < (x - a) * (x + a) :=
          mul_pos (by linarith) (by linarith)
        nlinarith [hmul, sq_nonneg y]
    simp [Set.indicator_apply, hx, hnot]

theorem gap2 (a : ℝ) (ha : 0 ≤ a) :
    (∫ x in -a..a,
        ∫ y in -Real.sqrt (a ^ 2 - x ^ 2)..Real.sqrt (a ^ 2 - x ^ 2),
          |x * y|) =
      ∫ x in -a..a, (a ^ 2 - x ^ 2) * |x| := by
  apply intervalIntegral.integral_congr
  intro x hx
  have hxa : x ∈ Set.Icc (-a) a := by
    simpa [Set.uIcc_of_le (by linarith : -a ≤ a)] using hx
  have hq : 0 ≤ a ^ 2 - x ^ 2 := by
    rcases hxa with ⟨hxlo, hxhi⟩
    nlinarith [sq_nonneg (x + a), sq_nonneg (x - a)]
  let s := Real.sqrt (a ^ 2 - x ^ 2)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = a ^ 2 - x ^ 2 := by
    dsimp [s]
    exact Real.sq_sqrt hq
  have habsLeft : IntervalIntegrable (fun y : ℝ => |y|) volume (-s) 0 :=
    continuous_abs.intervalIntegrable _ _
  have habsRight : IntervalIntegrable (fun y : ℝ => |y|) volume 0 s :=
    continuous_abs.intervalIntegrable _ _
  have hleft : (∫ y in -s..0, |y|) = ∫ y in 0..s, y := by
    calc
      (∫ y in -s..0, |y|) = ∫ y in 0..s, |-y| := by
        simpa using
          (intervalIntegral.integral_comp_neg
            (f := fun y : ℝ => |y|) (a := 0) (b := s)).symm
      _ = ∫ y in 0..s, y := by
        apply intervalIntegral.integral_congr
        intro y hy
        have hy' : 0 ≤ y := by
          have : y ∈ Set.Icc (0 : ℝ) s := by
            simpa [Set.uIcc_of_le hs] using hy
          exact this.1
        change |-y| = y
        simp [abs_of_nonneg hy']
  have hright : (∫ y in 0..s, |y|) = ∫ y in 0..s, y := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hy' : 0 ≤ y := by
      have : y ∈ Set.Icc (0 : ℝ) s := by
        simpa [Set.uIcc_of_le hs] using hy
      exact this.1
    rw [abs_of_nonneg hy']
  have hpow : (∫ y in 0..s, y) = s ^ 2 / 2 :=
    integral_id_zero_3934 s
  have habsInt : (∫ y in -s..s, |y|) = s ^ 2 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals habsLeft habsRight]
    rw [hleft, hright, hpow]
    ring
  calc
    (∫ y in -s..s, |x * y|) = |x| * ∫ y in -s..s, |y| := by
      simp_rw [abs_mul]
      rw [intervalIntegral.integral_const_mul]
    _ = (a ^ 2 - x ^ 2) * |x| := by
      rw [habsInt, hs2]
      ring

theorem gap3 (a : ℝ) (ha : 0 ≤ a) :
    (∫ x in -a..a, (a ^ 2 - x ^ 2) * |x|) =
      2 * ∫ x in (0 : ℝ)..a, (a ^ 2 - x ^ 2) * x := by
  let f : ℝ → ℝ := fun x => (a ^ 2 - x ^ 2) * |x|
  have hf : Continuous f :=
    (continuous_const.sub (continuous_id.pow 2)).mul continuous_abs
  have hleft : IntervalIntegrable f volume (-a) 0 :=
    hf.intervalIntegrable _ _
  have hright : IntervalIntegrable f volume 0 a :=
    hf.intervalIntegrable _ _
  have hneg : (∫ x in -a..0, f x) =
      ∫ x in 0..a, (a ^ 2 - x ^ 2) * x := by
    calc
      (∫ x in -a..0, f x) = ∫ x in 0..a, f (-x) := by
        simpa using
          (intervalIntegral.integral_comp_neg (f := f) (a := 0) (b := a)).symm
      _ = ∫ x in 0..a, (a ^ 2 - x ^ 2) * x := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : 0 ≤ x := by
          have : x ∈ Set.Icc (0 : ℝ) a := by
            simpa [Set.uIcc_of_le ha] using hx
          exact this.1
        dsimp [f]
        rw [abs_neg, abs_of_nonneg hx']
        ring
  change (∫ x in -a..a, f x) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  rw [hneg]
  have hpos : (∫ x in 0..a, f x) =
      ∫ x in 0..a, (a ^ 2 - x ^ 2) * x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : 0 ≤ x := by
      have : x ∈ Set.Icc (0 : ℝ) a := by
        simpa [Set.uIcc_of_le ha] using hx
      exact this.1
    simp [f, abs_of_nonneg hx']
  rw [hpos]
  ring

theorem gap4 (a : ℝ) (ha : 0 ≤ a) :
    2 * (∫ x in (0 : ℝ)..a, (a ^ 2 - x ^ 2) * x) =
      a ^ 4 / 2 := by
  have hfun : (fun x : ℝ => (a ^ 2 - x ^ 2) * x) =
      fun x : ℝ => a ^ 2 * x - x ^ 3 := by
    funext x
    ring
  have hlin : IntervalIntegrable (fun x : ℝ => a ^ 2 * x) volume 0 a :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hcub : IntervalIntegrable (fun x : ℝ => x ^ 3) volume 0 a :=
    (continuous_id.pow 3).intervalIntegrable _ _
  have hone : (∫ x in (0 : ℝ)..a, x) = a ^ 2 / 2 :=
    integral_id_zero_3934 a
  have hthree : (∫ x in (0 : ℝ)..a, x ^ 3) = a ^ 4 / 4 := by
    have hfour :
        IntervalIntegrable (fun x : ℝ => (4 : ℝ) * x ^ 3) volume 0 a :=
      (continuous_const.mul (continuous_id.pow 3)).intervalIntegrable _ _
    have hsq (x : ℝ) :
        HasDerivAt (fun t : ℝ => t * t) (2 * x) x := by
      simpa [two_mul] using
        (hasDerivAt_id x).mul (hasDerivAt_id x)
    have hderiv (x : ℝ) :
        HasDerivAt (fun t : ℝ => (t * t) * (t * t)) (4 * x ^ 3) x := by
      convert (hsq x).mul (hsq x) using 1 <;> ring
    have hFTC :
        (∫ x in (0 : ℝ)..a, (4 : ℝ) * x ^ 3) =
          (a * a) * (a * a) -
            (((0 : ℝ) * 0) * ((0 : ℝ) * 0)) := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hderiv x) hfour
    rw [intervalIntegral.integral_const_mul] at hFTC
    nlinarith [hFTC]
  rw [hfun]
  rw [intervalIntegral.integral_sub hlin hcub]
  rw [intervalIntegral.integral_const_mul]
  rw [hone, hthree]
  ring

theorem gap5 (a : ℝ) (ha : 0 ≤ a) :
    diskIntegral a = a ^ 4 / 2 := by
  rw [gap1 a ha, gap2 a ha, gap3 a ha, gap4 a ha]

end

end ProofGap.Exercise3934
