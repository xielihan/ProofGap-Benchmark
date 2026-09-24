import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise2389
noncomputable section

open Filter Set MeasureTheory
open scoped Interval

def weighted (p : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := Real.rpow x p * f x
def cLower (p : ℝ) : ℝ := ∫ t in (1 / 2 : ℝ)..1, Real.rpow t p
def cUpper (p : ℝ) : ℝ := ∫ t in (1 : ℝ)..2, Real.rpow t p
def ImproperConvergesAtZero (p : ℝ) (f : ℝ → ℝ) (a : ℝ) : Prop :=
  (∀ b ∈ Ioo (0 : ℝ) a, IntervalIntegrable (weighted p f) volume b a) ∧
    ∃ L : ℝ,
      Tendsto (fun b => ∫ t in b..a, weighted p f t)
        (nhdsWithin 0 (Ioi 0)) (nhds L)

private theorem weighted_intervalIntegrable (f : ℝ → ℝ) (p a u v : ℝ)
    (hf : AntitoneOn f (Ioo 0 a)) (hu : 0 < u) (huv : u ≤ v) (hv : v < a) :
    IntervalIntegrable (weighted p f) volume u v := by
  have hfint : IntervalIntegrable f volume u v := by
    apply AntitoneOn.intervalIntegrable
    rw [Set.uIcc_of_le huv]
    exact hf.mono fun x hx => ⟨hu.trans_le hx.1, hx.2.trans_lt hv⟩
  have hrpow : ContinuousOn (fun x : ℝ => Real.rpow x p) (Set.uIcc u v) := by
    rw [Set.uIcc_of_le huv]
    intro x hx
    exact (Real.continuousAt_rpow_const x p
      (Or.inl (hu.trans_le hx.1).ne')).continuousWithinAt
  simpa only [weighted] using hfint.continuousOn_mul hrpow

private theorem rpow_intervalIntegrable_of_pos (p u v : ℝ)
    (hu : 0 < u) (huv : u ≤ v) :
    IntervalIntegrable (fun x : ℝ => Real.rpow x p) volume u v := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le huv]
  intro x hx
  exact (Real.continuousAt_rpow_const x p
    (Or.inl (hu.trans_le hx.1).ne')).continuousWithinAt

private theorem cLower_pos (p : ℝ) : 0 < cLower p := by
  unfold cLower
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (rpow_intervalIntegrable_of_pos p (1 / 2) 1 (by norm_num) (by norm_num))
  · intro x hx
    exact Real.rpow_pos_of_pos (by linarith [hx.1]) p
  · norm_num

private theorem cUpper_pos (p : ℝ) : 0 < cUpper p := by
  unfold cUpper
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (rpow_intervalIntegrable_of_pos p 1 2 (by norm_num) (by norm_num))
  · intro x hx
    exact Real.rpow_pos_of_pos (by linarith [hx.1]) p
  · norm_num

private theorem lower_rpow_integral_scale (p x : ℝ) (hx : 0 < x) :
    (∫ t in x / 2..x, Real.rpow t p) = cLower p * Real.rpow x (p + 1) := by
  have hscale := intervalIntegral.smul_integral_comp_mul_right
    (fun t : ℝ => Real.rpow t p) x (a := (1 / 2 : ℝ)) (b := 1)
  have heq : (∫ t in (1 / 2 : ℝ)..1, Real.rpow (t * x) p) =
      Real.rpow x p * cLower p := by
    calc
      (∫ t in (1 / 2 : ℝ)..1, Real.rpow (t * x) p) =
          ∫ t in (1 / 2 : ℝ)..1, Real.rpow x p * Real.rpow t p := by
        apply intervalIntegral.integral_congr
        intro t ht
        change Real.rpow (t * x) p = Real.rpow x p * Real.rpow t p
        have ht0 : 0 ≤ t := by
          rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
          linarith [ht.1]
        have hm : Real.rpow (t * x) p = Real.rpow t p * Real.rpow x p := by
          simpa only using Real.mul_rpow ht0 hx.le
        rw [hm]
        ring
      _ = Real.rpow x p * ∫ t in (1 / 2 : ℝ)..1, Real.rpow t p := by
        rw [intervalIntegral.integral_const_mul]
      _ = Real.rpow x p * cLower p := by rfl
  rw [heq] at hscale
  change x * (Real.rpow x p * cLower p) =
    ∫ t in (1 / 2 : ℝ) * x..1 * x, Real.rpow t p at hscale
  have hadd : Real.rpow x (p + 1) = Real.rpow x p * x := by
    simpa only [Real.rpow_one] using Real.rpow_add hx p 1
  rw [show (1 / 2 : ℝ) * x = x / 2 by ring, one_mul] at hscale
  calc
    (∫ t in x / 2..x, Real.rpow t p) = x * (Real.rpow x p * cLower p) := hscale.symm
    _ = cLower p * (Real.rpow x p * x) := by ring
    _ = cLower p * Real.rpow x (p + 1) := by rw [hadd]

private theorem upper_rpow_integral_scale (p x : ℝ) (hx : 0 < x) :
    (∫ t in x..2 * x, Real.rpow t p) = cUpper p * Real.rpow x (p + 1) := by
  have hscale := intervalIntegral.smul_integral_comp_mul_right
    (fun t : ℝ => Real.rpow t p) x (a := (1 : ℝ)) (b := 2)
  have heq : (∫ t in (1 : ℝ)..2, Real.rpow (t * x) p) =
      Real.rpow x p * cUpper p := by
    calc
      (∫ t in (1 : ℝ)..2, Real.rpow (t * x) p) =
          ∫ t in (1 : ℝ)..2, Real.rpow x p * Real.rpow t p := by
        apply intervalIntegral.integral_congr
        intro t ht
        change Real.rpow (t * x) p = Real.rpow x p * Real.rpow t p
        have ht0 : 0 ≤ t := by
          rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
          linarith [ht.1]
        have hm : Real.rpow (t * x) p = Real.rpow t p * Real.rpow x p := by
          simpa only using Real.mul_rpow ht0 hx.le
        rw [hm]
        ring
      _ = Real.rpow x p * ∫ t in (1 : ℝ)..2, Real.rpow t p := by
        rw [intervalIntegral.integral_const_mul]
      _ = Real.rpow x p * cUpper p := by rfl
  rw [heq] at hscale
  change x * (Real.rpow x p * cUpper p) =
    ∫ t in (1 : ℝ) * x..2 * x, Real.rpow t p at hscale
  have hadd : Real.rpow x (p + 1) = Real.rpow x p * x := by
    simpa only [Real.rpow_one] using Real.rpow_add hx p 1
  rw [one_mul] at hscale
  calc
    (∫ t in x..2 * x, Real.rpow t p) = x * (Real.rpow x p * cUpper p) := hscale.symm
    _ = cUpper p * (Real.rpow x p * x) := by ring
    _ = cUpper p * Real.rpow x (p + 1) := by rw [hadd]

theorem gap1 (f : ℝ → ℝ) (p a δ x : ℝ)
    (hf : AntitoneOn f (Ioo 0 a)) (hδ : 0 < δ) (hδa : δ < a)
    (hf0 : ∀ t ∈ Ioo 0 δ, 0 ≤ f t) (hx : x ∈ Ioo 0 δ) :
    f x * (∫ t in x / 2..x, Real.rpow t p) ≤
      ∫ t in x / 2..x, weighted p f t := by
  have hxhalf : 0 < x / 2 := half_pos hx.1
  have hhalfx : x / 2 ≤ x := by linarith
  have hxa : x < a := hx.2.trans hδa
  have hrint := rpow_intervalIntegrable_of_pos p (x / 2) x hxhalf hhalfx
  have hwint := weighted_intervalIntegrable f p a (x / 2) x hf hxhalf hhalfx hxa
  have hmono := intervalIntegral.integral_mono_on hhalfx (hrint.const_mul (f x)) hwint
    (fun t ht => by
      have htx : f x ≤ f t := hf
        ⟨hxhalf.trans_le ht.1, ht.2.trans_lt hxa⟩ ⟨hx.1, hxa⟩ ht.2
      unfold weighted
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left htx
        (Real.rpow_nonneg (hxhalf.trans_le ht.1).le p))
  rw [intervalIntegral.integral_const_mul] at hmono
  exact hmono

theorem gap2 (f : ℝ → ℝ) (p x : ℝ) (hx : 0 < x) :
    f x * (∫ t in x / 2..x, Real.rpow t p) =
      cLower p * Real.rpow x (p + 1) * f x := by
  rw [lower_rpow_integral_scale p x hx]
  ring

theorem gap3 (f : ℝ → ℝ) (p x : ℝ) (hx : 0 < x) (hfx : 0 ≤ f x) :
    0 ≤ cLower p * Real.rpow x (p + 1) * f x := by
  exact mul_nonneg (mul_nonneg (cLower_pos p).le (Real.rpow_nonneg hx.le _)) hfx

theorem gap4 (f : ℝ → ℝ) (p a δ x : ℝ)
    (hf : AntitoneOn f (Ioo 0 a)) (hδ : 0 < δ) (hδa : δ < a)
    (hf0 : ∀ t ∈ Ioo 0 δ, 0 ≤ f t) (hx : x ∈ Ioo 0 δ) :
    0 ≤ ∫ t in x / 2..x, weighted p f t := by
  have hlower := gap1 f p a δ x hf hδ hδa hf0 hx
  rw [gap2 f p x hx.1] at hlower
  exact (gap3 f p x hx.1 (hf0 x hx)).trans hlower

theorem gap5 (p : ℝ) :
    cLower p =
      if p = -1 then Real.log 2
      else (1 - Real.rpow (1 / 2) (p + 1)) / (p + 1) := by
  by_cases hp : p = -1
  · subst p
    rw [cLower, if_pos rfl]
    have heq : (fun t : ℝ => Real.rpow t (-1 : ℝ)) = fun t => t⁻¹ := by
      funext t
      simpa only using Real.rpow_neg_one t
    rw [heq]
    rw [integral_inv_of_pos (by norm_num) (by norm_num)]
    norm_num
  · have hzero : (0 : ℝ) ∉ Set.uIcc (1 / 2) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
      norm_num
    have hform : (∫ t in (1 / 2 : ℝ)..1, Real.rpow t p) =
        (Real.rpow 1 (p + 1) - Real.rpow (1 / 2) (p + 1)) / (p + 1) := by
      simpa only using (integral_rpow (r := p) (a := (1 / 2 : ℝ)) (b := 1)
        (Or.inr ⟨hp, hzero⟩))
    rw [cLower, hform, if_neg hp]
    have hone : Real.rpow 1 (p + 1) = 1 := by
      simpa only using Real.one_rpow (p + 1)
    rw [hone]

theorem gap6 (p : ℝ) : 0 < cLower p := by
  exact cLower_pos p

theorem gap7 (f : ℝ → ℝ) (p a : ℝ) (ha : 0 < a)
    (hconv : ImproperConvergesAtZero p f a) :
    Tendsto (fun x => ∫ t in x / 2..x, weighted p f t)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  let l : Filter ℝ := nhdsWithin 0 (Ioi 0)
  obtain ⟨hint, L, hL⟩ := hconv
  have hhalf : Tendsto (fun x : ℝ => x / 2) l l := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hzero : Tendsto (fun x : ℝ => x / 2) l (nhds 0) := by
        have hid : Tendsto (fun x : ℝ => x) l (nhds 0) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        simpa using hid.div_const 2
      exact hzero
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact half_pos (show 0 < x from hx)
  have hsub : Tendsto
      (fun x => (∫ t in x / 2..a, weighted p f t) -
        ∫ t in x..a, weighted p f t) l (nhds 0) := by
    simpa using (hL.comp hhalf).sub hL
  refine hsub.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT ha] with x hx
  have hxhalf : 0 < x / 2 := half_pos hx.1
  have hhalfx : x / 2 ≤ x := by linarith
  have hfirst := hint (x / 2) ⟨hxhalf, (half_lt_self hx.1).trans hx.2⟩
  have hsecond := hint x hx
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hfirst.trans hsecond.symm) hsecond
  linarith [hadd]

theorem gap8 (f : ℝ → ℝ) (p a δ : ℝ)
    (hf : AntitoneOn f (Ioo 0 a)) (hδ : 0 < δ) (hδa : δ < a)
    (hf0 : ∀ t ∈ Ioo 0 δ, 0 ≤ f t)
    (hconv : ImproperConvergesAtZero p f a) :
    Tendsto (fun x => Real.rpow x (p + 1) * f x)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  let l : Filter ℝ := nhdsWithin 0 (Ioi 0)
  have hc : 0 < cLower p := gap6 p
  have hblock := gap7 f p a (hδ.trans hδa) hconv
  have hbound : Tendsto
      (fun x => (1 / cLower p) * (∫ t in x / 2..x, weighted p f t))
      l (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hblock
  change Tendsto (fun x => Real.rpow x (p + 1) * f x) l (nhds 0)
  apply squeeze_zero'
    (by
      filter_upwards [Ioo_mem_nhdsGT hδ] with x hx
      exact mul_nonneg (Real.rpow_nonneg hx.1.le _) (hf0 x hx))
    (by
      filter_upwards [Ioo_mem_nhdsGT hδ] with x hx
      have hlower := gap1 f p a δ x hf hδ hδa hf0 hx
      rw [gap2 f p x hx.1] at hlower
      rw [one_div_mul_eq_div]
      apply (le_div_iff₀ hc).2
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hlower)
    hbound

theorem gap9 (f : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hf : AntitoneOn f (Ioo 0 a))
    (hneg : ¬ ∃ δ ∈ Ioo 0 a, ∀ x ∈ Ioo 0 δ, 0 ≤ f x) :
    ∀ x ∈ Ioo 0 a, f x < 0 := by
  intro x hx
  by_contra hn
  have hfx : 0 ≤ f x := le_of_not_gt hn
  apply hneg
  refine ⟨x, hx, fun y hy => ?_⟩
  exact hfx.trans (hf ⟨hy.1, hy.2.trans hx.2⟩ ⟨hx.1, hx.2⟩ hy.2.le)

theorem gap10 (f : ℝ → ℝ) (p a x : ℝ)
    (hf : AntitoneOn f (Ioo 0 a)) (hx : x ∈ Ioo 0 (a / 2)) :
    (∫ t in x..2 * x, weighted p f t) ≤
      f x * ∫ t in x..2 * x, Real.rpow t p := by
  have hxx : x ≤ 2 * x := by linarith [hx.1]
  have h2xa : 2 * x < a := by linarith [hx.2]
  have hrint := rpow_intervalIntegrable_of_pos p x (2 * x) hx.1 hxx
  have hwint := weighted_intervalIntegrable f p a x (2 * x) hf hx.1 hxx h2xa
  have hmono := intervalIntegral.integral_mono_on hxx hwint (hrint.const_mul (f x))
    (fun t ht => by
      have hft : f t ≤ f x := hf
        ⟨hx.1, by linarith [hx.1, hx.2]⟩
        ⟨hx.1.trans_le ht.1, ht.2.trans_lt h2xa⟩ ht.1
      unfold weighted
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hft
        (Real.rpow_nonneg (hx.1.trans_le ht.1).le p))
  rw [intervalIntegral.integral_const_mul] at hmono
  exact hmono

theorem gap11 (f : ℝ → ℝ) (p x : ℝ) (hx : 0 < x) :
    f x * (∫ t in x..2 * x, Real.rpow t p) =
      cUpper p * Real.rpow x (p + 1) * f x := by
  rw [upper_rpow_integral_scale p x hx]
  ring

theorem gap12 (f : ℝ → ℝ) (p x : ℝ)
    (hx : 0 < x) (hfx : f x < 0) :
    cUpper p * Real.rpow x (p + 1) * f x < 0 := by
  exact mul_neg_of_pos_of_neg (mul_pos (cUpper_pos p) (Real.rpow_pos_of_pos hx _)) hfx

theorem gap13 (f : ℝ → ℝ) (p a x : ℝ)
    (hf : AntitoneOn f (Ioo 0 a)) (hx : x ∈ Ioo 0 (a / 2))
    (hfx : f x < 0) :
    (∫ t in x..2 * x, weighted p f t) < 0 := by
  have hle := gap10 f p a x hf hx
  rw [gap11 f p x hx.1] at hle
  exact hle.trans_lt (gap12 f p x hx.1 hfx)

theorem gap14 (p : ℝ) :
    cUpper p =
      if p = -1 then Real.log 2
      else (Real.rpow 2 (p + 1) - 1) / (p + 1) := by
  by_cases hp : p = -1
  · subst p
    rw [cUpper, if_pos rfl]
    have heq : (fun t : ℝ => Real.rpow t (-1 : ℝ)) = fun t => t⁻¹ := by
      funext t
      simpa only using Real.rpow_neg_one t
    rw [heq, integral_inv_of_pos (by norm_num) (by norm_num)]
    norm_num
  · have hzero : (0 : ℝ) ∉ Set.uIcc 1 2 := by
      rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
      norm_num
    have hform : (∫ t in (1 : ℝ)..2, Real.rpow t p) =
        (Real.rpow 2 (p + 1) - Real.rpow 1 (p + 1)) / (p + 1) := by
      simpa only using (integral_rpow (r := p) (a := (1 : ℝ)) (b := 2)
        (Or.inr ⟨hp, hzero⟩))
    rw [cUpper, hform, if_neg hp]
    have hone : Real.rpow 1 (p + 1) = 1 := by
      simpa only using Real.one_rpow (p + 1)
    rw [hone]

theorem gap15 (p : ℝ) : 0 < cUpper p := by
  exact cUpper_pos p

theorem gap16 (f : ℝ → ℝ) (p a x : ℝ)
    (hf : AntitoneOn f (Ioo 0 a)) (hx : x ∈ Ioo 0 (a / 2))
    (hfx : f x < 0) :
    |Real.rpow x (p + 1) * f x| ≤
      (1 / cUpper p) * |∫ t in x..2 * x, weighted p f t| := by
  have hc : 0 < cUpper p := gap15 p
  have hz : Real.rpow x (p + 1) * f x < 0 :=
    mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos hx.1 _) hfx
  have hI := gap13 f p a x hf hx hfx
  have hle := gap10 f p a x hf hx
  rw [gap11 f p x hx.1] at hle
  rw [abs_of_neg hz, abs_of_neg hI, one_div_mul_eq_div]
  apply (le_div_iff₀ hc).2
  nlinarith

theorem gap17 (f : ℝ → ℝ) (p a : ℝ) (ha : 0 < a)
    (hconv : ImproperConvergesAtZero p f a) :
    Tendsto (fun x => ∫ t in x..2 * x, weighted p f t)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  let l : Filter ℝ := nhdsWithin 0 (Ioi 0)
  obtain ⟨hint, L, hL⟩ := hconv
  have hdouble : Tendsto (fun x : ℝ => 2 * x) l l := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hid : Tendsto (fun x : ℝ => x) l (nhds 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using tendsto_const_nhds.mul hid
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_pos (by norm_num) (show 0 < x from hx)
  have hsub : Tendsto
      (fun x => (∫ t in x..a, weighted p f t) -
        ∫ t in 2 * x..a, weighted p f t) l (nhds 0) := by
    simpa using hL.sub (hL.comp hdouble)
  refine hsub.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (half_pos ha)] with x hx
  have h2x : 2 * x ∈ Ioo (0 : ℝ) a := by
    constructor
    · nlinarith [hx.1]
    · nlinarith [hx.2]
  have hfirst := hint x ⟨hx.1, hx.2.trans (half_lt_self ha)⟩
  have hsecond := hint (2 * x) h2x
  have hblock := hfirst.trans hsecond.symm
  have hadd := intervalIntegral.integral_add_adjacent_intervals hblock hsecond
  linarith [hadd]

theorem gap18 (f : ℝ → ℝ) (p a : ℝ) (ha : 0 < a)
    (hf : AntitoneOn f (Ioo 0 a))
    (hneg : ∀ x ∈ Ioo 0 a, f x < 0)
    (hconv : ImproperConvergesAtZero p f a) :
    Tendsto (fun x => Real.rpow x (p + 1) * f x)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  let l : Filter ℝ := nhdsWithin 0 (Ioi 0)
  have hblock := gap17 f p a ha hconv
  have hbound : Tendsto
      (fun x => (1 / cUpper p) * |∫ t in x..2 * x, weighted p f t|)
      l (nhds 0) := by
    have habs := hblock.abs
    simpa only [abs_zero, mul_zero] using tendsto_const_nhds.mul habs
  change Tendsto (fun x => Real.rpow x (p + 1) * f x) l (nhds 0)
  apply squeeze_zero_norm'
    (by
      filter_upwards [Ioo_mem_nhdsGT (half_pos ha)] with x hx
      have hxa : x ∈ Ioo (0 : ℝ) a := ⟨hx.1, hx.2.trans (half_lt_self ha)⟩
      simpa only [Real.norm_eq_abs] using gap16 f p a x hf hx (hneg x hxa))
    hbound

theorem gap19 (f : ℝ → ℝ) (p a : ℝ) (ha : 0 < a)
    (hf : AntitoneOn f (Ioo 0 a))
    (hconv : ImproperConvergesAtZero p f a) :
    Tendsto (fun x => Real.rpow x (p + 1) * f x)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  by_cases hpos : ∃ δ ∈ Ioo (0 : ℝ) a, ∀ x ∈ Ioo 0 δ, 0 ≤ f x
  · obtain ⟨δ, hδ, hf0⟩ := hpos
    exact gap8 f p a δ hf hδ.1 hδ.2 hf0 hconv
  · exact gap18 f p a ha hf (gap9 f a ha hf hpos) hconv

theorem gap20 (f : ℝ → ℝ) (p a : ℝ) (ha : 0 < a)
    (hf : AntitoneOn f (Ioo 0 a))
    (hconv : ImproperConvergesAtZero p f a) :
    Tendsto (fun x => Real.rpow x (p + 1) * f x)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  exact gap19 f p a ha hf hconv

end
end ProofGap.Exercise2389
