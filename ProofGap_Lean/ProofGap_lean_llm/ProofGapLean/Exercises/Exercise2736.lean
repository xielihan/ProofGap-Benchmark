import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.AtTopBot.Defs

namespace ProofGap.Exercise2736

noncomputable section

open Filter

def term (x y : ℝ) (n : ℕ) : ℝ :=
  Real.tan (x + y / n) ^ n

def rootMagnitude (x y : ℝ) (n : ℕ) : ℝ :=
  Real.rpow |term x y n| (1 / (n : ℝ))

private theorem abs_tan_lt_one_iff_of_mem (z : ℝ)
    (hz : z ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    |Real.tan z| < 1 ↔ |z| < Real.pi / 4 := by
  have hnq : -(Real.pi / 4) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have hpq : Real.pi / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have hlo := Real.strictMonoOn_tan.lt_iff_lt hnq hz
  have hhi := Real.strictMonoOn_tan.lt_iff_lt hz hpq
  rw [abs_lt, abs_lt]
  constructor
  · rintro ⟨hl, hu⟩
    constructor
    · apply hlo.mp
      simpa [Real.tan_neg, Real.tan_pi_div_four] using hl
    · apply hhi.mp
      simpa [Real.tan_pi_div_four] using hu
  · rintro ⟨hl, hu⟩
    constructor
    · have h := hlo.mpr hl
      simpa [Real.tan_neg, Real.tan_pi_div_four] using h
    · have h := hhi.mpr hu
      simpa [Real.tan_pi_div_four] using h

private theorem tendsto_shift_argument (x y : ℝ) :
    Tendsto (fun n : ℕ => x + y / ((n + 1 : ℕ) : ℝ)) atTop (nhds x) := by
  have hzero : Tendsto (fun n : ℕ => y / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hzero' :
      Tendsto (fun n : ℕ => y / ((n + 1 : ℕ) : ℝ)) atTop (nhds 0) := by
    simpa using ((tendsto_add_atTop_iff_nat 1).2 hzero)
  simpa using tendsto_const_nhds.add hzero'

private theorem tendsto_tan_shift (x y : ℝ) (hx : Real.cos x ≠ 0) :
    Tendsto (fun n : ℕ => Real.tan (x + y / ((n + 1 : ℕ) : ℝ)))
      atTop (nhds (Real.tan x)) := by
  exact ((Real.continuousAt_tan).2 hx).tendsto.comp
    (tendsto_shift_argument x y)

private theorem rootMagnitude_succ_eq (x y : ℝ) (n : ℕ) :
    rootMagnitude x y (n + 1) =
      |Real.tan (x + y / ((n + 1 : ℕ) : ℝ))| := by
  simp only [rootMagnitude, term, abs_pow]
  simpa [one_div] using
    (Real.pow_rpow_inv_natCast
      (x := |Real.tan (x + y / ((n + 1 : ℕ) : ℝ))|)
      (n := n + 1) (abs_nonneg _) (Nat.succ_ne_zero n))

private theorem pow_lower_not_tendsto_zero
    (u : ℕ → ℝ) (C : ℝ)
    (hlower : ∀ᶠ n : ℕ in atTop,
      1 - C / ((n + 1 : ℕ) : ℝ) ≤ |u n|) :
    ¬ Tendsto (fun n : ℕ => u n ^ (n + 1)) atTop (nhds 0) := by
  let D : ℝ := |C|
  have hD0 : 0 ≤ D := by
    dsimp [D]
    exact abs_nonneg C
  have hCD : C ≤ D := by
    simpa [D] using (le_abs_self C)
  have hlarge0 : ∀ᶠ n : ℕ in atTop, 2 * D ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (2 * D))
  have hlarge :
      ∀ᶠ n : ℕ in atTop, 2 * D ≤ ((n + 1 : ℕ) : ℝ) := by
    filter_upwards [hlarge0] with n hn
    calc
      2 * D ≤ (n : ℝ) := hn
      _ ≤ ((n + 1 : ℕ) : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (le_add_of_nonneg_right
            (show (0 : ℝ) ≤ 1 from zero_le_one) :
              (n : ℝ) ≤ (n : ℝ) + 1)
  intro ht
  have habs0 :
      Tendsto (fun n : ℕ => |u n ^ (n + 1)|) atTop (nhds 0) := by
    change Tendsto (abs ∘ (fun n : ℕ => u n ^ (n + 1))) atTop (nhds 0)
    simpa only [abs_zero] using ((continuous_abs.tendsto 0).comp ht)
  have heps : 0 < Real.exp (-2 * D) := Real.exp_pos _
  have hsmall :
      ∀ᶠ n : ℕ in atTop, |u n ^ (n + 1)| < Real.exp (-2 * D) :=
    habs0.eventually (isOpen_Iio.mem_nhds heps)
  rcases (hlower.and (hlarge.and hsmall)).exists with
    ⟨n, hn, hN, hsn⟩
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  let s : ℝ := D / (N - D)
  have hNlarge : 2 * D ≤ N := by
    simpa [N] using hN
  have hNpos : 0 < N := by
    dsimp [N]
    positivity
  have hden : 0 < N - D := by
    nlinarith
  have hhalf : D / N ≤ (1 : ℝ) / 2 := by
    apply (div_le_iff₀ hNpos).2
    nlinarith
  have hbase0 : 0 ≤ 1 - D / N := by
    nlinarith
  have hCDiv : C / N ≤ D / N := by
    simp only [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hCD (inv_nonneg.mpr hNpos.le)
  have hubase : 1 - D / N ≤ |u n| := by
    have hcomp : 1 - D / N ≤ 1 - C / N := by
      linarith
    exact hcomp.trans hn
  have hs0 : 0 ≤ s := by
    dsimp [s]
    positivity
  have hident : (1 - D / N) * (1 + s) = 1 := by
    dsimp [s]
    field_simp [ne_of_gt hNpos, ne_of_gt hden] <;> ring
  have hexp : 1 + s ≤ Real.exp s := by
    simpa [add_comm] using Real.add_one_le_exp s
  have hm : 1 ≤ (1 - D / N) * Real.exp s := by
    calc
      1 = (1 - D / N) * (1 + s) := hident.symm
      _ ≤ (1 - D / N) * Real.exp s :=
        mul_le_mul_of_nonneg_left hexp hbase0
  have hexpbase : Real.exp (-s) ≤ 1 - D / N := by
    have hmul :
        Real.exp (-s) * Real.exp s ≤
          (1 - D / N) * Real.exp s := by
      calc
        Real.exp (-s) * Real.exp s = 1 := by
          rw [← Real.exp_add]
          simp
        _ ≤ (1 - D / N) * Real.exp s := hm
    by_contra hle
    have hstrict :
        (1 - D / N) * Real.exp s < Real.exp (-s) * Real.exp s :=
      mul_lt_mul_of_pos_right (lt_of_not_ge hle) (Real.exp_pos s)
    exact (not_lt_of_ge hmul) hstrict
  have hsN : s * N ≤ 2 * D := by
    dsimp [s]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).2
    have hp : 0 ≤ D * (N - 2 * D) :=
      mul_nonneg hD0 (sub_nonneg.mpr hNlarge)
    nlinarith
  have hneg :
      -2 * D ≤ ((n + 1 : ℕ) : ℝ) * (-s) := by
    calc
      -2 * D = -(2 * D) := by ring
      _ ≤ -(s * N) := neg_le_neg hsN
      _ = ((n + 1 : ℕ) : ℝ) * (-s) := by
        dsimp [N]
        ring
  have hfixed :
      Real.exp (-2 * D) ≤ (Real.exp (-s)) ^ (n + 1) := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr hneg
  have hexpu : Real.exp (-s) ≤ |u n| :=
    hexpbase.trans hubase
  have hpow :
      (Real.exp (-s)) ^ (n + 1) ≤ |u n| ^ (n + 1) := by
    gcongr
  rw [abs_pow] at hsn
  exact (not_lt_of_ge (hfixed.trans hpow)) hsn

theorem gap1 (x y : ℝ) (hx : Real.cos x ≠ 0) :
    Tendsto (fun n : ℕ => rootMagnitude x y (n + 1))
      atTop (nhds |Real.tan x|) := by
  have htan := tendsto_tan_shift x y hx
  have habs :
      Tendsto (fun n : ℕ => |Real.tan (x + y / ((n + 1 : ℕ) : ℝ))|)
        atTop (nhds |Real.tan x|) :=
    (continuous_abs.tendsto (Real.tan x)).comp htan
  apply habs.congr'
  filter_upwards with n
  exact (rootMagnitude_succ_eq x y n).symm

theorem gap2 (x : ℝ) (hx : Real.cos x ≠ 0) :
    |Real.tan x| < 1 ↔
      ∃ k : ℤ, |x - (k : ℝ) * Real.pi| < Real.pi / 4 := by
  constructor
  · intro htanx
    let k : ℤ := ⌊x / Real.pi + 1 / 2⌋
    let z : ℝ := x - (k : ℝ) * Real.pi
    have hkfloor : (k : ℝ) ≤ x / Real.pi + 1 / 2 := by
      dsimp [k]
      exact Int.floor_le _
    have hkupper : x / Real.pi + 1 / 2 < (k : ℝ) + 1 := by
      dsimp [k]
      exact Int.lt_floor_add_one _
    have hxpi : x / Real.pi * Real.pi = x := by
      field_simp [ne_of_gt Real.pi_pos]
    have hzlower : -(Real.pi / 2) ≤ z := by
      have hm := mul_le_mul_of_nonneg_right hkfloor Real.pi_pos.le
      dsimp [z]
      nlinarith
    have hzupper : z < Real.pi / 2 := by
      have hm := mul_lt_mul_of_pos_right hkupper Real.pi_pos
      dsimp [z]
      nlinarith
    have hxrepr : x = z + (k : ℝ) * Real.pi := by
      dsimp [z]
      ring
    have hzcos : Real.cos z ≠ 0 := by
      intro hz0
      apply hx
      calc
        Real.cos x = Real.cos (z + (k : ℝ) * Real.pi) :=
          congrArg Real.cos hxrepr
        _ = Real.cos z * Real.cos ((k : ℝ) * Real.pi) -
              Real.sin z * Real.sin ((k : ℝ) * Real.pi) :=
          Real.cos_add z ((k : ℝ) * Real.pi)
        _ = 0 := by simp [hz0, Real.sin_int_mul_pi]
    have hzne : z ≠ -(Real.pi / 2) := by
      intro hzeq
      apply hzcos
      rw [hzeq, Real.cos_neg, Real.cos_pi_div_two]
    have hzlower' : -(Real.pi / 2) < z :=
      lt_of_le_of_ne hzlower (Ne.symm hzne)
    have hzmem : z ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨hzlower', hzupper⟩
    have hperiod :
        Real.tan (z + (k : ℝ) * Real.pi) = Real.tan z := by
      simpa using ((Real.tan_periodic.int_mul k) z)
    have htaneq : Real.tan x = Real.tan z := by
      calc
        Real.tan x = Real.tan (z + (k : ℝ) * Real.pi) :=
          congrArg Real.tan hxrepr
        _ = Real.tan z := hperiod
    refine ⟨k, ?_⟩
    exact (abs_tan_lt_one_iff_of_mem z hzmem).1 (by simpa [htaneq] using htanx)
  · rintro ⟨k, hk⟩
    let z : ℝ := x - (k : ℝ) * Real.pi
    have hzsmall : |z| < Real.pi / 4 := by
      simpa [z] using hk
    have hzabs := abs_lt.mp hzsmall
    have hzmem : z ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith [Real.pi_pos]
    have hxrepr : x = z + (k : ℝ) * Real.pi := by
      dsimp [z]
      ring
    have hperiod :
        Real.tan (z + (k : ℝ) * Real.pi) = Real.tan z := by
      simpa using ((Real.tan_periodic.int_mul k) z)
    have htaneq : Real.tan x = Real.tan z := by
      calc
        Real.tan x = Real.tan (z + (k : ℝ) * Real.pi) :=
          congrArg Real.tan hxrepr
        _ = Real.tan z := hperiod
    rw [htaneq]
    exact (abs_tan_lt_one_iff_of_mem z hzmem).2 hzsmall

theorem gap3 (x y : ℝ) (hcos : Real.cos x ≠ 0) (hx : |Real.tan x| < 1) :
    Summable (fun n : ℕ => |term x y (n + 1)|) := by
  let r : ℝ := (|Real.tan x| + 1) / 2
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr1 : r < 1 := by
    dsimp [r]
    linarith
  have har : |Real.tan x| < r := by
    dsimp [r]
    linarith
  have htan := tendsto_tan_shift x y hcos
  have habs :
      Tendsto (fun n : ℕ => |Real.tan (x + y / ((n + 1 : ℕ) : ℝ))|)
        atTop (nhds |Real.tan x|) :=
    (continuous_abs.tendsto (Real.tan x)).comp htan
  have hev :
      ∀ᶠ n : ℕ in atTop,
        |Real.tan (x + y / ((n + 1 : ℕ) : ℝ))| < r :=
    habs.eventually (isOpen_Iio.mem_nhds har)
  have hev' :
      ∀ᶠ n : ℕ in cofinite,
        |Real.tan (x + y / ((n + 1 : ℕ) : ℝ))| < r := by
    simpa only [Nat.cofinite_eq_atTop] using hev
  have hgeom : Summable (fun n : ℕ => r ^ n) := by
    apply summable_geometric_of_norm_lt_one
    simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  refine hgeom.of_norm_bounded_eventually ?_
  filter_upwards [hev'] with n hn
  have hbound :
      |Real.tan (x + y / ((n + 1 : ℕ) : ℝ))| ^ (n + 1) ≤ r ^ n := by
    calc
      |Real.tan (x + y / ((n + 1 : ℕ) : ℝ))| ^ (n + 1) ≤ r ^ (n + 1) := by
        gcongr
      _ = r ^ n * r := by rw [pow_succ]
      _ ≤ r ^ n := by
        nlinarith [pow_nonneg hr0 n]
  simpa [Real.norm_eq_abs, term, abs_pow,
    abs_of_nonneg (pow_nonneg hr0 n)] using hbound

theorem gap4 (x y : ℝ) (hx0 : Real.cos x ≠ 0) (hx : 1 ≤ |Real.tan x|) :
    ¬ Tendsto (fun n : ℕ => term x y (n + 1)) atTop (nhds 0) := by
  rcases lt_or_eq_of_le hx with hgt | heq
  · intro ht
    have htan := tendsto_tan_shift x y hx0
    have habs :
        Tendsto (fun n : ℕ => |Real.tan (x + y / ((n + 1 : ℕ) : ℝ))|)
          atTop (nhds |Real.tan x|) :=
      (continuous_abs.tendsto (Real.tan x)).comp htan
    have hbase :
        ∀ᶠ n : ℕ in atTop,
          1 < |Real.tan (x + y / ((n + 1 : ℕ) : ℝ))| :=
      habs.eventually (isOpen_Ioi.mem_nhds hgt)
    have htermAbs :
        Tendsto (fun n : ℕ => |term x y (n + 1)|) atTop (nhds 0) := by
      simpa using (continuous_abs.tendsto 0).comp ht
    have hsmall : ∀ᶠ n : ℕ in atTop, |term x y (n + 1)| < 1 :=
      htermAbs.eventually (isOpen_Iio.mem_nhds zero_lt_one)
    rcases (hbase.and hsmall).exists with ⟨n, hn, hs⟩
    rw [term, abs_pow] at hs
    let a : ℝ := |Real.tan (x + y / ((n + 1 : ℕ) : ℝ))|
    have ha0 : 0 ≤ a := abs_nonneg _
    have ha1 : 1 < a := by simpa [a] using hn
    have hpall : ∀ m : ℕ, 1 ≤ a ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ihm =>
          rw [pow_succ]
          nlinarith [pow_nonneg ha0 m]
    have hp := hpall (n + 1)
    dsimp [a] at hp
    linarith
  · have habs : |Real.tan x| = 1 := heq.symm
    have hz :
        Tendsto (fun n : ℕ => x + y / ((n + 1 : ℕ) : ℝ)) atTop (nhds x) :=
      tendsto_shift_argument x y
    have hO :
        (fun z : ℝ => Real.tan z - Real.tan x) =O[nhds x]
          (fun z : ℝ => z - x) :=
      (Real.hasDerivAt_tan hx0).isBigO_sub
    rcases hO.bound with ⟨c, hc⟩
    have hbound :
        ∀ᶠ n : ℕ in atTop,
          |Real.tan (x + y / ((n + 1 : ℕ) : ℝ)) - Real.tan x| ≤
            c * (|y| / |((n + 1 : ℕ) : ℝ)|) := by
      simpa [Real.norm_eq_abs, add_sub_cancel_left, abs_div] using hz.eventually hc
    have hlower :
        ∀ᶠ n : ℕ in atTop,
          1 - (c * |y|) / ((n + 1 : ℕ) : ℝ) ≤
            |Real.tan (x + y / ((n + 1 : ℕ) : ℝ))| := by
      filter_upwards [hbound] with n hn
      have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      rw [abs_of_pos hpos] at hn
      have htri := abs_sub_abs_le_abs_sub
        (Real.tan x) (Real.tan (x + y / ((n + 1 : ℕ) : ℝ)))
      rw [habs] at htri
      have hsymm :
          |Real.tan x - Real.tan (x + y / ((n + 1 : ℕ) : ℝ))| =
            |Real.tan (x + y / ((n + 1 : ℕ) : ℝ)) - Real.tan x| := by
        rw [abs_sub_comm]
      rw [hsymm] at htri
      have hh :
          1 - |Real.tan (x + y / ((n + 1 : ℕ) : ℝ))| ≤
            (c * |y|) / ((n + 1 : ℕ) : ℝ) := by
        calc
          1 - |Real.tan (x + y / ((n + 1 : ℕ) : ℝ))| ≤
              |Real.tan (x + y / ((n + 1 : ℕ) : ℝ)) - Real.tan x| := htri
          _ ≤ c * (|y| / ((n + 1 : ℕ) : ℝ)) := hn
          _ = (c * |y|) / ((n + 1 : ℕ) : ℝ) := by ring
      linarith
    simpa [term] using
      (pow_lower_not_tendsto_zero
        (fun n : ℕ => Real.tan (x + y / ((n + 1 : ℕ) : ℝ)))
        (c * |y|) hlower)

theorem gap5 (x y : ℝ) (hx0 : Real.cos x ≠ 0) (hx : 1 ≤ |Real.tan x|) :
    ¬ Summable (fun n : ℕ => term x y (n + 1)) := by
  intro hs
  exact gap4 x y hx0 hx hs.tendsto_atTop_zero

theorem gap6 (x y : ℝ) (hx : Real.cos x ≠ 0) :
    Summable (fun n : ℕ => term x y (n + 1)) ↔
      ∃ k : ℤ, |x - (k : ℝ) * Real.pi| < Real.pi / 4 := by
  constructor
  · intro hs
    have hlt : |Real.tan x| < 1 := by
      by_contra h
      have hge : 1 ≤ |Real.tan x| := le_of_not_gt h
      exact (gap5 x y hx hge) hs
    exact (gap2 x hx).1 hlt
  · intro hk
    apply Summable.of_norm
    simpa [Real.norm_eq_abs] using
      (gap3 x y hx ((gap2 x hx).2 hk))

end

end ProofGap.Exercise2736
