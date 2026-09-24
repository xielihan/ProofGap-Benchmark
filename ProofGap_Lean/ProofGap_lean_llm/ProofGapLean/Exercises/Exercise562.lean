import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise562

noncomputable section

def original (x : ℝ) : ℝ :=
  Real.log (1 + Real.rpow 2 x) * Real.log (1 + 3 / x)
def normalized (x : ℝ) : ℝ :=
  (Real.log (1 + 3 / x) / (3 / x)) *
    ((x * Real.log 2 + Real.log (Real.rpow 2 (-x) + 1)) / (x / 3))
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

/-- Exercise 562, gap 1. -/
private theorem original_eq_normalized_of_pos {x : ℝ} (hx : 0 < x) :
    original x = normalized x := by
  unfold original normalized
  have hp : 0 < Real.rpow 2 x :=
    Real.rpow_pos_of_pos (by norm_num) x
  have hprod : Real.rpow 2 x * Real.rpow 2 (-x) = 1 := by
    calc
      Real.rpow 2 x * Real.rpow 2 (-x) =
          Real.rpow 2 (x + (-x)) :=
        (Real.rpow_add (by norm_num : (0 : ℝ) < 2) x (-x)).symm
      _ = 1 := by norm_num
  have hfactor :
      Real.rpow 2 x * (Real.rpow 2 (-x) + 1) =
        1 + Real.rpow 2 x := by
    calc
      Real.rpow 2 x * (Real.rpow 2 (-x) + 1) =
          Real.rpow 2 x * Real.rpow 2 (-x) + Real.rpow 2 x := by ring
      _ = 1 + Real.rpow 2 x := by rw [hprod]
  have hlogpow :
      Real.log (Real.rpow 2 x) = x * Real.log 2 := by
    simpa using Real.log_rpow (by norm_num : (0 : ℝ) < 2) x
  have hq : 0 < Real.rpow 2 (-x) + 1 := by
    have hn : 0 < Real.rpow 2 (-x) :=
      Real.rpow_pos_of_pos (by norm_num) (-x)
    linarith
  have hlog :
      Real.log (1 + Real.rpow 2 x) =
        x * Real.log 2 + Real.log (Real.rpow 2 (-x) + 1) := by
    calc
      Real.log (1 + Real.rpow 2 x) =
          Real.log (Real.rpow 2 x * (Real.rpow 2 (-x) + 1)) := by
            rw [hfactor]
      _ = Real.log (Real.rpow 2 x) +
          Real.log (Real.rpow 2 (-x) + 1) := by
            rw [Real.log_mul hp.ne' hq.ne']
      _ = x * Real.log 2 + Real.log (Real.rpow 2 (-x) + 1) := by
            rw [hlogpow]
  rw [hlog]
  field_simp [hx.ne']

theorem gap1 (L : ℝ) :
    HasLimitAtPosInfinity original L ↔ HasLimitAtPosInfinity normalized L := by
  unfold HasLimitAtPosInfinity
  have heq : ∀ᶠ x : ℝ in Filter.atTop, original x = normalized x := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    apply original_eq_normalized_of_pos
    linarith
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' (heq.mono fun x hx => hx.symm)

/-- Exercise 562, gap 2. -/
theorem gap2 : HasLimitAtPosInfinity normalized (3 * Real.log 2) := by
  unfold HasLimitAtPosInfinity
  have hi : Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have ht0 :
      Filter.Tendsto (fun x : ℝ => 3 / x) Filter.atTop (nhds 0) := by
    have hc :
        Filter.Tendsto (fun _ : ℝ => (3 : ℝ)) Filter.atTop (nhds 3) :=
      tendsto_const_nhds
    simpa [div_eq_mul_inv] using hc.mul hi
  have htne : ∀ᶠ x : ℝ in Filter.atTop, 3 / x ≠ 0 := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : x ≠ 0 := by linarith
    exact div_ne_zero (by norm_num) hx0
  have ht1nhds :
      Filter.Tendsto (fun x : ℝ => 1 + 3 / x) Filter.atTop (nhds 1) := by
    have hc :
        Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) :=
      tendsto_const_nhds
    simpa using hc.add ht0
  have ht1 :
      Filter.Tendsto (fun x : ℝ => 1 + 3 / x) Filter.atTop
        (nhdsWithin (1 : ℝ) ({1} : Set ℝ)ᶜ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨ht1nhds, ?_⟩
    filter_upwards [htne] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro heq
    apply hx
    linarith
  have hA :
      Filter.Tendsto
        (fun x : ℝ => Real.log (1 + 3 / x) / (3 / x))
        Filter.atTop (nhds 1) := by
    have hs :=
      (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto_slope.comp ht1
    have hs' :
        Filter.Tendsto
          (slope Real.log 1 ∘ fun x : ℝ => 1 + 3 / x)
          Filter.atTop (nhds 1) := by
      simpa using hs
    apply hs'.congr'
    filter_upwards with x
    simp [Function.comp_apply, slope, div_eq_mul_inv, mul_comm]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp :
      Filter.Tendsto (fun x : ℝ => Real.log 2 * (-x)) Filter.atTop Filter.atBot := by
    refine Filter.tendsto_atBot.2 ?_
    intro b
    filter_upwards [Filter.eventually_ge_atTop (-b / Real.log 2)] with x hx
    have hmul : -b ≤ x * Real.log 2 := by
      calc
        -b = (-b / Real.log 2) * Real.log 2 := by
          field_simp [hlog2.ne']
        _ ≤ x * Real.log 2 := mul_le_mul_of_nonneg_right hx hlog2.le
    nlinarith
  have hpExp :
      Filter.Tendsto
        (fun x : ℝ => Real.exp (Real.log 2 * (-x)))
        Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hexp
  have hpEq :
      (fun x : ℝ => Real.exp (Real.log 2 * (-x))) =ᶠ[Filter.atTop]
        (fun x : ℝ => Real.rpow 2 (-x)) := by
    filter_upwards with x
    exact (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (-x)).symm
  have hp :
      Filter.Tendsto (fun x : ℝ => Real.rpow 2 (-x))
        Filter.atTop (nhds 0) :=
    hpExp.congr' hpEq
  have hp1 :
      Filter.Tendsto (fun x : ℝ => Real.rpow 2 (-x) + 1)
        Filter.atTop (nhds 1) := by
    have hc :
        Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) :=
      tendsto_const_nhds
    simpa using hp.add hc
  have hl :
      Filter.Tendsto
        (fun x : ℝ => Real.log (Real.rpow 2 (-x) + 1))
        Filter.atTop (nhds 0) := by
    have hc : ContinuousAt Real.log (1 : ℝ) :=
      Real.continuousAt_log (by norm_num)
    simpa using hc.tendsto.comp hp1
  have hsmall :
      Filter.Tendsto
        (fun x : ℝ => Real.log (Real.rpow 2 (-x) + 1) / x)
        Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hl.mul hi
  have hBsimple :
      Filter.Tendsto
        (fun x : ℝ =>
          3 * Real.log 2 +
            3 * (Real.log (Real.rpow 2 (-x) + 1) / x))
        Filter.atTop (nhds (3 * Real.log 2)) := by
    have hcmain :
        Filter.Tendsto (fun _ : ℝ => 3 * Real.log 2)
          Filter.atTop (nhds (3 * Real.log 2)) :=
      tendsto_const_nhds
    have hc3 :
        Filter.Tendsto (fun _ : ℝ => (3 : ℝ)) Filter.atTop (nhds 3) :=
      tendsto_const_nhds
    simpa using hcmain.add (hc3.mul hsmall)
  have hB :
      Filter.Tendsto
        (fun x : ℝ =>
          (x * Real.log 2 + Real.log (Real.rpow 2 (-x) + 1)) / (x / 3))
        Filter.atTop (nhds (3 * Real.log 2)) := by
    apply hBsimple.congr'
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : x ≠ 0 := by linarith
    field_simp [hx0] <;> ring
  simpa [normalized] using hA.mul hB

/-- Exercise 562, gap 3. -/
theorem gap3 : 3 * Real.log 2 = Real.log 8 := by
  calc
    3 * Real.log 2 = Real.log ((2 : ℝ) ^ 3) :=
      (Real.log_pow (2 : ℝ) 3).symm
    _ = Real.log 8 := by
      congr 1
      norm_num

/-- Exercise 562, gap 4. -/
theorem gap4 : HasLimitAtPosInfinity original (Real.log 8) := by
  rw [← gap3]
  exact (gap1 (3 * Real.log 2)).mpr gap2

end

end ProofGap.Exercise562
