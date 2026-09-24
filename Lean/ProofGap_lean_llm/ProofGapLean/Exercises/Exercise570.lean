import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise570

noncomputable section

def original (x : ℝ) : ℝ :=
  Real.log ((x + Real.sqrt (x ^ 2 + 1)) / (x + Real.sqrt (x ^ 2 - 1))) /
    Real.log ((x + 1) / (x - 1)) ^ 2
def firstRewrite (x : ℝ) : ℝ :=
  Real.log (1 + (Real.sqrt (x ^ 2 + 1) - Real.sqrt (x ^ 2 - 1)) /
    (x + Real.sqrt (x ^ 2 - 1))) / Real.log (1 + 2 / (x - 1)) ^ 2
def rationalized (x : ℝ) : ℝ :=
  Real.log (1 + 2 / ((x + Real.sqrt (x ^ 2 - 1)) *
    (Real.sqrt (x ^ 2 + 1) + Real.sqrt (x ^ 2 - 1)))) /
    Real.log (1 + 2 / (x - 1)) ^ 2
def reduced (x : ℝ) : ℝ :=
  (x - 1) ^ 2 /
    (2 * (x + Real.sqrt (x ^ 2 - 1)) *
      (Real.sqrt (x ^ 2 + 1) + Real.sqrt (x ^ 2 - 1)))
def normalized (x : ℝ) : ℝ :=
  (1 - 1 / x) ^ 2 /
    (2 * (1 + Real.sqrt (1 - 1 / x ^ 2)) *
      (Real.sqrt (1 + 1 / x ^ 2) + Real.sqrt (1 - 1 / x ^ 2)))
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

/-- Exercise 570, gap 1. -/
private lemma log_one_add_div_tendsto
    {u : ℝ → ℝ}
    (hu : Filter.Tendsto u Filter.atTop (nhds 0))
    (hu0 : ∀ᶠ x in Filter.atTop, u x ≠ 0) :
    Filter.Tendsto (fun x => Real.log (1 + u x) / u x)
      Filter.atTop (nhds 1) := by
  have hadd :
      Filter.Tendsto (fun x => 1 + u x) Filter.atTop (nhds (1 : ℝ)) := by
    simpa using
      ((tendsto_const_nhds.add hu) :
        Filter.Tendsto (fun x => (1 : ℝ) + u x)
          Filter.atTop (nhds (1 + 0)))
  have hmem :
      ∀ᶠ x in Filter.atTop, (1 + u x) ∈ ({1}ᶜ : Set ℝ) := by
    filter_upwards [hu0] with x hx
    simpa using hx
  have hpunct :
      Filter.Tendsto (fun x => 1 + u x) Filter.atTop
        (nhdsWithin (1 : ℝ) ({1}ᶜ : Set ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hadd, hmem⟩
  have hslope :=
    (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto_slope
  have hcomp := hslope.comp hpunct
  simpa [Function.comp_def, slope, Real.log_one, div_eq_mul_inv, mul_comm]
    using hcomp

theorem gap1 (L : ℝ) :
    HasLimitAtPosInfinity original L ↔ HasLimitAtPosInfinity firstRewrite L := by
  unfold HasLimitAtPosInfinity
  have heq : original =ᶠ[Filter.atTop] firstRewrite := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hbase : x + Real.sqrt (x ^ 2 - 1) ≠ 0 := by
      have hs := Real.sqrt_nonneg (x ^ 2 - 1)
      nlinarith
    have hx1 : x - 1 ≠ 0 := by linarith
    have harg₁ :
        (x + Real.sqrt (x ^ 2 + 1)) /
            (x + Real.sqrt (x ^ 2 - 1)) =
          1 + (Real.sqrt (x ^ 2 + 1) - Real.sqrt (x ^ 2 - 1)) /
            (x + Real.sqrt (x ^ 2 - 1)) := by
      field_simp [hbase] <;> ring
    have harg₂ : (x + 1) / (x - 1) = 1 + 2 / (x - 1) := by
      field_simp [hx1] <;> ring
    unfold original firstRewrite
    rw [harg₁, harg₂]
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Exercise 570, gap 2. -/
theorem gap2 (L : ℝ) :
    HasLimitAtPosInfinity rationalized L ↔ HasLimitAtPosInfinity reduced L := by
  unfold HasLimitAtPosInfinity
  let u : ℝ → ℝ := fun x =>
    2 / ((x + Real.sqrt (x ^ 2 - 1)) *
      (Real.sqrt (x ^ 2 + 1) + Real.sqrt (x ^ 2 - 1)))
  let v : ℝ → ℝ := fun x => 2 / (x - 1)
  let q : ℝ → ℝ := fun x =>
    (Real.log (1 + u x) / u x) /
      (Real.log (1 + v x) / v x) ^ 2
  have hshift :
      Filter.Tendsto (fun x : ℝ => x - 1) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [Filter.eventually_ge_atTop (b + 1)] with x hx
    linarith
  have hinv_shift :
      Filter.Tendsto (fun x : ℝ => (x - 1)⁻¹)
        Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hshift
  have hlower0 : Filter.Tendsto v Filter.atTop (nhds 0) := by
    have htwo :
        Filter.Tendsto (fun _ : ℝ => (2 : ℝ)) Filter.atTop (nhds 2) :=
      tendsto_const_nhds
    simpa [v, div_eq_mul_inv] using htwo.mul hinv_shift
  have hd₁top :
      Filter.Tendsto (fun x : ℝ => x + Real.sqrt (x ^ 2 - 1))
        Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with x hx
    exact le_trans hx (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  have hd₂top :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.sqrt (x ^ 2 + 1) + Real.sqrt (x ^ 2 - 1))
        Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [Filter.eventually_ge_atTop b,
      Filter.eventually_gt_atTop (1 : ℝ)] with x hxb hx
    have hp0 : 0 ≤ x ^ 2 + 1 := by nlinarith [sq_nonneg x]
    have hsquare : (Real.sqrt (x ^ 2 + 1)) ^ 2 = x ^ 2 + 1 :=
      Real.sq_sqrt hp0
    have hsplus : x ≤ Real.sqrt (x ^ 2 + 1) := by
      have hsnonneg := Real.sqrt_nonneg (x ^ 2 + 1)
      nlinarith
    have hsminus := Real.sqrt_nonneg (x ^ 2 - 1)
    nlinarith
  have hinv₁ :
      Filter.Tendsto
        (fun x : ℝ => (x + Real.sqrt (x ^ 2 - 1))⁻¹)
        Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hd₁top
  have hinv₂ :
      Filter.Tendsto
        (fun x : ℝ =>
          (Real.sqrt (x ^ 2 + 1) + Real.sqrt (x ^ 2 - 1))⁻¹)
        Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hd₂top
  have hupper0 : Filter.Tendsto u Filter.atTop (nhds 0) := by
    have htwo :
        Filter.Tendsto (fun _ : ℝ => (2 : ℝ)) Filter.atTop (nhds 2) :=
      tendsto_const_nhds
    have h := (htwo.mul hinv₁).mul hinv₂
    simpa [u, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  have hpositive : ∀ᶠ x in Filter.atTop, 0 < u x ∧ 0 < v x := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hd₁ : 0 < x + Real.sqrt (x ^ 2 - 1) := by
      have hs := Real.sqrt_nonneg (x ^ 2 - 1)
      nlinarith
    have hd₂ :
        0 < Real.sqrt (x ^ 2 + 1) + Real.sqrt (x ^ 2 - 1) := by
      have hsplus : 0 < Real.sqrt (x ^ 2 + 1) :=
        Real.sqrt_pos.2 (by nlinarith [sq_nonneg x])
      have hsminus := Real.sqrt_nonneg (x ^ 2 - 1)
      nlinarith
    dsimp [u, v]
    exact ⟨div_pos (by norm_num) (mul_pos hd₁ hd₂),
      div_pos (by norm_num) (sub_pos.mpr hx)⟩
  have hlog_upper :
      Filter.Tendsto (fun x => Real.log (1 + u x) / u x)
        Filter.atTop (nhds 1) :=
    log_one_add_div_tendsto hupper0
      (hpositive.mono fun _ h => h.1.ne')
  have hlog_lower :
      Filter.Tendsto (fun x => Real.log (1 + v x) / v x)
        Filter.atTop (nhds 1) :=
    log_one_add_div_tendsto hlower0
      (hpositive.mono fun _ h => h.2.ne')
  have hq : Filter.Tendsto q Filter.atTop (nhds 1) := by
    have h := hlog_upper.div (hlog_lower.pow 2)
      (by norm_num : (1 : ℝ) ^ 2 ≠ 0)
    simpa [q] using h
  have hupper_eq :
      u =ᶠ[Filter.atTop] fun x => reduced x * (v x) ^ 2 := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hd₁ : x + Real.sqrt (x ^ 2 - 1) ≠ 0 := by
      have hs := Real.sqrt_nonneg (x ^ 2 - 1)
      nlinarith
    have hd₂ :
        Real.sqrt (x ^ 2 + 1) + Real.sqrt (x ^ 2 - 1) ≠ 0 := by
      have hsplus : 0 < Real.sqrt (x ^ 2 + 1) :=
        Real.sqrt_pos.2 (by nlinarith [sq_nonneg x])
      have hsminus := Real.sqrt_nonneg (x ^ 2 - 1)
      nlinarith
    have hx1 : x - 1 ≠ 0 := by linarith
    dsimp [u, v]
    unfold reduced
    field_simp [hd₁, hd₂, hx1] <;> ring
  have factor_identity :
      ∀ {a b r A B : ℝ},
        a = r * b ^ 2 → a ≠ 0 → b ≠ 0 → B ≠ 0 →
          A / B ^ 2 = r * ((A / a) / (B / b) ^ 2) := by
    intro a b r A B ha ha0 hb0 hB0
    have hr0 : r ≠ 0 := by
      intro hr
      apply ha0
      calc
        a = r * b ^ 2 := ha
        _ = 0 := by simp [hr]
    rw [ha]
    field_simp [hr0, hb0, hB0] <;> ring
  have hrat_eq :
      rationalized =ᶠ[Filter.atTop] fun x => reduced x * q x := by
    filter_upwards [hupper_eq, hpositive] with x haeq hpos
    have hlogne : Real.log (1 + v x) ≠ 0 :=
      (Real.log_pos (by linarith [hpos.2])).ne'
    simpa [rationalized, q, u, v] using
      (factor_identity
        (a := u x) (b := v x) (r := reduced x)
        (A := Real.log (1 + u x)) (B := Real.log (1 + v x))
        haeq hpos.1.ne' hpos.2.ne' hlogne)
  have hqpos : ∀ᶠ x in Filter.atTop, 0 < q x := by
    filter_upwards [hpositive] with x hpos
    have huLog : 0 < Real.log (1 + u x) :=
      Real.log_pos (by linarith [hpos.1])
    have hvLog : 0 < Real.log (1 + v x) :=
      Real.log_pos (by linarith [hpos.2])
    dsimp [q]
    exact div_pos (div_pos huLog hpos.1)
      (sq_pos_of_pos (div_pos hvLog hpos.2))
  constructor
  · intro hrat
    have hdiv := hrat.div hq (by norm_num : (1 : ℝ) ≠ 0)
    have hdiv' :
        Filter.Tendsto (fun x => rationalized x / q x)
          Filter.atTop (nhds L) := by
      simpa using hdiv
    have heqdiv :
        (fun x => rationalized x / q x) =ᶠ[Filter.atTop] reduced := by
      filter_upwards [hrat_eq, hqpos] with x he hqp
      rw [he]
      field_simp [hqp.ne'] <;> ring
    exact hdiv'.congr' heqdiv
  · intro hred
    have hmul := hred.mul hq
    have hmul' :
        Filter.Tendsto (fun x => reduced x * q x)
          Filter.atTop (nhds L) := by
      simpa using hmul
    exact hmul'.congr' hrat_eq.symm

/-- Exercise 570, gap 3. -/
theorem gap3 (L : ℝ) :
    HasLimitAtPosInfinity reduced L ↔ HasLimitAtPosInfinity normalized L := by
  unfold HasLimitAtPosInfinity
  have heq : reduced =ᶠ[Filter.atTop] normalized := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hxne : x ≠ 0 := ne_of_gt hx0
    have hm0 : 0 ≤ x ^ 2 - 1 := by nlinarith
    have hp0 : 0 ≤ x ^ 2 + 1 := by nlinarith [sq_nonneg x]
    have him : 0 ≤ 1 - 1 / x ^ 2 := by
      rw [show 1 - 1 / x ^ 2 = (x ^ 2 - 1) / x ^ 2 by
        field_simp [hxne] <;> ring]
      exact div_nonneg hm0 (sq_nonneg x)
    have hip : 0 ≤ 1 + 1 / x ^ 2 := by
      rw [show 1 + 1 / x ^ 2 = (x ^ 2 + 1) / x ^ 2 by
        field_simp [hxne] <;> ring]
      exact div_nonneg hp0 (sq_nonneg x)
    have hm :
        x * Real.sqrt (1 - 1 / x ^ 2) = Real.sqrt (x ^ 2 - 1) := by
      have hsquare :
          (x * Real.sqrt (1 - 1 / x ^ 2)) ^ 2 =
            (Real.sqrt (x ^ 2 - 1)) ^ 2 := by
        calc
          (x * Real.sqrt (1 - 1 / x ^ 2)) ^ 2 =
              x ^ 2 * (Real.sqrt (1 - 1 / x ^ 2)) ^ 2 := by ring
          _ = x ^ 2 * (1 - 1 / x ^ 2) := by rw [Real.sq_sqrt him]
          _ = x ^ 2 - 1 := by field_simp [hxne]
          _ = (Real.sqrt (x ^ 2 - 1)) ^ 2 := (Real.sq_sqrt hm0).symm
      have hleft : 0 ≤ x * Real.sqrt (1 - 1 / x ^ 2) :=
        mul_nonneg (le_of_lt hx0) (Real.sqrt_nonneg _)
      have hright := Real.sqrt_nonneg (x ^ 2 - 1)
      nlinarith
    have hp :
        x * Real.sqrt (1 + 1 / x ^ 2) = Real.sqrt (x ^ 2 + 1) := by
      have hsquare :
          (x * Real.sqrt (1 + 1 / x ^ 2)) ^ 2 =
            (Real.sqrt (x ^ 2 + 1)) ^ 2 := by
        calc
          (x * Real.sqrt (1 + 1 / x ^ 2)) ^ 2 =
              x ^ 2 * (Real.sqrt (1 + 1 / x ^ 2)) ^ 2 := by ring
          _ = x ^ 2 * (1 + 1 / x ^ 2) := by rw [Real.sq_sqrt hip]
          _ = x ^ 2 + 1 := by field_simp [hxne]
          _ = (Real.sqrt (x ^ 2 + 1)) ^ 2 := (Real.sq_sqrt hp0).symm
      have hleft : 0 ≤ x * Real.sqrt (1 + 1 / x ^ 2) :=
        mul_nonneg (le_of_lt hx0) (Real.sqrt_nonneg _)
      have hright := Real.sqrt_nonneg (x ^ 2 + 1)
      nlinarith
    have hfac₁ : 1 + Real.sqrt (1 - 1 / x ^ 2) ≠ 0 := by
      have hs := Real.sqrt_nonneg (1 - 1 / x ^ 2)
      nlinarith
    have hfac₂ :
        Real.sqrt (1 + 1 / x ^ 2) +
            Real.sqrt (1 - 1 / x ^ 2) ≠ 0 := by
      have hsplus : 0 < Real.sqrt (1 + 1 / x ^ 2) :=
        Real.sqrt_pos.2 (by
          have hnonneg : 0 ≤ 1 / x ^ 2 :=
            div_nonneg (by norm_num) (sq_nonneg x)
          linarith)
      have hsminus := Real.sqrt_nonneg (1 - 1 / x ^ 2)
      nlinarith
    unfold reduced normalized
    rw [← hp, ← hm]
    field_simp [hxne, hfac₁, hfac₂] <;> ring
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Exercise 570, gap 4. -/
theorem gap4 : HasLimitAtPosInfinity normalized (1 / 8) := by
  unfold HasLimitAtPosInfinity
  have hinv : Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero :
        Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0))
  have hinv_sq :
      Filter.Tendsto (fun x : ℝ => 1 / x ^ 2) Filter.atTop (nhds 0) := by
    simpa [one_div] using hinv.pow 2
  have hone :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have hsminus :
      Filter.Tendsto
        (fun x : ℝ => Real.sqrt (1 - 1 / x ^ 2))
        Filter.atTop (nhds 1) := by
    simpa using
      Real.continuous_sqrt.continuousAt.tendsto.comp (hone.sub hinv_sq)
  have hsplus :
      Filter.Tendsto
        (fun x : ℝ => Real.sqrt (1 + 1 / x ^ 2))
        Filter.atTop (nhds 1) := by
    simpa using
      Real.continuous_sqrt.continuousAt.tendsto.comp (hone.add hinv_sq)
  have hnum :
      Filter.Tendsto (fun x : ℝ => (1 - 1 / x) ^ 2)
        Filter.atTop (nhds 1) := by
    simpa using (hone.sub hinv).pow 2
  have hden_raw :=
    ((tendsto_const_nhds.mul (hone.add hsminus)).mul
      (hsplus.add hsminus) :
      Filter.Tendsto
        (fun x : ℝ =>
          2 * (1 + Real.sqrt (1 - 1 / x ^ 2)) *
            (Real.sqrt (1 + 1 / x ^ 2) +
              Real.sqrt (1 - 1 / x ^ 2)))
        Filter.atTop (nhds (2 * (1 + 1) * (1 + 1))))
  have hden :
      Filter.Tendsto
        (fun x : ℝ =>
          2 * (1 + Real.sqrt (1 - 1 / x ^ 2)) *
            (Real.sqrt (1 + 1 / x ^ 2) +
              Real.sqrt (1 - 1 / x ^ 2)))
        Filter.atTop (nhds 8) := by
    norm_num at hden_raw ⊢
    exact hden_raw
  have hquot := hnum.div hden (by norm_num : (8 : ℝ) ≠ 0)
  change Filter.Tendsto
    (fun x : ℝ =>
      (1 - 1 / x) ^ 2 /
        (2 * (1 + Real.sqrt (1 - 1 / x ^ 2)) *
          (Real.sqrt (1 + 1 / x ^ 2) +
            Real.sqrt (1 - 1 / x ^ 2))))
    Filter.atTop (nhds (1 / 8 : ℝ))
  norm_num at hquot ⊢
  exact hquot

/-- Exercise 570, gap 5. -/
theorem gap5 : HasLimitAtPosInfinity rationalized (1 / 8) := by
  exact (gap2 (1 / 8)).2 ((gap3 (1 / 8)).2 gap4)

end

end ProofGap.Exercise570
