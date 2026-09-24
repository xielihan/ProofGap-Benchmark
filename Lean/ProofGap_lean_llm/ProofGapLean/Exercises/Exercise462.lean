import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise462

noncomputable section

def cbrt (x : ℝ) : ℝ := Real.rpow x (1 / 3 : ℝ)
def sixthRoot (x : ℝ) : ℝ := Real.rpow x (1 / 6 : ℝ)
def u (x : ℝ) : ℝ := cbrt (x ^ 3 + 3 * x ^ 2)
def v (x : ℝ) : ℝ := Real.sqrt (x ^ 2 - 2 * x)
def original (x : ℝ) : ℝ := u x - v x
def denominator (x : ℝ) : ℝ :=
  (Finset.range 6).sum (fun k => (u x) ^ (5 - k) * (v x) ^ k)
def rationalized (x : ℝ) : ℝ :=
  ((x ^ 3 + 3 * x ^ 2) ^ 2 - (x ^ 2 - 2 * x) ^ 3) / denominator x
def normalizedDenominator (x : ℝ) : ℝ :=
  denominator x / x ^ 5
def normalized (x : ℝ) : ℝ :=
  (12 - 3 / x + 8 / x ^ 2) / normalizedDenominator x
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

/-- Source: `proof_gap/exercise_462/1.txt`; replace the six-term ellipsis by a finite sum. -/
private theorem eventualRootData :
    ∀ᶠ x : ℝ in Filter.atTop,
      2 < x ∧
      0 < u x ∧
      0 ≤ v x ∧
      u x ^ 3 = x ^ 3 + 3 * x ^ 2 ∧
      v x ^ 2 = x ^ 2 - 2 * x ∧
      0 < denominator x := by
  filter_upwards [Filter.eventually_gt_atTop (2 : ℝ)] with x hx
  have hxpos : 0 < x := lt_trans (by norm_num) hx
  have hA : 0 < x ^ 3 + 3 * x ^ 2 := by positivity
  have hB : 0 < x ^ 2 - 2 * x := by
    have hp : 0 < x * (x - 2) := mul_pos hxpos (sub_pos.mpr hx)
    nlinarith
  have hu : 0 < u x := by
    exact Real.rpow_pos_of_pos hA _
  have hv : 0 ≤ v x := Real.sqrt_nonneg _
  have hu3 : u x ^ 3 = x ^ 3 + 3 * x ^ 2 := by
    unfold u cbrt
    calc
      (Real.rpow (x ^ 3 + 3 * x ^ 2) (1 / 3 : ℝ)) ^ 3 =
          Real.rpow (Real.rpow (x ^ 3 + 3 * x ^ 2) (1 / 3 : ℝ)) (3 : ℝ) := by
            rw [← Real.rpow_natCast (n := 3)]
            norm_num
      _ = Real.rpow (x ^ 3 + 3 * x ^ 2) ((1 / 3 : ℝ) * 3) := by
            exact (Real.rpow_mul hA.le (1 / 3 : ℝ) (3 : ℝ)).symm
      _ = x ^ 3 + 3 * x ^ 2 := by norm_num
  have hv2 : v x ^ 2 = x ^ 2 - 2 * x := by
    unfold v
    exact Real.sq_sqrt hB.le
  have hden : 0 < denominator x := by
    norm_num [denominator, Finset.sum_range_succ] <;> positivity
  exact ⟨hx, hu, hv, hu3, hv2, hden⟩

theorem gap1 (L : ℝ) :
    HasLimitAtPosInfinity original L ↔ HasLimitAtPosInfinity rationalized L := by
  have hEq : original =ᶠ[Filter.atTop] rationalized := by
    filter_upwards [eventualRootData] with x hx
    rcases hx with ⟨_, _, _, hu3, hv2, hden⟩
    have hu6 : u x ^ 6 = (x ^ 3 + 3 * x ^ 2) ^ 2 := by
      calc
        u x ^ 6 = (u x ^ 3) ^ 2 := by ring
        _ = (x ^ 3 + 3 * x ^ 2) ^ 2 := by rw [hu3]
    have hv6 : v x ^ 6 = (x ^ 2 - 2 * x) ^ 3 := by
      calc
        v x ^ 6 = (v x ^ 2) ^ 3 := by ring
        _ = (x ^ 2 - 2 * x) ^ 3 := by rw [hv2]
    have hfactor :
        original x * denominator x = u x ^ 6 - v x ^ 6 := by
      simp [original, denominator, Finset.sum_range_succ] <;> ring
    have hnum :
        original x * denominator x =
          (x ^ 3 + 3 * x ^ 2) ^ 2 - (x ^ 2 - 2 * x) ^ 3 := by
      calc
        original x * denominator x = u x ^ 6 - v x ^ 6 := hfactor
        _ = (x ^ 3 + 3 * x ^ 2) ^ 2 - (x ^ 2 - 2 * x) ^ 3 := by
          rw [hu6, hv6]
    unfold rationalized
    exact (eq_div_iff hden.ne').2 hnum
  constructor
  · intro h
    exact h.congr' hEq
  · intro h
    exact h.congr' hEq.symm

/-- Source: `proof_gap/exercise_462/2.txt`; divide numerator and denominator by `x^5`. -/
theorem gap2 (L : ℝ) :
    HasLimitAtPosInfinity rationalized L ↔ HasLimitAtPosInfinity normalized L := by
  have hEq : rationalized =ᶠ[Filter.atTop] normalized := by
    filter_upwards [eventualRootData] with x hx
    rcases hx with ⟨hx, _, _, _, _, hden⟩
    have hxpos : 0 < x := lt_trans (by norm_num) hx
    unfold rationalized normalized normalizedDenominator
    field_simp [hden.ne', hxpos.ne'] <;> ring
  constructor
  · intro h
    exact h.congr' hEq
  · intro h
    exact h.congr' hEq.symm

/-- Source: `proof_gap/exercise_462/3.txt`. -/
theorem gap3 : HasLimitAtPosInfinity normalized 2 := by
  have hinv :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hc1 :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have hc2 :
      Filter.Tendsto (fun _ : ℝ => (2 : ℝ)) Filter.atTop (nhds 2) :=
    tendsto_const_nhds
  have hc3 :
      Filter.Tendsto (fun _ : ℝ => (3 : ℝ)) Filter.atTop (nhds 3) :=
    tendsto_const_nhds
  have hc8 :
      Filter.Tendsto (fun _ : ℝ => (8 : ℝ)) Filter.atTop (nhds 8) :=
    tendsto_const_nhds
  have hc12 :
      Filter.Tendsto (fun _ : ℝ => (12 : ℝ)) Filter.atTop (nhds 12) :=
    tendsto_const_nhds
  have hplus :
      Filter.Tendsto (fun x : ℝ => 1 + 3 / x) Filter.atTop (nhds 1) := by
    simpa [div_eq_mul_inv] using hc1.add (hc3.mul hinv)
  have hminus :
      Filter.Tendsto (fun x : ℝ => 1 - 2 / x) Filter.atTop (nhds 1) := by
    simpa [div_eq_mul_inv] using hc1.sub (hc2.mul hinv)
  have huBounds :
      ∀ᶠ x : ℝ in Filter.atTop,
        1 ≤ u x / x ∧ u x / x ≤ 1 + 3 / x := by
    filter_upwards [eventualRootData] with x hx
    rcases hx with ⟨hx, hu, _, hu3, _, _⟩
    have hxpos : 0 < x := lt_trans (by norm_num) hx
    let a : ℝ := u x / x
    have ha0 : 0 ≤ a := by
      dsimp [a]
      positivity
    have ha3 : a ^ 3 = 1 + 3 / x := by
      dsimp [a]
      calc
        (u x / x) ^ 3 = u x ^ 3 / x ^ 3 := by rw [div_pow]
        _ = (x ^ 3 + 3 * x ^ 2) / x ^ 3 := by rw [hu3]
        _ = 1 + 3 / x := by
          field_simp [hxpos.ne'] <;> ring
    have hfac : 1 ≤ a ^ 2 + a + 1 := by
      nlinarith [sq_nonneg a]
    have ha1 : 1 ≤ a := by
      by_contra h
      have halt : a < 1 := lt_of_not_ge h
      have hp : 0 < (1 - a) * (a ^ 2 + a + 1) :=
        mul_pos (sub_pos.mpr halt) (lt_of_lt_of_le zero_lt_one hfac)
      have hid : 1 - a ^ 3 = (1 - a) * (a ^ 2 + a + 1) := by ring
      have hd : 0 < 3 / x := div_pos (by norm_num) hxpos
      nlinarith
    have hmul :
        0 ≤ (a - 1) * ((a ^ 2 + a + 1) - 1) :=
      mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hfac)
    have hid : a ^ 3 - 1 = (a - 1) * (a ^ 2 + a + 1) := by ring
    have haup : a ≤ 1 + 3 / x := by
      nlinarith
    exact ⟨ha1, haup⟩
  have hvBounds :
      ∀ᶠ x : ℝ in Filter.atTop,
        1 - 2 / x ≤ v x / x ∧ v x / x ≤ 1 := by
    filter_upwards [eventualRootData] with x hx
    rcases hx with ⟨hx, _, hv, _, hv2, _⟩
    have hxpos : 0 < x := lt_trans (by norm_num) hx
    let b : ℝ := v x / x
    have hb0 : 0 ≤ b := by
      dsimp [b]
      positivity
    have hb2 : b ^ 2 = 1 - 2 / x := by
      dsimp [b]
      calc
        (v x / x) ^ 2 = v x ^ 2 / x ^ 2 := by rw [div_pow]
        _ = (x ^ 2 - 2 * x) / x ^ 2 := by rw [hv2]
        _ = 1 - 2 / x := by
          field_simp [hxpos.ne'] <;> ring
    have hble : b ≤ 1 := by
      by_contra h
      have hgt : 1 < b := lt_of_not_ge h
      have hp : 0 < (b - 1) * (b + 1) := by
        apply mul_pos (sub_pos.mpr hgt)
        nlinarith
      have hid : b ^ 2 - 1 = (b - 1) * (b + 1) := by ring
      have hd : 0 < 2 / x := div_pos (by norm_num) hxpos
      nlinarith
    have hmul : 0 ≤ b * (1 - b) :=
      mul_nonneg hb0 (sub_nonneg.mpr hble)
    have hid : b - b ^ 2 = b * (1 - b) := by ring
    have hlow : 1 - 2 / x ≤ b := by
      nlinarith
    exact ⟨hlow, hble⟩
  have huLimit :
      Filter.Tendsto (fun x : ℝ => u x / x) Filter.atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hc1 hplus
      (huBounds.mono fun _ h => h.1)
      (huBounds.mono fun _ h => h.2)
  have hvLimit :
      Filter.Tendsto (fun x : ℝ => v x / x) Filter.atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hminus hc1
      (hvBounds.mono fun _ h => h.1)
      (hvBounds.mono fun _ h => h.2)
  have hdenEq :
      normalizedDenominator =ᶠ[Filter.atTop]
        (fun x : ℝ =>
          (u x / x) ^ 5 +
          (u x / x) ^ 4 * (v x / x) +
          (u x / x) ^ 3 * (v x / x) ^ 2 +
          (u x / x) ^ 2 * (v x / x) ^ 3 +
          (u x / x) * (v x / x) ^ 4 +
          (v x / x) ^ 5) := by
    filter_upwards [eventualRootData] with x hx
    rcases hx with ⟨hx, _, _, _, _, _⟩
    have hxpos : 0 < x := lt_trans (by norm_num) hx
    simp [normalizedDenominator, denominator, Finset.sum_range_succ]
      <;> field_simp [hxpos.ne'] <;> ring
  have hsum :
      Filter.Tendsto
        (fun x : ℝ =>
          (u x / x) ^ 5 +
          (u x / x) ^ 4 * (v x / x) +
          (u x / x) ^ 3 * (v x / x) ^ 2 +
          (u x / x) ^ 2 * (v x / x) ^ 3 +
          (u x / x) * (v x / x) ^ 4 +
          (v x / x) ^ 5)
        Filter.atTop (nhds 6) := by
    have h0 := (huLimit.pow 5).add ((huLimit.pow 4).mul hvLimit)
    have h1 := h0.add ((huLimit.pow 3).mul (hvLimit.pow 2))
    have h2 := h1.add ((huLimit.pow 2).mul (hvLimit.pow 3))
    have h3 := h2.add (huLimit.mul (hvLimit.pow 4))
    have h := h3.add (hvLimit.pow 5)
    have hSix :
        (1 : ℝ) ^ 5 + 1 ^ 4 * 1 + 1 ^ 3 * 1 ^ 2 +
          1 ^ 2 * 1 ^ 3 + 1 * 1 ^ 4 + 1 ^ 5 = 6 := by
      norm_num
    rw [hSix] at h
    exact h
  have hdenLimit :
      Filter.Tendsto normalizedDenominator Filter.atTop (nhds 6) :=
    hsum.congr' hdenEq.symm
  have hnum :
      Filter.Tendsto
        (fun x : ℝ => 12 - 3 / x + 8 / x ^ 2)
        Filter.atTop (nhds 12) := by
    simpa [div_eq_mul_inv, inv_pow] using
      ((hc12.sub (hc3.mul hinv)).add (hc8.mul (hinv.pow 2)))
  have hquot :
      Filter.Tendsto
        (fun x : ℝ =>
          (12 - 3 / x + 8 / x ^ 2) / normalizedDenominator x)
        Filter.atTop (nhds ((12 : ℝ) / 6)) :=
    hnum.div hdenLimit (by norm_num : (6 : ℝ) ≠ 0)
  have hratio : (12 : ℝ) / 6 = 2 := by norm_num
  rw [hratio] at hquot
  change Filter.Tendsto
    (fun x : ℝ =>
      (12 - 3 / x + 8 / x ^ 2) / normalizedDenominator x)
    Filter.atTop (nhds 2)
  exact hquot

end

end ProofGap.Exercise462
