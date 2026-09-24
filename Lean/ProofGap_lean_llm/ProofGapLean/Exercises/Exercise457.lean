import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise457

noncomputable section

def original (a b x : ℝ) : ℝ := Real.sqrt ((x + a) * (x + b)) - x
def rationalized (a b x : ℝ) : ℝ :=
  ((x + a) * (x + b) - x ^ 2) / (Real.sqrt ((x + a) * (x + b)) + x)
def normalized (a b x : ℝ) : ℝ :=
  (a + b + a * b / x) / (1 + Real.sqrt ((1 + a / x) * (1 + b / x)))
def HasLimitAtPosInfinity (g : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N > 0, ∀ x, N < x → |g x - L| < ε

/-- Source: `proof_gap/exercise_457/1.txt`. -/
private theorem hasLimitAtPosInfinity_congr_of_tail_eq
    {f g : ℝ → ℝ} {L : ℝ}
    (hfg : ∃ C > 0, ∀ x, C < x → f x = g x) :
    HasLimitAtPosInfinity f L ↔ HasLimitAtPosInfinity g L := by
  constructor
  · intro hf ε hε
    rcases hf ε hε with ⟨N, hN, hfN⟩
    rcases hfg with ⟨C, hC, hfgC⟩
    refine ⟨max N C, lt_of_lt_of_le hN (le_max_left _ _), ?_⟩
    intro x hx
    have hxN : N < x := lt_of_le_of_lt (le_max_left _ _) hx
    have hxC : C < x := lt_of_le_of_lt (le_max_right _ _) hx
    rw [← hfgC x hxC]
    exact hfN x hxN
  · intro hg ε hε
    rcases hg ε hε with ⟨N, hN, hgN⟩
    rcases hfg with ⟨C, hC, hfgC⟩
    refine ⟨max N C, lt_of_lt_of_le hN (le_max_left _ _), ?_⟩
    intro x hx
    have hxN : N < x := lt_of_le_of_lt (le_max_left _ _) hx
    have hxC : C < x := lt_of_le_of_lt (le_max_right _ _) hx
    rw [hfgC x hxC]
    exact hgN x hxN

theorem gap1 (a b : ℝ) :
    HasLimitAtPosInfinity (original a b) ((a + b) / 2) ↔
      HasLimitAtPosInfinity (rationalized a b) ((a + b) / 2) := by
  apply hasLimitAtPosInfinity_congr_of_tail_eq
  let C : ℝ := max |a| |b| + 1
  refine ⟨C, ?_, ?_⟩
  · have hm : 0 ≤ max |a| |b| :=
      le_trans (abs_nonneg a) (le_max_left _ _)
    dsimp [C]
    linarith
  · intro x hx
    have hax : |a| < x := by
      have ha : |a| ≤ max |a| |b| := le_max_left _ _
      dsimp [C] at hx
      linarith
    have hbx : |b| < x := by
      have hb : |b| ≤ max |a| |b| := le_max_right _ _
      dsimp [C] at hx
      linarith
    have hx0 : 0 < x := lt_of_le_of_lt (abs_nonneg a) hax
    have hxa : 0 < x + a := by
      have ha := neg_abs_le a
      linarith
    have hxb : 0 < x + b := by
      have hb := neg_abs_le b
      linarith
    have hr : 0 ≤ (x + a) * (x + b) :=
      mul_nonneg (le_of_lt hxa) (le_of_lt hxb)
    have hs : (Real.sqrt ((x + a) * (x + b))) ^ 2 =
        (x + a) * (x + b) := Real.sq_sqrt hr
    have hden : Real.sqrt ((x + a) * (x + b)) + x ≠ 0 := by
      have hs0 := Real.sqrt_nonneg ((x + a) * (x + b))
      linarith
    simp only [original, rationalized]
    apply (eq_div_iff hden).2
    calc
      (Real.sqrt ((x + a) * (x + b)) - x) *
          (Real.sqrt ((x + a) * (x + b)) + x) =
          (Real.sqrt ((x + a) * (x + b))) ^ 2 - x ^ 2 := by ring
      _ = (x + a) * (x + b) - x ^ 2 := by rw [hs]

/-- Source: `proof_gap/exercise_457/2.txt`. -/
theorem gap2 (a b : ℝ) :
    HasLimitAtPosInfinity (rationalized a b) ((a + b) / 2) ↔
      HasLimitAtPosInfinity (normalized a b) ((a + b) / 2) := by
  apply hasLimitAtPosInfinity_congr_of_tail_eq
  let C : ℝ := max |a| |b| + 1
  refine ⟨C, ?_, ?_⟩
  · have hm : 0 ≤ max |a| |b| :=
      le_trans (abs_nonneg a) (le_max_left _ _)
    dsimp [C]
    linarith
  · intro x hx
    have hax : |a| < x := by
      have ha : |a| ≤ max |a| |b| := le_max_left _ _
      dsimp [C] at hx
      linarith
    have hbx : |b| < x := by
      have hb : |b| ≤ max |a| |b| := le_max_right _ _
      dsimp [C] at hx
      linarith
    have hx0 : 0 < x := lt_of_le_of_lt (abs_nonneg a) hax
    have hxne : x ≠ 0 := ne_of_gt hx0
    have hxa : 0 < x + a := by
      have ha := neg_abs_le a
      linarith
    have hxb : 0 < x + b := by
      have hb := neg_abs_le b
      linarith
    have hfa_eq : 1 + a / x = (x + a) / x := by
      field_simp [hxne]
    have hfb_eq : 1 + b / x = (x + b) / x := by
      field_simp [hxne]
    have hfa : 0 < 1 + a / x := by
      rw [hfa_eq]
      exact div_pos hxa hx0
    have hfb : 0 < 1 + b / x := by
      rw [hfb_eq]
      exact div_pos hxb hx0
    let q : ℝ := (1 + a / x) * (1 + b / x)
    have hq : 0 ≤ q := by
      dsimp [q]
      exact mul_nonneg (le_of_lt hfa) (le_of_lt hfb)
    have hy : 0 ≤ (x + a) * (x + b) :=
      mul_nonneg (le_of_lt hxa) (le_of_lt hxb)
    have hrad : (x + a) * (x + b) = x ^ 2 * q := by
      dsimp [q]
      field_simp [hxne]
    have hsq_q : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq
    have hsq_y : (Real.sqrt ((x + a) * (x + b))) ^ 2 =
        (x + a) * (x + b) := Real.sq_sqrt hy
    have hxsq : (x * Real.sqrt q) ^ 2 = (x + a) * (x + b) := by
      calc
        (x * Real.sqrt q) ^ 2 = x ^ 2 * (Real.sqrt q) ^ 2 := by ring
        _ = x ^ 2 * q := by rw [hsq_q]
        _ = (x + a) * (x + b) := hrad.symm
    have hsqrt : Real.sqrt ((x + a) * (x + b)) = x * Real.sqrt q := by
      have hy0 := Real.sqrt_nonneg ((x + a) * (x + b))
      have hq0 := Real.sqrt_nonneg q
      have hxs0 : 0 ≤ x * Real.sqrt q :=
        mul_nonneg (le_of_lt hx0) hq0
      nlinarith
    have hd : 1 + Real.sqrt q ≠ 0 := by
      have hq0 := Real.sqrt_nonneg q
      linarith
    have hleft : x * Real.sqrt q + x ≠ 0 := by
      have hq0 := Real.sqrt_nonneg q
      nlinarith
    simp only [rationalized, normalized]
    change ((x + a) * (x + b) - x ^ 2) /
        (Real.sqrt ((x + a) * (x + b)) + x) =
      (a + b + a * b / x) / (1 + Real.sqrt q)
    rw [hsqrt]
    field_simp [hxne, hd, hleft]
    ring

/-- Source: `proof_gap/exercise_457/3.txt`. -/
theorem gap3 (a b : ℝ) :
    HasLimitAtPosInfinity (normalized a b) ((a + b) / 2) := by
  have hinv : Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop
      (nhds 0) := tendsto_inv_atTop_zero
  have ha : Filter.Tendsto (fun x : ℝ => a / x) Filter.atTop
      (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul hinv :
        Filter.Tendsto (fun x : ℝ => a * x⁻¹) Filter.atTop
          (nhds (a * 0)))
  have hb : Filter.Tendsto (fun x : ℝ => b / x) Filter.atTop
      (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul hinv :
        Filter.Tendsto (fun x : ℝ => b * x⁻¹) Filter.atTop
          (nhds (b * 0)))
  have hab : Filter.Tendsto (fun x : ℝ => a * b / x) Filter.atTop
      (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul hinv :
        Filter.Tendsto (fun x : ℝ => (a * b) * x⁻¹) Filter.atTop
          (nhds ((a * b) * 0)))
  have hpa : Filter.Tendsto (fun x : ℝ => 1 + a / x) Filter.atTop
      (nhds 1) := by
    have hone : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop
        (nhds 1) := tendsto_const_nhds
    simpa using hone.add ha
  have hpb : Filter.Tendsto (fun x : ℝ => 1 + b / x) Filter.atTop
      (nhds 1) := by
    have hone : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop
        (nhds 1) := tendsto_const_nhds
    simpa using hone.add hb
  have hp : Filter.Tendsto
      (fun x : ℝ => (1 + a / x) * (1 + b / x)) Filter.atTop
      (nhds 1) := by
    simpa using hpa.mul hpb
  have hs : Filter.Tendsto
      (fun x : ℝ => Real.sqrt ((1 + a / x) * (1 + b / x)))
      Filter.atTop (nhds 1) := by
    simpa using (Real.continuous_sqrt.tendsto 1).comp hp
  have hnum : Filter.Tendsto
      (fun x : ℝ => a + b + a * b / x) Filter.atTop
      (nhds (a + b)) := by
    have hc : Filter.Tendsto (fun _ : ℝ => a + b) Filter.atTop
        (nhds (a + b)) := tendsto_const_nhds
    simpa using hc.add hab
  have hden : Filter.Tendsto
      (fun x : ℝ => 1 + Real.sqrt ((1 + a / x) * (1 + b / x)))
      Filter.atTop (nhds 2) := by
    have hone : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop
        (nhds 1) := tendsto_const_nhds
    have h := hone.add hs
    norm_num at h
    exact h
  have hlim : Filter.Tendsto (normalized a b) Filter.atTop
      (nhds ((a + b) / 2)) := by
    have hquot := hnum.div hden (by norm_num : (2 : ℝ) ≠ 0)
    simpa only [normalized] using hquot
  intro ε hε
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      dist (normalized a b x) ((a + b) / 2) < ε :=
    (Metric.tendsto_nhds.1 hlim) ε hε
  rcases Filter.eventually_atTop.1 hev with ⟨N, hN⟩
  refine ⟨max N 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x hx
  have hxN : N ≤ x :=
    le_trans (le_max_left _ _) (le_of_lt hx)
  have h := hN x hxN
  simpa [Real.dist_eq] using h

end

end ProofGap.Exercise457
