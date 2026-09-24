import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise632

noncomputable section

def cbrt (x : ℝ) : ℝ := Real.rpow x (1 / 3)
def linearized (x : ℝ) : ℝ := (cbrt (1 + x) - 1) / (x / 3)
def conjugateExpr (x : ℝ) : ℝ :=
  (cbrt ((1 + x) ^ 2) + cbrt (1 + x) + 1) / 3
def comparisonSum (n : ℕ) : ℝ :=
  (Finset.Icc 1 n).sum (fun k => (k : ℝ) / (3 * (n : ℝ) ^ 2))
def targetSum (n : ℕ) : ℝ :=
  (Finset.Icc 1 n).sum (fun k =>
    cbrt (1 + (k : ℝ) / (n : ℝ) ^ 2) - 1)

/-- Source: `proof_gap/exercise_632/1.txt`. -/
private lemma cbrt_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ cbrt x := by
  unfold cbrt
  exact Real.rpow_nonneg hx _

private lemma cbrt_cube (x : ℝ) (hx : 0 ≤ x) : cbrt x ^ 3 = x := by
  unfold cbrt
  calc
    x.rpow (1 / 3) ^ 3 = (x.rpow (1 / 3)).rpow (3 : ℝ) :=
      (Real.rpow_natCast (x.rpow (1 / 3)) (n := 3)).symm
    _ = x.rpow ((1 / 3 : ℝ) * 3) :=
      (Real.rpow_mul hx (1 / 3 : ℝ) (3 : ℝ)).symm
    _ = x := by norm_num

private lemma cbrt_sq (x : ℝ) (hx : 0 ≤ x) :
    cbrt (x ^ 2) = cbrt x ^ 2 := by
  let a := cbrt (x ^ 2)
  let b := cbrt x ^ 2
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact cbrt_nonneg (sq_nonneg x)
  have hb0 : 0 ≤ b := by
    dsimp [b]
    positivity
  have ha3 : a ^ 3 = x ^ 2 := by
    dsimp [a]
    exact cbrt_cube _ (sq_nonneg x)
  have hb3 : b ^ 3 = x ^ 2 := by
    dsimp [b]
    calc
      (cbrt x ^ 2) ^ 3 = (cbrt x ^ 3) ^ 2 := by ring
      _ = x ^ 2 := by rw [cbrt_cube x hx]
  have hfac : (a - b) * (a ^ 2 + a * b + b ^ 2) = 0 := by
    calc
      (a - b) * (a ^ 2 + a * b + b ^ 2) = a ^ 3 - b ^ 3 := by ring
      _ = 0 := by rw [ha3, hb3]; ring
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · have ha : a = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b]
    exact ha.trans hb.symm

private theorem cbrt_tendsto_one :
    Filter.Tendsto cbrt (nhds 1) (nhds 1) := by
  have hlog :
      Filter.Tendsto Real.log (nhds (1 : ℝ)) (nhds 0) := by
    convert
      (Real.continuousAt_log (show (1 : ℝ) ≠ 0 by norm_num)).tendsto using 1 <;>
      norm_num
  have hscaled :
      Filter.Tendsto (fun x : ℝ => Real.log x * (1 / 3 : ℝ))
        (nhds 1) (nhds 0) := by
    convert hlog.mul tendsto_const_nhds using 1 <;> norm_num
  have hraw :
      Filter.Tendsto
        (fun x : ℝ => Real.exp (Real.log x * (1 / 3 : ℝ)))
        (nhds 1) (nhds 1) := by
    convert Real.continuous_exp.continuousAt.tendsto.comp hscaled using 1 <;>
      norm_num
  have heq :
      cbrt =ᶠ[nhds (1 : ℝ)]
        (fun x : ℝ => Real.exp (Real.log x * (1 / 3 : ℝ))) := by
    filter_upwards [eventually_gt_nhds zero_lt_one] with x hx
    unfold cbrt
    exact Real.rpow_def_of_pos hx (1 / 3 : ℝ)
  exact hraw.congr' heq.symm

private theorem conjugate_tendsto_one :
    Filter.Tendsto conjugateExpr (nhds 0) (nhds 1) := by
  have hone :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) (nhds 0) (nhds 1) :=
    tendsto_const_nhds
  have hid :
      Filter.Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0) :=
    continuousAt_id
  have hbase :
      Filter.Tendsto (fun x : ℝ => 1 + x) (nhds 0) (nhds 1) := by
    convert hone.add hid using 1 <;> norm_num
  have hbaseSq :
      Filter.Tendsto (fun x : ℝ => (1 + x) ^ 2) (nhds 0) (nhds 1) := by
    simpa using hbase.pow 2
  have hc :
      Filter.Tendsto (fun x : ℝ => cbrt (1 + x)) (nhds 0) (nhds 1) :=
    cbrt_tendsto_one.comp hbase
  have hcsq :
      Filter.Tendsto (fun x : ℝ => cbrt ((1 + x) ^ 2))
        (nhds 0) (nhds 1) :=
    cbrt_tendsto_one.comp hbaseSq
  have hnum :
      Filter.Tendsto
        (fun x : ℝ => cbrt ((1 + x) ^ 2) + cbrt (1 + x) + 1)
        (nhds 0) (nhds 3) := by
    convert (hcsq.add hc).add tendsto_const_nhds using 1 <;>
      norm_num
  have hconst :
      Filter.Tendsto (fun _ : ℝ => (3 : ℝ)⁻¹)
        (nhds 0) (nhds ((3 : ℝ)⁻¹)) :=
    tendsto_const_nhds
  convert hnum.mul hconst using 1 <;>
    norm_num [conjugateExpr, div_eq_mul_inv]

private lemma linearized_eventually_eq_inv :
    linearized =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
      (fun x => (conjugateExpr x)⁻¹) := by
  have hone :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) (nhds 0) (nhds 1) :=
    tendsto_const_nhds
  have hid :
      Filter.Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0) :=
    continuousAt_id
  have hbase :
      Filter.Tendsto (fun x : ℝ => 1 + x) (nhds 0) (nhds 1) := by
    convert hone.add hid using 1 <;> norm_num
  have hposFull : ∀ᶠ x : ℝ in nhds 0, 0 < 1 + x :=
    hbase.eventually (eventually_gt_nhds zero_lt_one)
  have hpos :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, 0 < 1 + x :=
    hposFull.filter_mono inf_le_left
  filter_upwards [hpos, self_mem_nhdsWithin] with x hxpos hxmem
  have hx0 : x ≠ 0 := by
    simpa using hxmem
  have hsquare :
      cbrt ((1 + x) ^ 2) = cbrt (1 + x) ^ 2 :=
    cbrt_sq _ (le_of_lt hxpos)
  have hcube : cbrt (1 + x) ^ 3 = 1 + x :=
    cbrt_cube _ (le_of_lt hxpos)
  have ha0 : 0 ≤ cbrt (1 + x) := cbrt_nonneg (le_of_lt hxpos)
  have hden : cbrt (1 + x) ^ 2 + cbrt (1 + x) + 1 ≠ 0 := by
    nlinarith [sq_nonneg (cbrt (1 + x))]
  unfold linearized conjugateExpr
  rw [hsquare]
  field_simp [hx0, hden]
  <;> nlinarith [hcube]

private theorem linearized_tendsto_one :
    Filter.Tendsto linearized
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have hinv :
      Filter.Tendsto (fun x => (conjugateExpr x)⁻¹)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    have h := conjugate_tendsto_one.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa using h.mono_left inf_le_left
  exact hinv.congr' linearized_eventually_eq_inv.symm

private lemma sum_range_cast (n : ℕ) :
    (Finset.range (n + 1)).sum (fun k => (k : ℝ)) =
      (n : ℝ) * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private lemma sum_Icc_cast (n : ℕ) :
    (Finset.Icc 1 n).sum (fun k => (k : ℝ)) =
      (n : ℝ) * (n + 1) / 2 := by
  calc
    (Finset.Icc 1 n).sum (fun k => (k : ℝ)) =
        (Finset.range (n + 1)).sum (fun k => (k : ℝ)) := by
      apply Finset.sum_subset
      · intro k hk
        simp only [Finset.mem_Icc] at hk
        simp only [Finset.mem_range]
        omega
      · intro k hkRange hkNot
        have hk0 : k = 0 := by
          by_contra hk0
          apply hkNot
          simp only [Finset.mem_Icc]
          constructor
          · omega
          · simp only [Finset.mem_range] at hkRange
            omega
        subst k
        norm_num
    _ = (n : ℝ) * (n + 1) / 2 := sum_range_cast n

private lemma comparisonSum_closed (n : ℕ) :
    comparisonSum n =
      (1 / 6 : ℝ) * ((n : ℝ) * (n + 1) / (n : ℝ) ^ 2) := by
  unfold comparisonSum
  rw [← Finset.sum_div, sum_Icc_cast]
  cases n with
  | zero => norm_num
  | succ n =>
      push_cast
      field_simp
      <;> ring

private lemma comparisonSum_fun :
    comparisonSum =
      (fun n : ℕ =>
        (1 / 6 : ℝ) * ((n : ℝ) * (n + 1) / (n : ℝ) ^ 2)) := by
  funext n
  exact comparisonSum_closed n

private lemma cbrt_error_bound {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ u / 3 - (cbrt (1 + u) - 1) ∧
      u / 3 - (cbrt (1 + u) - 1) ≤ u ^ 2 := by
  let a := cbrt (1 + u)
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact cbrt_nonneg (by linarith)
  have hcube : a ^ 3 = 1 + u := by
    dsimp [a]
    exact cbrt_cube _ (by linarith)
  have hid : u = (a - 1) * (a ^ 2 + a + 1) := by
    nlinarith [hcube]
  have hDpos : 0 < a ^ 2 + a + 1 := by
    nlinarith [sq_nonneg a]
  have ha1 : 1 ≤ a := by
    by_contra h
    have ha_lt : a < 1 := lt_of_not_ge h
    have hneg : (a - 1) * (a ^ 2 + a + 1) < 0 :=
      mul_neg_of_neg_of_pos (sub_neg.mpr ha_lt) hDpos
    linarith [hid]
  have ha2 : a ≤ 2 := by
    by_contra h
    have htwo : 2 < a := lt_of_not_ge h
    have hcoef : 0 < a ^ 2 + 2 * a + 4 := by
      nlinarith [sq_nonneg a]
    have hpoly : a ^ 3 - 8 = (a - 2) * (a ^ 2 + 2 * a + 4) := by
      ring
    have hprodpos : 0 < (a - 2) * (a ^ 2 + 2 * a + 4) :=
      mul_pos (sub_pos.mpr htwo) hcoef
    have hlarge : 8 < a ^ 3 := by
      nlinarith [hpoly, hprodpos]
    nlinarith [hcube]
  have haSq : 1 ≤ a ^ 2 := by
    nlinarith [sq_nonneg (a - 1)]
  have hD3 : 3 ≤ a ^ 2 + a + 1 := by
    linarith
  have ht0 : 0 ≤ a - 1 := sub_nonneg.mpr ha1
  have htle : a - 1 ≤ u / 3 := by
    have hmul := mul_le_mul_of_nonneg_left hD3 ht0
    rw [← hid] at hmul
    linarith
  have herr :
      u / 3 - (a - 1) = (a - 1) ^ 2 * (a + 2) / 3 := by
    rw [hid]
    ring
  constructor
  · rw [herr]
    positivity
  · rw [herr]
    have hsquare : (a - 1) ^ 2 ≤ (u / 3) ^ 2 := by
      nlinarith
    have ha4 : a + 2 ≤ 4 := by linarith
    have hprod :
        (a - 1) ^ 2 * (a + 2) ≤ (u / 3) ^ 2 * 4 :=
      mul_le_mul hsquare ha4 (by positivity) (sq_nonneg _)
    nlinarith [hprod, sq_nonneg u]

theorem gap1 (L : ℝ) :
    Filter.Tendsto linearized (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L) ↔
      Filter.Tendsto conjugateExpr (nhds 0) (nhds L) := by
  constructor
  · intro h
    have hL : L = 1 := tendsto_nhds_unique h linearized_tendsto_one
    subst L
    exact conjugate_tendsto_one
  · intro h
    have hL : L = 1 := tendsto_nhds_unique h conjugate_tendsto_one
    subst L
    exact linearized_tendsto_one

/-- Source: `proof_gap/exercise_632/2.txt`. -/
theorem gap2 : Filter.Tendsto conjugateExpr (nhds 0) (nhds 1) := by
  exact conjugate_tendsto_one

/-- Source: `proof_gap/exercise_632/3.txt`. -/
theorem gap3 :
    Filter.Tendsto linearized (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  exact (gap1 1).2 gap2

/-- Source: `proof_gap/exercise_632/4.txt`; bind the previously free fixed `k`. -/
theorem gap4 (k : ℕ) :
    Filter.Tendsto (fun n : ℕ => (k : ℝ) / (n : ℝ) ^ 2)
      Filter.atTop (nhds 0) := by
  have hinv :
      Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hkconst :
      Filter.Tendsto (fun _ : ℕ => (k : ℝ)) Filter.atTop (nhds (k : ℝ)) :=
    tendsto_const_nhds
  simpa [div_eq_mul_inv, inv_pow] using hkconst.mul (hinv.pow 2)

/-- Source: `proof_gap/exercise_632/5.txt`; replace the sum ellipsis by `comparisonSum`. -/
theorem gap5 :
    Filter.Tendsto comparisonSum Filter.atTop (nhds (1 / 6 : ℝ)) ↔
      Filter.Tendsto
        (fun n : ℕ => (1 / 6 : ℝ) * ((n : ℝ) * (n + 1) / (n : ℝ) ^ 2))
        Filter.atTop (nhds (1 / 6 : ℝ)) := by
  rw [comparisonSum_fun]

/-- Source: `proof_gap/exercise_632/6.txt`. -/
theorem gap6 :
    Filter.Tendsto
      (fun n : ℕ => (1 / 6 : ℝ) * ((n : ℝ) * (n + 1) / (n : ℝ) ^ 2))
      Filter.atTop (nhds (1 / 6 : ℝ)) := by
  have hinv :
      Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim :
      Filter.Tendsto
        (fun n : ℕ => (1 / 6 : ℝ) * (1 + (n : ℝ)⁻¹))
        Filter.atTop (nhds (1 / 6 : ℝ)) := by
    convert tendsto_const_nhds.mul (tendsto_const_nhds.add hinv) using 1 <;>
      norm_num
  have hpos : ∀ᶠ n : ℕ in Filter.atTop, 0 < n := by
    apply Filter.eventually_atTop.2
    exact ⟨1, by
      intro n hn
      omega⟩
  apply hlim.congr'
  filter_upwards [hpos] with n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  field_simp [hn0]

/-- Source: `proof_gap/exercise_632/7.txt`. -/
theorem gap7 :
    Filter.Tendsto comparisonSum Filter.atTop (nhds (1 / 6 : ℝ)) := by
  exact gap5.mpr gap6

/-- Source: `proof_gap/exercise_632/8.txt`. -/
theorem gap8 :
    Filter.Tendsto targetSum Filter.atTop (nhds (1 / 6 : ℝ)) := by
  have hinv :
      Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hbounds : ∀ n : ℕ, 1 ≤ n →
      0 ≤ comparisonSum n - targetSum n ∧
        comparisonSum n - targetSum n ≤ (n : ℝ)⁻¹ := by
    intro n hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by
      norm_cast
    have hn0R : (n : ℝ) ≠ 0 := by
      have hnPos : (0 : ℝ) < (n : ℝ) := by linarith
      exact ne_of_gt hnPos
    have hdenpos : 0 < (n : ℝ) ^ 2 := by
      positivity
    have hterm : ∀ k ∈ Finset.Icc 1 n,
        0 ≤ (k : ℝ) / (3 * (n : ℝ) ^ 2) -
            (cbrt (1 + (k : ℝ) / (n : ℝ) ^ 2) - 1) ∧
        (k : ℝ) / (3 * (n : ℝ) ^ 2) -
            (cbrt (1 + (k : ℝ) / (n : ℝ) ^ 2) - 1) ≤
          ((k : ℝ) / (n : ℝ) ^ 2) ^ 2 := by
      intro k hk
      have hk_le : k ≤ n := (Finset.mem_Icc.mp hk).2
      have hkR : (k : ℝ) ≤ (n : ℝ) := by
        norm_cast
      have hu0 : 0 ≤ (k : ℝ) / (n : ℝ) ^ 2 := by
        positivity
      have hu1 : (k : ℝ) / (n : ℝ) ^ 2 ≤ 1 := by
        apply (div_le_one hdenpos).2
        nlinarith
      have hb := cbrt_error_bound hu0 hu1
      have heq :
          (k : ℝ) / (3 * (n : ℝ) ^ 2) =
            ((k : ℝ) / (n : ℝ) ^ 2) / 3 := by
        field_simp [hn0R]
        <;> ring
      simpa only [heq] using hb
    have hsum_sq :
        (Finset.Icc 1 n).sum
            (fun k => ((k : ℝ) / (n : ℝ) ^ 2) ^ 2) ≤
          (n : ℝ)⁻¹ := by
      have hcard : (Finset.Icc 1 n).card = n := by
        simp [Nat.card_Icc]
      calc
        (Finset.Icc 1 n).sum
              (fun k => ((k : ℝ) / (n : ℝ) ^ 2) ^ 2)
            ≤ (Finset.Icc 1 n).sum
                (fun _k => ((n : ℝ)⁻¹) ^ 2) := by
              apply Finset.sum_le_sum
              intro k hk
              have hk_le : k ≤ n := (Finset.mem_Icc.mp hk).2
              have hkR : (k : ℝ) ≤ (n : ℝ) := by
                norm_cast
              have hu0 : 0 ≤ (k : ℝ) / (n : ℝ) ^ 2 := by
                positivity
              have hu_le :
                  (k : ℝ) / (n : ℝ) ^ 2 ≤ (n : ℝ)⁻¹ := by
                calc
                  (k : ℝ) / (n : ℝ) ^ 2
                      ≤ (n : ℝ) / (n : ℝ) ^ 2 :=
                    div_le_div_of_nonneg_right hkR (le_of_lt hdenpos)
                  _ = (n : ℝ)⁻¹ := by
                    field_simp [hn0R]
              nlinarith [sq_nonneg
                ((n : ℝ)⁻¹ - (k : ℝ) / (n : ℝ) ^ 2)]
        _ = (n : ℝ) * ((n : ℝ)⁻¹) ^ 2 := by
              simp [hcard]
        _ = (n : ℝ)⁻¹ := by
              field_simp [hn0R]
    unfold comparisonSum targetSum
    rw [← Finset.sum_sub_distrib]
    constructor
    · exact Finset.sum_nonneg (fun k hk => (hterm k hk).1)
    · calc
        (Finset.Icc 1 n).sum
              (fun k =>
                (k : ℝ) / (3 * (n : ℝ) ^ 2) -
                  (cbrt (1 + (k : ℝ) / (n : ℝ) ^ 2) - 1))
            ≤ (Finset.Icc 1 n).sum
                (fun k => ((k : ℝ) / (n : ℝ) ^ 2) ^ 2) := by
              exact Finset.sum_le_sum (fun k hk => (hterm k hk).2)
        _ ≤ (n : ℝ)⁻¹ := hsum_sq
  have hone : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ n := by
    apply Filter.eventually_atTop.2
    exact ⟨1, by
      intro n hn
      exact hn⟩
  have hnonneg :
      ∀ᶠ n : ℕ in Filter.atTop,
        0 ≤ comparisonSum n - targetSum n := by
    filter_upwards [hone] with n hn
    exact (hbounds n hn).1
  have hupper :
      ∀ᶠ n : ℕ in Filter.atTop,
        comparisonSum n - targetSum n ≤ (n : ℝ)⁻¹ := by
    filter_upwards [hone] with n hn
    exact (hbounds n hn).2
  have hdiff :
      Filter.Tendsto
        (fun n : ℕ => comparisonSum n - targetSum n)
        Filter.atTop (nhds 0) :=
    squeeze_zero' hnonneg hupper hinv
  have h := gap7.sub hdiff
  simpa only [sub_zero, sub_sub_cancel] using h

end

end ProofGap.Exercise632
