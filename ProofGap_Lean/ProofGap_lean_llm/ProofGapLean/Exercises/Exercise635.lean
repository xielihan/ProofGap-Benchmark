import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise635

noncomputable section

def productSeq (n : ℕ) : ℝ :=
  (Finset.Icc 1 n).prod (fun k => 1 + (k : ℝ) / (n : ℝ) ^ 2)
def logSum (n : ℕ) : ℝ :=
  (Finset.Icc 1 n).sum (fun k =>
    Real.log (1 + (k : ℝ) / (n : ℝ) ^ 2))
def linearSum (n : ℕ) : ℝ :=
  (Finset.Icc 1 n).sum (fun k => (k : ℝ) / (n : ℝ) ^ 2)

/-- Exercise 635, gap 1; replace the product ellipsis by `Finset.prod`. -/
private lemma sum_range_succ_cast (n : ℕ) :
    (Finset.range (n + 1)).sum (fun k => (k : ℝ)) =
      (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      simp only [Finset.sum_range_succ, ih, Nat.cast_add, Nat.cast_one]
      ring

private lemma sum_Icc_cast (n : ℕ) :
    (Finset.Icc 1 n).sum (fun k => (k : ℝ)) =
      (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  have hs : Finset.Icc 1 n ∪ {0} = Finset.range (n + 1) := by
    ext k
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton,
      Finset.mem_range]
    omega
  have hd : Disjoint (Finset.Icc 1 n) ({0} : Finset ℕ) := by
    refine Finset.disjoint_left.mpr ?_
    intro a haI ha0
    have ha_pos : 1 ≤ a := (Finset.mem_Icc.mp haI).1
    have ha_zero : a = 0 := Finset.mem_singleton.mp ha0
    omega
  calc
    (Finset.Icc 1 n).sum (fun k => (k : ℝ)) =
        (Finset.Icc 1 n ∪ {0}).sum (fun k => (k : ℝ)) := by
      rw [Finset.sum_union hd]
      simp
    _ = (Finset.range (n + 1)).sum (fun k => (k : ℝ)) := by rw [hs]
    _ = (n : ℝ) * ((n : ℝ) + 1) / 2 := sum_range_succ_cast n

private lemma linearSum_formula (n : ℕ) :
    linearSum n =
      ((n : ℝ) * ((n : ℝ) + 1) / 2) / (n : ℝ) ^ 2 := by
  unfold linearSum
  rw [← Finset.sum_div, sum_Icc_cast]

private lemma natCast_inv_tendsto :
    Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹))
      Filter.atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

private lemma log_one_add_error (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ x - Real.log (1 + x) ∧
      x - Real.log (1 + x) ≤ x ^ 2 := by
  have hp : 0 < 1 + x := by linarith
  have hne : 1 + x ≠ 0 := ne_of_gt hp
  have hu : Real.log (1 + x) ≤ x := by
    have h := Real.log_le_sub_one_of_pos hp
    linarith
  have hInv := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  have hid : (1 + x)⁻¹ - 1 = -(x / (1 + x)) := by
    field_simp [hne] <;> ring
  rw [Real.log_inv, hid] at hInv
  have hlfrac : x / (1 + x) ≤ Real.log (1 + x) := by
    linarith
  have hl : x ≤ (1 + x) * Real.log (1 + x) := by
    have hm := mul_le_mul_of_nonneg_right hlfrac hp.le
    have hcancel : x / (1 + x) * (1 + x) = x := by
      field_simp [hne]
    rw [hcancel] at hm
    simpa [mul_comm] using hm
  have hmul : x * Real.log (1 + x) ≤ x * x :=
    mul_le_mul_of_nonneg_left hu hx
  constructor
  · linarith
  · nlinarith

private lemma logSum_error_bound (n : ℕ) :
    0 ≤ linearSum n - logSum n ∧
      linearSum n - logSum n ≤ (n : ℝ)⁻¹ * linearSum n := by
  by_cases hn0 : n = 0
  · subst n
    simp [linearSum, logSum]
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hterm : ∀ k ∈ Finset.Icc 1 n,
        0 ≤ (k : ℝ) / (n : ℝ) ^ 2 -
            Real.log (1 + (k : ℝ) / (n : ℝ) ^ 2) ∧
        (k : ℝ) / (n : ℝ) ^ 2 -
            Real.log (1 + (k : ℝ) / (n : ℝ) ^ 2) ≤
          (n : ℝ)⁻¹ * ((k : ℝ) / (n : ℝ) ^ 2) := by
      intro k hk
      have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
      have hkR : (k : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hkn
      have hx : 0 ≤ (k : ℝ) / (n : ℝ) ^ 2 :=
        div_nonneg (Nat.cast_nonneg k) (sq_nonneg (n : ℝ))
      have hxle : (k : ℝ) / (n : ℝ) ^ 2 ≤ (n : ℝ)⁻¹ := by
        calc
          (k : ℝ) / (n : ℝ) ^ 2 ≤
              (n : ℝ) / (n : ℝ) ^ 2 :=
            (div_le_div_iff_of_pos_right (sq_pos_of_pos hnR)).2 hkR
          _ = (n : ℝ)⁻¹ := by
            field_simp [ne_of_gt hnR] <;> ring
      have hsq : ((k : ℝ) / (n : ℝ) ^ 2) ^ 2 ≤
          (n : ℝ)⁻¹ * ((k : ℝ) / (n : ℝ) ^ 2) := by
        simpa [pow_two] using mul_le_mul_of_nonneg_right hxle hx
      have hb := log_one_add_error ((k : ℝ) / (n : ℝ) ^ 2) hx
      exact ⟨hb.1, hb.2.trans hsq⟩
    constructor
    · rw [linearSum, logSum, ← Finset.sum_sub_distrib]
      exact Finset.sum_nonneg fun k hk => (hterm k hk).1
    · rw [linearSum, logSum, ← Finset.sum_sub_distrib]
      calc
        (Finset.Icc 1 n).sum (fun k =>
            (k : ℝ) / (n : ℝ) ^ 2 -
              Real.log (1 + (k : ℝ) / (n : ℝ) ^ 2)) ≤
            (Finset.Icc 1 n).sum (fun k =>
              (n : ℝ)⁻¹ * ((k : ℝ) / (n : ℝ) ^ 2)) :=
          Finset.sum_le_sum fun k hk => (hterm k hk).2
        _ = (n : ℝ)⁻¹ * linearSum n := by
          rw [linearSum, Finset.mul_sum]

private lemma productSeq_pos (n : ℕ) : 0 < productSeq n := by
  unfold productSeq
  apply Finset.prod_pos
  intro k _
  have hq : 0 ≤ (k : ℝ) / (n : ℝ) ^ 2 :=
    div_nonneg (Nat.cast_nonneg k) (sq_nonneg (n : ℝ))
  linarith

theorem gap1 (n : ℕ) : Real.log (productSeq n) = logSum n := by
  classical
  let f : ℕ → ℝ := fun k => 1 + (k : ℝ) / (n : ℝ) ^ 2
  change Real.log ((Finset.Icc 1 n).prod f) =
    (Finset.Icc 1 n).sum (fun k => Real.log (f k))
  have hf (k : ℕ) : 0 < f k := by
    dsimp [f]
    have hq : 0 ≤ (k : ℝ) / (n : ℝ) ^ 2 :=
      div_nonneg (Nat.cast_nonneg k) (sq_nonneg (n : ℝ))
    linarith
  generalize Finset.Icc 1 n = s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hs : 0 < s.prod f := Finset.prod_pos fun i _ => hf i
      simp only [Finset.prod_insert ha, Finset.sum_insert ha]
      calc
        Real.log (f a * s.prod f) =
            Real.log (f a) + Real.log (s.prod f) :=
          Real.log_mul (ne_of_gt (hf a)) (ne_of_gt hs)
        _ = Real.log (f a) + s.sum (fun k => Real.log (f k)) := by rw [ih]

/-- Exercise 635, gap 2. -/
theorem gap2 :
    Filter.Tendsto (fun x : ℝ => Real.log (1 + x) / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  simpa only [Real.log_one, sub_zero, div_eq_mul_inv, mul_comm,
    smul_eq_mul, inv_one] using
    (Real.hasDerivAt_log (show (1 : ℝ) ≠ 0 by norm_num)).tendsto_slope_zero

/-- Exercise 635, gap 3. -/
theorem gap3 (k : ℕ) :
    Filter.Tendsto (fun n : ℕ => (k : ℝ) / (n : ℝ) ^ 2)
      Filter.atTop (nhds 0) := by
  have h :
      Filter.Tendsto
        (fun n : ℕ => (k : ℝ) * (((n : ℝ)⁻¹) ^ 2))
        Filter.atTop (nhds 0) := by
    simpa using
      ((tendsto_const_nhds.mul
        (natCast_inv_tendsto.pow 2)) :
        Filter.Tendsto
          (fun n : ℕ => (k : ℝ) * (((n : ℝ)⁻¹) ^ 2))
          Filter.atTop (nhds ((k : ℝ) * 0 ^ 2)))
  simpa [div_eq_mul_inv, inv_pow] using h

/-- Exercise 635, gap 4. -/
theorem gap4 :
    Filter.Tendsto linearSum Filter.atTop (nhds (1 / 2 : ℝ)) := by
  have hone :
      Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
        Filter.atTop (nhds 1) := tendsto_const_nhds
  have hmodel :
      Filter.Tendsto
        (fun n : ℕ => (1 + (n : ℝ)⁻¹) / 2)
        Filter.atTop (nhds (1 / 2 : ℝ)) := by
    simpa using (hone.add natCast_inv_tendsto).div_const (2 : ℝ)
  refine hmodel.congr' ?_
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun b hb => hb⟩] with n hn
  symm
  rw [linearSum_formula]
  have hnR : (n : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (by omega : 0 < n))
  field_simp [hnR] <;> ring

/-- Exercise 635, gap 5. -/
theorem gap5 :
    Filter.Tendsto logSum Filter.atTop (nhds (1 / 2 : ℝ)) := by
  have hupper :
      Filter.Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ * linearSum n)
        Filter.atTop (nhds 0) := by
    simpa using natCast_inv_tendsto.mul gap4
  have herr :
      Filter.Tendsto
        (fun n : ℕ => linearSum n - logSum n)
        Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupper ?_ ?_
    · intro n
      exact (logSum_error_bound n).1
    · intro n
      exact (logSum_error_bound n).2
  have h := gap4.sub herr
  simpa using h

/-- Exercise 635, gap 6. -/
theorem gap6 :
    Filter.Tendsto productSeq Filter.atTop (nhds (Real.exp (1 / 2))) := by
  have h :
      Filter.Tendsto (fun n : ℕ => Real.exp (logSum n))
        Filter.atTop (nhds (Real.exp (1 / 2))) :=
    Real.continuous_exp.continuousAt.tendsto.comp gap5
  refine h.congr' (Filter.Eventually.of_forall ?_)
  intro n
  rw [← gap1 n, Real.exp_log (productSeq_pos n)]

/-- Exercise 635, gap 7. -/
theorem gap7 : Real.exp (1 / 2) = Real.sqrt (Real.exp 1) := by
  have hsq : (Real.exp (1 / 2)) ^ 2 = Real.exp 1 := by
    rw [pow_two, ← Real.exp_add]
    norm_num
  have he : 0 ≤ Real.exp (1 / 2) := (Real.exp_pos _).le
  have hr : 0 ≤ Real.sqrt (Real.exp 1) := Real.sqrt_nonneg _
  have hr2 : (Real.sqrt (Real.exp 1)) ^ 2 = Real.exp 1 :=
    Real.sq_sqrt (Real.exp_pos 1).le
  nlinarith

/-- Exercise 635, gap 8. -/
theorem gap8 :
    Filter.Tendsto productSeq Filter.atTop (nhds (Real.sqrt (Real.exp 1))) := by
  rw [← gap7]
  exact gap6

end

end ProofGap.Exercise635
