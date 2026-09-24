import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise508

noncomputable section

def base (x : ℝ) : ℝ := (3 * x ^ 2 - x + 1) / (2 * x ^ 2 + x + 1)
def exponent (x : ℝ) : ℝ := x ^ 3 / (1 - x)
def exponentNormalized (x : ℝ) : ℝ := x ^ 2 / (1 / x - 1)
def f (x : ℝ) : ℝ := Real.rpow (base x) (exponent x)

/-- Source: `proof_gap/exercise_508/1.txt`. -/
theorem gap1 : Filter.Tendsto base Filter.atTop (nhds (3 / 2)) := by
  have hinv :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hthree :
      Filter.Tendsto (fun _ : ℝ => (3 : ℝ)) Filter.atTop (nhds 3) :=
    tendsto_const_nhds
  have htwo :
      Filter.Tendsto (fun _ : ℝ => (2 : ℝ)) Filter.atTop (nhds 2) :=
    tendsto_const_nhds
  have hnum :
      Filter.Tendsto (fun x : ℝ => 3 - x⁻¹ + x⁻¹ ^ 2)
        Filter.atTop (nhds 3) := by
    simpa using (hthree.sub hinv).add (hinv.pow 2)
  have hden :
      Filter.Tendsto (fun x : ℝ => 2 + x⁻¹ + x⁻¹ ^ 2)
        Filter.atTop (nhds 2) := by
    simpa using (htwo.add hinv).add (hinv.pow 2)
  have hquot :
      Filter.Tendsto
        (fun x : ℝ =>
          (3 - x⁻¹ + x⁻¹ ^ 2) / (2 + x⁻¹ + x⁻¹ ^ 2))
        Filter.atTop (nhds (3 / 2)) :=
    hnum.div hden (by norm_num)
  refine hquot.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hbaseDen : 2 * x ^ 2 + x + 1 ≠ 0 := by
    apply ne_of_gt
    nlinarith [sq_nonneg (4 * x + 1)]
  have hnormDen : 2 + x⁻¹ + x⁻¹ ^ 2 ≠ 0 := by
    have hinvpos : 0 < x⁻¹ := inv_pos.mpr hx
    positivity
  unfold base
  field_simp [hx0, hbaseDen, hnormDen]

/-- Source: `proof_gap/exercise_508/2.txt`; exclude both vanishing denominators. -/
theorem gap2 (x : ℝ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    exponent x = exponentNormalized x := by
  have h1x : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have hnorm : 1 / x - 1 ≠ 0 := by
    intro h
    apply hx1
    have h' : 1 / x = 1 := sub_eq_zero.mp h
    calc
      x = 1 * x := by ring
      _ = (1 / x) * x := by rw [h']
      _ = 1 := by field_simp [hx0]
  unfold exponent exponentNormalized
  field_simp [hx0, h1x, hnorm]

/-- Source: `proof_gap/exercise_508/3.txt`. -/
theorem gap3 : Filter.Tendsto exponentNormalized Filter.atTop Filter.atBot := by
  refine Filter.tendsto_atBot.2 ?_
  intro b
  filter_upwards
    [Filter.eventually_ge_atTop (max (2 : ℝ) (-b + 1))] with x hx
  have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
  have hxb : -b + 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : x ≠ 0 := by nlinarith
  have hx1 : x ≠ 1 := by nlinarith
  rw [← gap2 x hx0 hx1]
  unfold exponent
  have hdneg : 1 - x < 0 := by nlinarith
  apply (div_le_iff_of_neg hdneg).2
  have hb : 1 - x ≤ b := by nlinarith
  have hprod : b * (1 - x) ≤ (1 - x) * (1 - x) :=
    mul_le_mul_of_nonpos_right hb (le_of_lt hdneg)
  have hsquare : (1 - x) * (1 - x) ≤ x ^ 2 := by
    nlinarith
  have hcubic : x ^ 2 ≤ x ^ 3 := by
    calc
      x ^ 2 = 1 * x ^ 2 := by ring
      _ ≤ x * x ^ 2 :=
        mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg x)
      _ = x ^ 3 := by ring
  exact hprod.trans (hsquare.trans hcubic)

/-- Source: `proof_gap/exercise_508/4.txt`. -/
theorem gap4 : Filter.Tendsto exponent Filter.atTop Filter.atBot := by
  refine gap3.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := by nlinarith
  have hx1 : x ≠ 1 := ne_of_gt hx
  simpa only [gap2 x hx0 hx1]

/-- Source: `proof_gap/exercise_508/5.txt`; interpret the real exponent by `Real.rpow`. -/
theorem gap5 : Filter.Tendsto f Filter.atTop (nhds 0) := by
  have hlogpos : 0 < Real.log (3 / 2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hlogCont :
      Filter.Tendsto Real.log (nhds (3 / 2 : ℝ))
        (nhds (Real.log (3 / 2 : ℝ))) :=
    Real.continuousAt_log (by norm_num)
  have hlog :
      Filter.Tendsto (fun x : ℝ => Real.log (base x)) Filter.atTop
        (nhds (Real.log (3 / 2 : ℝ))) :=
    hlogCont.comp gap1
  let c : ℝ := Real.log (3 / 2 : ℝ) / 2
  have hcpos : 0 < c := by
    dsimp [c]
    linarith
  have hlogLower :
      ∀ᶠ x in Filter.atTop, c < Real.log (base x) :=
    hlog.eventually (Ioi_mem_nhds (by dsimp [c]; linarith))
  have hprod :
      Filter.Tendsto
        (fun x : ℝ => Real.log (base x) * exponent x)
        Filter.atTop Filter.atBot := by
    refine Filter.tendsto_atBot.2 ?_
    intro b
    have hexponent :
        ∀ᶠ x in Filter.atTop, exponent x ≤ min 0 (b / c) :=
      (Filter.tendsto_atBot.1 gap4) (min 0 (b / c))
    filter_upwards [hlogLower, hexponent] with x hxlog hxexp
    have he0 : exponent x ≤ 0 :=
      le_trans hxexp (min_le_left _ _)
    have heb : exponent x ≤ b / c :=
      le_trans hxexp (min_le_right _ _)
    calc
      Real.log (base x) * exponent x =
          exponent x * Real.log (base x) := by ring
      _ ≤ exponent x * c :=
        mul_le_mul_of_nonpos_left (le_of_lt hxlog) he0
      _ ≤ (b / c) * c :=
        mul_le_mul_of_nonneg_right heb (le_of_lt hcpos)
      _ = b := by field_simp [ne_of_gt hcpos]
  have hexp :
      Filter.Tendsto
        (fun x : ℝ => Real.exp (Real.log (base x) * exponent x))
        Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hprod
  have hbasePos : ∀ᶠ x in Filter.atTop, 0 < base x :=
    gap1.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 3 / 2))
  refine hexp.congr' ?_
  filter_upwards [hbasePos] with x hx
  unfold f
  exact (Real.rpow_def_of_pos hx (exponent x)).symm

end

end ProofGap.Exercise508
