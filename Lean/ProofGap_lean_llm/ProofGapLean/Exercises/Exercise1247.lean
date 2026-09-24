import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1247

noncomputable section

open Filter

def θ (x : ℝ) : ℝ :=
  1 / 4 + 1 / 2 * (Real.sqrt (x * (x + 1)) - x)

def limitAtZero (u : ℝ → ℝ) (L : ℝ) : Prop :=
  Tendsto u (nhdsWithin 0 (Set.Ici 0)) (nhds L)

def limitAtTop (u : ℝ → ℝ) (L : ℝ) : Prop :=
  Tendsto u atTop (nhds L)

theorem gap1 (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (x + 1) - Real.sqrt x =
      1 / (2 * Real.sqrt (x + θ x)) := by
  have hx1 : 0 ≤ x + 1 := by linarith
  have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsx1 : 0 ≤ Real.sqrt (x + 1) := Real.sqrt_nonneg (x + 1)
  have hsx_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  have hsx1_sq : (Real.sqrt (x + 1)) ^ 2 = x + 1 :=
    Real.sq_sqrt hx1
  have hsqrt_mul :
      Real.sqrt (x * (x + 1)) =
        Real.sqrt x * Real.sqrt (x + 1) := by
    rw [Real.sqrt_mul hx]
  have htheta :
      x + θ x =
        ((Real.sqrt (x + 1) + Real.sqrt x) / 2) ^ 2 := by
    rw [θ]
    nlinarith [hsqrt_mul]
  have hhalf :
      0 ≤ (Real.sqrt (x + 1) + Real.sqrt x) / 2 := by
    nlinarith
  have hsqrt_theta :
      Real.sqrt (x + θ x) =
        (Real.sqrt (x + 1) + Real.sqrt x) / 2 := by
    rw [htheta, Real.sqrt_sq_eq_abs, abs_of_nonneg hhalf]
  have hsqrt1_pos : 0 < Real.sqrt (x + 1) :=
    Real.sqrt_pos.2 (by linarith)
  have hsum_pos :
      0 < Real.sqrt (x + 1) + Real.sqrt x := by
    nlinarith
  have hprod :
      (Real.sqrt (x + 1) - Real.sqrt x) *
          (Real.sqrt (x + 1) + Real.sqrt x) = 1 := by
    nlinarith
  rw [hsqrt_theta]
  rw [show
    2 * ((Real.sqrt (x + 1) + Real.sqrt x) / 2) =
      Real.sqrt (x + 1) + Real.sqrt x by ring]
  exact (eq_div_iff (ne_of_gt hsum_pos)).2 hprod

theorem gap2 (x : ℝ) (hx : 0 ≤ x) :
    θ x = 1 / 4 + 1 / 2 * (Real.sqrt (x * (x + 1)) - x) := by
  rfl

theorem gap3 :
    θ 0 = 1 / 4 := by
  norm_num [θ]

theorem gap4 (x : ℝ) (hx : 0 < x) :
    0 ≤ Real.sqrt (x * (x + 1)) - x := by
  have hp : 0 ≤ x * (x + 1) :=
    mul_nonneg (le_of_lt hx) (by linarith)
  have hs : 0 ≤ Real.sqrt (x * (x + 1)) :=
    Real.sqrt_nonneg _
  have hs_sq : (Real.sqrt (x * (x + 1))) ^ 2 = x * (x + 1) :=
    Real.sq_sqrt hp
  nlinarith

theorem gap5 (x : ℝ) (hx : 0 < x) :
    Real.sqrt (x * (x + 1)) - x =
      x / (Real.sqrt (x * (x + 1)) + x) := by
  have hp : 0 ≤ x * (x + 1) :=
    mul_nonneg (le_of_lt hx) (by linarith)
  have hs_sq : (Real.sqrt (x * (x + 1))) ^ 2 = x * (x + 1) :=
    Real.sq_sqrt hp
  have hden : 0 < Real.sqrt (x * (x + 1)) + x := by
    nlinarith [Real.sqrt_nonneg (x * (x + 1))]
  apply (eq_div_iff (ne_of_gt hden)).2
  nlinarith

theorem gap6 (x : ℝ) (hx : 0 < x) :
    x / (Real.sqrt (x * (x + 1)) + x) < x / (2 * x) := by
  have hp : 0 ≤ x * (x + 1) :=
    mul_nonneg (le_of_lt hx) (by linarith)
  have hs_sq : (Real.sqrt (x * (x + 1))) ^ 2 = x * (x + 1) :=
    Real.sq_sqrt hp
  have hsqrt_gt : x < Real.sqrt (x * (x + 1)) := by
    nlinarith [Real.sqrt_nonneg (x * (x + 1))]
  have hden : 0 < Real.sqrt (x * (x + 1)) + x := by
    nlinarith
  have hright : x / (2 * x) = (1 / 2 : ℝ) := by
    field_simp [ne_of_gt hx]
  rw [hright]
  apply (div_lt_iff₀ hden).2
  nlinarith

theorem gap7 (x : ℝ) (hx : 0 < x) :
    x / (2 * x) = 1 / 2 := by
  field_simp [ne_of_gt hx]

theorem gap8 (x : ℝ) (hx : 0 < x) :
    Real.sqrt (x * (x + 1)) - x < 1 / 2 := by
  rw [gap5 x hx]
  calc
    x / (Real.sqrt (x * (x + 1)) + x) < x / (2 * x) := gap6 x hx
    _ = 1 / 2 := gap7 x hx

theorem gap9 (x : ℝ) (hx : 0 < x) :
    1 / 4 ≤ θ x := by
  rw [gap2 x (le_of_lt hx)]
  nlinarith [gap4 x hx]

theorem gap10 (x : ℝ) (hx : 0 < x) :
    θ x < 1 / 4 + 1 / 4 := by
  rw [gap2 x (le_of_lt hx)]
  nlinarith [gap8 x hx]

theorem gap11 :
    (1 / 4 : ℝ) + 1 / 4 = 1 / 2 := by
  norm_num

theorem gap12 :
    (1 / 4 : ℝ) < 1 / 2 := by
  norm_num

theorem gap13 :
    limitAtZero θ (1 / 4) := by
  unfold limitAtZero
  have hinner :
      ContinuousAt (fun x : ℝ => x * (x + 1)) 0 :=
    continuousAt_id.mul (continuousAt_id.add continuousAt_const)
  have hsqrt :
      ContinuousAt (fun x : ℝ => Real.sqrt (x * (x + 1))) 0 := by
    simpa only [Function.comp_apply] using
      Real.continuous_sqrt.continuousAt.comp hinner
  have hcont : ContinuousAt θ 0 := by
    unfold θ
    exact continuousAt_const.add
      (continuousAt_const.mul (hsqrt.sub continuousAt_id))
  rw [← gap3]
  exact hcont.continuousWithinAt

theorem gap14 :
    limitAtTop θ (1 / 2) ↔
      limitAtTop (fun x => 1 / 4 +
        x / (2 * (Real.sqrt (x * (x + 1)) + x))) (1 / 2) := by
  unfold limitAtTop
  refine tendsto_congr' ((eventually_gt_atTop (0 : ℝ)).mono ?_)
  intro x hx
  have hden : Real.sqrt (x * (x + 1)) + x ≠ 0 := by
    apply ne_of_gt
    nlinarith [Real.sqrt_nonneg (x * (x + 1))]
  rw [θ, gap5 x hx]
  field_simp [hden] <;> ring

theorem gap15 :
    limitAtTop (fun x => 1 / 4 +
      x / (2 * (Real.sqrt (x * (x + 1)) + x))) (1 / 2) := by
  unfold limitAtTop
  have hinv :
      Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have honeConst :
      Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hone :
      Tendsto (fun x : ℝ => 1 + x⁻¹) atTop (nhds 1) := by
    convert honeConst.add hinv using 1 <;> norm_num
  have hsqrtAtOne :
      Tendsto Real.sqrt (nhds (1 : ℝ)) (nhds (Real.sqrt 1)) :=
    Real.continuous_sqrt.continuousAt
  have hsqrt :
      Tendsto (fun x : ℝ => Real.sqrt (1 + x⁻¹)) atTop (nhds 1) := by
    simpa only [Function.comp_apply, Real.sqrt_one] using
      hsqrtAtOne.comp hone
  have hsum :
      Tendsto (fun x : ℝ => Real.sqrt (1 + x⁻¹) + 1)
        atTop (nhds 2) := by
    convert hsqrt.add honeConst using 1 <;> norm_num
  have htwo :
      Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hden :
      Tendsto (fun x : ℝ => 2 * (Real.sqrt (1 + x⁻¹) + 1))
        atTop (nhds 4) := by
    convert htwo.mul hsum using 1 <;> norm_num
  have hfrac :
      Tendsto
        (fun x : ℝ => (2 * (Real.sqrt (1 + x⁻¹) + 1))⁻¹)
        atTop (nhds (1 / 4)) := by
    convert hden.inv₀ (by norm_num : (4 : ℝ) ≠ 0) using 1 <;> norm_num
  have hquarter :
      Tendsto (fun _ : ℝ => (1 / 4 : ℝ)) atTop (nhds (1 / 4)) :=
    tendsto_const_nhds
  have hnorm :
      Tendsto
        (fun x : ℝ => 1 / 4 +
          (2 * (Real.sqrt (1 + x⁻¹) + 1))⁻¹)
        atTop (nhds (1 / 2)) := by
    convert hquarter.add hfrac using 1 <;> norm_num
  apply hnorm.congr'
  refine (eventually_gt_atTop (0 : ℝ)).mono ?_
  intro x hx
  have hfactor :
      x * (x + 1) = x ^ 2 * (1 + x⁻¹) := by
    field_simp [ne_of_gt hx] <;> ring
  have hsqrtScale :
      Real.sqrt (x * (x + 1)) =
        x * Real.sqrt (1 + x⁻¹) := by
    rw [hfactor, Real.sqrt_mul (sq_nonneg x),
      Real.sqrt_sq_eq_abs, abs_of_pos hx]
  have hplus : Real.sqrt (1 + x⁻¹) + 1 ≠ 0 := by
    nlinarith [Real.sqrt_nonneg (1 + x⁻¹)]
  change
    1 / 4 + (2 * (Real.sqrt (1 + x⁻¹) + 1))⁻¹ =
      1 / 4 + x / (2 * (Real.sqrt (x * (x + 1)) + x))
  rw [hsqrtScale]
  field_simp [ne_of_gt hx, hplus] <;> ring

theorem gap16 :
    limitAtTop θ (1 / 2) := by
  exact (gap14).2 gap15

theorem gap17 :
    (∀ x ≥ 0, Real.sqrt (x + 1) - Real.sqrt x =
      1 / (2 * Real.sqrt (x + θ x))) ∧
    (∀ x ≥ 0, 1 / 4 ≤ θ x ∧ θ x ≤ 1 / 2) ∧
    limitAtZero θ (1 / 4) ∧ limitAtTop θ (1 / 2) := by
  constructor
  · intro x hx
    exact gap1 x hx
  constructor
  · intro x hx
    rcases eq_or_lt_of_le hx with hzero | hpos
    · subst x
      constructor <;> norm_num [gap3]
    · constructor
      · exact gap9 x hpos
      · exact le_of_lt (by
          simpa only [gap11] using gap10 x hpos)
  constructor
  · exact gap13
  · exact gap16

end

end ProofGap.Exercise1247
