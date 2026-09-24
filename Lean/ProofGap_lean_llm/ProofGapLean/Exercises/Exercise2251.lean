import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed

open scoped Interval

namespace ProofGap.Exercise2251

noncomputable section

def unitIntegral : ℝ := ∫ _x in (-1 : ℝ)..1, (1 : ℝ)
def degenerateIntegral : ℝ :=
  ∫ t in (1 : ℝ)..1, Real.rpow t (1 / 2 : ℝ)

def SignedPowerGraph (t y : ℝ) : Prop :=
  y = Real.rpow t (3 / 2 : ℝ) ∨ y = -Real.rpow t (3 / 2 : ℝ)

def rationalIntegral : ℝ :=
  ∫ x in (-1 : ℝ)..1, 1 / (1 + x ^ 2)

def trigonometricIntegral : ℝ :=
  ∫ x in (0 : ℝ)..Real.pi, 1 / (1 + Real.sin x ^ 2)

def naivePrimitive (x : ℝ) : ℝ :=
  (1 / Real.sqrt 2) *
    Real.arctan (Real.sqrt 2 * Real.tan x)

private abbrev NeBot {α : Type*} (l : Filter α) := Filter.NeBot l

private theorem eventually_gt_atTop (a : ℝ) :
    ∀ᶠ b : ℝ in Filter.atTop, a < b :=
  Filter.eventually_gt_atTop a

private theorem Real.tendsto_tan_nhdsWithin_pi_div_two :
    Tendsto Real.tan
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) Filter.atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro b
  let c : ℝ := 1 / (2 * (|b| + 1))
  have hp : 0 < Real.pi / 2 := by positivity
  have habs : 0 < |b| + 1 := by positivity
  have hden : 0 < 2 * (|b| + 1) := by positivity
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hsinMem :
      Set.Ioi (1 / 2 : ℝ) ∈ nhds (Real.sin (Real.pi / 2)) := by
    simpa using Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)
  have hcosMem :
      Set.Iio c ∈ nhds (Real.cos (Real.pi / 2)) := by
    simpa using Iio_mem_nhds hc
  have hsin :
      ∀ᶠ x in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
        1 / 2 < Real.sin x :=
    (show nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) ≤
        nhds (Real.pi / 2) from inf_le_left)
      (Real.continuous_sin.continuousAt hsinMem)
  have hcos :
      ∀ᶠ x in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
        Real.cos x < c :=
    (show nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) ≤
        nhds (Real.pi / 2) from inf_le_left)
      (Real.continuous_cos.continuousAt hcosMem)
  have hxpos :
      ∀ᶠ x in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)), 0 < x :=
    (show nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) ≤
        nhds (Real.pi / 2) from inf_le_left)
      (Ioi_mem_nhds hp)
  filter_upwards [self_mem_nhdsWithin, hxpos, hsin, hcos] with x hxp hx hs hclt
  have hcx : 0 < Real.cos x := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith
    · exact hxp
  have hscaled : Real.cos x * (2 * (|b| + 1)) < 1 := by
    apply (lt_div_iff₀ hden).mp
    simpa [c] using hclt
  have hbm : b * Real.cos x ≤ |b| * Real.cos x :=
    mul_le_mul_of_nonneg_right (le_abs_self b) hcx.le
  rw [Real.tan_eq_sin_div_cos]
  apply (le_div_iff₀ hcx).2
  nlinarith

theorem gap1 :
    unitIntegral = 2 := by
  norm_num [unitIntegral]

theorem gap2 :
    ¬∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      unitIntegral = s * (3 / 2 : ℝ) * degenerateIntegral := by
  rintro ⟨s, hs, h⟩
  have hdeg : degenerateIntegral = 0 := by
    simp [degenerateIntegral]
  rw [hdeg] at h
  norm_num [gap1] at h

theorem gap3 (s : ℝ) :
    s * (3 / 2 : ℝ) * degenerateIntegral = 0 := by
  simp [degenerateIntegral]

theorem gap4 :
    unitIntegral ≠ 0 := by
  norm_num [gap1]

theorem gap5 :
    ¬∃ g : ℝ → ℝ, ∀ t y : ℝ, SignedPowerGraph t y ↔ g t = y := by
  rintro ⟨g, hg⟩
  have hp : g 1 = 1 :=
    (hg 1 1).mp (by
      left
      norm_num)
  have hn : g 1 = -1 :=
    (hg 1 (-1)).mp (by
      right
      norm_num)
  linarith

theorem gap6 :
    rationalIntegral =
      Real.arctan 1 - Real.arctan (-1) := by
  unfold rationalIntegral
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    simpa [one_div] using Real.hasDerivAt_arctan x
  · exact
      (continuous_const.div
        (continuous_const.add (continuous_id.pow 2))
        (fun x => by
          change (1 + x ^ 2 : ℝ) ≠ 0
          nlinarith [sq_nonneg x])).intervalIntegrable _ _

theorem gap7 :
    Real.arctan 1 - Real.arctan (-1) = Real.pi / 2 := by
  rw [Real.arctan_neg, Real.arctan_one]
  ring

theorem gap8 :
    rationalIntegral = Real.pi / 2 := by
  rw [gap6, gap7]

theorem gap9 :
    rationalIntegral ≠ -rationalIntegral := by
  intro h
  rw [gap8] at h
  have hp := Real.pi_pos
  linarith

theorem gap10 :
    ¬ContinuousAt (fun t : ℝ => 1 / t) 0 := by
  intro h
  have hI : Set.Ioo (-1 : ℝ) 1 ∈ nhds ((fun t : ℝ => 1 / t) 0) := by
    simpa using
      (Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
        (show (0 : ℝ) < 1 by norm_num))
  have hpre : (fun t : ℝ => 1 / t) ⁻¹' Set.Ioo (-1) 1 ∈ nhds 0 := h hI
  rcases Metric.mem_nhds_iff.1 hpre with ⟨ε, hε, hsub⟩
  let x : ℝ := min (ε / 2) (1 / 2)
  have hxpos : 0 < x := by
    dsimp [x]
    exact lt_min (half_pos hε) (by norm_num)
  have hxltε : x < ε :=
    lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hxle : x ≤ 1 := by
    calc
      x ≤ 1 / 2 := min_le_right _ _
      _ ≤ 1 := by norm_num
  have hxball : x ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball]
    simpa [Real.dist_eq, abs_of_pos hxpos] using hxltε
  have hxrange : 1 / x < 1 := (hsub hxball).2
  have hone : 1 ≤ 1 / x := by
    apply (le_div_iff₀ hxpos).2
    simpa using hxle
  linarith

theorem gap11 :
    0 < trigonometricIntegral := by
  unfold trigonometricIntegral
  have hcont : Continuous (fun x : ℝ => 1 / (1 + Real.sin x ^ 2)) :=
    continuous_const.div
      (continuous_const.add (Real.continuous_sin.pow 2))
      (fun x => by nlinarith [sq_nonneg (Real.sin x)])
  refine intervalIntegral.integral_pos Real.pi_pos hcont.continuousOn ?_ ?_
  · intro x hx
    positivity
  · refine ⟨0, ⟨le_rfl, Real.pi_pos.le⟩, ?_⟩
    norm_num

theorem gap12 :
    trigonometricIntegral ≠
      naivePrimitive Real.pi - naivePrimitive 0 := by
  have hprim : naivePrimitive Real.pi - naivePrimitive 0 = 0 := by
    simp [naivePrimitive]
  rw [hprim]
  exact ne_of_gt gap11

theorem gap13 :
    naivePrimitive Real.pi - naivePrimitive 0 = 0 := by
  simp [naivePrimitive]

theorem gap14 :
    trigonometricIntegral ≠ 0 := by
  exact ne_of_gt gap11

theorem gap15 :
    ¬ContinuousAt Real.tan (Real.pi / 2) := by
  intro h
  have htop :
      Tendsto Real.tan
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) atTop :=
    Real.tendsto_tan_nhdsWithin_pi_div_two
  have hgt :
      ∀ᶠ x in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
        1 < Real.tan x :=
    htop (eventually_gt_atTop (1 : ℝ))
  have htan0 : Real.tan (Real.pi / 2) = 0 := by
    simp [Real.tan_eq_sin_div_cos]
  have htarget : Set.Iio (1 : ℝ) ∈ nhds (Real.tan (Real.pi / 2)) := by
    rw [htan0]
    exact Iio_mem_nhds (by norm_num)
  have hpre : Real.tan ⁻¹' Set.Iio (1 : ℝ) ∈ nhds (Real.pi / 2) :=
    h htarget
  have hlt :
      ∀ᶠ x in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
        Real.tan x < 1 :=
    (show nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) ≤
        nhds (Real.pi / 2) from inf_le_left) hpre
  have hpclosure :
      Real.pi / 2 ∈ closure (Set.Iio (Real.pi / 2)) := by
    simp
  letI : NeBot (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) :=
    mem_closure_iff_nhdsWithin_neBot.mp hpclosure
  rcases (hgt.and hlt).exists with ⟨x, hxgt, hxlt⟩
  linarith

end

end ProofGap.Exercise2251
