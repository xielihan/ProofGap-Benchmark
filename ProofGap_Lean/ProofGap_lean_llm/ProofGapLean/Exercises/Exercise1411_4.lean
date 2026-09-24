import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Neighborhoods
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise1411_4

noncomputable section
open Filter
open scoped Topology

def punctured := nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ
def target (x : ℝ) := Real.log 2 / Real.log (1 + x / 100)
def quadraticStage (x : ℝ) :=
  Real.log 2 / (x / 100 - x ^ 2 / 20000)
def leadingModel (x : ℝ) := 100 * Real.log 2 / x
def decimalModel (x : ℝ) := 70 / x
def EventuallyRelApprox (f g : ℝ → ℝ) (ε : ℝ) : Prop :=
  ∀ᶠ x in punctured, |f x - g x| ≤ ε * |g x|

private lemma log_two_bounds :
    (343 / 500 : ℝ) < Real.log 2 ∧ Real.log 2 < 7 / 10 := by
  have hpow_lower : (201 / 200 : ℝ) ^ 138 < 2 := by norm_num
  have hlog_power_lower :
      Real.log ((201 / 200 : ℝ) ^ 138) < Real.log 2 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) hpow_lower
  rw [Real.log_pow] at hlog_power_lower
  have hunit_lower : (1 / 201 : ℝ) ≤ Real.log (201 / 200) := by
    have h := Real.log_le_sub_one_of_pos
      (by norm_num : 0 < (200 / 201 : ℝ))
    rw [show (200 / 201 : ℝ) = (201 / 200 : ℝ)⁻¹ by norm_num,
      Real.log_inv] at h
    norm_num at h ⊢
    linarith
  have hlower : (343 / 500 : ℝ) < Real.log 2 := by
    nlinarith
  have hpow_upper : (2 : ℝ) < (101 / 100 : ℝ) ^ 70 := by norm_num
  have hlog_power_upper :
      Real.log 2 < Real.log ((101 / 100 : ℝ) ^ 70) :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) hpow_upper
  rw [Real.log_pow] at hlog_power_upper
  have hunit_upper : Real.log (101 / 100) ≤ (1 / 100 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos
      (by norm_num : 0 < (101 / 100 : ℝ))
    norm_num at h ⊢
    linarith
  constructor
  · exact hlower
  · nlinarith

theorem gap1 :
    Asymptotics.IsEquivalent punctured target quadraticStage := by
  have hlog2_ne : Real.log 2 ≠ 0 :=
    ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 343 / 500) log_two_bounds.1)
  have hx0 : Tendsto (fun x : ℝ => x) punctured (𝓝 0) := by
    change Tendsto id (𝓝 (0 : ℝ) ⊓ Filter.principal ({0} : Set ℝ)ᶜ) (𝓝 0)
    exact tendsto_id.mono_left inf_le_left
  have ht : Tendsto (fun x : ℝ => x / 100) punctured (𝓝 0) := by
    simpa using hx0.div_const (100 : ℝ)
  have hfac : Tendsto (fun x : ℝ => 1 - x / 200) punctured (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (hx0.div_const (200 : ℝ))
  have hx_ne : ∀ᶠ x in punctured, x ≠ 0 := by
    simpa only [punctured, Set.mem_compl_iff, Set.mem_singleton_iff] using
      (self_mem_nhdsWithin :
        ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, x ∈ ({0} : Set ℝ)ᶜ)
  have hfac_pos : ∀ᶠ x in punctured, 0 < 1 - x / 200 :=
    (tendsto_order.1 hfac).1 0 (by norm_num)
  have hfac_ne : ∀ᶠ x in punctured, 1 - x / 200 ≠ 0 :=
    hfac_pos.mono fun _ hx => ne_of_gt hx
  have hlin_ne : ∀ᶠ x in punctured, x / 100 ≠ 0 :=
    hx_ne.mono fun _ hx => div_ne_zero hx (by norm_num)
  have hqden_ne :
      ∀ᶠ x in punctured, x / 100 - x ^ 2 / 20000 ≠ 0 := by
    filter_upwards [hx_ne, hfac_ne] with x hx hf
    rw [show x / 100 - x ^ 2 / 20000 =
      (x / 100) * (1 - x / 200) by ring]
    exact mul_ne_zero (div_ne_zero hx (by norm_num)) hf
  have hq :
      Asymptotics.IsEquivalent punctured
        (fun x : ℝ => x / 100 - x ^ 2 / 20000)
        (fun x : ℝ => x / 100) := by
    refine (Asymptotics.isEquivalent_iff_tendsto_one hlin_ne).2 ?_
    have heq :
        (fun x : ℝ => 1 - x / 200) =ᶠ[punctured]
          (fun x : ℝ => (x / 100 - x ^ 2 / 20000) / (x / 100)) := by
      filter_upwards [hx_ne] with x hx
      field_simp [hx]
      <;> ring
    exact (tendsto_congr' heq).1 hfac
  have ht_zero :
      Tendsto (fun x : ℝ => x / 100) punctured (𝓝[≠] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨ht, ?_⟩
    filter_upwards [hlin_ne] with x hx
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
  have hlog_slope :
      Tendsto
        (fun t : ℝ => Real.log (1 + t) / t)
        (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa [div_eq_mul_inv, mul_comm, add_comm] using
      (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto_slope_zero
  have hlog_ratio :
      Tendsto
        (fun x : ℝ => Real.log (1 + x / 100) / (x / 100))
        punctured (𝓝 1) := by
    simpa only [Function.comp_apply] using hlog_slope.comp ht_zero
  have hlog :
      Asymptotics.IsEquivalent punctured
        (fun x : ℝ => Real.log (1 + x / 100))
        (fun x : ℝ => x / 100) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hlin_ne).2 hlog_ratio
  have hden :
      Asymptotics.IsEquivalent punctured
        (fun x : ℝ => Real.log (1 + x / 100))
        (fun x : ℝ => x / 100 - x ^ 2 / 20000) :=
    Asymptotics.IsEquivalent.trans hlog hq.symm
  have hratio :
      Tendsto
        (fun x : ℝ =>
          Real.log (1 + x / 100) /
            (x / 100 - x ^ 2 / 20000))
        punctured (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hqden_ne).1 hden
  have hratio_pos :
      ∀ᶠ x in punctured,
        0 < Real.log (1 + x / 100) /
          (x / 100 - x ^ 2 / 20000) :=
    (tendsto_order.1 hratio).1 0 (by norm_num)
  have hlog_ne :
      ∀ᶠ x in punctured, Real.log (1 + x / 100) ≠ 0 := by
    filter_upwards [hratio_pos] with x hx
    intro hzero
    rw [hzero] at hx
    norm_num at hx
  have hstage_ne : ∀ᶠ x in punctured, quadraticStage x ≠ 0 := by
    filter_upwards [hqden_ne] with x hx
    exact div_ne_zero hlog2_ne hx
  refine (Asymptotics.isEquivalent_iff_tendsto_one hstage_ne).2 ?_
  have hinv :
      Tendsto
        (fun x : ℝ =>
          (Real.log (1 + x / 100) /
            (x / 100 - x ^ 2 / 20000))⁻¹)
        punctured (𝓝 1) := by
    simpa using hratio.inv₀ (by norm_num)
  have heq :
      (fun x : ℝ =>
        (Real.log (1 + x / 100) /
          (x / 100 - x ^ 2 / 20000))⁻¹) =ᶠ[punctured]
      (fun x : ℝ => target x / quadraticStage x) := by
    filter_upwards [hqden_ne, hlog_ne] with x hq hl
    dsimp [target, quadraticStage]
    field_simp [hlog2_ne, hq, hl]
  exact (tendsto_congr' heq).1 hinv
theorem gap2 :
    Asymptotics.IsEquivalent punctured quadraticStage leadingModel := by
  have hlog2_ne : Real.log 2 ≠ 0 :=
    ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 343 / 500) log_two_bounds.1)
  have hx0 : Tendsto (fun x : ℝ => x) punctured (𝓝 0) := by
    change Tendsto id (𝓝 (0 : ℝ) ⊓ Filter.principal ({0} : Set ℝ)ᶜ) (𝓝 0)
    exact tendsto_id.mono_left inf_le_left
  have hfac : Tendsto (fun x : ℝ => 1 - x / 200) punctured (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (hx0.div_const (200 : ℝ))
  have hx_ne : ∀ᶠ x in punctured, x ≠ 0 := by
    simpa only [punctured, Set.mem_compl_iff, Set.mem_singleton_iff] using
      (self_mem_nhdsWithin :
        ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, x ∈ ({0} : Set ℝ)ᶜ)
  have hfac_pos : ∀ᶠ x in punctured, 0 < 1 - x / 200 :=
    (tendsto_order.1 hfac).1 0 (by norm_num)
  have hfac_ne : ∀ᶠ x in punctured, 1 - x / 200 ≠ 0 :=
    hfac_pos.mono fun _ hx => ne_of_gt hx
  have hqden_ne :
      ∀ᶠ x in punctured, x / 100 - x ^ 2 / 20000 ≠ 0 := by
    filter_upwards [hx_ne, hfac_ne] with x hx hf
    rw [show x / 100 - x ^ 2 / 20000 =
      (x / 100) * (1 - x / 200) by ring]
    exact mul_ne_zero (div_ne_zero hx (by norm_num)) hf
  have hquad_ne : ∀ᶠ x in punctured, quadraticStage x ≠ 0 := by
    filter_upwards [hqden_ne] with x hx
    exact div_ne_zero hlog2_ne hx
  have hlead_ne : ∀ᶠ x in punctured, leadingModel x ≠ 0 := by
    filter_upwards [hx_ne] with x hx
    exact div_ne_zero (mul_ne_zero (by norm_num) hlog2_ne) hx
  refine (Asymptotics.isEquivalent_iff_tendsto_one hlead_ne).2 ?_
  have hinv :
      Tendsto (fun x : ℝ => (1 - x / 200)⁻¹) punctured (𝓝 1) := by
    simpa using hfac.inv₀ (by norm_num)
  have heq :
      (fun x : ℝ => (1 - x / 200)⁻¹) =ᶠ[punctured]
        (fun x : ℝ => quadraticStage x / leadingModel x) := by
    filter_upwards [hx_ne, hfac_ne] with x hx hf
    dsimp [quadraticStage, leadingModel]
    rw [show x / 100 - x ^ 2 / 20000 =
      (x / 100) * (1 - x / 200) by ring]
    field_simp [hlog2_ne, hx, hf]
  exact (tendsto_congr' heq).1 hinv
theorem gap3 (x : ℝ) (hx : x ≠ 0) :
    Real.log 2 / (x / 100) = leadingModel x := by
  unfold leadingModel
  field_simp [hx]
  <;> ring
theorem gap4 :
    EventuallyRelApprox leadingModel decimalModel (1 / 50 : ℝ) := by
  unfold EventuallyRelApprox
  have hx_ne : ∀ᶠ x in punctured, x ≠ 0 := by
    simpa only [punctured, Set.mem_compl_iff, Set.mem_singleton_iff] using
      (self_mem_nhdsWithin :
        ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, x ∈ ({0} : Set ℝ)ᶜ)
  rcases log_two_bounds with ⟨hlog_lower, hlog_upper⟩
  have hcoef : |100 * Real.log 2 - 70| < (7 / 5 : ℝ) := by
    rw [abs_lt]
    constructor <;> nlinarith
  filter_upwards [hx_ne] with x hx
  have hdiff :
      leadingModel x - decimalModel x =
        (100 * Real.log 2 - 70) / x := by
    dsimp [leadingModel, decimalModel]
    field_simp [hx]
    <;> ring
  calc
    |leadingModel x - decimalModel x| =
        |100 * Real.log 2 - 70| / |x| := by rw [hdiff, abs_div]
    _ ≤ (7 / 5 : ℝ) / |x| :=
      (div_le_div_iff_of_pos_right (abs_pos.mpr hx)).2 (le_of_lt hcoef)
    _ = (1 / 50 : ℝ) * |decimalModel x| := by
      rw [decimalModel, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 70)]
      field_simp [abs_ne_zero.mpr hx]
      <;> ring
theorem gap5 :
    EventuallyRelApprox target decimalModel (1 / 50 : ℝ) := by
  unfold EventuallyRelApprox
  have hlog2_ne : Real.log 2 ≠ 0 :=
    ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 343 / 500) log_two_bounds.1)
  have hx_ne : ∀ᶠ x in punctured, x ≠ 0 := by
    simpa only [punctured, Set.mem_compl_iff, Set.mem_singleton_iff] using
      (self_mem_nhdsWithin :
        ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, x ∈ ({0} : Set ℝ)ᶜ)
  have hlead_ne : ∀ᶠ x in punctured, leadingModel x ≠ 0 := by
    filter_upwards [hx_ne] with x hx
    exact div_ne_zero (mul_ne_zero (by norm_num) hlog2_ne) hx
  have hequiv :
      Asymptotics.IsEquivalent punctured target leadingModel :=
    Asymptotics.IsEquivalent.trans gap1 gap2
  have hratio :
      Tendsto (fun x : ℝ => target x / leadingModel x)
        punctured (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hlead_ne).1 hequiv
  have hscaled :
      Tendsto
        (fun x : ℝ =>
          (100 * Real.log 2) * (target x / leadingModel x))
        punctured (𝓝 (100 * Real.log 2)) := by
    simpa using
      (tendsto_const_nhds.mul hratio :
        Tendsto
          (fun x : ℝ =>
            (100 * Real.log 2) * (target x / leadingModel x))
          punctured (𝓝 ((100 * Real.log 2) * 1)))
  have hscale_eq :
      (fun x : ℝ =>
        (100 * Real.log 2) * (target x / leadingModel x)) =ᶠ[punctured]
      (fun x : ℝ => x * target x) := by
    filter_upwards [hx_ne] with x hx
    dsimp [leadingModel]
    field_simp [hlog2_ne, hx]
    <;> ring
  have hcoeflim :
      Tendsto (fun x : ℝ => x * target x)
        punctured (𝓝 (100 * Real.log 2)) :=
    (tendsto_congr' hscale_eq).1 hscaled
  have habslim :
      Tendsto (fun x : ℝ => |x * target x - 70|)
        punctured (𝓝 |100 * Real.log 2 - 70|) := by
    simpa using (hcoeflim.sub tendsto_const_nhds).abs
  rcases log_two_bounds with ⟨hlog_lower, hlog_upper⟩
  have hcoef : |100 * Real.log 2 - 70| < (7 / 5 : ℝ) := by
    rw [abs_lt]
    constructor <;> nlinarith
  have hclose :
      ∀ᶠ x in punctured, |x * target x - 70| < (7 / 5 : ℝ) :=
    (tendsto_order.1 habslim).2 (7 / 5 : ℝ) hcoef
  filter_upwards [hx_ne, hclose] with x hx hclose_x
  have hdiff :
      target x - decimalModel x = (x * target x - 70) / x := by
    dsimp [decimalModel]
    field_simp [hx]
    <;> ring
  calc
    |target x - decimalModel x| =
        |x * target x - 70| / |x| := by rw [hdiff, abs_div]
    _ ≤ (7 / 5 : ℝ) / |x| :=
      (div_le_div_iff_of_pos_right (abs_pos.mpr hx)).2 (le_of_lt hclose_x)
    _ = (1 / 50 : ℝ) * |decimalModel x| := by
      rw [decimalModel, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 70)]
      field_simp [abs_ne_zero.mpr hx]
      <;> ring

end
end ProofGap.Exercise1411_4
