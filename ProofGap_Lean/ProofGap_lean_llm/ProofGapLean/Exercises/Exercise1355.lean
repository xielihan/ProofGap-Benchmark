import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1355

noncomputable section

def HasLimitAtOne (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds L)

def f₀ (x : ℝ) : ℝ := 1 / Real.log x - 1 / (x - 1)
def f₁ (x : ℝ) : ℝ := (x - Real.log x - 1) / ((x - 1) * Real.log x)
def f₂ (x : ℝ) : ℝ := (1 - 1 / x) / ((x - 1) / x + Real.log x)
def f₃ (x : ℝ) : ℝ := (x - 1) / (x - 1 + x * Real.log x)
def f₄ (x : ℝ) : ℝ := 1 / (2 + Real.log x)

private theorem all_function_limits :
    HasLimitAtOne f₀ (1 / 2) ∧ HasLimitAtOne f₁ (1 / 2) ∧
      HasLimitAtOne f₂ (1 / 2) ∧ HasLimitAtOne f₃ (1 / 2) ∧
        HasLimitAtOne f₄ (1 / 2) := by
  let F := nhdsWithin (1 : ℝ) ({1} : Set ℝ)ᶜ
  have hIdN : Filter.Tendsto (fun x : ℝ => x) (nhds 1) (nhds 1) :=
    continuousAt_id
  have honeN : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) (nhds 1) (nhds 1) :=
    tendsto_const_nhds
  have hlogN : Filter.Tendsto Real.log (nhds 1) (nhds 0) := by
    have hc : ContinuousAt Real.log 1 :=
      (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).continuousAt
    change Filter.Tendsto Real.log (nhds 1) (nhds (Real.log 1)) at hc
    simpa only [Real.log_one] using hc
  have hId : Filter.Tendsto (fun x : ℝ => x) F (nhds 1) :=
    hIdN.mono_left inf_le_left
  have hone : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) F (nhds 1) :=
    honeN.mono_left inf_le_left
  have hx0N : ∀ᶠ x : ℝ in nhds 1, x ≠ 0 :=
    eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0)
  have hx0 : ∀ᶠ x : ℝ in F, x ≠ 0 :=
    hx0N.filter_mono inf_le_left
  have hxpos : ∀ᶠ x : ℝ in F, 0 < x := by
    exact hId.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  have hx1 : ∀ᶠ x : ℝ in F, x ≠ 1 := by
    simpa [F] using
      (self_mem_nhdsWithin : ∀ᶠ x : ℝ in nhdsWithin 1 ({1} : Set ℝ)ᶜ,
        x ∈ ({1} : Set ℝ)ᶜ)
  have hlog : Filter.Tendsto Real.log F (nhds 0) :=
    hlogN.mono_left inf_le_left
  have hlogSlope :
      Filter.Tendsto (fun x : ℝ => Real.log x / (x - 1)) F (nhds 1) := by
    have h := (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto_slope
    unfold slope at h
    simpa only [Real.log_one, vsub_eq_sub, sub_zero, one_div, inv_one,
      smul_eq_mul, div_eq_mul_inv, mul_comm] using h
  have hden :
      Filter.Tendsto (fun x : ℝ => 1 + x * (Real.log x / (x - 1))) F
        (nhds 2) := by
    have h := hone.add (hId.mul hlogSlope)
    norm_num at h
    exact h
  have hrecip : ContinuousAt (fun y : ℝ => (1 : ℝ) / y) 2 :=
    (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) 2).div
      continuousAt_id (by norm_num)
  have hrat :
      Filter.Tendsto (fun x : ℝ => 1 / (1 + x * (Real.log x / (x - 1)))) F
        (nhds (1 / 2)) := by
    simpa using hrecip.tendsto.comp hden
  have heq3 :
      (fun x : ℝ => f₃ x) =ᶠ[F]
        (fun x : ℝ => 1 / (1 + x * (Real.log x / (x - 1)))) := by
    filter_upwards [hx1] with x hx
    have hxm : x - 1 ≠ 0 := sub_ne_zero.mpr hx
    have hs :
        1 + x * (Real.log x / (x - 1)) =
          (x - 1 + x * Real.log x) / (x - 1) := by
      field_simp [hxm]
    unfold f₃
    rw [hs, one_div_div]
  have h3 : HasLimitAtOne f₃ (1 / 2) := by
    unfold HasLimitAtOne
    exact hrat.congr' heq3.symm
  have heq23 : (fun x : ℝ => f₂ x) =ᶠ[F] (fun x : ℝ => f₃ x) := by
    filter_upwards [hx0] with x hx
    have hn : 1 - 1 / x = (x - 1) / x := by
      field_simp [hx]
    have hd :
        (x - 1) / x + Real.log x =
          (x - 1 + x * Real.log x) / x := by
      field_simp [hx]
    unfold f₂ f₃
    rw [hn, hd]
    by_cases hs : x - 1 + x * Real.log x = 0
    · simp [hs]
    · field_simp [hx, hs]
  have h2 : HasLimitAtOne f₂ (1 / 2) := by
    unfold HasLimitAtOne at h3 ⊢
    exact h3.congr' heq23.symm
  have hN :
      Filter.Tendsto (fun x : ℝ => x - Real.log x - 1) (nhds 1) (nhds 0) := by
    simpa using (hIdN.sub hlogN).sub honeN
  have hD :
      Filter.Tendsto (fun x : ℝ => (x - 1) * Real.log x) (nhds 1) (nhds 0) := by
    simpa using (hIdN.sub honeN).mul hlogN
  have hq : ∀ᶠ x : ℝ in F, (x - 1) / x + Real.log x ≠ 0 := by
    filter_upwards [hxpos, hx1] with x hxp hx
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · have ha : (x - 1) / x < 0 :=
        div_neg_of_neg_of_pos (sub_neg.mpr hlt) hxp
      have hb : Real.log x < 0 := Real.log_neg hxp hlt
      linarith
    · have ha : 0 < (x - 1) / x := div_pos (sub_pos.mpr hgt) hxp
      have hb : 0 < Real.log x := Real.log_pos hgt
      linarith
  have hNder : ∀ᶠ x : ℝ in nhds 1,
      HasDerivAt (fun y : ℝ => y - Real.log y - 1) (1 - 1 / x) x := by
    filter_upwards [hx0N] with x hx
    simpa [div_eq_mul_inv] using
      ((hasDerivAt_id x).sub (Real.hasDerivAt_log hx)).sub_const 1
  have hDder : ∀ᶠ x : ℝ in nhds 1,
      HasDerivAt (fun y : ℝ => (y - 1) * Real.log y)
        ((x - 1) / x + Real.log x) x := by
    filter_upwards [hx0N] with x hx
    simpa [div_eq_mul_inv, add_comm] using
      ((hasDerivAt_id x).sub_const 1).mul (Real.hasDerivAt_log hx)
  have hder :
      Filter.Tendsto
        (fun x : ℝ => (1 - 1 / x) / ((x - 1) / x + Real.log x)) F
        (nhds (1 / 2)) := by
    unfold HasLimitAtOne at h2
    change Filter.Tendsto
      (fun x : ℝ => (1 - 1 / x) / ((x - 1) / x + Real.log x)) F
      (nhds (1 / 2)) at h2
    exact h2
  have hGTle : nhdsWithin (1 : ℝ) (Set.Ioi 1) ≤ F := by
    dsimp [F]
    apply nhdsWithin_mono
    intro x hx
    simp only [Set.mem_Ioi] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt hx
  have hLTle : nhdsWithin (1 : ℝ) (Set.Iio 1) ≤ F := by
    dsimp [F]
    apply nhdsWithin_mono
    intro x hx
    simp only [Set.mem_Iio] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_lt hx
  have hquotGT :
      Filter.Tendsto
        (fun x : ℝ => (x - Real.log x - 1) / ((x - 1) * Real.log x))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 / 2)) := by
    exact HasDerivAt.lhopital_zero_nhdsGT
      (hNder.filter_mono inf_le_left)
      (hDder.filter_mono inf_le_left)
      (hq.filter_mono hGTle)
      (hN.mono_left inf_le_left)
      (hD.mono_left inf_le_left)
      (hder.mono_left hGTle)
  have hquotLT :
      Filter.Tendsto
        (fun x : ℝ => (x - Real.log x - 1) / ((x - 1) * Real.log x))
        (nhdsWithin 1 (Set.Iio 1)) (nhds (1 / 2)) := by
    exact HasDerivAt.lhopital_zero_nhdsLT
      (hNder.filter_mono inf_le_left)
      (hDder.filter_mono inf_le_left)
      (hq.filter_mono hLTle)
      (hN.mono_left inf_le_left)
      (hD.mono_left inf_le_left)
      (hder.mono_left hLTle)
  have hcompl : ({1} : Set ℝ)ᶜ = Set.Iio 1 ∪ Set.Ioi 1 := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_Iio, Set.mem_Ioi]
    constructor
    · exact lt_or_gt_of_ne
    · intro h
      exact h.elim ne_of_lt ne_of_gt
  have hquot :
      Filter.Tendsto
        (fun x : ℝ => (x - Real.log x - 1) / ((x - 1) * Real.log x)) F
        (nhds (1 / 2)) := by
    dsimp [F]
    rw [hcompl, nhdsWithin_union]
    exact hquotLT.sup hquotGT
  have h1 : HasLimitAtOne f₁ (1 / 2) := by
    simpa [HasLimitAtOne, f₁, F] using hquot
  have heq01 : (fun x : ℝ => f₀ x) =ᶠ[F] (fun x : ℝ => f₁ x) := by
    filter_upwards [hx1, hxpos] with x hx hxp
    have hxm : x - 1 ≠ 0 := sub_ne_zero.mpr hx
    have hl : Real.log x ≠ 0 := by
      intro hz
      rcases lt_or_gt_of_ne hx with hlt | hgt
      · exact (ne_of_lt (Real.log_neg hxp hlt)) hz
      · exact (ne_of_gt (Real.log_pos hgt)) hz
    unfold f₀ f₁
    field_simp [hxm, hl]
    ring
  have h0 : HasLimitAtOne f₀ (1 / 2) := by
    unfold HasLimitAtOne at h1 ⊢
    exact h1.congr' heq01.symm
  have htwo : Filter.Tendsto (fun _ : ℝ => (2 : ℝ)) F (nhds 2) :=
    tendsto_const_nhds
  have hden4 :
      Filter.Tendsto (fun x : ℝ => 2 + Real.log x) F (nhds 2) := by
    simpa using htwo.add hlog
  have h4 : HasLimitAtOne f₄ (1 / 2) := by
    unfold HasLimitAtOne f₄
    simpa only [Function.comp_apply, one_div] using hrecip.tendsto.comp hden4
  exact ⟨h0, h1, h2, h3, h4⟩

theorem gap1 : HasLimitAtOne f₀ (1 / 2) ↔ HasLimitAtOne f₁ (1 / 2) := by
  exact iff_of_true all_function_limits.1 all_function_limits.2.1
theorem gap2 : HasLimitAtOne f₁ (1 / 2) ↔ HasLimitAtOne f₂ (1 / 2) := by
  exact iff_of_true all_function_limits.2.1 all_function_limits.2.2.1
theorem gap3 : HasLimitAtOne f₂ (1 / 2) ↔ HasLimitAtOne f₃ (1 / 2) := by
  exact iff_of_true all_function_limits.2.2.1 all_function_limits.2.2.2.1
theorem gap4 : HasLimitAtOne f₃ (1 / 2) ↔ HasLimitAtOne f₄ (1 / 2) := by
  exact iff_of_true all_function_limits.2.2.2.1 all_function_limits.2.2.2.2
theorem gap5 : HasLimitAtOne f₄ (1 / 2) := by
  exact all_function_limits.2.2.2.2
theorem gap6 : HasLimitAtOne f₀ (1 / 2) := by
  exact all_function_limits.1

end

end ProofGap.Exercise1355
