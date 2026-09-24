import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise506_2

noncomputable section

def original (x : ℝ) : ℝ :=
  Real.rpow ((1 + x) / (2 + x)) ((1 - Real.sqrt x) / (1 - x))
def simplified (x : ℝ) : ℝ :=
  Real.rpow ((1 + x) / (2 + x)) (1 / (1 + Real.sqrt x))

/-- Exercise 506_2, gap 1; express equality of the two represented limits. -/
private theorem original_eq_simplified_of_nonneg
    {x : ℝ} (hx : 0 ≤ x) (hne : x ≠ 1) :
    original x = simplified x := by
  unfold original simplified
  congr 1
  have hsub : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hadd : 1 + Real.sqrt x ≠ 0 := by
    nlinarith
  field_simp [hsub, hadd]
  nlinarith [Real.sq_sqrt hx]

private theorem simplified_continuousAt_one :
    ContinuousAt simplified 1 := by
  have hxpositive : ∀ᶠ x : ℝ in nhds 1, 0 < x := by
    exact Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)
  have hbasePositive :
      ∀ᶠ x : ℝ in nhds 1, 0 < (1 + x) / (2 + x) := by
    filter_upwards [hxpositive] with x hx
    exact div_pos (by linarith) (by linarith)
  have hmodel :
      ContinuousAt
        (fun x : ℝ =>
          Real.exp
            (Real.log ((1 + x) / (2 + x)) *
              (1 / (1 + Real.sqrt x)))) 1 := by
    fun_prop (disch := norm_num)
  have heq :
      simplified =ᶠ[nhds 1]
        (fun x : ℝ =>
          Real.exp
            (Real.log ((1 + x) / (2 + x)) *
              (1 / (1 + Real.sqrt x)))) := by
    filter_upwards [hbasePositive] with x hx
    unfold simplified
    have hrpow :
        Real.rpow ((1 + x) / (2 + x)) (1 / (1 + Real.sqrt x)) =
          Real.exp
            (Real.log ((1 + x) / (2 + x)) *
              (1 / (1 + Real.sqrt x))) := by
      exact Real.rpow_def_of_pos
        (x := (1 + x) / (2 + x))
        (y := 1 / (1 + Real.sqrt x)) hx
    exact hrpow
  have hone :
      simplified 1 =
        Real.exp
          (Real.log ((1 + (1 : ℝ)) / (2 + 1)) *
            (1 / (1 + Real.sqrt 1))) := by
    unfold simplified
    exact Real.rpow_def_of_pos
      (x := (1 + (1 : ℝ)) / (2 + 1))
      (y := 1 / (1 + Real.sqrt 1)) (by norm_num)
  show Filter.Tendsto simplified (nhds 1) (nhds (simplified 1))
  rw [hone]
  exact hmodel.tendsto.congr' heq.symm

theorem gap1 (L : ℝ) :
    Filter.Tendsto original (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds L) ↔
      Filter.Tendsto simplified (nhds 1) (nhds L) := by
  have hnear : ∀ᶠ x : ℝ in nhds 1, 0 < x := by
    exact Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)
  have hpositive :
      ∀ᶠ x : ℝ in nhdsWithin 1 ({1} : Set ℝ)ᶜ, 0 < x := by
    exact Filter.Eventually.filter_mono
      (show nhdsWithin (1 : ℝ) ({1} : Set ℝ)ᶜ ≤ nhds 1 from inf_le_left)
      hnear
  have hne :
      ∀ᶠ x : ℝ in nhdsWithin 1 ({1} : Set ℝ)ᶜ, x ≠ 1 := by
    simpa using
      (self_mem_nhdsWithin :
        ∀ᶠ x : ℝ in nhdsWithin 1 ({1} : Set ℝ)ᶜ,
          x ∈ ({1} : Set ℝ)ᶜ)
  have heq :
      original =ᶠ[nhdsWithin 1 ({1} : Set ℝ)ᶜ] simplified := by
    filter_upwards [hpositive, hne] with x hx hnx
    exact original_eq_simplified_of_nonneg (le_of_lt hx) hnx
  constructor
  · intro h
    have hs :
        Filter.Tendsto simplified (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds L) :=
      h.congr' heq
    have hsub : Set.Ioi (1 : ℝ) ⊆ ({1} : Set ℝ)ᶜ := by
      intro x hx
      simpa using (ne_of_gt hx)
    have hsRight :
        Filter.Tendsto simplified (nhdsWithin 1 (Set.Ioi 1)) (nhds L) :=
      hs.mono_left (nhdsWithin_mono 1 hsub)
    have hcRight :
        Filter.Tendsto simplified (nhdsWithin 1 (Set.Ioi 1))
          (nhds (simplified 1)) :=
      simplified_continuousAt_one.tendsto.mono_left inf_le_left
    have hL : L = simplified 1 := tendsto_nhds_unique hsRight hcRight
    rw [hL]
    exact simplified_continuousAt_one.tendsto
  · intro h
    have hs :
        Filter.Tendsto simplified (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds L) :=
      h.mono_left inf_le_left
    exact hs.congr' heq.symm

/-- Exercise 506_2, gap 2. -/
theorem gap2 :
    Filter.Tendsto simplified (nhds 1) (nhds (Real.sqrt (2 / 3))) := by
  have hvalue : simplified 1 = Real.sqrt (2 / 3) := by
    calc
      simplified 1 = Real.rpow (2 / 3) (1 / 2) := by
        unfold simplified
        norm_num
      _ = Real.sqrt (2 / 3) := by
        simpa only [one_div] using
          (Real.sqrt_eq_rpow (x := (2 / 3 : ℝ))).symm
  rw [← hvalue]
  exact simplified_continuousAt_one.tendsto

/-- Exercise 506_2, gap 3. -/
theorem gap3 :
    Filter.Tendsto original (nhdsWithin 1 ({1} : Set ℝ)ᶜ)
      (nhds (Real.sqrt (2 / 3))) := by
  exact (gap1 (Real.sqrt (2 / 3))).mpr gap2

end

end ProofGap.Exercise506_2
