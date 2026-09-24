import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise479

noncomputable section

def original (x : ℝ) : ℝ :=
  Real.tan (2 * x) * Real.tan (Real.pi / 4 - x)
def sineCosine (x : ℝ) : ℝ :=
  (Real.sin (2 * x) * Real.sin (Real.pi / 4 - x)) /
    (Real.cos (2 * x) * Real.cos (Real.pi / 4 - x))
def shifted (y : ℝ) : ℝ :=
  Real.cos (2 * y) * Real.sin y / (Real.sin (2 * y) * Real.cos y)
def reduced (y : ℝ) : ℝ :=
  Real.cos (2 * y) / (2 * Real.cos y ^ 2)
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 479, gap 1. -/
private theorem tendsto_translate_punctured (a c : ℝ) :
    Filter.Tendsto (fun x : ℝ => x + c)
      (nhdsWithin a (({a} : Set ℝ)ᶜ))
      (nhdsWithin (a + c) (({a + c} : Set ℝ)ᶜ)) := by
  change
    Filter.map (fun x : ℝ => x + c)
        (nhdsWithin a (({a} : Set ℝ)ᶜ)) ≤
      nhds (a + c) ⊓ Filter.principal (({a + c} : Set ℝ)ᶜ)
  refine le_inf ?_ ?_
  · exact
      (continuousAt_id.add continuousAt_const).tendsto.mono_left
        (show nhdsWithin a (({a} : Set ℝ)ᶜ) ≤ nhds a from inf_le_left)
  · refine Filter.tendsto_principal.2 ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
    intro h
    apply hx
    linarith

theorem gap1 (L : ℝ) :
    HasLimitAt original (Real.pi / 4) L ↔
      HasLimitAt sineCosine (Real.pi / 4) L := by
  have hfun : original = sineCosine := by
    funext x
    simp only [original, sineCosine, Real.tan_eq_sin_div_cos]
    exact div_mul_div_comm _ _ _ _
  rw [hfun]

/-- Exercise 479, gap 2; use `y=x-π/4`. -/
theorem gap2 (L : ℝ) :
    HasLimitAt sineCosine (Real.pi / 4) L ↔ HasLimitAt shifted 0 L := by
  have hfun :
      (fun y : ℝ => sineCosine (y + Real.pi / 4)) = shifted := by
    funext y
    unfold sineCosine shifted
    rw [show 2 * (y + Real.pi / 4) = 2 * y + Real.pi / 2 by ring]
    rw [show Real.pi / 4 - (y + Real.pi / 4) = -y by ring]
    simp [Real.sin_add, Real.cos_add]
  have hadd :
      Filter.Tendsto (fun y : ℝ => y + Real.pi / 4)
        (nhdsWithin 0 (({0} : Set ℝ)ᶜ))
        (nhdsWithin (Real.pi / 4) (({Real.pi / 4} : Set ℝ)ᶜ)) := by
    simpa using tendsto_translate_punctured 0 (Real.pi / 4)
  have hsub :
      Filter.Tendsto (fun x : ℝ => x - Real.pi / 4)
        (nhdsWithin (Real.pi / 4) (({Real.pi / 4} : Set ℝ)ᶜ))
        (nhdsWithin 0 (({0} : Set ℝ)ᶜ)) := by
    simpa [sub_eq_add_neg] using
      tendsto_translate_punctured (Real.pi / 4) (-(Real.pi / 4))
  unfold HasLimitAt
  constructor
  · intro h
    rw [← hfun]
    simpa [Function.comp_def] using h.comp hadd
  · intro h
    have hback :
        (fun x : ℝ => shifted (x - Real.pi / 4)) = sineCosine := by
      funext x
      have hx := congrFun hfun (x - Real.pi / 4)
      simpa using hx.symm
    rw [← hback]
    simpa [Function.comp_def] using h.comp hsub

/-- Exercise 479, gap 3. -/
theorem gap3 (L : ℝ) :
    HasLimitAt shifted 0 L ↔ HasLimitAt reduced 0 L := by
  have hI :
      Set.Ioo (-Real.pi) Real.pi ∈
        nhdsWithin 0 (({0} : Set ℝ)ᶜ) :=
    (show nhdsWithin 0 (({0} : Set ℝ)ᶜ) ≤ nhds 0 from inf_le_left)
      (isOpen_Ioo.mem_nhds
        ⟨neg_lt_zero.mpr Real.pi_pos, Real.pi_pos⟩)
  have heq :
      shifted =ᶠ[nhdsWithin 0 (({0} : Set ℝ)ᶜ)] reduced := by
    filter_upwards [hI, self_mem_nhdsWithin] with y hy hy0
    have hy0' : y ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy0
    have hs : Real.sin y ≠ 0 := by
      rcases lt_or_gt_of_ne hy0' with hyneg | hypos
      · have hsneg : Real.sin (-y) ≠ 0 := by
          apply ne_of_gt
          apply Real.sin_pos_of_pos_of_lt_pi
          · linarith
          · linarith [hy.1]
        simpa using hsneg
      · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hypos hy.2)
    by_cases hc : Real.cos y = 0
    · simp [shifted, reduced, Real.sin_two_mul, hc]
    · simp only [shifted, reduced, Real.sin_two_mul]
      field_simp [hs, hc]
  unfold HasLimitAt
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Exercise 479, gap 4. -/
theorem gap4 : HasLimitAt reduced 0 (1 / 2) := by
  have hcont : ContinuousAt reduced 0 := by
    unfold reduced
    apply ContinuousAt.div
    · exact Real.continuous_cos.continuousAt.comp
        (continuousAt_const.mul continuousAt_id)
    · exact continuousAt_const.mul
        (Real.continuous_cos.continuousAt.pow 2)
    · norm_num
  unfold HasLimitAt
  have ht := hcont.tendsto.mono_left
    (show nhdsWithin 0 (({0} : Set ℝ)ᶜ) ≤ nhds 0 from inf_le_left)
  simpa [reduced] using ht

/-- Exercise 479, gap 5. -/
theorem gap5 : HasLimitAt original (Real.pi / 4) (1 / 2) := by
  exact
    (gap1 (1 / 2)).2
      ((gap2 (1 / 2)).2
        ((gap3 (1 / 2)).2 gap4))

end

end ProofGap.Exercise479
