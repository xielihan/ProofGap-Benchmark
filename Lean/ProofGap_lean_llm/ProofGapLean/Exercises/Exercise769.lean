import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise769

noncomputable section

def rationalMap (x : ℝ) : ℝ := 2 * x / (1 + x ^ 2)
def inverseFiber (y : ℝ) : Set ℝ := {x | rationalMap x = y}
def smallBranch (y : ℝ) : ℝ :=
  if y = 0 then 0 else (1 - Real.sqrt (1 - y ^ 2)) / y
def largeBranch (y : ℝ) : ℝ :=
  (1 + Real.sqrt (1 - y ^ 2)) / y

/-- Exercise 769, gap 1; add the defining relation and clear
the nonzero denominator `1+x²`. -/
theorem gap1 (x y : ℝ) (h : y = rationalMap x) :
    x ^ 2 * y - 2 * x + y = 0 := by
  rw [rationalMap] at h
  have hden : 1 + x ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg x]
  field_simp [hden] at h
  nlinarith

/-- Exercise 769, gap 2; interpret `±` as the two inverse
branches and handle `y=0` separately. -/
theorem gap2 (x y : ℝ) (hy : |y| ≤ 1)
    (h : x ^ 2 * y - 2 * x + y = 0) :
    if y = 0 then x = 0
    else x = smallBranch y ∨ x = largeBranch y := by
  by_cases hy0 : y = 0
  · rw [if_pos hy0]
    subst y
    norm_num at h
    linarith
  · rw [if_neg hy0]
    simp only [smallBranch, largeBranch, if_neg hy0]
    rcases abs_le.mp hy with ⟨hyl, hyu⟩
    have hrad : 0 ≤ 1 - y ^ 2 := by
      have hp : 0 ≤ (1 - y) * (1 + y) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    have hsnonneg : 0 ≤ Real.sqrt (1 - y ^ 2) :=
      Real.sqrt_nonneg _
    have hsq : (Real.sqrt (1 - y ^ 2)) ^ 2 = 1 - y ^ 2 :=
      Real.sq_sqrt hrad
    have hyh : y * (x ^ 2 * y - 2 * x + y) = 0 := by
      rw [h, mul_zero]
    have heq :
        (y * x - 1) ^ 2 = (Real.sqrt (1 - y ^ 2)) ^ 2 := by
      nlinarith [hyh, hsq]
    by_cases hz : 0 ≤ y * x - 1
    · right
      field_simp [hy0]
      nlinarith [heq, hsnonneg]
    · have hzlt : y * x - 1 < 0 := lt_of_not_ge hz
      left
      field_simp [hy0]
      nlinarith [heq, hsnonneg]

/-- Exercise 769, gap 3; state equality on the punctured
neighborhood where both quotients are defined. -/
theorem gap3 :
    ∀ᶠ y in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      (1 - Real.sqrt (1 - y ^ 2)) / y =
        y ^ 2 / (y * (1 + Real.sqrt (1 - y ^ 2))) := by
  have hIoo :
      ∀ᶠ y : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        y ∈ Set.Ioo (-1) 1 := by
    exact
      (show nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ ≤ nhds (0 : ℝ) from
        inf_le_left)
        (Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
          (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hIoo, self_mem_nhdsWithin] with y hyI hy0
  have hyne : y ≠ 0 := by
    simpa using hy0
  have hrad : 0 ≤ 1 - y ^ 2 := by
    have hp : 0 < (1 - y) * (1 + y) :=
      mul_pos (by linarith [hyI.2]) (by linarith [hyI.1])
    nlinarith
  have hsq : (Real.sqrt (1 - y ^ 2)) ^ 2 = 1 - y ^ 2 :=
    Real.sq_sqrt hrad
  have hconj : 1 + Real.sqrt (1 - y ^ 2) ≠ 0 := by
    nlinarith [Real.sqrt_nonneg (1 - y ^ 2)]
  have hnum :
      (1 - Real.sqrt (1 - y ^ 2)) *
          (1 + Real.sqrt (1 - y ^ 2)) = y ^ 2 := by
    nlinarith [hsq]
  calc
    (1 - Real.sqrt (1 - y ^ 2)) / y =
        ((1 - Real.sqrt (1 - y ^ 2)) *
            (1 + Real.sqrt (1 - y ^ 2))) /
          (y * (1 + Real.sqrt (1 - y ^ 2))) := by
            field_simp [hyne, hconj]
    _ = y ^ 2 / (y * (1 + Real.sqrt (1 - y ^ 2))) := by
      rw [hnum]

/-- Exercise 769, gap 4. -/
theorem gap4 :
    Filter.Tendsto
      (fun y : ℝ => y ^ 2 / (y * (1 + Real.sqrt (1 - y ^ 2))))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
  have hy0 :
      Filter.Tendsto (fun y : ℝ => y) (nhds 0) (nhds 0) :=
    continuousAt_id
  have hy :
      Filter.Tendsto (fun y : ℝ => y)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
    Filter.Tendsto.mono_left hy0 inf_le_left
  have hinner :
      Filter.Tendsto (fun y : ℝ => 1 - y ^ 2)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using
      ((tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
            (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1)).sub (hy.pow 2))
  have hsqrt :
      Filter.Tendsto (fun y : ℝ => Real.sqrt (1 - y ^ 2))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hinner)
  have hden :
      Filter.Tendsto
        (fun y : ℝ => 1 + Real.sqrt (1 - y ^ 2))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 2) := by
    have hden' :
        Filter.Tendsto
          (fun y : ℝ => 1 + Real.sqrt (1 - y ^ 2))
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds ((1 : ℝ) + 1)) :=
      (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
            (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1)).add hsqrt
    norm_num at hden'
    exact hden'
  have ht :
      Filter.Tendsto
        (fun y : ℝ => y / (1 + Real.sqrt (1 - y ^ 2)))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using hy.div hden (by norm_num : (2 : ℝ) ≠ 0)
  have heq :
      (fun y : ℝ => y ^ 2 /
        (y * (1 + Real.sqrt (1 - y ^ 2)))) =ᶠ[
          nhdsWithin 0 ({0} : Set ℝ)ᶜ]
      (fun y : ℝ => y / (1 + Real.sqrt (1 - y ^ 2))) := by
    filter_upwards [self_mem_nhdsWithin] with y hy0
    have hyne : y ≠ 0 := by
      simpa using hy0
    have hconj : 1 + Real.sqrt (1 - y ^ 2) ≠ 0 := by
      nlinarith [Real.sqrt_nonneg (1 - y ^ 2)]
    field_simp [hyne, hconj]
  exact (Filter.Tendsto.congr' heq.symm) ht

/-- Exercise 769, gap 5. -/
theorem gap5 :
    Filter.Tendsto (fun y : ℝ => (1 - Real.sqrt (1 - y ^ 2)) / y)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
  have heq :
      (fun y : ℝ => y ^ 2 /
        (y * (1 + Real.sqrt (1 - y ^ 2)))) =ᶠ[
          nhdsWithin 0 ({0} : Set ℝ)ᶜ]
      (fun y : ℝ => (1 - Real.sqrt (1 - y ^ 2)) / y) := by
    filter_upwards [gap3] with y hy
    exact hy.symm
  exact (Filter.Tendsto.congr' heq) gap4

/-- Exercise 769, gap 6; replace the unsigned `∞` by the
two one-sided infinite limits. -/
theorem gap6 :
    Filter.Tendsto largeBranch (nhdsWithin 0 (Set.Ioi 0))
        (Filter.atTop : Filter ℝ) ∧
      Filter.Tendsto largeBranch (nhdsWithin 0 (Set.Iio 0))
        (Filter.atBot : Filter ℝ) := by
  constructor
  · have hinv :
        Filter.Tendsto (fun y : ℝ => y⁻¹)
          (nhdsWithin 0 (Set.Ioi 0)) (Filter.atTop : Filter ℝ) :=
      tendsto_inv_nhdsGT_zero
    apply Filter.tendsto_atTop.2
    intro b
    have hb := Filter.tendsto_atTop.1 hinv b
    filter_upwards [hb, self_mem_nhdsWithin] with y hby hy
    have hypos : 0 < y := by
      simpa using hy
    have hnum : 1 ≤ 1 + Real.sqrt (1 - y ^ 2) := by
      nlinarith [Real.sqrt_nonneg (1 - y ^ 2)]
    have hinvnonneg : 0 ≤ y⁻¹ :=
      le_of_lt (inv_pos.mpr hypos)
    calc
      b ≤ y⁻¹ := hby
      _ ≤ largeBranch y := by
        simpa [largeBranch, div_eq_mul_inv] using
          mul_le_mul_of_nonneg_right hnum hinvnonneg
  · have hinv :
        Filter.Tendsto (fun y : ℝ => y⁻¹)
          (nhdsWithin 0 (Set.Iio 0)) (Filter.atBot : Filter ℝ) :=
      tendsto_inv_nhdsLT_zero
    apply Filter.tendsto_atBot.2
    intro b
    have hb := Filter.tendsto_atBot.1 hinv b
    filter_upwards [hb, self_mem_nhdsWithin] with y hby hy
    have hyneg : y < 0 := by
      simpa using hy
    have hnum : 1 ≤ 1 + Real.sqrt (1 - y ^ 2) := by
      nlinarith [Real.sqrt_nonneg (1 - y ^ 2)]
    have hinvnonpos : y⁻¹ ≤ 0 :=
      inv_nonpos.mpr (le_of_lt hyneg)
    calc
      largeBranch y ≤ y⁻¹ := by
        simpa [largeBranch, div_eq_mul_inv] using
          mul_le_mul_of_nonpos_right hnum hinvnonpos
      _ ≤ b := hby

/-- Exercise 769, gap 7; represent the multivalued inverse
as a fiber and make the `y=0` branch explicit. -/
theorem gap7 (y : ℝ) (hy : |y| ≤ 1) :
    inverseFiber y =
      if y = 0 then {0} else {smallBranch y, largeBranch y} := by
  by_cases hy0 : y = 0
  · subst y
    rw [if_pos rfl]
    ext x
    simp only [inverseFiber, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hx
      have hden : 1 + x ^ 2 ≠ 0 := by
        nlinarith [sq_nonneg x]
      rw [rationalMap] at hx
      field_simp [hden] at hx
      nlinarith
    · intro hx
      subst x
      norm_num [rationalMap]
  · rcases abs_le.mp hy with ⟨hyl, hyu⟩
    have hrad : 0 ≤ 1 - y ^ 2 := by
      have hp : 0 ≤ (1 - y) * (1 + y) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    have hsq : (Real.sqrt (1 - y ^ 2)) ^ 2 = 1 - y ^ 2 :=
      Real.sq_sqrt hrad
    have hsq_y :=
      congrArg (fun t : ℝ => y * t) hsq
    have hsmall :
        (smallBranch y) ^ 2 * y - 2 * smallBranch y + y = 0 := by
      simp only [smallBranch, if_neg hy0]
      field_simp [hy0]
      nlinarith [hsq, hsq_y]
    have hlarge :
        (largeBranch y) ^ 2 * y - 2 * largeBranch y + y = 0 := by
      simp only [largeBranch]
      field_simp [hy0]
      nlinarith [hsq, hsq_y]
    have recover (z : ℝ)
        (hz : z ^ 2 * y - 2 * z + y = 0) : rationalMap z = y := by
      rw [rationalMap]
      have hden : 1 + z ^ 2 ≠ 0 := by
        nlinarith [sq_nonneg z]
      field_simp [hden]
      nlinarith
    rw [if_neg hy0]
    ext x
    simp only [inverseFiber, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · intro hx
      have hb := gap2 x y hy (gap1 x y hx.symm)
      simpa only [if_neg hy0] using hb
    · intro hx
      rcases hx with hx | hx
      · subst x
        exact recover (smallBranch y) hsmall
      · subst x
        exact recover (largeBranch y) hlarge

end

end ProofGap.Exercise769
