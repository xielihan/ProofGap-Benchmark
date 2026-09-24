import ProofGapLean.Prelude.Core
import Mathlib.Data.Set.Card
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3365_4

noncomputable section

def identityFunction (x : ℝ) : ℝ :=
  x

def negIdentityFunction (x : ℝ) : ℝ :=
  -x

def absoluteValueFunction (x : ℝ) : ℝ :=
  |x|

def negAbsoluteValueFunction (x : ℝ) : ℝ :=
  -|x|

def IsContinuousSquareRootChoice (y : ℝ → ℝ) : Prop :=
  Continuous y ∧ ∀ x, x ^ 2 = y x ^ 2

def valueOneAtOneSolutions : Set (ℝ → ℝ) :=
  {y | IsContinuousSquareRootChoice y ∧ y 1 = 1}

def valueZeroAtZeroSolutions : Set (ℝ → ℝ) :=
  {y | IsContinuousSquareRootChoice y ∧ y 0 = 0}

private theorem classifySquareRootChoice (y : ℝ → ℝ)
    (hy : IsContinuousSquareRootChoice y) :
    y = identityFunction ∨ y = negIdentityFunction ∨
      y = absoluteValueFunction ∨ y = negAbsoluteValueFunction := by
  rcases hy with ⟨hcont, hsq⟩
  have hcases : ∀ x : ℝ, y x = x ∨ y x = -x := by
    intro x
    have hfac : (y x - x) * (y x + x) = 0 := by
      nlinarith [hsq x]
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (by nlinarith)
    · exact Or.inr (by nlinarith)
  have hpos_same : ∀ {a b : ℝ}, 0 < a → 0 < b → y a = a → y b = b := by
    intro a b ha hb hya
    rcases hcases b with hyb | hyb
    · exact hyb
    · exfalso
      rcases le_total a b with hab | hba
      · have hz : (0 : ℝ) ∈ Set.Icc (-y a) (-y b) := by
          constructor <;> nlinarith
        rcases (intermediate_value_Icc hab hcont.neg.continuousOn) hz with
          ⟨c, hc, hc0⟩
        rcases hc with ⟨hac, hcb⟩
        change -y c = 0 at hc0
        nlinarith [hsq c]
      · have hz : (0 : ℝ) ∈ Set.Icc (y b) (y a) := by
          constructor <;> nlinarith
        rcases (intermediate_value_Icc hba hcont.continuousOn) hz with
          ⟨c, hc, hc0⟩
        rcases hc with ⟨hbc, hca⟩
        nlinarith [hsq c]
  have hneg_same : ∀ {a b : ℝ}, a < 0 → b < 0 → y a = a → y b = b := by
    intro a b ha hb hya
    rcases hcases b with hyb | hyb
    · exact hyb
    · exfalso
      rcases le_total a b with hab | hba
      · have hz : (0 : ℝ) ∈ Set.Icc (y a) (y b) := by
          constructor <;> nlinarith
        rcases (intermediate_value_Icc hab hcont.continuousOn) hz with
          ⟨c, hc, hc0⟩
        rcases hc with ⟨hac, hcb⟩
        nlinarith [hsq c]
      · have hz : (0 : ℝ) ∈ Set.Icc (-y b) (-y a) := by
          constructor <;> nlinarith
        rcases (intermediate_value_Icc hba hcont.neg.continuousOn) hz with
          ⟨c, hc, hc0⟩
        rcases hc with ⟨hbc, hca⟩
        change -y c = 0 at hc0
        nlinarith [hsq c]
  have hzero : y 0 = 0 := by
    nlinarith [hsq 0]
  have hpos_id : ∀ {x : ℝ}, 0 < x → y 1 = 1 → y x = x := by
    intro x hx h1
    exact hpos_same zero_lt_one hx h1
  have hpos_neg : ∀ {x : ℝ}, 0 < x → y 1 = -(1 : ℝ) → y x = -x := by
    intro x hx h1
    rcases hcases x with hxeq | hxneg
    · have hback := hpos_same hx zero_lt_one hxeq
      exfalso
      nlinarith
    · exact hxneg
  have hneg_id : ∀ {x : ℝ}, x < 0 → y (-1) = (-1 : ℝ) → y x = x := by
    intro x hx hm
    exact hneg_same neg_one_lt_zero hx hm
  have hneg_neg :
      ∀ {x : ℝ}, x < 0 → y (-1) = -(-1 : ℝ) → y x = -x := by
    intro x hx hm
    rcases hcases x with hxeq | hxneg
    · have hback := hneg_same hx neg_one_lt_zero hxeq
      exfalso
      nlinarith
    · exact hxneg
  have hone := hcases (1 : ℝ)
  have hmone := hcases (-1 : ℝ)
  rcases hone with h1 | h1
  · rcases hmone with hm | hm
    · refine Or.inl ?_
      funext x
      change y x = x
      rcases lt_trichotomy x 0 with hx | hx | hx
      · exact hneg_id hx hm
      · subst x
        exact hzero
      · exact hpos_id hx h1
    · refine Or.inr (Or.inr (Or.inl ?_))
      funext x
      change y x = |x|
      rcases lt_trichotomy x 0 with hx | hx | hx
      · simpa [abs_of_neg hx] using hneg_neg hx hm
      · subst x
        simpa using hzero
      · simpa [abs_of_pos hx] using hpos_id hx h1
  · rcases hmone with hm | hm
    · refine Or.inr (Or.inr (Or.inr ?_))
      funext x
      change y x = -|x|
      rcases lt_trichotomy x 0 with hx | hx | hx
      · simpa [abs_of_neg hx] using hneg_id hx hm
      · subst x
        simpa using hzero
      · simpa [abs_of_pos hx] using hpos_neg hx h1
    · refine Or.inr (Or.inl ?_)
      funext x
      change y x = -x
      rcases lt_trichotomy x 0 with hx | hx | hx
      · exact hneg_neg hx hm
      · subst x
        simpa using hzero
      · exact hpos_neg hx h1

theorem gap1 :
    valueOneAtOneSolutions =
      {identityFunction, absoluteValueFunction} := by
  ext y
  simp only [valueOneAtOneSolutions, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨hy, hy1⟩
    rcases classifySquareRootChoice y hy with h | h | h | h
    · exact Or.inl h
    · exfalso
      rw [h] at hy1
      norm_num [negIdentityFunction] at hy1
    · exact Or.inr h
    · exfalso
      rw [h] at hy1
      norm_num [negAbsoluteValueFunction] at hy1
  · rintro (rfl | rfl)
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa [identityFunction] using
          (continuous_id : Continuous (fun x : ℝ => x))
      · intro x
        simp [identityFunction]
      · simp [identityFunction]
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa [absoluteValueFunction] using
          (continuous_abs : Continuous (fun x : ℝ => |x|))
      · intro x
        simpa [absoluteValueFunction] using (sq_abs x).symm
      · simp [absoluteValueFunction]

theorem gap2 :
    valueOneAtOneSolutions.ncard = 2 := by
  rw [gap1]
  have hne : identityFunction ≠ absoluteValueFunction := by
    intro h
    have hx := congrFun h (-1)
    norm_num [identityFunction, absoluteValueFunction] at hx
  simp [hne]

theorem gap3 :
    valueZeroAtZeroSolutions =
      {negIdentityFunction, identityFunction,
        absoluteValueFunction, negAbsoluteValueFunction} := by
  ext y
  simp only [valueZeroAtZeroSolutions, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨hy, _⟩
    rcases classifySquareRootChoice y hy with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro (rfl | rfl | rfl | rfl)
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · have hid : Continuous (fun x : ℝ => x) := continuous_id
        simpa [negIdentityFunction] using hid.neg
      · intro x
        simp [negIdentityFunction]
      · simp [negIdentityFunction]
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa [identityFunction] using
          (continuous_id : Continuous (fun x : ℝ => x))
      · intro x
        simp [identityFunction]
      · simp [identityFunction]
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa [absoluteValueFunction] using
          (continuous_abs : Continuous (fun x : ℝ => |x|))
      · intro x
        simpa [absoluteValueFunction] using (sq_abs x).symm
      · simp [absoluteValueFunction]
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · have habs : Continuous (fun x : ℝ => |x|) := continuous_abs
        simpa [negAbsoluteValueFunction] using habs.neg
      · intro x
        simpa [negAbsoluteValueFunction] using (sq_abs x).symm
      · simp [negAbsoluteValueFunction]

theorem gap4 :
    valueZeroAtZeroSolutions.ncard = 4 := by
  rw [gap3]
  classical
  have hNI_I : negIdentityFunction ≠ identityFunction := by
    intro h
    have hx := congrFun h 1
    norm_num [negIdentityFunction, identityFunction] at hx
  have hNI_A : negIdentityFunction ≠ absoluteValueFunction := by
    intro h
    have hx := congrFun h 1
    norm_num [negIdentityFunction, absoluteValueFunction] at hx
  have hNI_NA : negIdentityFunction ≠ negAbsoluteValueFunction := by
    intro h
    have hx := congrFun h (-1)
    norm_num [negIdentityFunction, negAbsoluteValueFunction] at hx
  have hI_A : identityFunction ≠ absoluteValueFunction := by
    intro h
    have hx := congrFun h (-1)
    norm_num [identityFunction, absoluteValueFunction] at hx
  have hI_NA : identityFunction ≠ negAbsoluteValueFunction := by
    intro h
    have hx := congrFun h 1
    norm_num [identityFunction, negAbsoluteValueFunction] at hx
  have hA_NA : absoluteValueFunction ≠ negAbsoluteValueFunction := by
    intro h
    have hx := congrFun h 1
    norm_num [absoluteValueFunction, negAbsoluteValueFunction] at hx
  let s : Finset (ℝ → ℝ) :=
    {negIdentityFunction, identityFunction, absoluteValueFunction,
      negAbsoluteValueFunction}
  have hs : (↑s : Set (ℝ → ℝ)) =
      {negIdentityFunction, identityFunction, absoluteValueFunction,
        negAbsoluteValueFunction} := by
    ext f
    simp [s]
  rw [← hs]
  simp [s, hNI_I, hNI_A, hNI_NA, hI_A, hI_NA, hA_NA]

end

end ProofGap.Exercise3365_4
