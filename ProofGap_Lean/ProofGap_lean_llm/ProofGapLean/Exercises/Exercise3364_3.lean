import ProofGapLean.Prelude.Elementary
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3364_3

noncomputable section

abbrev UnitInterval :=
  {x : ℝ // x ∈ Set.Icc (-1 : ℝ) 1}

def upperSemicircle (x : UnitInterval) : ℝ :=
  Real.sqrt (1 - (x : ℝ) ^ 2)

def lowerSemicircle (x : UnitInterval) : ℝ :=
  -Real.sqrt (1 - (x : ℝ) ^ 2)

def IsContinuousCircleSolution (y : UnitInterval → ℝ) : Prop :=
  Continuous y ∧
    ∀ x : UnitInterval, (x : ℝ) ^ 2 + y x ^ 2 = 1

def hasValueAt (y : UnitInterval → ℝ) (x value : ℝ) : Prop :=
  ∀ p : UnitInterval, (p : ℝ) = x → y p = value

def positiveAtZeroSolutions : Set (UnitInterval → ℝ) :=
  {y | IsContinuousCircleSolution y ∧ hasValueAt y 0 1}

def zeroAtOneSolutions : Set (UnitInterval → ℝ) :=
  {y | IsContinuousCircleSolution y ∧ hasValueAt y 1 0}

private theorem eq_upper_of_zero_value_one
    (y : UnitInterval → ℝ)
    (hy : IsContinuousCircleSolution y)
    (hy0 : hasValueAt y 0 1) :
    y = upperSemicircle := by
  let z : UnitInterval := ⟨0, by norm_num⟩
  have hyz : y z = 1 := hy0 z rfl
  let c : ℝ → UnitInterval := fun t =>
    ⟨max (-1) (min 1 t), by
      constructor
      · exact le_max_left _ _
      · exact max_le (by norm_num) (min_le_left _ _)⟩
  have hc : Continuous c := by
    unfold c
    exact
      (continuous_const.max (continuous_const.min continuous_id)).subtype_mk
        (fun t => by
          constructor
          · exact le_max_left _ _
          · exact max_le (by norm_num) (min_le_left _ _))
  have hcz : c 0 = z := by
    apply Subtype.ext
    norm_num [c, z]
  have hf : Continuous (fun t : ℝ => y (c t)) := hy.1.comp hc
  funext p
  have hcp : c (p : ℝ) = p := by
    apply Subtype.ext
    change max (-1) (min 1 (p : ℝ)) = (p : ℝ)
    rw [min_eq_right p.property.2, max_eq_right p.property.1]
  have hfp : y (c (p : ℝ)) = y p := by rw [hcp]
  have hf0 : y (c 0) = 1 := by rw [hcz]; exact hyz
  have hyp : 0 ≤ y p := by
    by_contra hn
    have hpneg : y p < 0 := lt_of_not_ge hn
    have hpxsq : (p : ℝ) ^ 2 < 1 := by
      nlinarith [hy.2 p]
    by_cases hpz : (p : ℝ) ≤ 0
    · have hzero :
          (0 : ℝ) ∈ Set.Icc (y (c (p : ℝ))) (y (c 0)) := by
        constructor
        · rw [hfp]
          exact le_of_lt hpneg
        · rw [hf0]
          norm_num
      rcases (intermediate_value_Icc hpz hf.continuousOn) hzero with
        ⟨q, hq, hfq⟩
      have hyq : y (c q) = 0 := hfq
      have hpLower : -1 < (p : ℝ) := by
        nlinarith [p.property.1]
      have hqLower : -1 < q := lt_of_lt_of_le hpLower hq.1
      have hq0 : q ≤ 0 := hq.2
      have hcqval : ((c q : UnitInterval) : ℝ) = q := by
        change max (-1) (min 1 q) = q
        rw [min_eq_right (by linarith), max_eq_right (by linarith)]
      have heq := hy.2 (c q)
      rw [hyq, hcqval] at heq
      norm_num at heq
      rcases heq with heq | heq
      · linarith
      · linarith
    · have hzp : (0 : ℝ) ≤ (p : ℝ) := le_of_not_ge hpz
      let g : ℝ → ℝ := fun t => -y (c t)
      have hg : Continuous g := hf.neg
      have hg0 : g 0 = -1 := by
        dsimp [g]
        rw [hf0]
      have hgp : g (p : ℝ) = -y p := by
        dsimp [g]
        rw [hfp]
      have hzero : (0 : ℝ) ∈ Set.Icc (g 0) (g (p : ℝ)) := by
        constructor
        · rw [hg0]
          norm_num
        · rw [hgp]
          linarith
      rcases (intermediate_value_Icc hzp hg.continuousOn) hzero with
        ⟨q, hq, hgq⟩
      have hyq : y (c q) = 0 := by
        dsimp [g] at hgq
        linarith
      have hq0 : 0 ≤ q := hq.1
      have hqp : q ≤ (p : ℝ) := hq.2
      have hpUpper : (p : ℝ) < 1 := by
        nlinarith [p.property.2]
      have hqUpper : q < 1 := lt_of_le_of_lt hqp hpUpper
      have hcqval : ((c q : UnitInterval) : ℝ) = q := by
        change max (-1) (min 1 q) = q
        rw [min_eq_right (by linarith), max_eq_right (by linarith)]
      have heq := hy.2 (c q)
      rw [hyq, hcqval] at heq
      norm_num at heq
      rcases heq with heq | heq
      · linarith
      · linarith
  unfold upperSemicircle
  have hprod :
      0 ≤ (1 - (p : ℝ)) * ((p : ℝ) - (-1)) :=
    mul_nonneg (sub_nonneg.mpr p.property.2)
      (sub_nonneg.mpr p.property.1)
  have hrad : 0 ≤ 1 - (p : ℝ) ^ 2 := by
    nlinarith
  have hsqrt := Real.sqrt_nonneg (1 - (p : ℝ) ^ 2)
  nlinarith [hy.2 p, Real.sq_sqrt hrad]

theorem gap1 :
    positiveAtZeroSolutions = {upperSemicircle} := by
  ext y
  constructor
  · intro hy
    change IsContinuousCircleSolution y ∧ hasValueAt y 0 1 at hy
    have hEq := eq_upper_of_zero_value_one y hy.1 hy.2
    simpa only [Set.mem_singleton_iff] using hEq
  · intro hy
    have hEq : y = upperSemicircle := by
      simpa only [Set.mem_singleton_iff] using hy
    subst y
    change IsContinuousCircleSolution upperSemicircle ∧
      hasValueAt upperSemicircle 0 1
    constructor
    · constructor
      · unfold upperSemicircle
        have hx : Continuous (fun x : UnitInterval => (x : ℝ)) :=
          continuous_subtype_val
        exact Real.continuous_sqrt.comp
          (continuous_const.sub (hx.pow 2))
      · intro p
        unfold upperSemicircle
        have hprod :
            0 ≤ (1 - (p : ℝ)) * ((p : ℝ) - (-1)) :=
          mul_nonneg (sub_nonneg.mpr p.property.2)
            (sub_nonneg.mpr p.property.1)
        have hrad : 0 ≤ 1 - (p : ℝ) ^ 2 := by
          nlinarith
        nlinarith [Real.sq_sqrt hrad]
    · intro p hp
      unfold upperSemicircle
      rw [hp]
      norm_num

theorem gap2 :
    positiveAtZeroSolutions.ncard = 1 := by
  rw [gap1]
  simp

theorem gap3 :
    zeroAtOneSolutions =
      {lowerSemicircle, upperSemicircle} := by
  have hu_mem : upperSemicircle ∈ positiveAtZeroSolutions := by
    rw [gap1]
    simp
  have hu : IsContinuousCircleSolution upperSemicircle := hu_mem.1
  have hl : IsContinuousCircleSolution lowerSemicircle := by
    constructor
    · simpa [lowerSemicircle, upperSemicircle] using hu.1.neg
    · intro p
      simpa [lowerSemicircle, upperSemicircle] using hu.2 p
  have hzeroAtOne :
      ∀ v : UnitInterval → ℝ,
        IsContinuousCircleSolution v → hasValueAt v 1 0 := by
    intro v hv p hp
    have heq := hv.2 p
    rw [hp] at heq
    norm_num at heq
    nlinarith [sq_nonneg (v p)]
  have hclass :
      ∀ v : UnitInterval → ℝ,
        IsContinuousCircleSolution v →
          v = lowerSemicircle ∨ v = upperSemicircle := by
    intro v hv
    let z : UnitInterval := ⟨0, by norm_num⟩
    have hzsq : (v z) ^ 2 = 1 := by
      simpa [z] using hv.2 z
    have hfac : (v z - 1) * (v z + 1) = 0 := by
      nlinarith [hzsq]
    have hzcase : v z = 1 ∨ v z = -1 := by
      rcases mul_eq_zero.mp hfac with h | h
      · left
        linarith
      · right
        linarith
    rcases hzcase with hz | hz
    · right
      apply eq_upper_of_zero_value_one v hv
      intro p hp
      have hpz : p = z := by
        apply Subtype.ext
        simpa [z] using hp
      simpa [hpz] using hz
    · left
      have hvneg :
          IsContinuousCircleSolution (fun p => -v p) := by
        constructor
        · exact hv.1.neg
        · intro p
          simpa only [neg_sq] using hv.2 p
      have hvneg0 : hasValueAt (fun p => -v p) 0 1 := by
        intro p hp
        have hpz : p = z := by
          apply Subtype.ext
          simpa [z] using hp
        subst p
        simp [hz]
      have hneg := eq_upper_of_zero_value_one (fun p => -v p) hvneg hvneg0
      funext p
      have hp := congrFun hneg p
      have hp' := congrArg (fun r : ℝ => -r) hp
      simpa [lowerSemicircle, upperSemicircle] using hp'
  ext y
  change
    (IsContinuousCircleSolution y ∧ hasValueAt y 1 0) ↔
      y ∈ ({lowerSemicircle, upperSemicircle} : Set (UnitInterval → ℝ))
  constructor
  · intro hy
    rcases hclass y hy.1 with h | h
    · simp [h]
    · simp [h]
  · intro hy
    have hcases : y = lowerSemicircle ∨ y = upperSemicircle := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hy
    rcases hcases with h | h
    · subst y
      exact ⟨hl, hzeroAtOne lowerSemicircle hl⟩
    · subst y
      exact ⟨hu, hzeroAtOne upperSemicircle hu⟩

theorem gap4 :
    zeroAtOneSolutions.ncard = 2 := by
  rw [gap3]
  have hne : lowerSemicircle ≠ upperSemicircle := by
    intro h
    let z : UnitInterval := ⟨0, by norm_num⟩
    have hz := congrFun h z
    norm_num [lowerSemicircle, upperSemicircle, z] at hz
  simp [hne]

end

end ProofGap.Exercise3364_3
