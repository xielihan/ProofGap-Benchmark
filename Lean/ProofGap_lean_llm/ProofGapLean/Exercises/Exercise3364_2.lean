import ProofGapLean.Prelude.Elementary
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3364_2

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

def continuousCircleSolutions : Set (UnitInterval → ℝ) :=
  {y | IsContinuousCircleSolution y}

private def circleCenter : UnitInterval :=
  ⟨0, by constructor <;> norm_num⟩

private def clampUnit (t : ℝ) : UnitInterval :=
  ⟨max (-1) (min 1 t), by
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)⟩

private theorem continuous_clampUnit : Continuous clampUnit := by
  unfold clampUnit
  exact (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _

theorem gap1 :
    continuousCircleSolutions =
      {lowerSemicircle, upperSemicircle} := by
  ext y
  constructor
  · intro hy
    change IsContinuousCircleSolution y at hy
    rcases hy with ⟨hcont, hcircle⟩
    have hcenter : y circleCenter ^ 2 = 1 := by
      simpa [circleCenter] using hcircle circleCenter
    let f : ℝ → ℝ := fun t => y (clampUnit t)
    have hf : Continuous f := hcont.comp continuous_clampUnit
    have hzero_between :
        ∀ a b : ℝ, a ≤ b → 0 ∈ Set.uIcc (f a) (f b) →
          ∃ z ∈ Set.Icc a b, f z = 0 := by
      intro a b hab hz
      rcases (Set.mem_uIcc).1 hz with hz | hz
      · exact intermediate_value_Icc hab hf.continuousOn hz
      · have hn : 0 ∈ Set.Icc (-f a) (-f b) := by
          constructor <;> linarith [hz.1, hz.2]
        rcases intermediate_value_Icc hab hf.neg.continuousOn hn with
          ⟨z, hzab, hz0⟩
        exact ⟨z, hzab, by linarith⟩
    have hnozero :
        ∀ x : UnitInterval, -1 < (x : ℝ) → (x : ℝ) < 1 →
          (0 : ℝ) ∉ Set.uIcc (y x) (y circleCenter) := by
      intro x hxlo hxhi hzmem
      have hclamp_x : clampUnit (x : ℝ) = x := by
        apply Subtype.ext
        simp [clampUnit, x.property.1, x.property.2]
      have hclamp_center : clampUnit 0 = circleCenter := by
        apply Subtype.ext
        norm_num [clampUnit, circleCenter]
      have hfx : f (x : ℝ) = y x := by
        simp [f, hclamp_x]
      have hfcenter : f 0 = y circleCenter := by
        simp [f, hclamp_center]
      rcases le_total (x : ℝ) 0 with hx0 | h0x
      · have hzmem' : 0 ∈ Set.uIcc (f (x : ℝ)) (f 0) := by
          simpa [hfx, hfcenter] using hzmem
        rcases hzero_between (x : ℝ) 0 hx0 hzmem' with
          ⟨z, hz, hz0⟩
        have hzlo : -1 < z := lt_of_lt_of_le hxlo hz.1
        have hzhi : z < 1 := lt_of_le_of_lt hz.2 (by norm_num)
        have hcoord : (clampUnit z : ℝ) = z := by
          simp [clampUnit, le_of_lt hzlo, le_of_lt hzhi]
        have hyz : y (clampUnit z) = 0 := by
          simpa [f] using hz0
        have hzsq := hcircle (clampUnit z)
        rw [hyz, hcoord] at hzsq
        norm_num at hzsq
        rcases hzsq with rfl | rfl
        · norm_num at hzhi
        · norm_num at hzlo
      · have hzmem' : 0 ∈ Set.uIcc (f 0) (f (x : ℝ)) := by
          rw [hfcenter, hfx]
          rcases (Set.mem_uIcc).1 hzmem with hz | hz
          · exact (Set.mem_uIcc).2 (Or.inr hz)
          · exact (Set.mem_uIcc).2 (Or.inl hz)
        rcases hzero_between 0 (x : ℝ) h0x hzmem' with
          ⟨z, hz, hz0⟩
        have hzlo : -1 < z := lt_of_lt_of_le (by norm_num) hz.1
        have hzhi : z < 1 := lt_of_le_of_lt hz.2 hxhi
        have hcoord : (clampUnit z : ℝ) = z := by
          simp [clampUnit, le_of_lt hzlo, le_of_lt hzhi]
        have hyz : y (clampUnit z) = 0 := by
          simpa [f] using hz0
        have hzsq := hcircle (clampUnit z)
        rw [hyz, hcoord] at hzsq
        norm_num at hzsq
        rcases hzsq with rfl | rfl
        · norm_num at hzhi
        · norm_num at hzlo
    change y = lowerSemicircle ∨ y = upperSemicircle
    rcases le_total 0 (y circleCenter) with hc_nonneg | hc_nonpos
    · right
      have hcval : y circleCenter = 1 := by
        nlinarith
      have hcpos : 0 < y circleCenter := by
        nlinarith
      funext x
      change y x = Real.sqrt (1 - (x : ℝ) ^ 2)
      by_cases hxlo : (x : ℝ) = -1
      · have hyzero : y x = 0 := by
          have hx := hcircle x
          rw [hxlo] at hx
          norm_num at hx
          nlinarith
        rw [hyzero, hxlo]
        norm_num
      by_cases hxhi : (x : ℝ) = 1
      · have hyzero : y x = 0 := by
          have hx := hcircle x
          rw [hxhi] at hx
          norm_num at hx
          nlinarith
        rw [hyzero, hxhi]
        norm_num
      have hxlo' : -1 < (x : ℝ) :=
        lt_of_le_of_ne x.property.1 (Ne.symm hxlo)
      have hxhi' : (x : ℝ) < 1 :=
        lt_of_le_of_ne x.property.2 hxhi
      have hy_nonneg : 0 ≤ y x := by
        by_contra h
        have hyneg : y x < 0 := lt_of_not_ge h
        apply hnozero x hxlo' hxhi'
        exact (Set.mem_uIcc).2
          (Or.inl ⟨le_of_lt hyneg, le_of_lt hcpos⟩)
      have hrad : 0 ≤ 1 - (x : ℝ) ^ 2 := by
        have hp : 0 < ((x : ℝ) + 1) * (1 - (x : ℝ)) :=
          mul_pos (by linarith) (by linarith)
        nlinarith
      have hsqrt := Real.sq_sqrt hrad
      have hsqrt_nonneg := Real.sqrt_nonneg (1 - (x : ℝ) ^ 2)
      nlinarith [hcircle x]
    · left
      have hcval : y circleCenter = -1 := by
        nlinarith
      have hcneg : y circleCenter < 0 := by
        nlinarith
      funext x
      change y x = -Real.sqrt (1 - (x : ℝ) ^ 2)
      by_cases hxlo : (x : ℝ) = -1
      · have hyzero : y x = 0 := by
          have hx := hcircle x
          rw [hxlo] at hx
          norm_num at hx
          nlinarith
        rw [hyzero, hxlo]
        norm_num
      by_cases hxhi : (x : ℝ) = 1
      · have hyzero : y x = 0 := by
          have hx := hcircle x
          rw [hxhi] at hx
          norm_num at hx
          nlinarith
        rw [hyzero, hxhi]
        norm_num
      have hxlo' : -1 < (x : ℝ) :=
        lt_of_le_of_ne x.property.1 (Ne.symm hxlo)
      have hxhi' : (x : ℝ) < 1 :=
        lt_of_le_of_ne x.property.2 hxhi
      have hy_nonpos : y x ≤ 0 := by
        by_contra h
        have hypos : 0 < y x := lt_of_not_ge h
        apply hnozero x hxlo' hxhi'
        exact (Set.mem_uIcc).2
          (Or.inr ⟨le_of_lt hcneg, le_of_lt hypos⟩)
      have hrad : 0 ≤ 1 - (x : ℝ) ^ 2 := by
        have hp : 0 < ((x : ℝ) + 1) * (1 - (x : ℝ)) :=
          mul_pos (by linarith) (by linarith)
        nlinarith
      have hsqrt := Real.sq_sqrt hrad
      have hsqrt_nonneg := Real.sqrt_nonneg (1 - (x : ℝ) ^ 2)
      nlinarith [hcircle x]
  · intro hy
    change y = lowerSemicircle ∨ y = upperSemicircle at hy
    change IsContinuousCircleSolution y
    rcases hy with rfl | rfl
    · constructor
      · change Continuous
          (fun x : UnitInterval => -Real.sqrt (1 - (x : ℝ) ^ 2))
        have hbase : Continuous
            (fun x : UnitInterval => (1 : ℝ) - (x : ℝ) ^ 2) :=
          continuous_const.sub (continuous_subtype_val.pow 2)
        exact (Real.continuous_sqrt.comp hbase).neg
      · intro x
        change (x : ℝ) ^ 2 + (-Real.sqrt (1 - (x : ℝ) ^ 2)) ^ 2 = 1
        have hp : 0 ≤ ((x : ℝ) + 1) * (1 - (x : ℝ)) :=
          mul_nonneg (by linarith [x.property.1])
            (by linarith [x.property.2])
        have hrad : 0 ≤ 1 - (x : ℝ) ^ 2 := by
          nlinarith
        nlinarith [Real.sq_sqrt hrad]
    · constructor
      · change Continuous
          (fun x : UnitInterval => Real.sqrt (1 - (x : ℝ) ^ 2))
        have hbase : Continuous
            (fun x : UnitInterval => (1 : ℝ) - (x : ℝ) ^ 2) :=
          continuous_const.sub (continuous_subtype_val.pow 2)
        exact Real.continuous_sqrt.comp hbase
      · intro x
        change (x : ℝ) ^ 2 + Real.sqrt (1 - (x : ℝ) ^ 2) ^ 2 = 1
        have hp : 0 ≤ ((x : ℝ) + 1) * (1 - (x : ℝ)) :=
          mul_nonneg (by linarith [x.property.1])
            (by linarith [x.property.2])
        have hrad : 0 ≤ 1 - (x : ℝ) ^ 2 := by
          nlinarith
        nlinarith [Real.sq_sqrt hrad]

theorem gap2 :
    continuousCircleSolutions.ncard = 2 := by
  rw [gap1]
  have hne : lowerSemicircle ≠ upperSemicircle := by
    intro h
    have hc := congrFun h circleCenter
    norm_num [lowerSemicircle, upperSemicircle, circleCenter] at hc
  simpa using Set.ncard_pair hne

end

end ProofGap.Exercise3364_2
