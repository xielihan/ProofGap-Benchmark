import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1956

noncomputable section

def q (x : ℝ) := x ^ 2 - 4 * x + 3
def branch : Set ℝ := {x | 0 < q x}
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def BranchwisePrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ u : Set ℝ, IsOpen u → IsPreconnected u → u ⊆ s →
    ∃ C : ℝ, ∀ x ∈ u, F x = p x + C}
def integrand (x : ℝ) :=
  x / ((x ^ 2 - 3 * x + 2) * Real.sqrt (q x))
def partialFraction (x : ℝ) :=
  (2 / (x - 2) - 1 / (x - 1)) / Real.sqrt (q x)
def i1 (x : ℝ) := 1 / ((x - 2) * Real.sqrt (q x))
def i2 (x : ℝ) := 1 / ((x - 1) * Real.sqrt (q x))
def I1 := AntiderivativesOn branch i1
def I2 := AntiderivativesOn branch i2
def TwoPartFamily : Set (ℝ → ℝ) :=
  {F | ∃ A ∈ I1, ∃ B ∈ I2,
    ∀ x ∈ branch, F x = 2 * A x - B x}
def i1Primitive (x : ℝ) := -Real.arcsin (1 / |x - 2|)
def i2Primitive (x : ℝ) := Real.sqrt (q x) / (x - 1)
def finalPrimitive (x : ℝ) :=
  -2 * Real.arcsin (1 / |x - 2|) - Real.sqrt (q x) / (x - 1)

private theorem branch_factor (x : ℝ) : q x = (x - 1) * (x - 3) := by
  unfold q
  ring

private theorem branch_isOpen : IsOpen branch := by
  have h4 : Continuous (fun x : ℝ => (4 : ℝ) * x) :=
    continuous_const.mul continuous_id
  have h3 : Continuous (fun _ : ℝ => (3 : ℝ)) := continuous_const
  have hq : Continuous q := by
    simpa [q] using ((continuous_id.pow 2).sub h4).add h3
  change IsOpen {x : ℝ | 0 < q x}
  exact isOpen_lt continuous_const hq

private theorem integrand_decomposition (x : ℝ) (hx : x ∈ branch) :
    integrand x = 2 * i1 x - i2 x := by
  have hq : 0 < q x := hx
  have hs : Real.sqrt (q x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  have h1 : x - 1 ≠ 0 := by
    intro h
    have : x = 1 := sub_eq_zero.mp h
    subst x
    norm_num [q] at hq
  have h2 : x - 2 ≠ 0 := by
    intro h
    have : x = 2 := sub_eq_zero.mp h
    subst x
    norm_num [q] at hq
  unfold integrand i1 i2
  rw [show x ^ 2 - 3 * x + 2 = (x - 1) * (x - 2) by ring]
  field_simp [h1, h2, hs] <;> ring

private theorem integrand_eq_partialFraction (x : ℝ) (hx : x ∈ branch) :
    integrand x = partialFraction x := by
  rw [integrand_decomposition x hx]
  have hq : 0 < q x := hx
  have hq0 : q x ≠ 0 := ne_of_gt hq
  have hs : Real.sqrt (q x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  have h1 : x - 1 ≠ 0 := by
    intro h
    have : x = 1 := sub_eq_zero.mp h
    subst x
    norm_num [q] at hq
  have h2 : x - 2 ≠ 0 := by
    intro h
    have : x = 2 := sub_eq_zero.mp h
    subst x
    norm_num [q] at hq
  unfold partialFraction i1 i2
  field_simp [h1, h2, hs, hq0, q] <;> ring

private theorem sqrt_ratio_identity (a : ℝ) (ha : 1 < a) :
    Real.sqrt (1 - (1 / a) ^ 2) * a = Real.sqrt (a ^ 2 - 1) := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have ha_ne : a ≠ 0 := ne_of_gt ha0
  have hfrac : 1 - (1 / a) ^ 2 = (a ^ 2 - 1) / a ^ 2 := by
    field_simp [ha_ne] <;> ring
  have harg : 0 ≤ 1 - (1 / a) ^ 2 := by
    rw [hfrac]
    exact div_nonneg (by nlinarith) (sq_nonneg a)
  have hrad : 0 ≤ a ^ 2 - 1 := by nlinarith
  have hs1 := Real.sq_sqrt harg
  have hs2 := Real.sq_sqrt hrad
  have hmul : (1 - (1 / a) ^ 2) * a ^ 2 = a ^ 2 - 1 := by
    field_simp [ha_ne] <;> ring
  have hsq : (Real.sqrt (1 - (1 / a) ^ 2) * a) ^ 2 =
      Real.sqrt (a ^ 2 - 1) ^ 2 := by
    rw [mul_pow, hs1, hs2, hmul]
  have hleft : 0 ≤ Real.sqrt (1 - (1 / a) ^ 2) * a :=
    mul_nonneg (Real.sqrt_nonneg _) (le_of_lt ha0)
  have hright : 0 ≤ Real.sqrt (a ^ 2 - 1) := Real.sqrt_nonneg _
  nlinarith

private theorem hasDerivAt_i2Primitive (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt i2Primitive (i2 x) x := by
  have hq : 0 < q x := hx
  have hq0 : q x ≠ 0 := ne_of_gt hq
  have hs : Real.sqrt (q x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  have h1 : x - 1 ≠ 0 := by
    intro h
    have : x = 1 := sub_eq_zero.mp h
    subst x
    norm_num [q] at hq
  have hqd : HasDerivAt q (2 * x - 4) x := by
    convert
      (((((hasDerivAt_id x).pow 2).sub
        ((hasDerivAt_const x (4 : ℝ)).mul (hasDerivAt_id x))).add
          (hasDerivAt_const x (3 : ℝ)))) using 1 <;>
      simp [q, id_eq] <;> ring
  have hsd : HasDerivAt (fun y : ℝ => Real.sqrt (q y))
      (1 / (2 * Real.sqrt (q x)) * (2 * x - 4)) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sqrt hq0).comp x hqd
  have hden : HasDerivAt (fun y : ℝ => y - 1) 1 x :=
    (hasDerivAt_id x).sub_const 1
  unfold i2Primitive i2
  convert hsd.div hden h1 using 1
  field_simp [h1, hs, hq0]
  rw [Real.sq_sqrt (le_of_lt hq)]
  unfold q
  ring

private theorem hasDerivAt_i1Primitive (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt i1Primitive (i1 x) x := by
  have hq : 0 < q x := hx
  have ht_sq : 1 < (x - 2) ^ 2 := by
    unfold q at hq
    nlinarith
  have hx2 : x ≠ 2 := by
    intro h
    subst x
    norm_num at ht_sq
  rcases lt_or_gt_of_ne hx2 with hxlt | hxgt
  · let a : ℝ := 2 - x
    have ha : 1 < a := by
      dsimp [a]
      nlinarith
    have ht : x - 2 ≠ 0 := sub_ne_zero.mpr hx2
    have hden_ne : 2 - x ≠ 0 := ne_of_gt (sub_pos.mpr hxlt)
    have hrecip : -(1 / (x - 2)) = 1 / (2 - x) := by
      field_simp [ht, hden_ne] <;> ring
    have hz : (-(1 / (x - 2))) ∈ Set.Ioo (-1 : ℝ) 1 := by
      have hden : 0 < 2 - x := by linarith
      rw [hrecip]
      constructor
      · have : 0 < 1 / (2 - x) := div_pos zero_lt_one hden
        linarith
      · rw [div_lt_iff₀ hden]
        linarith
    have hrec : HasDerivAt (fun y : ℝ => -(1 / (y - 2)))
        (1 / (x - 2) ^ 2) x := by
      convert (((hasDerivAt_const x (1 : ℝ)).div
        ((hasDerivAt_id x).sub_const 2) ht).neg) using 1 <;>
        simp only [id_eq] <;> field_simp [ht] <;> ring
    have harc := ((Real.hasDerivAt_arcsin
      (ne_of_gt hz.1) (ne_of_lt hz.2)).comp x hrec).neg
    rw [hrecip] at harc
    have hratio := sqrt_ratio_identity a ha
    have hqeq : q x = a ^ 2 - 1 := by
      unfold q a
      ring
    have hratioQ : Real.sqrt (1 - (1 / a) ^ 2) * a = Real.sqrt (q x) := by
      rw [hqeq]
      exact hratio
    have hs : Real.sqrt (q x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
    have hsarg : Real.sqrt (1 - (1 / a) ^ 2) ≠ 0 := by
      intro hs0
      apply hs
      rw [← hratioQ, hs0, zero_mul]
    dsimp [a] at hratioQ hsarg
    have hcoef :
        -(1 / Real.sqrt (1 - (1 / (2 - x)) ^ 2) *
          (1 / (x - 2) ^ 2)) = i1 x := by
      calc
        -(1 / Real.sqrt (1 - (1 / (2 - x)) ^ 2) *
            (1 / (x - 2) ^ 2)) =
            1 / ((x - 2) *
              (Real.sqrt (1 - (1 / (2 - x)) ^ 2) * (2 - x))) := by
          field_simp [ht, hden_ne, hsarg] <;> ring
        _ = i1 x := by
          unfold i1
          rw [hratioQ]
    have hbase : HasDerivAt (fun y : ℝ => -Real.arcsin (-(1 / (y - 2))))
        (i1 x) x := by
      simpa only [Function.comp_apply, hcoef] using harc
    apply hbase.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hxlt] with y hy
    have hy' : y < 2 := hy
    have hyt : y - 2 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hy')
    have hyden : 2 - y ≠ 0 := ne_of_gt (sub_pos.mpr hy')
    have harg : -(1 / (y - 2)) = 1 / |y - 2| := by
      rw [abs_of_neg (sub_neg.mpr hy')]
      field_simp [hyt, hyden] <;> ring
    unfold i1Primitive
    rw [harg]
  · let a : ℝ := x - 2
    have ha : 1 < a := by
      dsimp [a]
      nlinarith
    have ht : x - 2 ≠ 0 := sub_ne_zero.mpr hx2
    have hz : (1 / (x - 2)) ∈ Set.Ioo (-1 : ℝ) 1 := by
      have hden : 0 < x - 2 := sub_pos.mpr hxgt
      constructor
      · have : 0 < 1 / (x - 2) := div_pos zero_lt_one hden
        linarith
      · rw [div_lt_iff₀ hden]
        linarith
    have hrec : HasDerivAt (fun y : ℝ => 1 / (y - 2))
        (-1 / (x - 2) ^ 2) x := by
      convert (hasDerivAt_const x (1 : ℝ)).div
        ((hasDerivAt_id x).sub_const 2) ht using 1 <;>
        simp only [id_eq] <;> field_simp [ht] <;> ring
    have harc := ((Real.hasDerivAt_arcsin
      (ne_of_gt hz.1) (ne_of_lt hz.2)).comp x hrec).neg
    have hratio := sqrt_ratio_identity a ha
    have hqeq : q x = a ^ 2 - 1 := by
      unfold q a
      ring
    have hratioQ : Real.sqrt (1 - (1 / a) ^ 2) * a = Real.sqrt (q x) := by
      rw [hqeq]
      exact hratio
    have hs : Real.sqrt (q x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
    have hsarg : Real.sqrt (1 - (1 / a) ^ 2) ≠ 0 := by
      intro hs0
      apply hs
      rw [← hratioQ, hs0, zero_mul]
    dsimp [a] at hratioQ hsarg
    have hcoef :
        -(1 / Real.sqrt (1 - (1 / (x - 2)) ^ 2) *
          (-1 / (x - 2) ^ 2)) = i1 x := by
      unfold i1
      rw [← hratioQ]
      field_simp [ht, hsarg] <;> ring
    have hbase : HasDerivAt (fun y : ℝ => -Real.arcsin (1 / (y - 2)))
        (i1 x) x := by
      simpa only [Function.comp_apply, hcoef] using harc
    apply hbase.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hxgt] with y hy
    have hy' : 2 < y := hy
    simp [i1Primitive, abs_of_pos (sub_pos.mpr hy')]

private theorem antiderivatives_eq_branchwise
    (p f : ℝ → ℝ)
    (hp : ∀ x ∈ branch, HasDerivAt p (f x) x) :
    AntiderivativesOn branch f = BranchwisePrimitiveFamilyOn branch p := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, BranchwisePrimitiveFamilyOn, Set.mem_setOf_eq]
  constructor
  · intro hF u hu_open hu_conn hu_sub
    by_cases hu_empty : u.Nonempty
    · rcases hu_empty with ⟨x0, hx0⟩
      refine ⟨F x0 - p x0, ?_⟩
      intro x hx
      have hdiff : DifferentiableOn ℝ (fun z : ℝ => F z - p z) u := by
        intro y hy
        exact ((hF y (hu_sub hy)).sub (hp y (hu_sub hy))).differentiableAt.differentiableWithinAt
      have hderiv : ∀ y ∈ u, deriv (fun z : ℝ => F z - p z) y = 0 := by
        intro y hy
        have hd := (hF y (hu_sub hy)).sub (hp y (hu_sub hy))
        have hd0 : HasDerivAt (fun z : ℝ => F z - p z) 0 y := by
          convert hd using 1 <;> ring
        exact hd0.deriv
      have heq := hu_open.is_const_of_deriv_eq_zero hu_conn hdiff hderiv hx0 hx
      linarith [heq]
    · refine ⟨0, ?_⟩
      intro x hx
      exact False.elim (hu_empty ⟨x, hx⟩)
  · intro hF x hx
    have hfac : 0 < (x - 1) * (x - 3) := by
      rw [← branch_factor]
      exact hx
    rcases mul_pos_iff.mp hfac with hpos | hneg
    · have hx3 : 3 < x := sub_pos.mp hpos.2
      have hsub : Set.Ioi (3 : ℝ) ⊆ branch := by
        intro y hy
        have hy3 : 3 < y := hy
        change 0 < q y
        rw [branch_factor]
        exact mul_pos
          (sub_pos.mpr (lt_trans (by norm_num) hy3))
          (sub_pos.mpr hy3)
      rcases hF (Set.Ioi (3 : ℝ)) isOpen_Ioi isPreconnected_Ioi hsub with ⟨C, hC⟩
      have hpC := (hp x hx).add_const C
      apply hpC.congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hx3] with y hy
      exact hC y hy
    · have hx1 : x < 1 := sub_neg.mp hneg.1
      have hsub : Set.Iio (1 : ℝ) ⊆ branch := by
        intro y hy
        have hy1 : y < 1 := hy
        change 0 < q y
        rw [branch_factor]
        exact mul_pos_of_neg_of_neg
          (sub_neg.mpr hy1)
          (sub_neg.mpr (lt_trans hy1 (by norm_num)))
      rcases hF (Set.Iio (1 : ℝ)) isOpen_Iio isPreconnected_Iio hsub with ⟨C, hC⟩
      have hpC := (hp x hx).add_const C
      apply hpC.congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hx1] with y hy
      exact hC y hy

theorem gap1 :
    AntiderivativesOn branch integrand =
      AntiderivativesOn branch partialFraction := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor <;> intro hF x hx
  · have heq : integrand x = partialFraction x := integrand_eq_partialFraction x hx
    simpa [heq] using hF x hx
  · have heq : integrand x = partialFraction x := integrand_eq_partialFraction x hx
    simpa [heq] using hF x hx
theorem gap2 :
    AntiderivativesOn branch integrand = TwoPartFamily := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, TwoPartFamily, I1, I2, Set.mem_setOf_eq]
  constructor
  · intro hF
    let A : ℝ → ℝ := fun y => (F y + i2Primitive y) / 2
    refine ⟨A, ?_, i2Primitive, ?_, ?_⟩
    · intro x hx
      have hder := ((hF x hx).add (hasDerivAt_i2Primitive x hx)).div_const 2
      have hdecomp := integrand_decomposition x hx
      change HasDerivAt (fun y => (F y + i2Primitive y) / 2) (i1 x) x
      convert hder using 1
      rw [hdecomp]
      ring
    · exact hasDerivAt_i2Primitive
    · intro x hx
      simp only [A]
      ring
  · rintro ⟨A, hA, B, hB, hF⟩
    intro x hx
    have hder : HasDerivAt (fun y => 2 * A y - B y)
        (2 * i1 x - i2 x) x := by
      simpa only [Pi.mul_apply, Pi.sub_apply] using
        ((hA x hx).const_mul 2).sub (hB x hx)
    have hdecomp := integrand_decomposition x hx
    rw [← hdecomp] at hder
    apply hder.congr_of_eventuallyEq
    filter_upwards [branch_isOpen.mem_nhds hx] with y hy
    exact hF y hy
theorem gap3 :
    ∃ A B : Set (ℝ → ℝ),
      A = I1 ∧ B = I2 ∧ TwoPartFamily = TwoPartFamily := by
  exact ⟨I1, I2, rfl, rfl, rfl⟩
theorem gap4 :
    ∃ A B : Set (ℝ → ℝ),
      A = I1 ∧ B = I2 ∧ AntiderivativesOn branch integrand = TwoPartFamily := by
  exact ⟨I1, I2, rfl, rfl, gap2⟩
theorem gap5 :
    I1 = BranchwisePrimitiveFamilyOn branch i1Primitive := by
  exact antiderivatives_eq_branchwise i1Primitive i1 hasDerivAt_i1Primitive
theorem gap6 :
    I2 = BranchwisePrimitiveFamilyOn branch i2Primitive := by
  exact antiderivatives_eq_branchwise i2Primitive i2 hasDerivAt_i2Primitive
theorem gap7 :
    AntiderivativesOn branch integrand =
      BranchwisePrimitiveFamilyOn branch finalPrimitive := by
  rw [gap2]
  apply Set.ext
  intro F
  simp only [TwoPartFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨A, hA, B, hB, hF⟩
    rw [gap5] at hA
    rw [gap6] at hB
    intro u hu_open hu_conn hu_sub
    rcases hA u hu_open hu_conn hu_sub with ⟨CA, hCA⟩
    rcases hB u hu_open hu_conn hu_sub with ⟨CB, hCB⟩
    refine ⟨2 * CA - CB, ?_⟩
    intro x hx
    rw [hF x (hu_sub hx), hCA x hx, hCB x hx]
    unfold finalPrimitive i1Primitive i2Primitive
    ring
  · intro hF
    let A : ℝ → ℝ := i1Primitive
    let B : ℝ → ℝ := fun x => 2 * i1Primitive x - F x
    refine ⟨A, ?_, B, ?_, ?_⟩
    · rw [gap5]
      intro u hu_open hu_conn hu_sub
      refine ⟨0, ?_⟩
      intro x hx
      simp only [A, add_zero]
    · rw [gap6]
      intro u hu_open hu_conn hu_sub
      rcases hF u hu_open hu_conn hu_sub with ⟨C, hC⟩
      refine ⟨-C, ?_⟩
      intro x hx
      simp only [B]
      rw [hC x hx]
      unfold finalPrimitive i1Primitive i2Primitive
      ring
    · intro x hx
      simp only [A, B]
      ring

end
end ProofGap.Exercise1956
