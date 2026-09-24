import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2093
noncomputable section

def f (x : ℝ) := (1 - 2 / x) ^ 2 * Real.exp x
def expanded (x : ℝ) := (1 - 4 / x + 4 / x ^ 2) * Real.exp x
def primitive (x : ℝ) := Real.exp x * (1 - 4 / x)
def Family (U : Set ℝ) (g : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (g x) x}
def Step2 (U : Set ℝ) := {F : ℝ → ℝ |
  ∃ L ∈ Family U (fun x => Real.exp x / x),
  ∃ G ∈ Family U (fun x => Real.exp x * deriv (fun y => 1 / y) x),
  ∃ C, ∀ x ∈ U, F x = Real.exp x - 4 * L x - 4 * G x + C}
def Step4 (U : Set ℝ) := {F : ℝ → ℝ |
  ∃ L ∈ Family U (fun x => Real.exp x / x), ∃ C, ∀ x ∈ U,
  F x = Real.exp x - 4 * L x - 4 / x * Real.exp x + 4 * L x + C}
def Translates (U : Set ℝ) (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ U, F x = p x + C}
def Regular (U : Set ℝ) :=
  IsOpen U ∧ IsPreconnected U ∧ ∀ x ∈ U, x ≠ 0

private theorem eq_add_const_of_same_deriv
    (U : Set ℝ) (hU : Regular U) (F p g : ℝ → ℝ)
    (hF : ∀ x ∈ U, HasDerivAt F (g x) x)
    (hp : ∀ x ∈ U, HasDerivAt p (g x) x) :
    ∃ C, ∀ x ∈ U, F x = p x + C := by
  rcases U.eq_empty_or_nonempty with hUe | ⟨a, ha⟩
  · refine ⟨0, ?_⟩
    intro x hx
    exact (hUe ▸ hx).elim
  · let q : ℝ → ℝ := fun x => F x - p x
    have hdiff : DifferentiableOn ℝ q U := by
      intro x hx
      simpa [q] using
        ((hF x hx).sub (hp x hx)).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ U, deriv q x = 0 := by
      intro x hx
      simpa [q] using ((hF x hx).sub (hp x hx)).deriv
    refine ⟨q a, ?_⟩
    intro x hx
    have hc : q x = q a :=
      hU.1.is_const_of_deriv_eq_zero hU.2.1 hdiff hzero hx ha
    calc
      F x = p x + q x := by simp [q]
      _ = p x + q a := by rw [hc]

private theorem family_eq_translates_of_same_deriv
    (U : Set ℝ) (hU : Regular U) (g p : ℝ → ℝ)
    (hp : ∀ x ∈ U, HasDerivAt p (g x) x) :
    Family U g = Translates U p := by
  ext F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    exact eq_add_const_of_same_deriv U hU F p g hF hp
  · rintro ⟨C, hF⟩
    intro x hx
    have hbase : HasDerivAt (fun y => p y + C) (g x) x :=
      (hp x hx).add_const C
    have hev : (fun y => p y + C) =ᶠ[nhds x] F :=
      Filter.mem_of_superset (hU.1.mem_nhds hx)
        (fun y hy => (hF y hy).symm)
    exact hbase.congr_of_eventuallyEq hev.symm

private theorem hasDerivAt_one_div (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => 1 / y) (-1 / x ^ 2) x := by
  simpa [one_div] using (hasDerivAt_id x).inv hx

private theorem deriv_one_div (x : ℝ) (hx : x ≠ 0) :
    deriv (fun y : ℝ => 1 / y) x = -1 / x ^ 2 := by
  exact (hasDerivAt_one_div x hx).deriv

private theorem hasDerivAt_one_sub_four_div (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => 1 - 4 / y) (4 / x ^ 2) x := by
  have h :=
    (hasDerivAt_const x (1 : ℝ)).sub
      ((hasDerivAt_const x (4 : ℝ)).div (hasDerivAt_id x) hx)
  convert h using 1 <;> simp <;> ring

private theorem primitive_hasDerivAt_f (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt primitive (f x) x := by
  have h := (Real.hasDerivAt_exp x).mul (hasDerivAt_one_sub_four_div x hx)
  have hcoef :
      Real.exp x * (1 - 4 / x) + Real.exp x * (4 / x ^ 2) = f x := by
    rw [f]
    field_simp [hx] <;> ring
  convert h using 1
  exact hcoef.symm

private theorem primitive_hasDerivAt_expanded (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt primitive (expanded x) x := by
  have h := primitive_hasDerivAt_f x hx
  have hfe : f x = expanded x := by
    unfold f expanded
    field_simp [hx] <;> ring
  simpa only [hfe] using h

private theorem exists_exp_div_antiderivative (U : Set ℝ) (hU : Regular U) :
    ∃ L, L ∈ Family U (fun x => Real.exp x / x) := by
  rcases U.eq_empty_or_nonempty with hUe | ⟨a, ha⟩
  · refine ⟨fun _ => 0, ?_⟩
    simp [Family, hUe]
  · let L : ℝ → ℝ := fun x => ∫ t in a..x, Real.exp t / t
    refine ⟨L, ?_⟩
    intro x hx
    have hcont :
        ContinuousOn (fun t : ℝ => Real.exp t / t) (Set.uIcc a x) := by
      apply Real.continuous_exp.continuousOn.div continuousOn_id
      intro y hy
      exact hU.2.2 y (hU.2.1.ordConnected.uIcc_subset ha hx hy)
    have hint :
        IntervalIntegrable (fun t : ℝ => Real.exp t / t)
          MeasureTheory.volume a x :=
      hcont.intervalIntegrable
    have hcontx : ContinuousAt (fun t : ℝ => Real.exp t / t) x :=
      Real.continuous_exp.continuousAt.div continuousAt_id (hU.2.2 x hx)
    have hopen : IsOpen U := hU.1
    have hcontU :
        ∀ y ∈ U, ContinuousAt (fun t : ℝ => Real.exp t / t) y := by
      intro y hy
      exact Real.continuous_exp.continuousAt.div continuousAt_id
        (hU.2.2 y hy)
    apply intervalIntegral.integral_hasDerivAt_right hint
    · apply ContinuousAt.stronglyMeasurableAtFilter (s := U) <;> assumption
    · exact hcontx

private theorem auxiliary_derivative
    (U : Set ℝ) (hU : Regular U) (L : ℝ → ℝ)
    (hL : L ∈ Family U (fun x => Real.exp x / x)) :
    let G : ℝ → ℝ := fun y => Real.exp y * (1 / y) - L y
    G ∈ Family U
      (fun x => Real.exp x * deriv (fun y => 1 / y) x) := by
  intro G
  intro x hx
  have hinv :
      HasDerivAt (fun y : ℝ => 1 / y) (deriv (fun y => 1 / y) x) x := by
    rw [deriv_one_div x (hU.2.2 x hx)]
    exact hasDerivAt_one_div x (hU.2.2 x hx)
  have hd := ((Real.hasDerivAt_exp x).mul hinv).sub (hL x hx)
  dsimp [G]
  convert hd using 1 <;> simp [div_eq_mul_inv] <;> ring

private theorem step2_eq_translates (U : Set ℝ) (hU : Regular U) :
    Step2 U = Translates U primitive := by
  ext F
  simp only [Step2, Translates, Set.mem_setOf_eq]
  constructor
  · rintro ⟨L, hL, G, hG, C, hEq⟩
    have hFam : ∀ x ∈ U, HasDerivAt F (expanded x) x := by
      intro x hx
      have hcoef :
          Real.exp x - 4 * (Real.exp x / x) -
              4 * (Real.exp x * deriv (fun y => 1 / y) x) = expanded x := by
        rw [deriv_one_div x (hU.2.2 x hx), expanded]
        field_simp [hU.2.2 x hx] <;> ring
      have hd :=
        (((Real.hasDerivAt_exp x).sub ((hL x hx).const_mul 4)).sub
          ((hG x hx).const_mul 4)).add_const C
      have hlocal :
          HasDerivAt
            (fun y => Real.exp y - 4 * L y - 4 * G y + C)
            (expanded x) x := by
        rw [← hcoef]
        simpa using hd
      have hev :
          (fun y => Real.exp y - 4 * L y - 4 * G y + C) =ᶠ[nhds x] F :=
        Filter.mem_of_superset (hU.1.mem_nhds hx)
          (fun y hy => (hEq y hy).symm)
      exact hlocal.congr_of_eventuallyEq hev.symm
    exact eq_add_const_of_same_deriv U hU F primitive expanded hFam
      (fun x hx => primitive_hasDerivAt_expanded x (hU.2.2 x hx))
  · rintro ⟨C, hF⟩
    rcases exists_exp_div_antiderivative U hU with ⟨L, hL⟩
    let G : ℝ → ℝ := fun y => Real.exp y * (1 / y) - L y
    have hG :
        G ∈ Family U
          (fun x => Real.exp x * deriv (fun y => 1 / y) x) :=
      auxiliary_derivative U hU L hL
    refine ⟨L, hL, G, hG, C, ?_⟩
    intro x hx
    calc
      F x = primitive x + C := hF x hx
      _ = Real.exp x - 4 * L x - 4 * G x + C := by
        dsimp [primitive, G]
        simp [div_eq_mul_inv]
        ring

private theorem step4_eq_translates (U : Set ℝ) (hU : Regular U) :
    Step4 U = Translates U primitive := by
  ext F
  simp only [Step4, Translates, Set.mem_setOf_eq]
  constructor
  · rintro ⟨L, hL, C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    calc
      F x = Real.exp x - 4 * L x - 4 / x * Real.exp x + 4 * L x + C :=
        hF x hx
      _ = primitive x + C := by
        dsimp [primitive]
        simp [div_eq_mul_inv]
        ring
  · rintro ⟨C, hF⟩
    rcases exists_exp_div_antiderivative U hU with ⟨L, hL⟩
    refine ⟨L, hL, C, ?_⟩
    intro x hx
    calc
      F x = primitive x + C := hF x hx
      _ = Real.exp x - 4 * L x - 4 / x * Real.exp x + 4 * L x + C := by
        dsimp [primitive]
        simp [div_eq_mul_inv]
        ring

theorem gap1 (U : Set ℝ) (hU : Regular U) :
    Family U f = Family U expanded := by
  calc
    Family U f = Translates U primitive :=
      family_eq_translates_of_same_deriv U hU f primitive
        (fun x hx => primitive_hasDerivAt_f x (hU.2.2 x hx))
    _ = Family U expanded :=
      (family_eq_translates_of_same_deriv U hU expanded primitive
        (fun x hx => primitive_hasDerivAt_expanded x (hU.2.2 x hx))).symm
theorem gap2 (U : Set ℝ) (hU : Regular U) :
    Family U expanded = Step2 U := by
  calc
    Family U expanded = Translates U primitive :=
      family_eq_translates_of_same_deriv U hU expanded primitive
        (fun x hx => primitive_hasDerivAt_expanded x (hU.2.2 x hx))
    _ = Step2 U := (step2_eq_translates U hU).symm
theorem gap3 (U : Set ℝ) (hU : Regular U) :
    Family U f = Step2 U := by
  calc
    Family U f = Translates U primitive :=
      family_eq_translates_of_same_deriv U hU f primitive
        (fun x hx => primitive_hasDerivAt_f x (hU.2.2 x hx))
    _ = Step2 U := (step2_eq_translates U hU).symm
theorem gap4 (U : Set ℝ) (hU : Regular U) :
    Family U f = Step4 U := by
  calc
    Family U f = Translates U primitive :=
      family_eq_translates_of_same_deriv U hU f primitive
        (fun x hx => primitive_hasDerivAt_f x (hU.2.2 x hx))
    _ = Step4 U := (step4_eq_translates U hU).symm
theorem gap5 (U : Set ℝ) (hU : Regular U) :
    Step4 U = Translates U primitive := by
  exact step4_eq_translates U hU
theorem gap6 (U : Set ℝ) (hU : Regular U) :
    Family U f = Translates U primitive := by
  exact family_eq_translates_of_same_deriv U hU f primitive
    (fun x hx => primitive_hasDerivAt_f x (hU.2.2 x hx))

end
end ProofGap.Exercise2093
