import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2126
noncomputable section

def AdmissibleBranch (U : Set ℝ) : Prop :=
  U = Set.Iio 0 ∨ U = Set.Ioi 0
def integrand (x : ℝ) := 1 / (x ^ 6 * (1 + x ^ 2))
def firstExpanded (x : ℝ) := (x ^ 2 + 1 - x ^ 2) / (x ^ 6 * (1 + x ^ 2))
def firstPower (x : ℝ) := 1 / x ^ 6
def firstRemainder (x : ℝ) := 1 / (x ^ 4 * (1 + x ^ 2))
def secondRemainder (x : ℝ) :=
  (x ^ 2 + 1 - x ^ 2) / (x ^ 4 * (1 + x ^ 2))
def inverseFourth (x : ℝ) := 1 / x ^ 4
def squarePart (x : ℝ) := x ^ 2 / (x ^ 4 * (1 + x ^ 2))
def finalRemainder (x : ℝ) := 1 / x ^ 2 - 1 / (1 + x ^ 2)
def primitive (x : ℝ) :=
  -(1 / (5 * x ^ 5)) + 1 / (3 * x ^ 3) - 1 / x - Real.arctan x

def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def DifferenceFamily (U : Set ℝ) (f g : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family U f, ∃ B ∈ Family U g,
    ∀ x ∈ U, F x = A x - B x}
def Stage3 (U : Set ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family U secondRemainder, ∀ x ∈ U,
    F x = -(1 / (5 * x ^ 5)) - A x}
def Stage5 (U : Set ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family U inverseFourth, ∃ B ∈ Family U squarePart,
    ∀ x ∈ U, F x = -(1 / (5 * x ^ 5)) - A x + B x}
def Stage6 (U : Set ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family U finalRemainder, ∀ x ∈ U,
    F x = -(1 / (5 * x ^ 5)) + 1 / (3 * x ^ 3) + A x}
def Translates (U : Set ℝ) (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x ∈ U, F x = p x + C}

private theorem admissibleOpen {U : Set ℝ} (hU : AdmissibleBranch U) : IsOpen U := by
  unfold AdmissibleBranch at hU
  rcases hU with rfl | rfl
  · exact isOpen_Iio
  · exact isOpen_Ioi

private theorem admissibleMemNeZero {U : Set ℝ} (hU : AdmissibleBranch U)
    {x : ℝ} (hx : x ∈ U) : x ≠ 0 := by
  unfold AdmissibleBranch at hU
  rcases hU with rfl | rfl
  · exact ne_of_lt hx
  · exact ne_of_gt hx

private theorem derivCongrOnAdmissible {U : Set ℝ} (hU : AdmissibleBranch U)
    {F G : ℝ → ℝ} {d x : ℝ} (hx : x ∈ U)
    (hEq : ∀ y ∈ U, F y = G y) (hG : HasDerivAt G d x) :
    HasDerivAt F d x := by
  have heq : F =ᶠ[nhds x] G := by
    filter_upwards [(admissibleOpen hU).mem_nhds hx] with y hy
    exact hEq y hy
  exact hG.congr_of_eventuallyEq heq

private theorem oneAddSqNeZero (x : ℝ) : 1 + x ^ 2 ≠ 0 := by
  nlinarith [sq_nonneg x]

private theorem firstExpandedEq (x : ℝ) : firstExpanded x = integrand x := by
  unfold firstExpanded integrand
  ring

private theorem secondEqualsFirst (x : ℝ) : secondRemainder x = firstRemainder x := by
  unfold secondRemainder firstRemainder
  ring

private theorem splitFirst (x : ℝ) (hx : x ≠ 0) :
    firstExpanded x = firstPower x - firstRemainder x := by
  unfold firstExpanded firstPower firstRemainder
  field_simp [hx, oneAddSqNeZero x]
  <;> ring_nf

private theorem integrandResidualSquare (x : ℝ) (hx : x ≠ 0) :
    integrand x - firstPower x + inverseFourth x = squarePart x := by
  unfold integrand firstPower inverseFourth squarePart
  field_simp [hx, oneAddSqNeZero x]
  <;> ring_nf

private theorem integrandResidualFinal (x : ℝ) (hx : x ≠ 0) :
    integrand x - firstPower x + inverseFourth x = finalRemainder x := by
  unfold integrand firstPower inverseFourth finalRemainder
  field_simp [hx, oneAddSqNeZero x]
  <;> ring_nf

private theorem derivFirstTerm {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => -(1 / (5 * y ^ 5))) (1 / x ^ 6) x := by
  have hd : 5 * x ^ 5 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 5 hx)
  convert (((hasDerivAt_const x (1 : ℝ)).div
    (((hasDerivAt_id x).pow 5).const_mul 5) hd).neg) using 1 <;>
    simp <;> field_simp [hx] <;> ring_nf

private theorem derivThirdTerm {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => 1 / (3 * y ^ 3)) (-(1 / x ^ 4)) x := by
  have hd : 3 * x ^ 3 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 3 hx)
  convert ((hasDerivAt_const x (1 : ℝ)).div
    (((hasDerivAt_id x).pow 3).const_mul 3) hd) using 1 <;>
    simp <;> field_simp [hx] <;> ring_nf

private theorem derivNegativeThirdTerm {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => -(1 / (3 * y ^ 3))) (1 / x ^ 4) x := by
  convert (derivThirdTerm hx).neg using 1 <;> ring

private theorem derivInvTerm {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => 1 / y) (-(1 / x ^ 2)) x := by
  convert (hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx using 1 <;>
    simp <;> field_simp [hx] <;> ring_nf

private theorem primitiveHasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt primitive (integrand x) x := by
  change HasDerivAt
    (fun y : ℝ => (-(1 / (5 * y ^ 5)) + 1 / (3 * y ^ 3) - 1 / y) -
      Real.arctan y)
    (integrand x) x
  have h := (((derivFirstTerm hx).add (derivThirdTerm hx)).sub
    (derivInvTerm hx)).sub (Real.hasDerivAt_arctan x)
  convert h using 1
  unfold integrand
  field_simp [hx, oneAddSqNeZero x]
  <;> ring_nf

private theorem zeroDerivativeEqOnAdmissible {U : Set ℝ}
    (hU : AdmissibleBranch U) {D : ℝ → ℝ}
    (hD : ∀ x ∈ U, HasDerivAt D 0 x) {x y : ℝ}
    (hx : x ∈ U) (hy : y ∈ U) : D x = D y := by
  have hdiff : DifferentiableOn ℝ D U := by
    intro z hz
    exact (hD z hz).differentiableAt.differentiableWithinAt
  have hder : ∀ z ∈ U, deriv D z = 0 := by
    intro z hz
    exact (hD z hz).deriv
  unfold AdmissibleBranch at hU
  rcases hU with rfl | rfl
  · apply isOpen_Iio.is_const_of_deriv_eq_zero isPreconnected_Iio hdiff hder
    · exact hx
    · exact hy
  · apply isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi hdiff hder
    · exact hx
    · exact hy

theorem gap1 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = Family U firstExpanded := by
  ext F
  simp only [Family, Set.mem_setOf_eq]
  constructor
  · intro hF x hx
    simpa only [firstExpandedEq] using hF x hx
  · intro hF x hx
    simpa only [firstExpandedEq] using hF x hx
theorem gap2 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U firstExpanded = DifferenceFamily U firstPower firstRemainder := by
  ext F
  simp only [Family, DifferenceFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨(fun y : ℝ => -(1 / (5 * y ^ 5))), ?_,
      (fun y : ℝ => -(1 / (5 * y ^ 5)) - F y), ?_, ?_⟩
    · intro x hx
      simpa only [firstPower] using derivFirstTerm (admissibleMemNeZero hU hx)
    · intro x hx
      have hx0 := admissibleMemNeZero hU hx
      convert (derivFirstTerm hx0).sub (hF x hx) using 1
      rw [splitFirst x hx0]
      unfold firstPower
      ring
    · intro x hx
      ring
  · rintro ⟨A, hA, B, hB, hEq⟩
    intro x hx
    have hx0 := admissibleMemNeZero hU hx
    have hAB : HasDerivAt (fun y : ℝ => A y - B y) (firstExpanded x) x := by
      convert (hA x hx).sub (hB x hx) using 1
      rw [splitFirst x hx0]
    exact derivCongrOnAdmissible hU hx hEq hAB
theorem gap3 (U : Set ℝ) (hU : AdmissibleBranch U) :
    DifferenceFamily U firstPower firstRemainder = Stage3 U := by
  ext F
  simp only [DifferenceFamily, Family, Stage3, Set.mem_setOf_eq]
  constructor
  · rintro ⟨A, hA, B, hB, hEq⟩
    have hF : ∀ x ∈ U, HasDerivAt F (firstExpanded x) x := by
      intro x hx
      have hx0 := admissibleMemNeZero hU hx
      have hAB : HasDerivAt (fun y : ℝ => A y - B y) (firstExpanded x) x := by
        convert (hA x hx).sub (hB x hx) using 1
        rw [splitFirst x hx0]
      exact derivCongrOnAdmissible hU hx hEq hAB
    refine ⟨(fun y : ℝ => -(1 / (5 * y ^ 5)) - F y), ?_, ?_⟩
    · intro x hx
      have hx0 := admissibleMemNeZero hU hx
      convert (derivFirstTerm hx0).sub (hF x hx) using 1
      rw [secondEqualsFirst x, splitFirst x hx0]
      unfold firstPower
      ring
    · intro x hx
      ring
  · rintro ⟨A, hA, hEq⟩
    refine ⟨(fun y : ℝ => -(1 / (5 * y ^ 5))), ?_, A, ?_, hEq⟩
    · intro x hx
      simpa only [firstPower] using derivFirstTerm (admissibleMemNeZero hU hx)
    · intro x hx
      simpa only [secondEqualsFirst] using hA x hx
theorem gap4 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = Stage3 U := by
  calc
    Family U integrand = Family U firstExpanded := gap1 U hU
    _ = DifferenceFamily U firstPower firstRemainder := gap2 U hU
    _ = Stage3 U := gap3 U hU
theorem gap5 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = Stage5 U := by
  ext F
  simp only [Family, Stage5, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨(fun y : ℝ => -(1 / (3 * y ^ 3))), ?_,
      (fun y : ℝ => F y - (-(1 / (5 * y ^ 5))) + (-(1 / (3 * y ^ 3)))), ?_, ?_⟩
    · intro x hx
      simpa only [inverseFourth] using
        derivNegativeThirdTerm (admissibleMemNeZero hU hx)
    · intro x hx
      have hx0 := admissibleMemNeZero hU hx
      convert ((hF x hx).sub (derivFirstTerm hx0)).add
        (derivNegativeThirdTerm hx0) using 1
      simpa only [firstPower, inverseFourth] using
        (integrandResidualSquare x hx0).symm
    · intro x hx
      ring
  · rintro ⟨A, hA, B, hB, hEq⟩
    intro x hx
    have hx0 := admissibleMemNeZero hU hx
    have hModel := ((derivFirstTerm hx0).sub (hA x hx)).add (hB x hx)
    have hModel' : HasDerivAt
        (fun y : ℝ => -(1 / (5 * y ^ 5)) - A y + B y)
        (integrand x) x := by
      convert hModel using 1
      have hid := integrandResidualSquare x hx0
      simp only [firstPower] at hid
      linarith
    exact derivCongrOnAdmissible hU hx hEq hModel'
theorem gap6 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Stage5 U = Stage6 U := by
  ext F
  constructor
  · intro h5
    have hF : F ∈ Family U integrand := by
      rw [gap5 U hU]
      exact h5
    change ∃ A ∈ Family U finalRemainder, ∀ x ∈ U,
      F x = -(1 / (5 * x ^ 5)) + 1 / (3 * x ^ 3) + A x
    refine ⟨(fun y : ℝ => F y - (-(1 / (5 * y ^ 5))) - 1 / (3 * y ^ 3)), ?_, ?_⟩
    · intro x hx
      have hx0 := admissibleMemNeZero hU hx
      convert ((hF x hx).sub (derivFirstTerm hx0)).sub
        (derivThirdTerm hx0) using 1
      simpa only [firstPower, inverseFourth, sub_neg_eq_add] using
        (integrandResidualFinal x hx0).symm
    · intro x hx
      ring
  · intro h6
    change ∃ A ∈ Family U finalRemainder, ∀ x ∈ U,
      F x = -(1 / (5 * x ^ 5)) + 1 / (3 * x ^ 3) + A x at h6
    rcases h6 with ⟨A, hA, hEq⟩
    have hF : F ∈ Family U integrand := by
      intro x hx
      have hx0 := admissibleMemNeZero hU hx
      have hModel := ((derivFirstTerm hx0).add (derivThirdTerm hx0)).add (hA x hx)
      have hModel' : HasDerivAt
          (fun y : ℝ => -(1 / (5 * y ^ 5)) + 1 / (3 * y ^ 3) + A y)
          (integrand x) x := by
        convert hModel using 1
        have hid := integrandResidualFinal x hx0
        simp only [firstPower, inverseFourth] at hid
        linarith
      exact derivCongrOnAdmissible hU hx hEq hModel'
    rw [← gap5 U hU]
    exact hF
theorem gap7 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = Stage6 U := by
  calc
    Family U integrand = Stage5 U := gap5 U hU
    _ = Stage6 U := gap6 U hU
theorem gap8 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = Translates U primitive := by
  ext F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    have hD : ∀ x ∈ U,
        HasDerivAt (fun y : ℝ => F y - primitive y) 0 x := by
      intro x hx
      have hx0 := admissibleMemNeZero hU hx
      convert (hF x hx).sub (primitiveHasDerivAt hx0) using 1 <;> ring
    rcases hU with hneg | hpos
    · refine ⟨F (-1) - primitive (-1), ?_⟩
      intro x hx
      have ha : (-1 : ℝ) ∈ U := by
        rw [hneg]
        norm_num
      have hc := zeroDerivativeEqOnAdmissible (Or.inl hneg) hD hx ha
      change F x - primitive x = F (-1) - primitive (-1) at hc
      linarith
    · refine ⟨F 1 - primitive 1, ?_⟩
      intro x hx
      have ha : (1 : ℝ) ∈ U := by
        rw [hpos]
        norm_num
      have hc := zeroDerivativeEqOnAdmissible (Or.inr hpos) hD hx ha
      change F x - primitive x = F 1 - primitive 1 at hc
      linarith
  · rintro ⟨C, hEq⟩
    intro x hx
    have hx0 := admissibleMemNeZero hU hx
    have hModel :=
      (primitiveHasDerivAt hx0).add (hasDerivAt_const x C)
    have hModel' : HasDerivAt
        (fun y : ℝ => primitive y + C) (integrand x) x := by
      convert hModel using 1 <;> simp
    exact derivCongrOnAdmissible hU hx hEq hModel'

end
end ProofGap.Exercise2126
