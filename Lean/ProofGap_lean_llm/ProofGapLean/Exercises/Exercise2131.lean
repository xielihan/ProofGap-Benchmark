import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2131
noncomputable section

def AdmissibleBranch (U : Set ℝ) : Prop :=
  U = Set.Ioo (-1) 0 ∨ U = Set.Ioo 0 1
def t (x : ℝ) := Real.arcsin x
def integrand (x : ℝ) := (x + 2) / (x ^ 2 * Real.sqrt (1 - x ^ 2))
def pulledBack (x : ℝ) :=
  (Real.sin (t x) + 2) / Real.sin (t x) ^ 2 * deriv t x
def csc (y : ℝ) := 1 / Real.sin y
def cot (y : ℝ) := Real.cos y / Real.sin y
def firstTerm (x : ℝ) := deriv t x / Real.sin (t x)
def secondTerm (x : ℝ) := deriv t x / Real.sin (t x) ^ 2
def primitiveT (x : ℝ) :=
  Real.log |csc (t x) - cot (t x)| - 2 * cot (t x)
def primitive (x : ℝ) :=
  -Real.log ((1 + Real.sqrt (1 - x ^ 2)) / |x|) -
    2 * Real.sqrt (1 - x ^ 2) / x

def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def SumFamily (U : Set ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family U firstTerm, ∃ B ∈ Family U secondTerm,
    ∀ x ∈ U, F x = A x + 2 * B x}
def Translates (U : Set ℝ) (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x ∈ U, F x = p x + C}

private theorem canonicalFacts
    (U : Set ℝ) (hU : AdmissibleBranch U) (x : ℝ) (hx : x ∈ U) :
    HasDerivAt primitiveT (pulledBack x) x ∧
      HasDerivAt (fun y => -cot (t y)) (secondTerm x) x ∧
      Real.sin (t x) ≠ 0 ∧ primitiveT x = primitive x := by
  have hlo : -1 < x := by
    rcases hU with rfl | rfl
    · exact hx.1
    · linarith [hx.1]
  have hhi : x < 1 := by
    rcases hU with rfl | rfl
    · linarith [hx.2]
    · exact hx.2
  have hxne : x ≠ 0 := by
    rcases hU with rfl | rfl
    · exact ne_of_lt hx.2
    · exact ne_of_gt hx.1
  have hs : Real.sin (t x) = x := by
    change Real.sin (Real.arcsin x) = x
    exact Real.sin_arcsin (le_of_lt hlo) (le_of_lt hhi)
  have hsne : Real.sin (t x) ≠ 0 := by
    rw [hs]
    exact hxne
  have hc : Real.cos (t x) = Real.sqrt (1 - x ^ 2) := by
    change Real.cos (Real.arcsin x) = Real.sqrt (1 - x ^ 2)
    exact Real.cos_arcsin x
  have hsqrtpos : 0 < Real.sqrt (1 - x ^ 2) :=
    Real.sqrt_pos.2 (by nlinarith)
  have harc := Real.hasDerivAt_arcsin (ne_of_gt hlo) (ne_of_lt hhi)
  have ht0 : HasDerivAt t (1 / Real.sqrt (1 - x ^ 2)) x := by
    change HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x
    exact harc
  have hd : deriv t x = 1 / Real.sqrt (1 - x ^ 2) := ht0.deriv
  have ht : HasDerivAt t (deriv t x) x := by
    rw [hd]
    exact ht0
  have hcd : Real.cos (t x) * deriv t x = 1 := by
    rw [hc, hd]
    field_simp [ne_of_gt hsqrtpos]
  have htrig : Real.sin (t x) ^ 2 + Real.cos (t x) ^ 2 = 1 := by
    simpa [add_comm] using Real.sin_sq_add_cos_sq (t x)
  have hsin := (Real.hasDerivAt_sin (t x)).comp x ht
  have hcos := (Real.hasDerivAt_cos (t x)).comp x ht
  have hcsc0 := (hasDerivAt_const x (1 : ℝ)).div hsin hsne
  have hcsc : HasDerivAt (fun y => csc (t y))
      (-1 / Real.sin (t x) ^ 2) x := by
    convert hcsc0 using 1 <;>
      dsimp [csc] <;>
      field_simp [hsne] <;>
      nlinarith [hcd]
  have hcot0 := hcos.div hsin hsne
  have hcot : HasDerivAt (fun y => cot (t y)) (-secondTerm x) x := by
    convert hcot0 using 1 <;>
      dsimp [cot, secondTerm] <;>
      field_simp [hsne] <;>
      nlinarith [htrig]
  have hB : HasDerivAt (fun y => -cot (t y)) (secondTerm x) x := by
    convert hcot.neg using 1 <;> simp
  have hg : HasDerivAt (fun y => csc (t y) - cot (t y))
      ((deriv t x - 1) / Real.sin (t x) ^ 2) x := by
    convert hcsc.sub hcot using 1 <;>
      dsimp [secondTerm] <;> ring
  let s := Real.sqrt (1 - x ^ 2)
  have hs0 : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - x ^ 2 := by
    dsimp [s]
    exact Real.sq_sqrt (by nlinarith)
  have hx2pos : 0 < x ^ 2 := sq_pos_of_ne_zero hxne
  have hslt : s < 1 := by
    nlinarith
  have honec : 0 < 1 - s := by linarith
  have hone : 0 < 1 + s := by linarith
  have hgform : csc (t x) - cot (t x) = (1 - s) / x := by
    dsimp [s]
    rw [csc, cot, hs, hc]
    ring
  have hg_ne : csc (t x) - cot (t x) ≠ 0 := by
    rw [hgform]
    exact div_ne_zero (ne_of_gt honec) hxne
  have hsD : s * deriv t x = 1 := by
    dsimp [s]
    rw [← hc]
    exact hcd
  have hlog0 := (Real.hasDerivAt_log hg_ne).comp x hg
  have hlog : HasDerivAt
      (fun y => Real.log (csc (t y) - cot (t y))) (firstTerm x) x := by
    convert hlog0 using 1 <;>
      dsimp [firstTerm] <;>
      rw [hgform, hs] <;>
      field_simp [hxne, ne_of_gt honec] <;>
      nlinarith [hsD]
  have hp0 := hlog.sub (hcot.const_mul 2)
  have hfun : primitiveT = fun y =>
      Real.log (csc (t y) - cot (t y)) - 2 * cot (t y) := by
    funext y
    simp only [primitiveT, Real.log_abs]
  have hp : HasDerivAt primitiveT (pulledBack x) x := by
    rw [hfun]
    convert hp0 using 1 <;>
      dsimp [pulledBack, firstTerm, secondTerm] <;>
      field_simp [hsne] <;> ring
  have habsarg : |csc (t x) - cot (t x)| = |x| / (1 + s) := by
    rw [hgform, abs_div, abs_of_pos honec]
    field_simp [abs_ne_zero.mpr hxne, ne_of_gt hone] <;>
      nlinarith [hs2, sq_abs x]
  have hlogeq : Real.log (|x| / (1 + s)) =
      -Real.log ((1 + s) / |x|) := by
    rw [Real.log_div (abs_ne_zero.mpr hxne) (ne_of_gt hone),
      Real.log_div (ne_of_gt hone) (abs_ne_zero.mpr hxne)]
    ring
  have hpeq : primitiveT x = primitive x := by
    rw [primitiveT, primitive, habsarg, hlogeq, cot, hs, hc]
    simpa [s, div_eq_mul_inv, mul_assoc]
  exact ⟨hp, hB, hsne, hpeq⟩

private theorem family_eq_translates_Ioo
    (a b : ℝ) (f p : ℝ → ℝ) (hab : a < b)
    (hp : ∀ x ∈ Set.Ioo a b, HasDerivAt p (f x) x) :
    Family (Set.Ioo a b) f = Translates (Set.Ioo a b) p := by
  ext F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    let z : ℝ := (a + b) / 2
    have hz : z ∈ Set.Ioo a b := by
      dsimp [z]
      constructor <;> linarith
    let q : ℝ → ℝ := fun y => F y - p y
    have hq : ∀ x ∈ Set.Ioo a b, HasDerivAt q 0 x := by
      intro x hx
      simpa [q] using (hF x hx).sub (hp x hx)
    have hdiff : DifferentiableOn ℝ q (Set.Ioo a b) :=
      fun x hx => (hq x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ Set.Ioo a b, deriv q x = 0 :=
      fun x hx => (hq x hx).deriv
    refine ⟨q z, fun x hx => ?_⟩
    have hconst : q x = q z :=
      isOpen_Ioo.is_const_of_deriv_eq_zero
        isPreconnected_Ioo hdiff hderiv hx hz
    dsimp [q] at hconst ⊢
    linarith
  · rintro ⟨C, hC⟩
    intro x hx
    have hev : F =ᶠ[nhds x] fun y => p y + C :=
      Filter.Eventually.mono (isOpen_Ioo.mem_nhds hx) (fun y hy => hC y hy)
    exact ((hp x hx).add_const C).congr_of_eventuallyEq hev

theorem gap1 (U : Set ℝ) (hU : AdmissibleBranch U) (x : ℝ) (hx : x ∈ U) :
    -(Real.pi / 2) < t x := by
  rw [t, Real.neg_pi_div_two_lt_arcsin]
  rcases hU with rfl | rfl
  · exact hx.1
  · linarith [hx.1]
theorem gap2 (U : Set ℝ) (hU : AdmissibleBranch U) (x : ℝ) (hx : x ∈ U) :
    t x < Real.pi / 2 := by
  rw [t, Real.arcsin_lt_pi_div_two]
  rcases hU with rfl | rfl
  · linarith [hx.2]
  · exact hx.2
theorem gap3 (U : Set ℝ) (hU : AdmissibleBranch U) (x : ℝ) (hx : x ∈ U) :
    1 = Real.cos (t x) * deriv t x := by
  have hlo : -1 < x := by
    rcases hU with rfl | rfl
    · exact hx.1
    · linarith [hx.1]
  have hhi : x < 1 := by
    rcases hU with rfl | rfl
    · linarith [hx.2]
    · exact hx.2
  have harc := Real.hasDerivAt_arcsin (ne_of_gt hlo) (ne_of_lt hhi)
  have ht : HasDerivAt t (1 / Real.sqrt (1 - x ^ 2)) x := by
    change HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x
    exact harc
  have hd : deriv t x = 1 / Real.sqrt (1 - x ^ 2) := ht.deriv
  have hc : Real.cos (t x) = Real.sqrt (1 - x ^ 2) := by
    change Real.cos (Real.arcsin x) = Real.sqrt (1 - x ^ 2)
    exact Real.cos_arcsin x
  have hspos : 0 < Real.sqrt (1 - x ^ 2) :=
    Real.sqrt_pos.2 (by nlinarith)
  rw [hc, hd]
  field_simp [ne_of_gt hspos]
theorem gap4 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = Family U pulledBack := by
  ext F
  simp only [Family, Set.mem_setOf_eq]
  constructor
  · intro hF x hx
    have hlo : -1 < x := by
      rcases hU with rfl | rfl
      · exact hx.1
      · linarith [hx.1]
    have hhi : x < 1 := by
      rcases hU with rfl | rfl
      · linarith [hx.2]
      · exact hx.2
    have hs : Real.sin (t x) = x := by
      change Real.sin (Real.arcsin x) = x
      exact Real.sin_arcsin (le_of_lt hlo) (le_of_lt hhi)
    have harc := Real.hasDerivAt_arcsin (ne_of_gt hlo) (ne_of_lt hhi)
    have ht : HasDerivAt t (1 / Real.sqrt (1 - x ^ 2)) x := by
      change HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x
      exact harc
    have hd : deriv t x = 1 / Real.sqrt (1 - x ^ 2) := ht.deriv
    convert hF x hx using 1
    rw [integrand, pulledBack, hs, hd]
    ring
  · intro hF x hx
    have hlo : -1 < x := by
      rcases hU with rfl | rfl
      · exact hx.1
      · linarith [hx.1]
    have hhi : x < 1 := by
      rcases hU with rfl | rfl
      · linarith [hx.2]
      · exact hx.2
    have hs : Real.sin (t x) = x := by
      change Real.sin (Real.arcsin x) = x
      exact Real.sin_arcsin (le_of_lt hlo) (le_of_lt hhi)
    have harc := Real.hasDerivAt_arcsin (ne_of_gt hlo) (ne_of_lt hhi)
    have ht : HasDerivAt t (1 / Real.sqrt (1 - x ^ 2)) x := by
      change HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x
      exact harc
    have hd : deriv t x = 1 / Real.sqrt (1 - x ^ 2) := ht.deriv
    convert hF x hx using 1
    rw [integrand, pulledBack, hs, hd]
    ring
theorem gap5 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U pulledBack = SumFamily U := by
  ext F
  simp only [Family, SumFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    let B : ℝ → ℝ := fun y => -cot (t y)
    let A : ℝ → ℝ := fun y => F y - 2 * B y
    refine ⟨A, ?_, B, ?_, ?_⟩
    · intro x hx
      have facts := canonicalFacts U hU x hx
      have hA := (hF x hx).sub (facts.2.1.const_mul 2)
      convert hA using 1 <;>
        dsimp [pulledBack, firstTerm, secondTerm] <;>
        field_simp [facts.2.2.1] <;> ring
    · intro x hx
      exact (canonicalFacts U hU x hx).2.1
    · intro x hx
      simp [A]
  · rintro ⟨A, hA, B, hB, hEq⟩
    intro x hx
    have hsum := (hA x hx).add ((hB x hx).const_mul 2)
    have hsne : Real.sin (t x) ≠ 0 := (canonicalFacts U hU x hx).2.2.1
    have hsum' : HasDerivAt (fun y => A y + 2 * B y) (pulledBack x) x := by
      convert hsum using 1 <;>
        dsimp [pulledBack, firstTerm, secondTerm] <;>
        field_simp [hsne] <;> ring
    have hopen : IsOpen U := by
      rcases hU with rfl | rfl <;> exact isOpen_Ioo
    have hev : F =ᶠ[nhds x] fun y => A y + 2 * B y :=
      Filter.Eventually.mono (hopen.mem_nhds hx) (fun y hy => hEq y hy)
    exact hsum'.congr_of_eventuallyEq hev
theorem gap6 (U : Set ℝ) (hU : AdmissibleBranch U) :
    SumFamily U = Translates U primitiveT := by
  rw [← gap5 U hU]
  rcases hU with rfl | rfl
  · apply family_eq_translates_Ioo (-1) 0 pulledBack primitiveT (by linarith)
    intro x hx
    exact (canonicalFacts (Set.Ioo (-1) 0) (Or.inl rfl) x hx).1
  · apply family_eq_translates_Ioo 0 1 pulledBack primitiveT (by linarith)
    intro x hx
    exact (canonicalFacts (Set.Ioo 0 1) (Or.inr rfl) x hx).1
theorem gap7 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = Translates U primitiveT := by
  calc
    Family U integrand = Family U pulledBack := gap4 U hU
    _ = SumFamily U := gap5 U hU
    _ = Translates U primitiveT := gap6 U hU
theorem gap8 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = Translates U primitive := by
  rw [gap7 U hU]
  ext F
  simp only [Translates, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun x hx => ?_⟩
    rw [hC x hx, (canonicalFacts U hU x hx).2.2.2]
  · rintro ⟨C, hC⟩
    refine ⟨C, fun x hx => ?_⟩
    rw [hC x hx, ← (canonicalFacts U hU x hx).2.2.2]

end
end ProofGap.Exercise2131
