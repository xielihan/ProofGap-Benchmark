import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1918

noncomputable section

def branch : Set ℝ := Set.Ioi 0
def substitution (x : ℝ) := x + 1 / x
def shiftedSubstitution (x : ℝ) := substitution x + 1 / 2
def integrand (x : ℝ) :=
  (x ^ 2 - 1) / (x ^ 4 + x ^ 3 + x ^ 2 + x + 1)
def dividedIntegrand (x : ℝ) :=
  (1 - 1 / x ^ 2) / (x ^ 2 + 1 / x ^ 2 + x + 1 / x + 1)
def substitutedIntegrand (x : ℝ) :=
  1 / ((substitution x) ^ 2 + substitution x - 1) * deriv substitution x
def shiftedIntegrand (x : ℝ) :=
  1 / ((shiftedSubstitution x) ^ 2 - 5 / 4) *
    deriv shiftedSubstitution x
def primitiveRaw (x : ℝ) :=
  1 / Real.sqrt 5 *
    Real.log ((substitution x + 1 / 2 - Real.sqrt 5 / 2) /
      (substitution x + 1 / 2 + Real.sqrt 5 / 2))
def primitive (x : ℝ) :=
  1 / Real.sqrt 5 *
    Real.log ((2 * x ^ 2 + (1 - Real.sqrt 5) * x + 2) /
      (2 * x ^ 2 + (1 + Real.sqrt 5) * x + 2))
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem substitution_derivative (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt substitution (1 - 1 / x ^ 2) x := by
  have h :=
    (hasDerivAt_id x).add
      ((hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx)
  convert h using 1 <;>
    simp [substitution, id, div_eq_mul_inv, sub_eq_add_neg]

theorem gap1 :
    AntiderivativesOn integrand = AntiderivativesOn dividedIntegrand := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · intro h x hx
    change 0 < x at hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have h₁ : 0 < x ^ 4 + x ^ 3 + x ^ 2 + x + 1 := by positivity
    have h₂ : 0 < x ^ 2 + 1 / x ^ 2 + x + 1 / x + 1 := by positivity
    have heq : integrand x = dividedIntegrand x := by
      unfold integrand dividedIntegrand
      field_simp [hx0, ne_of_gt h₁, ne_of_gt h₂] <;> ring
    simpa [heq] using h x (by simpa [branch] using hx)
  · intro h x hx
    change 0 < x at hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have h₁ : 0 < x ^ 4 + x ^ 3 + x ^ 2 + x + 1 := by positivity
    have h₂ : 0 < x ^ 2 + 1 / x ^ 2 + x + 1 / x + 1 := by positivity
    have heq : integrand x = dividedIntegrand x := by
      unfold integrand dividedIntegrand
      field_simp [hx0, ne_of_gt h₁, ne_of_gt h₂] <;> ring
    simpa [heq] using h x (by simpa [branch] using hx)
theorem gap2 :
    AntiderivativesOn dividedIntegrand = AntiderivativesOn substitutedIntegrand := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  have heq : ∀ x ∈ branch, dividedIntegrand x = substitutedIntegrand x := by
    intro x hx
    change 0 < x at hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hd := substitution_derivative x hx0
    have hden :
        substitution x ^ 2 + substitution x - 1 =
          x ^ 2 + 1 / x ^ 2 + x + 1 / x + 1 := by
      unfold substitution
      field_simp [hx0] <;> ring
    rw [substitutedIntegrand, hd.deriv, hden]
    simp [dividedIntegrand, div_eq_mul_inv, mul_comm]
  constructor
  · intro h x hx
    simpa [heq x hx] using h x hx
  · intro h x hx
    simpa [heq x hx] using h x hx
theorem gap3 :
    AntiderivativesOn integrand = AntiderivativesOn substitutedIntegrand := by
  exact gap1.trans gap2
theorem gap4 :
    AntiderivativesOn integrand = AntiderivativesOn shiftedIntegrand := by
  calc
    AntiderivativesOn integrand = AntiderivativesOn dividedIntegrand := gap1
    _ = AntiderivativesOn shiftedIntegrand := by
      apply Set.ext
      intro F
      simp only [AntiderivativesOn, Set.mem_setOf_eq]
      have heq : ∀ x ∈ branch, dividedIntegrand x = shiftedIntegrand x := by
        intro x hx
        change 0 < x at hx
        have hx0 : x ≠ 0 := ne_of_gt hx
        have hd := substitution_derivative x hx0
        have hds : HasDerivAt shiftedSubstitution (1 - 1 / x ^ 2) x := by
          simpa only [shiftedSubstitution] using hd.add_const (1 / 2)
        have hden :
            shiftedSubstitution x ^ 2 - 5 / 4 =
              x ^ 2 + 1 / x ^ 2 + x + 1 / x + 1 := by
          unfold shiftedSubstitution substitution
          field_simp [hx0] <;> ring
        rw [shiftedIntegrand, hds.deriv, hden]
        simp [dividedIntegrand, div_eq_mul_inv, mul_comm]
      constructor
      · intro h x hx
        simpa [heq x hx] using h x hx
      · intro h x hx
        simpa [heq x hx] using h x hx
theorem gap5 :
    AntiderivativesOn integrand = PrimitiveFamily primitiveRaw := by
  have hPshift : primitiveRaw ∈ AntiderivativesOn shiftedIntegrand := by
    intro x hx
    change 0 < x at hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hspos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
    have hs0 : Real.sqrt 5 ≠ 0 := ne_of_gt hspos
    have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hslt : Real.sqrt 5 < 3 := by
      nlinarith [Real.sqrt_nonneg 5, hsq]
    have hsub : 2 ≤ substitution x := by
      have hid : substitution x - 2 = (x - 1) ^ 2 / x := by
        unfold substitution
        field_simp [hx0] <;> ring
      have hn : 0 ≤ (x - 1) ^ 2 / x := by positivity
      linarith
    have hminus : 0 < shiftedSubstitution x - Real.sqrt 5 / 2 := by
      unfold shiftedSubstitution
      nlinarith
    have hplus : 0 < shiftedSubstitution x + Real.sqrt 5 / 2 := by
      unfold shiftedSubstitution
      nlinarith [Real.sqrt_nonneg 5]
    have hquad : 0 < shiftedSubstitution x ^ 2 - 5 / 4 := by
      nlinarith [mul_pos hminus hplus, hsq]
    have hd := substitution_derivative x hx0
    have hds : HasDerivAt shiftedSubstitution (1 - 1 / x ^ 2) x := by
      simpa only [shiftedSubstitution] using hd.add_const (1 / 2)
    have hnum :
        HasDerivAt (fun y => shiftedSubstitution y - Real.sqrt 5 / 2)
          (1 - 1 / x ^ 2) x :=
      hds.sub_const (Real.sqrt 5 / 2)
    have hden :
        HasDerivAt (fun y => shiftedSubstitution y + Real.sqrt 5 / 2)
          (1 - 1 / x ^ 2) x :=
      hds.add_const (Real.sqrt 5 / 2)
    have hratio := hnum.div hden (ne_of_gt hplus)
    have hlog :=
      (Real.hasDerivAt_log
        (div_ne_zero (ne_of_gt hminus) (ne_of_gt hplus))).comp x hratio
    have hraw := hlog.const_mul (1 / Real.sqrt 5)
    have hfactor :
        (shiftedSubstitution x - Real.sqrt 5 / 2) *
            (shiftedSubstitution x + Real.sqrt 5 / 2) =
          shiftedSubstitution x ^ 2 - 5 / 4 := by
      calc
        (shiftedSubstitution x - Real.sqrt 5 / 2) *
              (shiftedSubstitution x + Real.sqrt 5 / 2) =
            shiftedSubstitution x ^ 2 - Real.sqrt 5 ^ 2 / 4 := by ring
        _ = shiftedSubstitution x ^ 2 - 5 / 4 := by rw [hsq]
    have halg :
        1 / Real.sqrt 5 *
            (((shiftedSubstitution x - Real.sqrt 5 / 2) /
                (shiftedSubstitution x + Real.sqrt 5 / 2))⁻¹ *
              (((1 - 1 / x ^ 2) *
                    (shiftedSubstitution x + Real.sqrt 5 / 2) -
                  (shiftedSubstitution x - Real.sqrt 5 / 2) *
                    (1 - 1 / x ^ 2)) /
                (shiftedSubstitution x + Real.sqrt 5 / 2) ^ 2)) =
          1 / (shiftedSubstitution x ^ 2 - 5 / 4) *
            (1 - 1 / x ^ 2) := by
      rw [← hfactor]
      field_simp [hs0, ne_of_gt hminus, ne_of_gt hplus] <;> ring
    have hraw' :
        HasDerivAt primitiveRaw
          (1 / Real.sqrt 5 *
            (((shiftedSubstitution x - Real.sqrt 5 / 2) /
                (shiftedSubstitution x + Real.sqrt 5 / 2))⁻¹ *
              (((1 - 1 / x ^ 2) *
                    (shiftedSubstitution x + Real.sqrt 5 / 2) -
                  (shiftedSubstitution x - Real.sqrt 5 / 2) *
                    (1 - 1 / x ^ 2)) /
                (shiftedSubstitution x + Real.sqrt 5 / 2) ^ 2))) x := by
      simpa only [primitiveRaw, shiftedSubstitution, Function.comp_apply] using hraw
    rw [halg] at hraw'
    rw [shiftedIntegrand, hds.deriv]
    exact hraw'
  have hP : primitiveRaw ∈ AntiderivativesOn integrand := by
    rw [gap4]
    exact hPshift
  apply Set.ext
  intro F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      ∃ C : ℝ, ∀ x ∈ branch, F x = primitiveRaw x + C
  constructor
  · intro hF
    have hzero : ∀ x ∈ branch,
        HasDerivAt (fun y => F y - primitiveRaw y) 0 x := by
      intro x hx
      convert (hF x hx).sub (hP x hx) using 1 <;> ring
    refine ⟨F 1 - primitiveRaw 1, ?_⟩
    intro x hx
    have hsame :
        F x - primitiveRaw x = F 1 - primitiveRaw 1 :=
      isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
        (fun y hy =>
          (hzero y (by simpa [branch] using hy)).differentiableAt.differentiableWithinAt)
        (fun y hy =>
          (hzero y (by simpa [branch] using hy)).deriv)
        (by simpa [branch] using hx)
        (by norm_num)
    linarith
  · rintro ⟨C, hC⟩
    intro x hx
    have hbase :
        HasDerivAt (fun y => primitiveRaw y + C) (integrand x) x :=
      (hP x hx).add_const C
    have hopen : IsOpen branch := by simpa [branch] using isOpen_Ioi
    exact hbase.congr_of_eventuallyEq
      (by
        filter_upwards [hopen.mem_nhds hx] with y hy
        exact hC y hy)
theorem gap6 :
    PrimitiveFamily primitiveRaw = PrimitiveFamily primitive := by
  apply Set.ext
  intro F
  simp only [PrimitiveFamily, Set.mem_setOf_eq]
  have hp : ∀ x ∈ branch, primitiveRaw x = primitive x := by
    intro x hx
    change 0 < x at hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hsub : 2 ≤ substitution x := by
      have hid : substitution x - 2 = (x - 1) ^ 2 / x := by
        unfold substitution
        field_simp [hx0] <;> ring
      have hn : 0 ≤ (x - 1) ^ 2 / x := by positivity
      linarith
    have hplus : 0 < substitution x + 1 / 2 + Real.sqrt 5 / 2 := by
      nlinarith [Real.sqrt_nonneg 5]
    have hnumPoly :
        2 * x ^ 2 + (1 - Real.sqrt 5) * x + 2 =
          2 * x * (substitution x + 1 / 2 - Real.sqrt 5 / 2) := by
      unfold substitution
      field_simp [hx0] <;> ring
    have hdenPoly :
        2 * x ^ 2 + (1 + Real.sqrt 5) * x + 2 =
          2 * x * (substitution x + 1 / 2 + Real.sqrt 5 / 2) := by
      unfold substitution
      field_simp [hx0] <;> ring
    have hratio :
        (substitution x + 1 / 2 - Real.sqrt 5 / 2) /
            (substitution x + 1 / 2 + Real.sqrt 5 / 2) =
          (2 * x ^ 2 + (1 - Real.sqrt 5) * x + 2) /
            (2 * x ^ 2 + (1 + Real.sqrt 5) * x + 2) := by
      rw [hnumPoly, hdenPoly]
      field_simp [hx0, ne_of_gt hplus] <;> ring
    unfold primitiveRaw primitive
    exact congrArg (fun z : ℝ => 1 / Real.sqrt 5 * Real.log z) hratio
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [← hp x hx]
    exact hC x hx
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [hp x hx]
    exact hC x hx
theorem gap7 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  exact gap5.trans gap6

end
end ProofGap.Exercise1918
