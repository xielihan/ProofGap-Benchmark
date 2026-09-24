import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1973

noncomputable section

def branch : Set ℝ := Set.Ioo (-1) 1
def originalIntegrand (x : ℝ) :=
  1 / (Real.sqrt 2 + Real.sqrt (1 - x) + Real.sqrt (1 + x))
def conjugateIntegrand (x : ℝ) :=
  (-Real.sqrt 2 + Real.sqrt (1 - x) + Real.sqrt (1 + x)) /
    ((Real.sqrt 2 + Real.sqrt (1 - x) + Real.sqrt (1 + x)) *
      (-Real.sqrt 2 + Real.sqrt (1 - x) + Real.sqrt (1 + x)))
def simplifiedIntegrand (x : ℝ) :=
  (-Real.sqrt 2 + Real.sqrt (1 - x) + Real.sqrt (1 + x)) /
    (2 * Real.sqrt (1 - x ^ 2))
def arcsinePart (x : ℝ) := 1 / Real.sqrt (1 - x ^ 2)
def plusPart (x : ℝ) := 1 / Real.sqrt (1 + x)
def minusPart (x : ℝ) := 1 / Real.sqrt (1 - x)
def primitive (x : ℝ) :=
  -1 / Real.sqrt 2 * Real.arcsin x +
    Real.sqrt (1 + x) - Real.sqrt (1 - x)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def SplitFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn arcsinePart,
    ∃ H ∈ AntiderivativesOn plusPart,
    ∃ K ∈ AntiderivativesOn minusPart,
      ∀ x ∈ branch,
        F x = -1 / Real.sqrt 2 * G x + 1 / 2 * H x + 1 / 2 * K x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private lemma original_eq_conjugate {x : ℝ} (hx : x ∈ branch) :
    originalIntegrand x = conjugateIntegrand x := by
  change -1 < x ∧ x < 1 at hx
  have ha : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hb : 0 < Real.sqrt (1 - x) := Real.sqrt_pos.2 (by linarith)
  have hc : 0 < Real.sqrt (1 + x) := Real.sqrt_pos.2 (by linarith)
  have ha2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hb2 : (Real.sqrt (1 - x)) ^ 2 = 1 - x :=
    Real.sq_sqrt (by linarith)
  have hc2 : (Real.sqrt (1 + x)) ^ 2 = 1 + x :=
    Real.sq_sqrt (by linarith)
  have hn : 0 < -Real.sqrt 2 + Real.sqrt (1 - x) + Real.sqrt (1 + x) := by
    have hbc : 0 < Real.sqrt (1 - x) * Real.sqrt (1 + x) := mul_pos hb hc
    nlinarith
  have hd : 0 < Real.sqrt 2 + Real.sqrt (1 - x) + Real.sqrt (1 + x) := by
    linarith
  unfold originalIntegrand conjugateIntegrand
  field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc, ne_of_gt hn,
    ne_of_gt hd]

private lemma conjugate_eq_simplified {x : ℝ} (hx : x ∈ branch) :
    conjugateIntegrand x = simplifiedIntegrand x := by
  change -1 < x ∧ x < 1 at hx
  have ha2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hb2 : (Real.sqrt (1 - x)) ^ 2 = 1 - x :=
    Real.sq_sqrt (by linarith)
  have hc2 : (Real.sqrt (1 + x)) ^ 2 = 1 + x :=
    Real.sq_sqrt (by linarith)
  have hm : Real.sqrt (1 - x) * Real.sqrt (1 + x) =
      Real.sqrt (1 - x ^ 2) := by
    rw [← Real.sqrt_mul (by linarith : 0 ≤ 1 - x)]
    congr 1
    ring
  have hden :
      (Real.sqrt 2 + Real.sqrt (1 - x) + Real.sqrt (1 + x)) *
        (-Real.sqrt 2 + Real.sqrt (1 - x) + Real.sqrt (1 + x)) =
        2 * Real.sqrt (1 - x ^ 2) := by
    calc
      _ = (Real.sqrt (1 - x) + Real.sqrt (1 + x)) ^ 2 -
          (Real.sqrt 2) ^ 2 := by ring
      _ = 2 * (Real.sqrt (1 - x) * Real.sqrt (1 + x)) := by
        rw [ha2]
        nlinarith [hb2, hc2]
      _ = 2 * Real.sqrt (1 - x ^ 2) := by rw [hm]
  unfold conjugateIntegrand simplifiedIntegrand
  rw [hden]

private lemma original_eq_simplified {x : ℝ} (hx : x ∈ branch) :
    originalIntegrand x = simplifiedIntegrand x :=
  (original_eq_conjugate hx).trans (conjugate_eq_simplified hx)

private lemma simplified_split {x : ℝ} (hx : x ∈ branch) :
    simplifiedIntegrand x =
      -1 / Real.sqrt 2 * arcsinePart x +
        1 / 2 * plusPart x + 1 / 2 * minusPart x := by
  change -1 < x ∧ x < 1 at hx
  have ha : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hb : 0 < Real.sqrt (1 - x) := Real.sqrt_pos.2 (by linarith)
  have hc : 0 < Real.sqrt (1 + x) := Real.sqrt_pos.2 (by linarith)
  have ha2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hm : Real.sqrt (1 - x) * Real.sqrt (1 + x) =
      Real.sqrt (1 - x ^ 2) := by
    rw [← Real.sqrt_mul (by linarith : 0 ≤ 1 - x)]
    congr 1
    ring
  unfold simplifiedIntegrand arcsinePart plusPart minusPart
  rw [← hm]
  field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc] <;>
    nlinarith [ha2]

private lemma hasDeriv_arc (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt Real.arcsin (arcsinePart x) x := by
  change -1 < x ∧ x < 1 at hx
  simpa [arcsinePart] using
    (Real.hasDerivAt_arcsin (by linarith : x ≠ -1)
      (by linarith : x ≠ 1))

private lemma hasDeriv_plus (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => 2 * Real.sqrt (1 + y)) (plusPart x) x := by
  change -1 < x ∧ x < 1 at hx
  have hp : 0 < 1 + x := by linarith
  have hs : HasDerivAt (fun y : ℝ => Real.sqrt (1 + y))
      (1 / (2 * Real.sqrt (1 + x))) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_sqrt (ne_of_gt hp)).comp x
        ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x))
  have hs0 : Real.sqrt (1 + x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  convert hs.const_mul 2 using 1
  simp only [plusPart]
  field_simp [hs0]

private lemma hasDeriv_minus (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => -2 * Real.sqrt (1 - y)) (minusPart x) x := by
  change -1 < x ∧ x < 1 at hx
  have hp : 0 < 1 - x := by linarith
  have hs : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y))
      ((1 / (2 * Real.sqrt (1 - x))) * (-1)) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_sqrt (ne_of_gt hp)).comp x
        ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))
  have hs0 : Real.sqrt (1 - x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  convert hs.const_mul (-2) using 1
  simp only [minusPart]
  field_simp [hs0]

private lemma arc_antiderivative :
    Real.arcsin ∈ AntiderivativesOn arcsinePart := by
  intro x hx
  exact hasDeriv_arc x hx

private lemma plus_antiderivative :
    (fun x : ℝ => 2 * Real.sqrt (1 + x)) ∈
      AntiderivativesOn plusPart := by
  intro x hx
  exact hasDeriv_plus x hx

private lemma minus_antiderivative :
    (fun x : ℝ => -2 * Real.sqrt (1 - x)) ∈
      AntiderivativesOn minusPart := by
  intro x hx
  exact hasDeriv_minus x hx

private lemma primitive_mem_split : primitive ∈ SplitFamily := by
  refine ⟨Real.arcsin, arc_antiderivative,
    (fun x : ℝ => 2 * Real.sqrt (1 + x)), plus_antiderivative,
    (fun x : ℝ => -2 * Real.sqrt (1 - x)), minus_antiderivative, ?_⟩
  intro x hx
  unfold primitive
  ring

theorem gap1 :
    AntiderivativesOn originalIntegrand =
      AntiderivativesOn conjugateIntegrand := by
  ext F
  constructor <;> intro h x hx
  · simpa only [original_eq_conjugate hx] using h x hx
  · simpa only [original_eq_conjugate hx] using h x hx
theorem gap2 :
    AntiderivativesOn originalIntegrand =
      AntiderivativesOn simplifiedIntegrand := by
  ext F
  constructor <;> intro h x hx
  · simpa only [original_eq_simplified hx] using h x hx
  · simpa only [original_eq_simplified hx] using h x hx
theorem gap3 :
    AntiderivativesOn simplifiedIntegrand = SplitFamily := by
  ext F
  constructor
  · intro hF
    let K : ℝ → ℝ := fun y =>
      2 * (F y - (-1 / Real.sqrt 2) * Real.arcsin y -
        (1 / 2) * (2 * Real.sqrt (1 + y)))
    refine ⟨Real.arcsin, arc_antiderivative,
      (fun y : ℝ => 2 * Real.sqrt (1 + y)), plus_antiderivative,
      K, ?_, ?_⟩
    · intro x hx
      have hd := (((hF x hx).sub
        ((hasDeriv_arc x hx).const_mul (-1 / Real.sqrt 2))).sub
        ((hasDeriv_plus x hx).const_mul (1 / 2))).const_mul 2
      have hc :
          2 * (simplifiedIntegrand x -
              (-1 / Real.sqrt 2) * arcsinePart x -
              (1 / 2) * plusPart x) = minusPart x := by
        rw [simplified_split hx]
        ring
      simpa only [K, hc] using hd
    · intro x hx
      dsimp [K]
      ring
  · rintro ⟨G, hG, H, hH, K, hK, hEq⟩
    intro x hx
    have hd := (((hG x hx).const_mul (-1 / Real.sqrt 2)).add
      ((hH x hx).const_mul (1 / 2))).add
      ((hK x hx).const_mul (1 / 2))
    have hd' : HasDerivAt
        (fun y => -1 / Real.sqrt 2 * G y + 1 / 2 * H y + 1 / 2 * K y)
        (simplifiedIntegrand x) x := by
      convert hd using 1
      exact simplified_split hx
    have hopen : IsOpen branch := by
      simpa [branch] using
        (isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) 1))
    have hev :
        (fun y => -1 / Real.sqrt 2 * G y + 1 / 2 * H y + 1 / 2 * K y)
          =ᶠ[nhds x] F :=
      Filter.Eventually.mono (hopen.mem_nhds hx)
        (fun y hy => (hEq y hy).symm)
    exact hd'.congr_of_eventuallyEq hev.symm
theorem gap4 :
    AntiderivativesOn originalIntegrand = SplitFamily := by
  exact gap2.trans gap3
theorem gap5 :
    AntiderivativesOn originalIntegrand = PrimitiveFamily := by
  have hPmem : primitive ∈ AntiderivativesOn originalIntegrand := by
    rw [gap4]
    exact primitive_mem_split
  ext F
  constructor
  · intro hF
    let D : ℝ → ℝ := fun y => F y - primitive y
    have hD : ∀ x ∈ branch, HasDerivAt D 0 x := by
      intro x hx
      dsimp [D]
      simpa using (hF x hx).sub (hPmem x hx)
    have hdiff : DifferentiableOn ℝ D branch := by
      intro x hx
      exact (hD x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ branch, deriv D x = 0 := by
      intro x hx
      exact (hD x hx).deriv
    refine ⟨D 0, ?_⟩
    intro x hx
    have hzero : (0 : ℝ) ∈ branch := by
      simp [branch]
    have heq : D x = D 0 :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hdiff hderiv hx hzero
    dsimp [D] at heq ⊢
    linarith
  · rintro ⟨C, hEq⟩
    intro x hx
    have hd := (hPmem x hx).add_const C
    have hopen : IsOpen branch := by
      simpa [branch] using
        (isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) 1))
    have hev : (fun y => primitive y + C) =ᶠ[nhds x] F :=
      Filter.Eventually.mono (hopen.mem_nhds hx)
        (fun y hy => (hEq y hy).symm)
    exact hd.congr_of_eventuallyEq hev.symm

end
end ProofGap.Exercise1973
