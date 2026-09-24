import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1955

noncomputable section

def q (x : ℝ) := 1 + 2 * x - x ^ 2
def branch : Set ℝ := {x | 0 < q x}
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def PrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}
def integrand (x : ℝ) := x ^ 3 / ((1 + x) * Real.sqrt (q x))
def rewrittenIntegrand (x : ℝ) :=
  (x ^ 3 + 1 - 1) / ((1 + x) * Real.sqrt (q x))
def polynomialPart (x : ℝ) := (x ^ 2 - x + 1) / Real.sqrt (q x)
def residual (x : ℝ) := 1 / ((1 + x) * Real.sqrt (q x))
def TwoPartFamily : Set (ℝ → ℝ) :=
  {F | ∃ A ∈ AntiderivativesOn branch polynomialPart,
    ∃ B ∈ AntiderivativesOn branch residual,
    ∀ x ∈ branch, F x = A x - B x}
def ExpandedReductionFamily : Set (ℝ → ℝ) :=
  {F | ∃ A ∈ AntiderivativesOn branch (fun x => q x / Real.sqrt (q x)),
    ∃ B ∈ AntiderivativesOn branch
      (fun x => (2 * x - 2) / Real.sqrt (q x)),
    ∃ D ∈ AntiderivativesOn branch (fun x => 1 / Real.sqrt (q x)),
    ∃ E ∈ AntiderivativesOn branch residual,
    ∀ x ∈ branch, F x = -A x + 1 / 2 * B x + 3 * D x - E x}
def standardReduction (x : ℝ) :=
  -(x + 1) / 2 * Real.sqrt (q x) +
    2 * Real.arcsin ((x - 1) / Real.sqrt 2)
def residualPrimitive (x : ℝ) :=
  1 / Real.sqrt 2 * Real.arcsin (x * Real.sqrt 2 / (x + 1))
def finalPrimitive (x : ℝ) :=
  -(1 + x) / 2 * Real.sqrt (q x) -
    2 * Real.arcsin ((1 - x) / Real.sqrt 2) -
    1 / Real.sqrt 2 * Real.arcsin (x * Real.sqrt 2 / (1 + x))

private theorem branch_eq_Ioo :
    branch = Set.Ioo (1 - Real.sqrt 2) (1 + Real.sqrt 2) := by
  ext x
  simp only [branch, Set.mem_setOf_eq, Set.mem_Ioo]
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  constructor
  · intro hx
    have hsq : (x - 1) ^ 2 < 2 := by
      dsimp [q] at hx
      nlinarith
    constructor <;>
      nlinarith [sq_nonneg (x - 1 + Real.sqrt 2),
        sq_nonneg (x - 1 - Real.sqrt 2)]
  · rintro ⟨hl, hu⟩
    have hp : 0 <
        (Real.sqrt 2 - (x - 1)) * (Real.sqrt 2 + (x - 1)) :=
      mul_pos (by linarith) (by linarith)
    change 0 < q x
    dsimp [q]
    nlinarith [hs2]

private theorem branch_open : IsOpen branch := by
  rw [branch_eq_Ioo]
  exact isOpen_Ioo

private theorem branch_convex : Convex ℝ branch := by
  rw [branch_eq_Ioo]
  exact convex_Ioo _ _

private theorem branch_add_one_pos {x : ℝ} (hx : x ∈ branch) :
    0 < x + 1 := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hslt : Real.sqrt 2 < 2 := by nlinarith
  have hx' : 1 - Real.sqrt 2 < x := by
    rw [branch_eq_Ioo] at hx
    exact hx.1
  linarith

private theorem transfer_deriv {F G : ℝ → ℝ} {d x : ℝ}
    (hx : x ∈ branch) (hG : HasDerivAt G d x)
    (hFG : Set.EqOn F G branch) : HasDerivAt F d x := by
  apply hG.congr_of_eventuallyEq
  filter_upwards [branch_open.mem_nhds hx] with y hy
  exact hFG hy

private theorem integrand_split (x : ℝ) (hx : x ∈ branch) :
    integrand x = polynomialPart x - residual x := by
  have hxq : 0 < q x := hx
  have hs : Real.sqrt (q x) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hxq)
  have hx1 : x + 1 ≠ 0 := ne_of_gt (branch_add_one_pos hx)
  have h1x : 1 + x ≠ 0 := by simpa [add_comm] using hx1
  simp only [integrand, polynomialPart, residual]
  field_simp [hs, hx1, h1x]
  ring

private theorem expanded_split (x : ℝ) (hx : x ∈ branch) :
    polynomialPart x =
      -(q x / Real.sqrt (q x)) +
        1 / 2 * ((2 * x - 2) / Real.sqrt (q x)) +
        3 * (1 / Real.sqrt (q x)) := by
  have hxq : 0 < q x := hx
  have hs : Real.sqrt (q x) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hxq)
  simp only [polynomialPart]
  field_simp [hs]
  dsimp [q]
  ring

private theorem hasDerivAt_branchArcsin (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y => Real.arcsin ((y - 1) / Real.sqrt 2))
      (1 / Real.sqrt (q x)) x := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := ne_of_gt hs
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hxI : x ∈ Set.Ioo (1 - Real.sqrt 2) (1 + Real.sqrt 2) := by
    rw [← branch_eq_Ioo]
    exact hx
  have hu : (x - 1) / Real.sqrt 2 ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · apply (lt_div_iff₀ hs).2
      linarith [hxI.1]
    · apply (div_lt_iff₀ hs).2
      linarith [hxI.2]
  have hu' : HasDerivAt (fun y : ℝ => (y - 1) / Real.sqrt 2)
      (1 / Real.sqrt 2) x := by
    simpa using (((hasDerivAt_id x).sub_const 1).div_const
      (Real.sqrt 2))
  have harg : 1 - ((x - 1) / Real.sqrt 2) ^ 2 = q x / 2 := by
    dsimp [q]
    field_simp [hs0]
    nlinarith [hs2]
  have hxq : 0 < q x := hx
  have hsqrtarg :
      Real.sqrt (1 - ((x - 1) / Real.sqrt 2) ^ 2) =
        Real.sqrt (q x) / Real.sqrt 2 := by
    rw [harg, Real.sqrt_div (le_of_lt hxq)]
  have h :=
    (Real.hasDerivAt_arcsin hu.1.ne' hu.2.ne).comp x hu'
  convert h using 1
  rw [hsqrtarg]
  field_simp [hs0, ne_of_gt (Real.sqrt_pos.2 hxq)]

private theorem hasDerivAt_sqrtQ (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y => Real.sqrt (q y))
      ((1 - x) / Real.sqrt (q x)) x := by
  have hxq : 0 < q x := hx
  have hq : HasDerivAt q (2 - 2 * x) x := by
    have h := ((hasDerivAt_const x (1 : ℝ)).add
      ((hasDerivAt_id x).const_mul 2)).sub ((hasDerivAt_id x).pow 2)
    convert h using 1 <;> simp [q] <;> ring
  have h := (Real.hasDerivAt_sqrt (ne_of_gt hxq)).comp x hq
  convert h using 1 <;>
    field_simp [ne_of_gt (Real.sqrt_pos.2 hxq)] <;> ring

private theorem standardReduction_mem :
    standardReduction ∈ AntiderivativesOn branch polynomialPart := by
  intro x hx
  have hsqrt := hasDerivAt_sqrtQ x hx
  have hasin := hasDerivAt_branchArcsin x hx
  have hcoef : HasDerivAt (fun y : ℝ => -(y + 1) / 2)
      (-1 / 2) x := by
    convert ((hasDerivAt_id x).add_const 1).const_mul (-1 / 2) using 1 <;>
      simp <;> ring
  have h : HasDerivAt standardReduction
      ((-1 / 2) * Real.sqrt (q x) +
        (-(x + 1) / 2) * ((1 - x) / Real.sqrt (q x)) +
        2 * (1 / Real.sqrt (q x))) x := by
    simpa only [standardReduction] using
      (hcoef.mul hsqrt).add (hasin.const_mul 2)
  have hxq : 0 < q x := hx
  have hs0 : Real.sqrt (q x) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hxq)
  have hs2 : (Real.sqrt (q x)) ^ 2 = q x :=
    Real.sq_sqrt (le_of_lt hxq)
  have hval :
      (-1 / 2) * Real.sqrt (q x) +
          (-(x + 1) / 2) * ((1 - x) / Real.sqrt (q x)) +
          2 * (1 / Real.sqrt (q x)) =
        polynomialPart x := by
    simp only [polynomialPart]
    field_simp [hs0]
    rw [hs2]
    dsimp [q]
    ring
  rw [← hval]
  exact h

private def canonicalD (x : ℝ) :=
  Real.arcsin ((x - 1) / Real.sqrt 2)

private def canonicalB (x : ℝ) :=
  -2 * Real.sqrt (q x)

private def canonicalA (x : ℝ) :=
  -standardReduction x + 1 / 2 * canonicalB x + 3 * canonicalD x

private theorem canonicalD_mem :
    canonicalD ∈ AntiderivativesOn branch
      (fun x => 1 / Real.sqrt (q x)) := by
  intro x hx
  simpa [canonicalD] using hasDerivAt_branchArcsin x hx

private theorem canonicalB_mem :
    canonicalB ∈ AntiderivativesOn branch
      (fun x => (2 * x - 2) / Real.sqrt (q x)) := by
  intro x hx
  have h : HasDerivAt canonicalB
      (-2 * ((1 - x) / Real.sqrt (q x))) x := by
    simpa only [canonicalB] using
      (hasDerivAt_sqrtQ x hx).const_mul (-2)
  convert h using 1
  ring

private theorem canonicalA_mem :
    canonicalA ∈ AntiderivativesOn branch
      (fun x => q x / Real.sqrt (q x)) := by
  intro x hx
  have hraw := ((standardReduction_mem x hx).neg.add
    ((canonicalB_mem x hx).const_mul (1 / 2))).add
      ((canonicalD_mem x hx).const_mul 3)
  have h : HasDerivAt canonicalA
      (-polynomialPart x +
        1 / 2 * ((2 * x - 2) / Real.sqrt (q x)) +
        3 * (1 / Real.sqrt (q x))) x := by
    simpa only [canonicalA] using hraw
  have hv :
      -polynomialPart x +
          1 / 2 * ((2 * x - 2) / Real.sqrt (q x)) +
          3 * (1 / Real.sqrt (q x)) =
        q x / Real.sqrt (q x) := by
    rw [expanded_split x hx]
    ring
  change HasDerivAt canonicalA (q x / Real.sqrt (q x)) x
  rw [← hv]
  exact h

private theorem standard_characterization :
    AntiderivativesOn branch integrand =
      {F | ∃ E ∈ AntiderivativesOn branch residual,
        ∀ x ∈ branch,
          F x = -(x + 1) / 2 * Real.sqrt (q x) +
            2 * Real.arcsin ((x - 1) / Real.sqrt 2) - E x} := by
  ext F
  constructor
  · intro hF
    let E : ℝ → ℝ := fun y => standardReduction y - F y
    refine ⟨E, ?_, ?_⟩
    · intro x hx
      have h := (standardReduction_mem x hx).sub (hF x hx)
      have hd : HasDerivAt (fun y => standardReduction y - F y)
          (residual x) x := by
        convert h using 1
        rw [integrand_split x hx]
        ring
      simpa [E] using hd
    · intro x hx
      simp [E, standardReduction]
  · rintro ⟨E, hE, hF⟩
    intro x hx
    have h := (standardReduction_mem x hx).sub (hE x hx)
    have hd : HasDerivAt (fun y => standardReduction y - E y)
        (integrand x) x := by
      convert h using 1
      rw [integrand_split x hx]
    apply transfer_deriv hx hd
    intro y hy
    simpa [standardReduction] using hF y hy

private theorem hasDerivAt_residualPrimitive (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt residualPrimitive (residual x) x := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := ne_of_gt hs
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hd : 0 < x + 1 := branch_add_one_pos hx
  have hd0 : x + 1 ≠ 0 := ne_of_gt hd
  have h1x : 1 + x ≠ 0 := by simpa [add_comm] using hd0
  have hxq : 0 < q x := hx
  have hdiff :
      (x + 1) ^ 2 - (x * Real.sqrt 2) ^ 2 = q x := by
    rw [q]
    nlinarith [hs2]
  have hzsq : (x * Real.sqrt 2) ^ 2 < (x + 1) ^ 2 := by
    nlinarith [hdiff]
  have hzlo : -(x + 1) < x * Real.sqrt 2 := by
    nlinarith [hzsq, sq_nonneg (x * Real.sqrt 2 + (x + 1))]
  have zhi : x * Real.sqrt 2 < x + 1 := by
    nlinarith [hzsq, sq_nonneg (x * Real.sqrt 2 - (x + 1))]
  have hu : x * Real.sqrt 2 / (x + 1) ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · apply (lt_div_iff₀ hd).2
      simpa using hzlo
    · apply (div_lt_iff₀ hd).2
      simpa using zhi
  have hnum : HasDerivAt (fun y : ℝ => y * Real.sqrt 2)
      (Real.sqrt 2) x := by
    simpa using (hasDerivAt_id x).mul_const (Real.sqrt 2)
  have hden : HasDerivAt (fun y : ℝ => y + 1) 1 x := by
    simpa using (hasDerivAt_id x).add_const 1
  have hraw : HasDerivAt
      (fun y : ℝ => y * Real.sqrt 2 / (y + 1))
      ((Real.sqrt 2 * (x + 1) - (x * Real.sqrt 2) * 1) /
        (x + 1) ^ 2) x :=
    hnum.div hden hd0
  have hu' : HasDerivAt
      (fun y : ℝ => y * Real.sqrt 2 / (y + 1))
      (Real.sqrt 2 / (x + 1) ^ 2) x := by
    convert hraw using 1
    ring
  have harg :
      1 - (x * Real.sqrt 2 / (x + 1)) ^ 2 =
        q x / (x + 1) ^ 2 := by
    field_simp [hd0]
    nlinarith [hdiff]
  have hsqrtarg :
      Real.sqrt (1 - (x * Real.sqrt 2 / (x + 1)) ^ 2) =
        Real.sqrt (q x) / (x + 1) := by
    rw [harg, Real.sqrt_div (le_of_lt hxq), Real.sqrt_sq_eq_abs,
      abs_of_pos hd]
  have h :=
    ((Real.hasDerivAt_arcsin hu.1.ne' hu.2.ne).comp x hu').const_mul
      (1 / Real.sqrt 2)
  have hscalar :
      1 / Real.sqrt 2 *
          (1 / Real.sqrt (1 - (x * Real.sqrt 2 / (x + 1)) ^ 2) *
            (Real.sqrt 2 / (x + 1) ^ 2)) = residual x := by
    rw [hsqrtarg]
    simp only [residual]
    field_simp [hs0, hd0, h1x,
      ne_of_gt (Real.sqrt_pos.2 hxq)]
    ring
  rw [← hscalar]
  change HasDerivAt
    (fun y : ℝ => 1 / Real.sqrt 2 *
      Real.arcsin (y * Real.sqrt 2 / (y + 1)))
    (1 / Real.sqrt 2 *
      (1 / Real.sqrt (1 - (x * Real.sqrt 2 / (x + 1)) ^ 2) *
        (Real.sqrt 2 / (x + 1) ^ 2))) x
  simpa only [one_div] using h

private theorem residual_family :
    AntiderivativesOn branch residual =
      PrimitiveFamilyOn branch residualPrimitive := by
  ext F
  constructor
  · intro hF
    let H : ℝ → ℝ := fun x => F x - residualPrimitive x
    have hH : ∀ x ∈ branch, HasDerivAt H 0 x := by
      intro x hx
      simpa [H] using
        (hF x hx).sub (hasDerivAt_residualPrimitive x hx)
    have hdiff : DifferentiableOn ℝ H branch := by
      intro x hx
      exact (hH x hx).differentiableAt.differentiableWithinAt
    have hconst : ∀ x ∈ branch, ∀ y ∈ branch, H x = H y := by
      intro x hx y hy
      exact branch_open.is_const_of_deriv_eq_zero
        branch_convex.isPreconnected hdiff
        (fun z hz => (hH z hz).deriv) hx hy
    have h1 : (1 : ℝ) ∈ branch := by norm_num [branch, q]
    refine ⟨H 1, ?_⟩
    intro x hx
    have heq := hconst x hx 1 h1
    dsimp [H] at heq ⊢
    linarith
  · rintro ⟨C, hF⟩
    intro x hx
    have hp := hasDerivAt_residualPrimitive x hx
    have hd : HasDerivAt (fun y => residualPrimitive y + C)
        (residual x) x := hp.add_const C
    apply transfer_deriv hx hd
    intro y hy
    exact hF y hy

theorem gap1 :
    AntiderivativesOn branch integrand =
      AntiderivativesOn branch rewrittenIntegrand := by
  ext F
  simp [AntiderivativesOn, integrand, rewrittenIntegrand]
theorem gap2 :
    AntiderivativesOn branch integrand = TwoPartFamily := by
  ext F
  constructor
  · intro hF
    obtain ⟨E, hE, hFE⟩ :=
      (Set.ext_iff.mp standard_characterization F).mp hF
    refine ⟨standardReduction, standardReduction_mem, E, hE, ?_⟩
    intro x hx
    simpa [standardReduction] using hFE x hx
  · rintro ⟨A, hA, B, hB, hF⟩
    intro x hx
    have hAB := (hA x hx).sub (hB x hx)
    have hd : HasDerivAt (fun y => A y - B y) (integrand x) x := by
      convert hAB using 1
      rw [integrand_split x hx]
    exact transfer_deriv hx hd hF
theorem gap3 :
    AntiderivativesOn branch integrand = ExpandedReductionFamily := by
  ext F
  constructor
  · intro hF
    obtain ⟨E, hE, hFE⟩ :=
      (Set.ext_iff.mp standard_characterization F).mp hF
    refine ⟨canonicalA, canonicalA_mem, canonicalB, canonicalB_mem,
      canonicalD, canonicalD_mem, E, hE, ?_⟩
    intro x hx
    have hstd : F x = standardReduction x - E x := by
      simpa [standardReduction] using hFE x hx
    rw [hstd]
    simp only [canonicalA]
    ring
  · rintro ⟨A, hA, B, hB, D, hD, E, hE, hF⟩
    intro x hx
    have hd := (((hA x hx).neg.add ((hB x hx).const_mul (1 / 2))).add
      ((hD x hx).const_mul 3)).sub (hE x hx)
    have hd' : HasDerivAt
        (fun y => -A y + 1 / 2 * B y + 3 * D y - E y)
        (integrand x) x := by
      convert hd using 1
      rw [integrand_split x hx, expanded_split x hx]
    exact transfer_deriv hx hd' hF
theorem gap4 :
    AntiderivativesOn branch integrand =
      {F | ∃ E ∈ AntiderivativesOn branch residual,
        ∀ x ∈ branch,
          F x = -(x + 1) / 2 * Real.sqrt (q x) +
            2 * Real.arcsin ((x - 1) / Real.sqrt 2) - E x} := by
  exact standard_characterization
theorem gap5 :
    AntiderivativesOn branch integrand =
      {F | ∃ E ∈ AntiderivativesOn branch residual,
        ∀ x ∈ branch,
          F x = (1 - x) / 2 * Real.sqrt (q x) -
            Real.arcsin ((x - 1) / Real.sqrt 2) -
            Real.sqrt (q x) +
            3 * Real.arcsin ((x - 1) / Real.sqrt 2) - E x} := by
  rw [gap4]
  ext F
  constructor
  · rintro ⟨E, hE, hF⟩
    refine ⟨E, hE, ?_⟩
    intro x hx
    rw [hF x hx]
    ring
  · rintro ⟨E, hE, hF⟩
    refine ⟨E, hE, ?_⟩
    intro x hx
    rw [hF x hx]
    ring
theorem gap6 :
    AntiderivativesOn branch integrand =
      {F | ∃ E ∈ AntiderivativesOn branch residual,
        ∀ x ∈ branch, F x = standardReduction x - E x} := by
  simpa [standardReduction] using gap4
theorem gap7 :
    AntiderivativesOn branch residual =
      AntiderivativesOn branch residual := by
  rfl
theorem gap8 :
    AntiderivativesOn branch residual =
      PrimitiveFamilyOn branch residualPrimitive := by
  exact residual_family
theorem gap9 :
    AntiderivativesOn branch residual =
      PrimitiveFamilyOn branch residualPrimitive := by
  exact gap8
theorem gap10 :
    AntiderivativesOn branch integrand =
      PrimitiveFamilyOn branch finalPrimitive := by
  rw [gap6, gap8]
  ext F
  constructor
  · rintro ⟨E, ⟨C, hEC⟩, hF⟩
    refine ⟨-C, ?_⟩
    intro x hx
    rw [hF x hx, hEC x hx]
    dsimp [finalPrimitive, standardReduction, residualPrimitive]
    rw [show (1 - x) / Real.sqrt 2 =
      -((x - 1) / Real.sqrt 2) by ring]
    rw [Real.arcsin_neg]
    ring
  · rintro ⟨C, hFC⟩
    refine ⟨fun x => residualPrimitive x - C, ?_, ?_⟩
    · refine ⟨-C, ?_⟩
      intro x hx
      ring
    · intro x hx
      rw [hFC x hx]
      dsimp [finalPrimitive, standardReduction, residualPrimitive]
      rw [show (1 - x) / Real.sqrt 2 =
        -((x - 1) / Real.sqrt 2) by ring]
      rw [Real.arcsin_neg]
      ring

end
end ProofGap.Exercise1955
