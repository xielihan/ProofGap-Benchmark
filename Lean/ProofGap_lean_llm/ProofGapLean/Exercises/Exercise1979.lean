import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1979

noncomputable section

def branch : Set ℝ := {x | x ≠ 0}
def negativeBranch : Set ℝ := Set.Iio 0
def positiveBranch : Set ℝ := Set.Ioi 0
def radicand (x : ℝ) := x ^ 4 + x ^ 2 + 1
def originalIntegrand (x : ℝ) :=
  (x ^ 2 + 1) / (x * Real.sqrt (radicand x))
def firstPart (x : ℝ) := x / Real.sqrt (radicand x)
def secondPart (x : ℝ) := 1 / (x * Real.sqrt (radicand x))
def firstSubstituted (x : ℝ) :=
  deriv (fun y : ℝ => y ^ 2 + 1 / 2) x /
    Real.sqrt ((x ^ 2 + 1 / 2) ^ 2 + 3 / 4)
def secondSubstituted (x : ℝ) :=
  deriv (fun y : ℝ => 1 / y ^ 2) x /
    Real.sqrt ((1 / x ^ 2 + 1 / 2) ^ 2 + 3 / 4)
def primitive₁ (x : ℝ) :=
  1 / 2 *
    Real.log
      ((x ^ 2 + 1 / 2 + Real.sqrt (radicand x)) /
        (1 / x ^ 2 + 1 / 2 + Real.sqrt (radicand x / x ^ 4)))
def primitive₂ (x : ℝ) :=
  1 / 2 *
    Real.log
      (x ^ 2 * (1 + 2 * x ^ 2 + 2 * Real.sqrt (radicand x)) /
        (2 + x ^ 2 + 2 * Real.sqrt (radicand x)))
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def SplitFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn firstPart,
    ∃ H ∈ AntiderivativesOn secondPart,
      ∀ x ∈ branch, F x = G x + H x}
def SubstitutedSplitFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn firstSubstituted,
    ∃ H ∈ AntiderivativesOn secondSubstituted,
      ∀ x ∈ branch, F x = 1 / 2 * G x - 1 / 2 * H x}
def BranchwisePrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ Cneg Cpos : ℝ,
    (∀ x ∈ negativeBranch, F x = p x + Cneg) ∧
    (∀ x ∈ positiveBranch, F x = p x + Cpos)}

private def exercise1979Q₁ (x : ℝ) :=
  Real.log ((x ^ 2 + 1 / 2) +
    Real.sqrt ((x ^ 2 + 1 / 2) ^ 2 + 3 / 4))

private def exercise1979Q₂ (x : ℝ) :=
  Real.log ((1 / x ^ 2 + 1 / 2) +
    Real.sqrt ((1 / x ^ 2 + 1 / 2) ^ 2 + 3 / 4))

private theorem exercise1979BranchMemNhds {x : ℝ} (hx : x ∈ branch) :
    branch ∈ nhds x := by
  have hbranch : branch = (({0} : Set ℝ)ᶜ) := by
    ext y
    simp [branch]
  rw [hbranch] at hx ⊢
  exact isOpen_compl_singleton.mem_nhds hx

private theorem exercise1979LogSqrtDerivative
    {u : ℝ → ℝ} {x du : ℝ} (hu : HasDerivAt u du x) :
    HasDerivAt
      (fun y => Real.log (u y + Real.sqrt ((u y) ^ 2 + 3 / 4)))
      (du / Real.sqrt ((u x) ^ 2 + 3 / 4)) x := by
  have hinner : 0 < (u x) ^ 2 + (3 / 4 : ℝ) := by
    nlinarith [sq_nonneg (u x)]
  have hspos : 0 < Real.sqrt ((u x) ^ 2 + 3 / 4) :=
    Real.sqrt_pos.2 hinner
  have hssq :
      (Real.sqrt ((u x) ^ 2 + 3 / 4)) ^ 2 = (u x) ^ 2 + 3 / 4 :=
    Real.sq_sqrt hinner.le
  have hsumpos :
      0 < u x + Real.sqrt ((u x) ^ 2 + 3 / 4) := by
    nlinarith
  have hsqrtRaw :=
    (Real.hasDerivAt_sqrt hinner.ne').comp x
      ((hu.pow 2).add_const (3 / 4 : ℝ))
  have hsqrt :
      HasDerivAt (fun y => Real.sqrt ((u y) ^ 2 + 3 / 4))
        (u x * du / Real.sqrt ((u x) ^ 2 + 3 / 4)) x := by
    convert hsqrtRaw using 1 <;>
      field_simp [hspos.ne'] <;> ring
  have hlog :=
    (Real.hasDerivAt_log hsumpos.ne').comp x (hu.add hsqrt)
  have hcancel :
      (du + u x * du / Real.sqrt ((u x) ^ 2 + 3 / 4)) *
          Real.sqrt ((u x) ^ 2 + 3 / 4) =
        du * (u x + Real.sqrt ((u x) ^ 2 + 3 / 4)) := by
    field_simp [hspos.ne'] <;> ring
  have hcoeff :
      (u x + Real.sqrt ((u x) ^ 2 + 3 / 4))⁻¹ *
          (du + u x * du / Real.sqrt ((u x) ^ 2 + 3 / 4)) =
        du / Real.sqrt ((u x) ^ 2 + 3 / 4) := by
    apply (eq_div_iff hspos.ne').2
    calc
      (u x + Real.sqrt ((u x) ^ 2 + 3 / 4))⁻¹ *
            (du + u x * du / Real.sqrt ((u x) ^ 2 + 3 / 4)) *
            Real.sqrt ((u x) ^ 2 + 3 / 4) =
          (u x + Real.sqrt ((u x) ^ 2 + 3 / 4))⁻¹ *
            ((du + u x * du / Real.sqrt ((u x) ^ 2 + 3 / 4)) *
              Real.sqrt ((u x) ^ 2 + 3 / 4)) := by ring
      _ = (u x + Real.sqrt ((u x) ^ 2 + 3 / 4))⁻¹ *
            (du * (u x + Real.sqrt ((u x) ^ 2 + 3 / 4))) := by
          rw [hcancel]
      _ = du * ((u x + Real.sqrt ((u x) ^ 2 + 3 / 4))⁻¹ *
            (u x + Real.sqrt ((u x) ^ 2 + 3 / 4))) := by ring
      _ = du := by simp [hsumpos.ne']
  convert hlog using 1
  exact hcoeff.symm

private theorem exercise1979SquareDeriv (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
  convert (hasDerivAt_id x).pow 2 using 1 <;>
    simp [id, pow_two] <;> ring

private theorem exercise1979ReciprocalSquareDeriv
    (x : ℝ) (hx0 : x ≠ 0) :
    HasDerivAt (fun y : ℝ => 1 / y ^ 2) (-2 / x ^ 3) x := by
  have hdiv := (hasDerivAt_const x (1 : ℝ)).div
    (exercise1979SquareDeriv x) (pow_ne_zero 2 hx0)
  convert hdiv using 1 <;>
    simp [id] <;> field_simp [hx0] <;> ring

private theorem exercise1979Q₁Deriv (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt exercise1979Q₁ (firstSubstituted x) x := by
  have hu : HasDerivAt (fun y : ℝ => y ^ 2 + 1 / 2)
      (2 * x) x := by
    convert (exercise1979SquareDeriv x).add_const (1 / 2 : ℝ) using 1 <;> ring
  have h := exercise1979LogSqrtDerivative hu
  change HasDerivAt
    (fun y : ℝ => Real.log ((y ^ 2 + 1 / 2) +
      Real.sqrt ((y ^ 2 + 1 / 2) ^ 2 + 3 / 4)))
    (firstSubstituted x) x
  unfold firstSubstituted
  rw [hu.deriv]
  exact h

private theorem exercise1979Q₂Deriv (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt exercise1979Q₂ (secondSubstituted x) x := by
  have hx0 : x ≠ 0 := by simpa [branch] using hx
  have hu₀ := exercise1979ReciprocalSquareDeriv x hx0
  have hu : HasDerivAt (fun y : ℝ => 1 / y ^ 2 + 1 / 2)
      (-2 / x ^ 3) x := by
    convert hu₀.add_const (1 / 2 : ℝ) using 1 <;> ring
  have h := exercise1979LogSqrtDerivative hu
  change HasDerivAt
    (fun y : ℝ => Real.log ((1 / y ^ 2 + 1 / 2) +
      Real.sqrt ((1 / y ^ 2 + 1 / 2) ^ 2 + 3 / 4)))
    (secondSubstituted x) x
  unfold secondSubstituted
  rw [hu₀.deriv]
  exact h

private theorem exercise1979SqrtFirst (x : ℝ) :
    Real.sqrt ((x ^ 2 + 1 / 2) ^ 2 + 3 / 4) =
      Real.sqrt (radicand x) := by
  congr 1
  unfold radicand
  ring

private theorem exercise1979RadicandSecond (x : ℝ) (hx : x ∈ branch) :
    radicand x / x ^ 4 =
      (1 / x ^ 2 + 1 / 2) ^ 2 + 3 / 4 := by
  have hx0 : x ≠ 0 := by simpa [branch] using hx
  unfold radicand
  field_simp [hx0] <;> ring

private theorem exercise1979SqrtSecond (x : ℝ) (hx : x ∈ branch) :
    Real.sqrt ((1 / x ^ 2 + 1 / 2) ^ 2 + 3 / 4) =
      Real.sqrt (radicand x) / x ^ 2 := by
  have hx0 : x ≠ 0 := by simpa [branch] using hx
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx0
  have hr : 0 ≤ radicand x := by
    unfold radicand
    positivity
  have hA : 0 ≤ (1 / x ^ 2 + 1 / 2) ^ 2 + (3 / 4 : ℝ) := by
    positivity
  have hs : 0 ≤ Real.sqrt (radicand x) / x ^ 2 :=
    div_nonneg (Real.sqrt_nonneg _) hx2.le
  have hsq :
      (Real.sqrt ((1 / x ^ 2 + 1 / 2) ^ 2 + 3 / 4)) ^ 2 =
        (Real.sqrt (radicand x) / x ^ 2) ^ 2 := by
    rw [Real.sq_sqrt hA]
    field_simp [hx0]
    rw [Real.sq_sqrt hr]
    unfold radicand
    ring
  nlinarith [Real.sqrt_nonneg ((1 / x ^ 2 + 1 / 2) ^ 2 + 3 / 4)]

private theorem exercise1979Parts (x : ℝ) (hx : x ∈ branch) :
    firstPart x + secondPart x = originalIntegrand x := by
  have hx0 : x ≠ 0 := by simpa [branch] using hx
  have hrpos : 0 < radicand x := by
    unfold radicand
    positivity
  have hs : Real.sqrt (radicand x) ≠ 0 :=
    (Real.sqrt_pos.2 hrpos).ne'
  unfold firstPart secondPart originalIntegrand
  field_simp [hx0, hs] <;> ring

private theorem exercise1979OriginalSubFirst (x : ℝ) (hx : x ∈ branch) :
    originalIntegrand x - firstPart x = secondPart x := by
  rw [← exercise1979Parts x hx]
  ring

private theorem exercise1979Q₁Half (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y => (1 / 2 : ℝ) * exercise1979Q₁ y)
      (firstPart x) x := by
  have h := (exercise1979Q₁Deriv x hx).const_mul (1 / 2 : ℝ)
  have hu : HasDerivAt (fun y : ℝ => y ^ 2 + 1 / 2)
      (2 * x) x := by
    convert (exercise1979SquareDeriv x).add_const (1 / 2 : ℝ) using 1 <;> ring
  convert h using 1
  unfold firstSubstituted firstPart
  rw [hu.deriv, exercise1979SqrtFirst]
  ring

private theorem exercise1979Combination (x : ℝ) (hx : x ∈ branch) :
    (1 / 2 : ℝ) * firstSubstituted x -
        (1 / 2 : ℝ) * secondSubstituted x = originalIntegrand x := by
  have hx0 : x ≠ 0 := by simpa [branch] using hx
  have hu : HasDerivAt (fun y : ℝ => y ^ 2 + 1 / 2)
      (2 * x) x := by
    convert (exercise1979SquareDeriv x).add_const (1 / 2 : ℝ) using 1 <;> ring
  have hv := exercise1979ReciprocalSquareDeriv x hx0
  unfold firstSubstituted secondSubstituted originalIntegrand
  rw [hu.deriv, hv.deriv, exercise1979SqrtFirst,
    exercise1979SqrtSecond x hx]
  have hrpos : 0 < radicand x := by
    unfold radicand
    positivity
  have hs : Real.sqrt (radicand x) ≠ 0 :=
    (Real.sqrt_pos.2 hrpos).ne'
  field_simp [hx0, hs] <;> ring

private theorem exercise1979PrimitiveAsCombination
    (x : ℝ) (hx : x ∈ branch) :
    primitive₁ x = (1 / 2 : ℝ) * exercise1979Q₁ x -
      (1 / 2 : ℝ) * exercise1979Q₂ x := by
  have hx0 : x ≠ 0 := by simpa [branch] using hx
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx0
  have hA : 0 < x ^ 2 + 1 / 2 + Real.sqrt (radicand x) := by
    positivity
  have hB : 0 < 1 / x ^ 2 + 1 / 2 +
      Real.sqrt (radicand x) / x ^ 2 := by
    positivity
  unfold primitive₁ exercise1979Q₁ exercise1979Q₂
  rw [exercise1979SqrtFirst, exercise1979RadicandSecond x hx,
    exercise1979SqrtSecond x hx]
  rw [Real.log_div hA.ne' hB.ne']
  ring

private theorem exercise1979PrimitiveDeriv (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive₁ (originalIntegrand x) x := by
  have hcomb := ((exercise1979Q₁Deriv x hx).const_mul (1 / 2 : ℝ)).sub
    ((exercise1979Q₂Deriv x hx).const_mul (1 / 2 : ℝ))
  have heq :
      primitive₁ =ᶠ[nhds x]
        ((fun y => (1 / 2 : ℝ) * exercise1979Q₁ y) -
          fun y => (1 / 2 : ℝ) * exercise1979Q₂ y) := by
    filter_upwards [exercise1979BranchMemNhds hx] with y hy
    exact exercise1979PrimitiveAsCombination y hy
  have h := hcomb.congr_of_eventuallyEq heq
  convert h using 1
  exact (exercise1979Combination x hx).symm

private theorem exercise1979AntiderivativesBranchwise :
    AntiderivativesOn originalIntegrand =
      BranchwisePrimitiveFamily primitive₁ := by
  ext F
  constructor
  · intro hF
    have hdneg : DifferentiableOn ℝ (fun x => F x - primitive₁ x) negativeBranch := by
      intro x hx
      have hxb : x ∈ branch := by
        show x ≠ 0
        exact ne_of_lt hx
      exact ((hF x hxb).sub
        (exercise1979PrimitiveDeriv x hxb)).differentiableAt.differentiableWithinAt
    have hzneg : ∀ x ∈ negativeBranch,
        deriv (fun y => F y - primitive₁ y) x = 0 := by
      intro x hx
      have hxb : x ∈ branch := by
        show x ≠ 0
        exact ne_of_lt hx
      simpa using ((hF x hxb).sub
        (exercise1979PrimitiveDeriv x hxb)).deriv
    have hpreNeg : IsPreconnected negativeBranch := by
      simpa [negativeBranch] using
        (isPreconnected_Iio : IsPreconnected (Set.Iio (0 : ℝ)))
    have hdpos : DifferentiableOn ℝ (fun x => F x - primitive₁ x) positiveBranch := by
      intro x hx
      have hxb : x ∈ branch := by
        show x ≠ 0
        exact ne_of_gt hx
      exact ((hF x hxb).sub
        (exercise1979PrimitiveDeriv x hxb)).differentiableAt.differentiableWithinAt
    have hzpos : ∀ x ∈ positiveBranch,
        deriv (fun y => F y - primitive₁ y) x = 0 := by
      intro x hx
      have hxb : x ∈ branch := by
        show x ≠ 0
        exact ne_of_gt hx
      simpa using ((hF x hxb).sub
        (exercise1979PrimitiveDeriv x hxb)).deriv
    have hprePos : IsPreconnected positiveBranch := by
      simpa [positiveBranch] using
        (isPreconnected_Ioi : IsPreconnected (Set.Ioi (0 : ℝ)))
    have hm : (-1 : ℝ) ∈ negativeBranch := by norm_num [negativeBranch]
    have hp : (1 : ℝ) ∈ positiveBranch := by norm_num [positiveBranch]
    refine ⟨F (-1) - primitive₁ (-1), F 1 - primitive₁ 1, ?_, ?_⟩
    · intro x hx
      have hEq :=
        isOpen_Iio.is_const_of_deriv_eq_zero hpreNeg hdneg hzneg hx hm
      linarith
    · intro x hx
      have hEq :=
        isOpen_Ioi.is_const_of_deriv_eq_zero hprePos hdpos hzpos hx hp
      linarith
  · rintro ⟨Cneg, Cpos, hneg, hpos⟩
    intro x hx
    have hx0 : x ≠ 0 := by simpa [branch] using hx
    rcases lt_or_gt_of_ne hx0 with hxn | hxp
    · have heq : F =ᶠ[nhds x] fun y => primitive₁ y + Cneg := by
        filter_upwards [isOpen_Iio.mem_nhds hxn] with y hy
        exact hneg y hy
      exact ((exercise1979PrimitiveDeriv x hx).add_const Cneg).congr_of_eventuallyEq heq
    · have heq : F =ᶠ[nhds x] fun y => primitive₁ y + Cpos := by
        filter_upwards [isOpen_Ioi.mem_nhds hxp] with y hy
        exact hpos y hy
      exact ((exercise1979PrimitiveDeriv x hx).add_const Cpos).congr_of_eventuallyEq heq

private theorem exercise1979PrimitiveEq (x : ℝ) (hx : x ∈ branch) :
    primitive₁ x = primitive₂ x := by
  have hx0 : x ≠ 0 := by simpa [branch] using hx
  unfold primitive₁ primitive₂
  rw [exercise1979RadicandSecond x hx, exercise1979SqrtSecond x hx]
  congr 2
  field_simp [hx0] <;> ring

theorem gap1 :
    AntiderivativesOn originalIntegrand = SplitFamily := by
  ext F
  constructor
  · intro hF
    let G : ℝ → ℝ := fun x => (1 / 2 : ℝ) * exercise1979Q₁ x
    let H : ℝ → ℝ := fun x => F x - G x
    refine ⟨G, ?_, H, ?_, ?_⟩
    · intro x hx
      exact exercise1979Q₁Half x hx
    · intro x hx
      have h := (hF x hx).sub (exercise1979Q₁Half x hx)
      convert h using 1
      exact (exercise1979OriginalSubFirst x hx).symm
    · intro x hx
      simp [H]
  · rintro ⟨G, hG, H, hH, hF⟩
    intro x hx
    have hsum := (hG x hx).add (hH x hx)
    have heq : F =ᶠ[nhds x] G + H := by
      filter_upwards [exercise1979BranchMemNhds hx] with y hy
      exact hF y hy
    have h := hsum.congr_of_eventuallyEq heq
    convert h using 1
    exact (exercise1979Parts x hx).symm
theorem gap2 :
    AntiderivativesOn originalIntegrand = SubstitutedSplitFamily := by
  ext F
  constructor
  · intro hF
    let G : ℝ → ℝ := exercise1979Q₁
    let H : ℝ → ℝ := fun x => G x - 2 * F x
    refine ⟨G, exercise1979Q₁Deriv, H, ?_, ?_⟩
    · intro x hx
      have h := (exercise1979Q₁Deriv x hx).sub
        ((hF x hx).const_mul 2)
      convert h using 1
      linarith [exercise1979Combination x hx]
    · intro x hx
      simp [H]
      ring
  · rintro ⟨G, hG, H, hH, hF⟩
    intro x hx
    have hcomb := ((hG x hx).const_mul (1 / 2 : ℝ)).sub
      ((hH x hx).const_mul (1 / 2 : ℝ))
    have heq :
        F =ᶠ[nhds x]
          ((fun y => (1 / 2 : ℝ) * G y) -
            fun y => (1 / 2 : ℝ) * H y) := by
      filter_upwards [exercise1979BranchMemNhds hx] with y hy
      exact hF y hy
    have h := hcomb.congr_of_eventuallyEq heq
    convert h using 1
    exact (exercise1979Combination x hx).symm
theorem gap3 :
    SubstitutedSplitFamily =
      BranchwisePrimitiveFamily primitive₁ := by
  rw [← gap2]
  exact exercise1979AntiderivativesBranchwise
theorem gap4 :
    AntiderivativesOn originalIntegrand =
      BranchwisePrimitiveFamily primitive₁ := by
  exact gap2.trans gap3
theorem gap5 :
    AntiderivativesOn originalIntegrand =
      BranchwisePrimitiveFamily primitive₂ := by
  rw [gap4]
  ext F
  constructor
  · rintro ⟨Cneg, Cpos, hneg, hpos⟩
    refine ⟨Cneg, Cpos, ?_, ?_⟩
    · intro x hx
      have hxb : x ∈ branch := by
        show x ≠ 0
        exact ne_of_lt hx
      rw [hneg x hx, exercise1979PrimitiveEq x hxb]
    · intro x hx
      have hxb : x ∈ branch := by
        show x ≠ 0
        exact ne_of_gt hx
      rw [hpos x hx, exercise1979PrimitiveEq x hxb]
  · rintro ⟨Cneg, Cpos, hneg, hpos⟩
    refine ⟨Cneg, Cpos, ?_, ?_⟩
    · intro x hx
      have hxb : x ∈ branch := by
        show x ≠ 0
        exact ne_of_lt hx
      rw [hneg x hx, exercise1979PrimitiveEq x hxb]
    · intro x hx
      have hxb : x ∈ branch := by
        show x ≠ 0
        exact ne_of_gt hx
      rw [hpos x hx, exercise1979PrimitiveEq x hxb]

end
end ProofGap.Exercise1979
