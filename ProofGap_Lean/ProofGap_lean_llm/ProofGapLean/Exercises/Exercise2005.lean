import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise2005

noncomputable section

def branch : Set ℝ := {x | Real.sin x ≠ 0}
def cot (x : ℝ) := Real.cos x / Real.sin x
def csc (x : ℝ) := 1 / Real.sin x
def originalIntegrand (x : ℝ) := cot x ^ 6
def rewrittenIntegrand (x : ℝ) :=
  cot x ^ 2 * (csc x ^ 2 - 1) ^ 2
def firstPart (x : ℝ) := cot x ^ 2 * csc x ^ 4
def secondPart (x : ℝ) := cot x ^ 2 * csc x ^ 2
def thirdPart (x : ℝ) := cot x ^ 2
def substitution₁ (x : ℝ) :=
  cot x ^ 2 * (1 + cot x ^ 2) * deriv cot x
def substitution₂ (x : ℝ) := cot x ^ 2 * deriv cot x
def residual (x : ℝ) := csc x ^ 2 - 1
def primitiveExpanded (x : ℝ) :=
  -1 / 3 * cot x ^ 3 - 1 / 5 * cot x ^ 5 +
    2 / 3 * cot x ^ 3 - cot x - x
def primitiveSimplified (x : ℝ) :=
  -1 / 5 * cot x ^ 5 + 1 / 3 * cot x ^ 3 - cot x - x
def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def ThreeTermFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives firstPart,
    ∃ H ∈ Antiderivatives secondPart,
    ∃ K ∈ Antiderivatives thirdPart,
      ∀ x ∈ branch, F x = G x - 2 * H x + K x}
def SubstitutionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives substitution₁,
    ∃ H ∈ Antiderivatives substitution₂,
    ∃ K ∈ Antiderivatives residual,
      ∀ x ∈ branch, F x = -G x + 2 * H x + K x}
def ComponentwisePrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ K : ℝ → ℝ,
    (∀ x ∈ branch, F x = p x + K x) ∧
    (∀ x ∈ branch, HasDerivAt K 0 x)}

private lemma branch_isOpen : IsOpen branch := by
  have hset : branch = Real.sin ⁻¹' ({0} : Set ℝ)ᶜ := by
    ext x
    simp [branch]
  rw [hset]
  exact isClosed_singleton.isOpen_compl.preimage Real.continuous_sin

private lemma csc_sq_eq (x : ℝ) (hx : x ∈ branch) :
    csc x ^ 2 = 1 + cot x ^ 2 := by
  change Real.sin x ≠ 0 at hx
  change (1 / Real.sin x) ^ 2 =
    1 + (Real.cos x / Real.sin x) ^ 2
  field_simp [hx]
  nlinarith [Real.sin_sq_add_cos_sq x]

private lemma cot_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt cot (-(1 + cot x ^ 2)) x := by
  change Real.sin x ≠ 0 at hx
  change HasDerivAt (fun y => Real.cos y / Real.sin y)
    (-(1 + (Real.cos x / Real.sin x) ^ 2)) x
  convert (Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hx using 1
  field_simp [hx]
  nlinarith [Real.sin_sq_add_cos_sq x]

private def cotPoly (a b c d : ℝ) (x : ℝ) :=
  a * cot x ^ 5 + b * cot x ^ 3 + c * cot x + d * x

private lemma cotPoly_hasDerivAt (a b c d x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (cotPoly a b c d)
      ((5 * a * cot x ^ 4 + 3 * b * cot x ^ 2 + c) *
        (-(1 + cot x ^ 2)) + d) x := by
  have hu := cot_hasDerivAt x hx
  unfold cotPoly
  convert (((((hu.pow 5).const_mul a).add
    ((hu.pow 3).const_mul b)).add (hu.const_mul c)).add
      ((hasDerivAt_id x).const_mul d)) using 1 <;> ring

private lemma original_eq_rewritten (x : ℝ) (hx : x ∈ branch) :
    originalIntegrand x = rewrittenIntegrand x := by
  unfold originalIntegrand rewrittenIntegrand
  rw [csc_sq_eq x hx]
  ring

private lemma rewritten_eq_three (x : ℝ) (_hx : x ∈ branch) :
    rewrittenIntegrand x =
      firstPart x - 2 * secondPart x + thirdPart x := by
  unfold rewrittenIntegrand firstPart secondPart thirdPart
  ring

private lemma original_eq_substitution (x : ℝ) (hx : x ∈ branch) :
    originalIntegrand x =
      -substitution₁ x + 2 * substitution₂ x + residual x := by
  unfold originalIntegrand substitution₁ substitution₂ residual
  rw [(cot_hasDerivAt x hx).deriv, csc_sq_eq x hx]
  ring

private lemma secondPrimitive_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (cotPoly 0 (-1 / 3) 0 0) (secondPart x) x := by
  convert cotPoly_hasDerivAt 0 (-1 / 3) 0 0 x hx using 1
  unfold secondPart
  rw [csc_sq_eq x hx]
  ring

private lemma thirdPrimitive_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (cotPoly 0 0 (-1) (-1)) (thirdPart x) x := by
  convert cotPoly_hasDerivAt 0 0 (-1) (-1) x hx using 1
  unfold thirdPart
  ring

private lemma substitution₁Primitive_hasDerivAt (x : ℝ)
    (hx : x ∈ branch) :
    HasDerivAt (cotPoly (1 / 5) (1 / 3) 0 0) (substitution₁ x) x := by
  convert cotPoly_hasDerivAt (1 / 5) (1 / 3) 0 0 x hx using 1
  unfold substitution₁
  rw [(cot_hasDerivAt x hx).deriv]
  ring

private lemma substitution₂Primitive_hasDerivAt (x : ℝ)
    (hx : x ∈ branch) :
    HasDerivAt (cotPoly 0 (1 / 3) 0 0) (substitution₂ x) x := by
  convert cotPoly_hasDerivAt 0 (1 / 3) 0 0 x hx using 1
  unfold substitution₂
  rw [(cot_hasDerivAt x hx).deriv]
  ring

private lemma residualPrimitive_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (cotPoly 0 0 (-1) (-1)) (residual x) x := by
  convert cotPoly_hasDerivAt 0 0 (-1) (-1) x hx using 1
  unfold residual
  rw [csc_sq_eq x hx]
  ring

private lemma primitiveExpanded_eq_simplified :
    primitiveExpanded = primitiveSimplified := by
  funext x
  unfold primitiveExpanded primitiveSimplified
  ring

private lemma primitiveSimplified_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitiveSimplified (originalIntegrand x) x := by
  have hp := cotPoly_hasDerivAt (-1 / 5) (1 / 3) (-1) (-1) x hx
  have hfun : cotPoly (-1 / 5) (1 / 3) (-1) (-1) =
      primitiveSimplified := by
    funext y
    unfold cotPoly primitiveSimplified
    ring
  rw [hfun] at hp
  convert hp using 1
  unfold originalIntegrand
  ring

private lemma hasDerivAt_congr_branch {F Q : ℝ → ℝ} {f' x : ℝ}
    (hx : x ∈ branch) (hEq : ∀ y ∈ branch, F y = Q y)
    (hQ : HasDerivAt Q f' x) : HasDerivAt F f' x := by
  have heq : F =ᶠ[nhds x] Q := by
    apply Filter.mem_of_superset (branch_isOpen.mem_nhds hx)
    intro y hy
    exact hEq y hy
  exact heq.hasDerivAt_iff.mpr hQ

private theorem antiderivatives_eq_componentwise (f p : ℝ → ℝ)
    (hp : ∀ x ∈ branch, HasDerivAt p (f x) x) :
    Antiderivatives f = ComponentwisePrimitiveFamily p := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (f x) x at hF
    change ∃ K : ℝ → ℝ,
      (∀ x ∈ branch, F x = p x + K x) ∧
      ∀ x ∈ branch, HasDerivAt K 0 x
    refine ⟨fun y => F y - p y, ?_, ?_⟩
    · intro x hx
      ring
    · intro x hx
      convert (hF x hx).sub (hp x hx) using 1 <;> ring
  · rintro ⟨K, hEq, hK⟩
    change ∀ x ∈ branch, HasDerivAt F (f x) x
    intro x hx
    have hsum := (hp x hx).add (hK x hx)
    have hRhs : HasDerivAt (fun y => p y + K y) (f x) x := by
      convert hsum using 1 <;> ring
    exact hasDerivAt_congr_branch (x := x) hx hEq hRhs

theorem gap1 :
    Antiderivatives originalIntegrand =
      Antiderivatives rewrittenIntegrand := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (originalIntegrand x) x at hF
    change ∀ x ∈ branch, HasDerivAt F (rewrittenIntegrand x) x
    intro x hx
    simpa only [original_eq_rewritten x hx] using hF x hx
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (rewrittenIntegrand x) x at hF
    change ∀ x ∈ branch, HasDerivAt F (originalIntegrand x) x
    intro x hx
    simpa only [original_eq_rewritten x hx] using hF x hx
theorem gap2 :
    Antiderivatives rewrittenIntegrand = ThreeTermFamily := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (rewrittenIntegrand x) x at hF
    change ∃ G ∈ Antiderivatives firstPart,
      ∃ H ∈ Antiderivatives secondPart,
      ∃ K ∈ Antiderivatives thirdPart,
        ∀ x ∈ branch, F x = G x - 2 * H x + K x
    let H := cotPoly 0 (-1 / 3) 0 0
    let K := cotPoly 0 0 (-1) (-1)
    let G := fun y => F y + 2 * H y - K y
    refine ⟨G, ?_, H, ?_, K, ?_, ?_⟩
    · intro x hx
      have hG := ((hF x hx).add
        ((secondPrimitive_hasDerivAt x hx).const_mul 2)).sub
          (thirdPrimitive_hasDerivAt x hx)
      have hcoef :
          rewrittenIntegrand x + 2 * secondPart x - thirdPart x =
            firstPart x := by
        rw [rewritten_eq_three x hx]
        ring
      simpa only [G, H, K, hcoef] using hG
    · intro x hx
      simpa only [H] using secondPrimitive_hasDerivAt x hx
    · intro x hx
      simpa only [K] using thirdPrimitive_hasDerivAt x hx
    · intro x hx
      simp only [G]
      ring
  · rintro ⟨G, hG, H, hH, K, hK, hEq⟩
    change ∀ x ∈ branch, HasDerivAt F (rewrittenIntegrand x) x
    intro x hx
    have hsum := ((hG x hx).sub ((hH x hx).const_mul 2)).add (hK x hx)
    have hcoef :
        firstPart x - 2 * secondPart x + thirdPart x =
          rewrittenIntegrand x := by
      rw [rewritten_eq_three x hx]
    have hRhs :
        HasDerivAt (fun y => G y - 2 * H y + K y)
          (rewrittenIntegrand x) x := by
      simpa only [hcoef] using hsum
    exact hasDerivAt_congr_branch (x := x) hx hEq hRhs
theorem gap3 :
    Antiderivatives originalIntegrand = ThreeTermFamily := by
  rw [gap1, gap2]
theorem gap4 :
    Antiderivatives originalIntegrand = SubstitutionFamily := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (originalIntegrand x) x at hF
    change ∃ G ∈ Antiderivatives substitution₁,
      ∃ H ∈ Antiderivatives substitution₂,
      ∃ K ∈ Antiderivatives residual,
        ∀ x ∈ branch, F x = -G x + 2 * H x + K x
    let H := cotPoly 0 (1 / 3) 0 0
    let K := cotPoly 0 0 (-1) (-1)
    let G := fun y => -F y + 2 * H y + K y
    refine ⟨G, ?_, H, ?_, K, ?_, ?_⟩
    · intro x hx
      have hG := ((hF x hx).neg.add
        ((substitution₂Primitive_hasDerivAt x hx).const_mul 2)).add
          (residualPrimitive_hasDerivAt x hx)
      have hcoef :
          -originalIntegrand x + 2 * substitution₂ x + residual x =
            substitution₁ x := by
        rw [original_eq_substitution x hx]
        ring
      simpa only [G, H, K, hcoef] using hG
    · intro x hx
      simpa only [H] using substitution₂Primitive_hasDerivAt x hx
    · intro x hx
      simpa only [K] using residualPrimitive_hasDerivAt x hx
    · intro x hx
      simp only [G]
      ring
  · rintro ⟨G, hG, H, hH, K, hK, hEq⟩
    change ∀ x ∈ branch, HasDerivAt F (originalIntegrand x) x
    intro x hx
    have hsum := ((hG x hx).neg.add ((hH x hx).const_mul 2)).add (hK x hx)
    have hcoef :
        -substitution₁ x + 2 * substitution₂ x + residual x =
          originalIntegrand x := by
      rw [original_eq_substitution x hx]
    have hRhs :
        HasDerivAt (fun y => -G y + 2 * H y + K y)
          (originalIntegrand x) x := by
      simpa only [hcoef] using hsum
    exact hasDerivAt_congr_branch (x := x) hx hEq hRhs
theorem gap5 :
    Antiderivatives originalIntegrand =
      ComponentwisePrimitiveFamily primitiveExpanded := by
  apply antiderivatives_eq_componentwise
  intro x hx
  rw [primitiveExpanded_eq_simplified]
  exact primitiveSimplified_hasDerivAt x hx
theorem gap6 :
    ComponentwisePrimitiveFamily primitiveExpanded =
      ComponentwisePrimitiveFamily primitiveSimplified := by
  rw [primitiveExpanded_eq_simplified]
theorem gap7 :
    Antiderivatives originalIntegrand =
      ComponentwisePrimitiveFamily primitiveSimplified := by
  rw [gap5, gap6]

end
end ProofGap.Exercise2005
