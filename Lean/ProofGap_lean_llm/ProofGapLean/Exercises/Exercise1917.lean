import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1917

noncomputable section

def branch : Set ℝ := Set.Ioi 0
def integrand (x : ℝ) := (x ^ 2 + 1) / (x ^ 4 + x ^ 2 + 1)
def rewrite₁ (x : ℝ) :=
  (x ^ 2 + 1) / ((x ^ 2 + 1) ^ 2 - x ^ 2)
def rewrite₂ (x : ℝ) :=
  (x ^ 2 + 1) / ((x ^ 2 - x + 1) * (x ^ 2 + x + 1))
def partialFraction (x : ℝ) :=
  (1 / 2 : ℝ) * (1 / (x ^ 2 - x + 1) + 1 / (x ^ 2 + x + 1))
def minusIntegrand (x : ℝ) := 1 / (x ^ 2 - x + 1)
def plusIntegrand (x : ℝ) := 1 / (x ^ 2 + x + 1)
def shiftedMinus (x : ℝ) :=
  1 / ((x - 1 / 2) ^ 2 + 3 / 4) *
    deriv (fun t : ℝ => t - 1 / 2) x
def shiftedPlus (x : ℝ) :=
  1 / ((x + 1 / 2) ^ 2 + 3 / 4) *
    deriv (fun t : ℝ => t + 1 / 2) x
def primitiveSum (x : ℝ) :=
  1 / Real.sqrt 3 * Real.arctan ((2 * x - 1) / Real.sqrt 3) +
    1 / Real.sqrt 3 * Real.arctan ((2 * x + 1) / Real.sqrt 3)
def primitiveCombined (x : ℝ) :=
  1 / Real.sqrt 3 *
    Real.arctan ((x ^ 2 - 1) / (x * Real.sqrt 3))
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def SplitFamily (f g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn f, ∃ H ∈ AntiderivativesOn g,
    ∀ x ∈ branch, F x = (1 / 2 : ℝ) * G x + (1 / 2 : ℝ) * H x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem half_components_eq_integrand (x : ℝ) :
    (1 / 2 : ℝ) * minusIntegrand x +
      (1 / 2 : ℝ) * plusIntegrand x = integrand x := by
  let A : ℝ := x ^ 2 - x + 1
  let B : ℝ := x ^ 2 + x + 1
  have hA : A ≠ 0 := by
    dsimp [A]
    nlinarith [sq_nonneg (x - 1 / 2)]
  have hB : B ≠ 0 := by
    dsimp [B]
    nlinarith [sq_nonneg (x + 1 / 2)]
  have hfactor : A * B = x ^ 4 + x ^ 2 + 1 := by
    dsimp [A, B]
    ring
  unfold minusIntegrand plusIntegrand integrand
  change (1 / 2 : ℝ) * (1 / A) + (1 / 2 : ℝ) * (1 / B) =
    (x ^ 2 + 1) / (x ^ 4 + x ^ 2 + 1)
  rw [← hfactor]
  field_simp [hA, hB] <;> ring

private def componentPrimitive (a x : ℝ) : ℝ :=
  2 / Real.sqrt 3 * Real.arctan ((2 * x + a) / Real.sqrt 3)

private theorem componentPrimitive_hasDerivAt (a x : ℝ) (ha : a ^ 2 = 1) :
    HasDerivAt (componentPrimitive a) (1 / (x ^ 2 + a * x + 1)) x := by
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt hspos
  have hsquare : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hq : 0 < x ^ 2 + a * x + 1 := by
    nlinarith [sq_nonneg (2 * x + a)]
  have hinner : HasDerivAt
      (fun t : ℝ => (2 * t + a) / Real.sqrt 3)
      (2 / Real.sqrt 3) x := by
    convert ((((hasDerivAt_id x).const_mul 2).add_const a).div_const
      (Real.sqrt 3)) using 1 <;> ring
  have hraw : HasDerivAt (componentPrimitive a)
      ((2 / Real.sqrt 3) *
        ((1 / (1 + ((2 * x + a) / Real.sqrt 3) ^ 2)) *
          (2 / Real.sqrt 3))) x := by
    simpa [componentPrimitive] using
      ((Real.hasDerivAt_arctan ((2 * x + a) / Real.sqrt 3)).comp x hinner).const_mul
        (2 / Real.sqrt 3)
  have harg :
      1 + ((2 * x + a) / Real.sqrt 3) ^ 2 =
        4 * (x ^ 2 + a * x + 1) / 3 := by
    field_simp [hs]
    nlinarith [hsquare, ha]
  have hcoef :
      (2 / Real.sqrt 3) *
          ((1 / (1 + ((2 * x + a) / Real.sqrt 3) ^ 2)) *
            (2 / Real.sqrt 3)) =
        1 / (x ^ 2 + a * x + 1) := by
    rw [harg]
    let q : ℝ := x ^ 2 + a * x + 1
    have hqne : q ≠ 0 := by
      dsimp [q]
      exact ne_of_gt hq
    change (2 / Real.sqrt 3) *
        ((1 / (4 * q / 3)) * (2 / Real.sqrt 3)) = 1 / q
    calc
      (2 / Real.sqrt 3) *
          ((1 / (4 * q / 3)) * (2 / Real.sqrt 3)) =
          (3 / q) / (Real.sqrt 3) ^ 2 := by
            field_simp [hs, hqne] <;> ring
      _ = 1 / q := by
        rw [hsquare]
        ring
  simpa only [hcoef] using hraw

private theorem primitiveSum_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitiveSum (integrand x) x := by
  have hm := (componentPrimitive_hasDerivAt (-1) x (by norm_num)).const_mul
    (1 / 2 : ℝ)
  have hp := (componentPrimitive_hasDerivAt 1 x (by norm_num)).const_mul
    (1 / 2 : ℝ)
  have hfun : primitiveSum =
      (fun y : ℝ => (1 / 2 : ℝ) * componentPrimitive (-1) y) +
        (fun y : ℝ => (1 / 2 : ℝ) * componentPrimitive 1 y) := by
    funext y
    unfold primitiveSum componentPrimitive
    simp only [Pi.add_apply, sub_eq_add_neg]
    ring
  have hcomponents : HasDerivAt primitiveSum
      ((1 / 2 : ℝ) * minusIntegrand x +
        (1 / 2 : ℝ) * plusIntegrand x) x := by
    rw [hfun]
    simpa [minusIntegrand, plusIntegrand] using hm.add hp
  simpa only [half_components_eq_integrand x] using hcomponents

private theorem antiderivatives_eq_primitiveSum :
    AntiderivativesOn integrand = PrimitiveFamily primitiveSum := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    let q : ℝ → ℝ := fun x => F x - primitiveSum x
    have hq : ∀ x ∈ branch, HasDerivAt q 0 x := by
      intro x hx
      dsimp [q]
      convert (hF x hx).sub (primitiveSum_hasDerivAt x hx) using 1
      ring
    have hdiff : DifferentiableOn ℝ q branch := by
      intro x hx
      exact (hq x hx).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ branch, deriv q x = 0 := by
      intro x hx
      exact (hq x hx).deriv
    have hopen : IsOpen branch := by
      simpa [branch] using (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))
    have hconvex : Convex ℝ branch := by
      simpa [branch] using (convex_Ioi (0 : ℝ))
    have hpre : IsPreconnected branch := hconvex.isPreconnected
    have hconst (x : ℝ) (hx : x ∈ branch) (y : ℝ) (hy : y ∈ branch) :
        q x = q y := by
      exact hopen.is_const_of_deriv_eq_zero hpre hdiff hzero hx hy
    have hone : (1 : ℝ) ∈ branch := by simp [branch]
    change ∃ C : ℝ, ∀ x ∈ branch, F x = primitiveSum x + C
    refine ⟨F 1 - primitiveSum 1, ?_⟩
    intro x hx
    have heq : q x = q 1 := hconst x hx 1 hone
    dsimp [q] at heq
    linarith
  · intro hF
    change ∃ C : ℝ, ∀ x ∈ branch, F x = primitiveSum x + C at hF
    rcases hF with ⟨C, hEq⟩
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    intro x hx
    have hopen : IsOpen branch := by
      simpa [branch] using (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))
    have hevent : Filter.EventuallyEq (nhds x) F
        (fun y => primitiveSum y + C) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hEq y hy
    exact (hevent.hasDerivAt_iff).2
      ((primitiveSum_hasDerivAt x hx).add_const C)

private theorem primitiveCombined_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitiveCombined (integrand x) x := by
  have hxpos : 0 < x := hx
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt hspos
  have hsquare : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hn : HasDerivAt (fun t : ℝ => t ^ 2 - 1) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).sub_const 1 using 1 <;>
      simp [id_eq] <;> ring
  have hd : HasDerivAt (fun t : ℝ => t * Real.sqrt 3) (Real.sqrt 3) x := by
    convert (hasDerivAt_id x).mul_const (Real.sqrt 3) using 1 <;>
      simp [id_eq] <;> ring
  have hinner : HasDerivAt
      (fun t : ℝ => (t ^ 2 - 1) / (t * Real.sqrt 3))
      ((x ^ 2 + 1) / (x ^ 2 * Real.sqrt 3)) x := by
    convert hn.div hd (mul_ne_zero hxne hs) using 1
    field_simp [hxne, hs]
    <;> ring
  have hraw : HasDerivAt primitiveCombined
      ((1 / Real.sqrt 3) *
        ((1 / (1 + ((x ^ 2 - 1) / (x * Real.sqrt 3)) ^ 2)) *
          ((x ^ 2 + 1) / (x ^ 2 * Real.sqrt 3)))) x := by
    change HasDerivAt
      (fun y : ℝ => 1 / Real.sqrt 3 *
        Real.arctan ((y ^ 2 - 1) / (y * Real.sqrt 3)))
      ((1 / Real.sqrt 3) *
        ((1 / (1 + ((x ^ 2 - 1) / (x * Real.sqrt 3)) ^ 2)) *
          ((x ^ 2 + 1) / (x ^ 2 * Real.sqrt 3)))) x
    simpa only using
      ((Real.hasDerivAt_arctan
        ((x ^ 2 - 1) / (x * Real.sqrt 3))).comp x hinner).const_mul
          (1 / Real.sqrt 3)
  have hpoly : x ^ 4 + x ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg (x ^ 2)]
  have harc : 1 + ((x ^ 2 - 1) / (x * Real.sqrt 3)) ^ 2 ≠ 0 := by
    positivity
  have hcoef :
      (1 / Real.sqrt 3) *
          ((1 / (1 + ((x ^ 2 - 1) / (x * Real.sqrt 3)) ^ 2)) *
            ((x ^ 2 + 1) / (x ^ 2 * Real.sqrt 3))) = integrand x := by
    unfold integrand
    field_simp [hxne, hs, hpoly, harc]
    nlinarith [hsquare]
  simpa only [hcoef] using hraw

theorem gap1 (x : ℝ) (hx : x ∈ branch) :
    integrand x = rewrite₁ x := by
  unfold integrand rewrite₁
  congr 1
  ring
theorem gap2 (x : ℝ) (hx : x ∈ branch) :
    rewrite₁ x = rewrite₂ x := by
  unfold rewrite₁ rewrite₂
  congr 1
  ring
theorem gap3 (x : ℝ) (hx : x ∈ branch) :
    rewrite₂ x = partialFraction x := by
  unfold rewrite₂
  rw [show (x ^ 2 - x + 1) * (x ^ 2 + x + 1) =
      x ^ 4 + x ^ 2 + 1 by ring]
  change integrand x = partialFraction x
  simpa only [partialFraction, minusIntegrand, plusIntegrand, mul_add] using
    (half_components_eq_integrand x).symm
theorem gap4 (x : ℝ) (hx : x ∈ branch) :
    integrand x = partialFraction x := by
  calc
    integrand x = rewrite₁ x := gap1 x hx
    _ = rewrite₂ x := gap2 x hx
    _ = partialFraction x := gap3 x hx
theorem gap5 :
    AntiderivativesOn integrand = SplitFamily minusIntegrand plusIntegrand := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    let H : ℝ → ℝ := componentPrimitive 1
    let G : ℝ → ℝ := fun x => 2 * F x - H x
    change ∃ G ∈ AntiderivativesOn minusIntegrand,
      ∃ H ∈ AntiderivativesOn plusIntegrand,
        ∀ x ∈ branch, F x = (1 / 2 : ℝ) * G x + (1 / 2 : ℝ) * H x
    refine ⟨G, ?_, H, ?_, ?_⟩
    · change ∀ x ∈ branch, HasDerivAt G (minusIntegrand x) x
      intro x hx
      have hd := ((hF x hx).const_mul 2).sub
        (componentPrimitive_hasDerivAt 1 x (by norm_num))
      have hd' : HasDerivAt
          ((fun y => 2 * F y) - componentPrimitive 1)
          (2 * integrand x - plusIntegrand x) x := by
        simpa [plusIntegrand] using hd
      have hval : 2 * integrand x - plusIntegrand x = minusIntegrand x := by
        linarith [half_components_eq_integrand x]
      rw [hval] at hd'
      change HasDerivAt
        (fun y => 2 * F y - componentPrimitive 1 y)
        (minusIntegrand x) x at hd'
      change HasDerivAt
        (fun y => 2 * F y - componentPrimitive 1 y)
        (minusIntegrand x) x
      exact hd'
    · change ∀ x ∈ branch, HasDerivAt H (plusIntegrand x) x
      intro x hx
      simpa [H, plusIntegrand] using
        (componentPrimitive_hasDerivAt 1 x (by norm_num))
    · intro x hx
      dsimp [G, H]
      ring
  · intro hF
    change ∃ G ∈ AntiderivativesOn minusIntegrand,
      ∃ H ∈ AntiderivativesOn plusIntegrand,
        ∀ x ∈ branch, F x = (1 / 2 : ℝ) * G x + (1 / 2 : ℝ) * H x at hF
    rcases hF with ⟨G, hG, H, hH, hEq⟩
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    change ∀ x ∈ branch, HasDerivAt G (minusIntegrand x) x at hG
    change ∀ x ∈ branch, HasDerivAt H (plusIntegrand x) x at hH
    intro x hx
    have hd : HasDerivAt
        (fun y => (1 / 2 : ℝ) * G y + (1 / 2 : ℝ) * H y)
        (integrand x) x := by
      convert ((hG x hx).const_mul (1 / 2 : ℝ)).add
        ((hH x hx).const_mul (1 / 2 : ℝ)) using 1
      exact (half_components_eq_integrand x).symm
    have hopen : IsOpen branch := by
      simpa [branch] using (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))
    have hevent : Filter.EventuallyEq (nhds x) F
        (fun y => (1 / 2 : ℝ) * G y + (1 / 2 : ℝ) * H y) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hEq y hy
    exact (hevent.hasDerivAt_iff).2 hd
theorem gap6 :
    AntiderivativesOn integrand = SplitFamily shiftedMinus shiftedPlus := by
  have hm : shiftedMinus = minusIntegrand := by
    funext x
    have hd : deriv (fun t : ℝ => t - 1 / 2) x = 1 :=
      (((hasDerivAt_id x).sub_const (1 / 2 : ℝ)).deriv)
    unfold shiftedMinus minusIntegrand
    rw [hd, mul_one]
    congr 1
    ring
  have hp : shiftedPlus = plusIntegrand := by
    funext x
    have hd : deriv (fun t : ℝ => t + 1 / 2) x = 1 :=
      (((hasDerivAt_id x).add_const (1 / 2 : ℝ)).deriv)
    unfold shiftedPlus plusIntegrand
    rw [hd, mul_one]
    congr 1
    ring
  rw [hm, hp]
  exact gap5
theorem gap7 :
    AntiderivativesOn integrand = PrimitiveFamily primitiveSum := by
  exact antiderivatives_eq_primitiveSum
theorem gap8 :
    PrimitiveFamily primitiveSum = PrimitiveFamily primitiveCombined := by
  have hpc : primitiveCombined ∈ AntiderivativesOn integrand := by
    change ∀ x ∈ branch, HasDerivAt primitiveCombined (integrand x) x
    intro x hx
    exact primitiveCombined_hasDerivAt x hx
  rw [antiderivatives_eq_primitiveSum] at hpc
  rcases hpc with ⟨C, hC⟩
  ext F
  constructor
  · intro hF
    change ∃ D : ℝ, ∀ x ∈ branch, F x = primitiveSum x + D at hF
    change ∃ D : ℝ, ∀ x ∈ branch, F x = primitiveCombined x + D
    rcases hF with ⟨D, hD⟩
    refine ⟨D - C, ?_⟩
    intro x hx
    linarith [hD x hx, hC x hx]
  · intro hF
    change ∃ D : ℝ, ∀ x ∈ branch, F x = primitiveCombined x + D at hF
    change ∃ D : ℝ, ∀ x ∈ branch, F x = primitiveSum x + D
    rcases hF with ⟨D, hD⟩
    refine ⟨C + D, ?_⟩
    intro x hx
    linarith [hD x hx, hC x hx]
theorem gap9 :
    AntiderivativesOn integrand = PrimitiveFamily primitiveCombined := by
  calc
    AntiderivativesOn integrand = PrimitiveFamily primitiveSum := gap7
    _ = PrimitiveFamily primitiveCombined := gap8

end
end ProofGap.Exercise1917
