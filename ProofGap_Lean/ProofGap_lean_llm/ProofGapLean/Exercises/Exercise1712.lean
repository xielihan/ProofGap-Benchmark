import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1712

noncomputable section

def branch : Set ℝ := Set.Ioi 0
def substitution (x : ℝ) := x - 1 / x
def integrand (x : ℝ) := (x ^ 2 + 1) / (x ^ 4 + 1)
def rewrittenIntegrand (x : ℝ) :=
  (1 + 1 / x ^ 2) / (x ^ 2 + 1 / x ^ 2)
def substitutedIntegrand (x : ℝ) :=
  deriv substitution x / ((substitution x) ^ 2 + 2)
def primitive (x : ℝ) :=
  1 / Real.sqrt 2 *
    Real.arctan ((x ^ 2 - 1) / (x * Real.sqrt 2))
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

theorem gap1 :
    AntiderivativesOn integrand =
      AntiderivativesOn rewrittenIntegrand := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (rewrittenIntegrand x) x
    intro x hx
    have hxpos : 0 < x := by simpa [branch] using hx
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    have hx2 : 0 < x ^ 2 := pow_pos hxpos 2
    have hden₁ : x ^ 4 + 1 ≠ 0 := by positivity
    have hden₂ : x ^ 2 + 1 / x ^ 2 ≠ 0 := by
      apply ne_of_gt
      exact add_pos hx2 (one_div_pos.mpr hx2)
    have heq : integrand x = rewrittenIntegrand x := by
      dsimp [integrand, rewrittenIntegrand]
      field_simp [hx0, hden₁, hden₂]
      <;> ring
    simpa only [heq] using hF x hx
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    intro x hx
    have hxpos : 0 < x := by simpa [branch] using hx
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    have hx2 : 0 < x ^ 2 := pow_pos hxpos 2
    have hden₁ : x ^ 4 + 1 ≠ 0 := by positivity
    have hden₂ : x ^ 2 + 1 / x ^ 2 ≠ 0 := by
      apply ne_of_gt
      exact add_pos hx2 (one_div_pos.mpr hx2)
    have heq : integrand x = rewrittenIntegrand x := by
      dsimp [integrand, rewrittenIntegrand]
      field_simp [hx0, hden₁, hden₂]
      <;> ring
    simpa only [← heq] using hF x hx
theorem gap2 :
    AntiderivativesOn rewrittenIntegrand =
      AntiderivativesOn substitutedIntegrand := by
  apply Set.ext
  intro F
  have heq : ∀ x ∈ branch, rewrittenIntegrand x = substitutedIntegrand x := by
    intro x hx
    have hxpos : 0 < x := by simpa [branch] using hx
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    have hx2 : 0 < x ^ 2 := pow_pos hxpos 2
    have hdsub : HasDerivAt substitution (1 + 1 / x ^ 2) x := by
      change HasDerivAt (fun y : ℝ => y - 1 / y) (1 + 1 / x ^ 2) x
      have h := (hasDerivAt_id x).sub
        ((hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx0)
      convert h using 1 <;> simp [id] <;>
        field_simp [hx0] <;> ring_nf
    have hden₁ : x ^ 2 + 1 / x ^ 2 ≠ 0 := by
      apply ne_of_gt
      exact add_pos hx2 (one_div_pos.mpr hx2)
    have hden₂ : (x - 1 / x) ^ 2 + 2 ≠ 0 := by positivity
    dsimp [rewrittenIntegrand, substitutedIntegrand, substitution]
    rw [hdsub.deriv]
    field_simp [hx0, hden₁, hden₂]
    <;> ring
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (substitutedIntegrand x) x
    intro x hx
    simpa only [← heq x hx] using hF x hx
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (rewrittenIntegrand x) x
    intro x hx
    simpa only [heq x hx] using hF x hx
theorem gap3 :
    AntiderivativesOn substitutedIntegrand = PrimitiveFamily primitive := by
  have hp : ∀ x ∈ branch, HasDerivAt primitive (substitutedIntegrand x) x := by
    intro x hx
    have hxpos : 0 < x := by simpa [branch] using hx
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    let s : ℝ := Real.sqrt 2
    have hspos : 0 < s := by
      dsimp [s]
      exact Real.sqrt_pos.2 (by norm_num)
    have hs0 : s ≠ 0 := ne_of_gt hspos
    have hsq : s ^ 2 = 2 := by
      dsimp [s]
      exact Real.sq_sqrt (by norm_num)
    have hdsub : HasDerivAt substitution (1 + 1 / x ^ 2) x := by
      change HasDerivAt (fun y : ℝ => y - 1 / y) (1 + 1 / x ^ 2) x
      have h := (hasDerivAt_id x).sub
        ((hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx0)
      convert h using 1 <;> simp [id] <;>
        field_simp [hx0] <;> ring_nf
    have hu :
        HasDerivAt (fun y : ℝ => (y ^ 2 - 1) / (y * s))
          ((1 + 1 / x ^ 2) / s) x := by
      have hnum := ((hasDerivAt_id x).pow 2).sub
        (hasDerivAt_const x (1 : ℝ))
      have hden := (hasDerivAt_id x).mul_const s
      have h := hnum.div hden (mul_ne_zero hx0 hs0)
      convert h using 1 <;> simp [id] <;>
        field_simp [hx0, hs0] <;> ring_nf
    have harctan :=
      (Real.hasDerivAt_arctan ((x ^ 2 - 1) / (x * s))).comp x hu
    have hscaled := harctan.const_mul (1 / s)
    have hden₁ :
        1 + ((x ^ 2 - 1) / (x * s)) ^ 2 ≠ 0 := by positivity
    have hden₂ : (x - 1 / x) ^ 2 + 2 ≠ 0 := by positivity
    have hcoef :
        1 / s *
            (1 / (1 + ((x ^ 2 - 1) / (x * s)) ^ 2) *
              ((1 + 1 / x ^ 2) / s)) =
          substitutedIntegrand x := by
      dsimp [substitutedIntegrand, substitution]
      rw [hdsub.deriv]
      field_simp [hx0, hs0, hden₁, hden₂]
      nlinarith [hsq]
    rw [← hcoef]
    simpa only [primitive, s] using hscaled
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (substitutedIntegrand x) x at hF
    change ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C
    let g : ℝ → ℝ := fun y => F y - primitive y
    have hgderiv : ∀ x ∈ branch, HasDerivAt g 0 x := by
      intro x hx
      dsimp [g]
      simpa using (hF x hx).sub (hp x hx)
    have hgdiff : DifferentiableOn ℝ g branch := by
      intro x hx
      exact (hgderiv x hx).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ branch, deriv g x = 0 := by
      intro x hx
      exact (hgderiv x hx).deriv
    have hopen : IsOpen branch := by
      simpa [branch] using (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))
    have hconv : Convex ℝ branch := by
      simpa [branch] using (convex_Ioi (0 : ℝ))
    have hpre : IsPreconnected branch := hconv.isPreconnected
    refine ⟨F 1 - primitive 1, ?_⟩
    intro x hx
    have hone : (1 : ℝ) ∈ branch := by norm_num [branch]
    have hg_eq : g x = g 1 :=
      hopen.is_const_of_deriv_eq_zero hpre hgdiff hzero hx hone
    dsimp [g] at hg_eq
    linarith
  · intro hF
    change ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C at hF
    change ∀ x ∈ branch, HasDerivAt F (substitutedIntegrand x) x
    obtain ⟨C, hC⟩ := hF
    intro x hx
    have hopen : IsOpen branch := by
      simpa [branch] using (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))
    have hbase :
        HasDerivAt (fun y => primitive y + C) (substitutedIntegrand x) x :=
      (hp x hx).add_const C
    have heq : F =ᶠ[nhds x] (fun y => primitive y + C) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    exact hbase.congr_of_eventuallyEq heq
theorem gap4 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  calc
    AntiderivativesOn integrand =
        AntiderivativesOn rewrittenIntegrand := gap1
    _ = AntiderivativesOn substitutedIntegrand := gap2
    _ = PrimitiveFamily primitive := gap3

end
end ProofGap.Exercise1712
