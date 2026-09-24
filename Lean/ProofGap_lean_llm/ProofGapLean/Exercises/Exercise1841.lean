import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1841

noncomputable section

def branch : Set ℝ := Set.univ
def denominator (α x : ℝ) := x ^ 2 - 2 * x * Real.cos α + 1
def integrand (α x : ℝ) := x / denominator α x
def rewrittenIntegrand (α x : ℝ) :=
  (x - Real.cos α + Real.cos α) /
    ((x - Real.cos α) ^ 2 + (Real.sin α) ^ 2)
def logIntegrand (α x : ℝ) :=
  deriv (fun t : ℝ => (t - Real.cos α) ^ 2 + (Real.sin α) ^ 2) x /
    ((x - Real.cos α) ^ 2 + (Real.sin α) ^ 2)
def atanIntegrand (α x : ℝ) :=
  deriv (fun t : ℝ => t - Real.cos α) x /
    ((x - Real.cos α) ^ 2 + (Real.sin α) ^ 2)
def primitive (α x : ℝ) :=
  (1 / 2 : ℝ) * Real.log (denominator α x) +
    Real.cos α / Real.sin α *
      Real.arctan ((x - Real.cos α) / Real.sin α)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def SplitFamily (α : ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn (logIntegrand α),
    ∃ H ∈ AntiderivativesOn (atanIntegrand α),
      ∀ x ∈ branch, F x = (1 / 2 : ℝ) * G x + Real.cos α * H x}
def PrimitiveFamily (α : ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive α x + C}

private lemma quadratic_eq_denominator (α x : ℝ) :
    (x - Real.cos α) ^ 2 + (Real.sin α) ^ 2 = denominator α x := by
  unfold denominator
  nlinarith [Real.sin_sq_add_cos_sq α]

private lemma quadratic_pos (α : ℝ) (hα : Real.sin α ≠ 0) (x : ℝ) :
    0 < (x - Real.cos α) ^ 2 + (Real.sin α) ^ 2 := by
  have hs : 0 < (Real.sin α) ^ 2 := sq_pos_of_ne_zero hα
  nlinarith [sq_nonneg (x - Real.cos α)]

private lemma deriv_quadratic (α x : ℝ) :
    deriv (fun t : ℝ => (t - Real.cos α) ^ 2 + (Real.sin α) ^ 2) x =
      2 * (x - Real.cos α) := by
  have hd := (((hasDerivAt_id x).sub_const (Real.cos α)).pow 2).add_const
    ((Real.sin α) ^ 2)
  convert hd.deriv using 1 <;> simp [id] <;> ring_nf

private lemma deriv_affine (α x : ℝ) :
    deriv (fun t : ℝ => t - Real.cos α) x = 1 := by
  simpa using ((hasDerivAt_id x).sub_const (Real.cos α)).deriv

private lemma integrand_eq_rewritten (α x : ℝ) :
    integrand α x = rewrittenIntegrand α x := by
  unfold integrand rewrittenIntegrand
  rw [← quadratic_eq_denominator α x]
  ring

private lemma split_deriv_eq_integrand (α : ℝ) (hα : Real.sin α ≠ 0) (x : ℝ) :
    (1 / 2 : ℝ) * logIntegrand α x +
        Real.cos α * atanIntegrand α x = integrand α x := by
  unfold logIntegrand atanIntegrand integrand
  rw [deriv_quadratic α x, deriv_affine α x,
    ← quadratic_eq_denominator α x]
  field_simp [ne_of_gt (quadratic_pos α hα x)]
  ring

private def atanPrimitive (α x : ℝ) : ℝ :=
  (1 / Real.sin α) *
    Real.arctan ((x - Real.cos α) / Real.sin α)

private lemma hasDerivAt_atanPrimitive (α : ℝ) (hα : Real.sin α ≠ 0) (x : ℝ) :
    HasDerivAt (atanPrimitive α) (atanIntegrand α x) x := by
  have hi := ((hasDerivAt_id x).sub_const (Real.cos α)).div_const
    (Real.sin α)
  have ha := (Real.hasDerivAt_arctan
    ((x - Real.cos α) / Real.sin α)).comp x hi
  have hd := ha.const_mul (1 / Real.sin α)
  unfold atanPrimitive atanIntegrand
  rw [deriv_affine α x]
  convert hd using 1
  field_simp [hα]
  ring

private def logPrimitive (α x : ℝ) : ℝ :=
  Real.log ((x - Real.cos α) ^ 2 + (Real.sin α) ^ 2)

private lemma hasDerivAt_logPrimitive (α : ℝ) (hα : Real.sin α ≠ 0) (x : ℝ) :
    HasDerivAt (logPrimitive α) (logIntegrand α x) x := by
  have hq := (((hasDerivAt_id x).sub_const (Real.cos α)).pow 2).add_const
    ((Real.sin α) ^ 2)
  have hl := (Real.hasDerivAt_log
    (ne_of_gt (quadratic_pos α hα x))).comp x hq
  unfold logPrimitive logIntegrand
  convert hl using 1
  rw [deriv_quadratic α x]
  field_simp [ne_of_gt (quadratic_pos α hα x)]
  simp only [id]
  ring

private lemma hasDerivAt_primitive (α : ℝ) (hα : Real.sin α ≠ 0) :
    ∀ x : ℝ, HasDerivAt (primitive α) (integrand α x) x := by
  intro x
  have hlog := (hasDerivAt_logPrimitive α hα x).const_mul (1 / 2 : ℝ)
  have hatan := (hasDerivAt_atanPrimitive α hα x).const_mul (Real.cos α)
  have hd := hlog.add hatan
  have hfun : primitive α = fun y =>
      (1 / 2 : ℝ) * logPrimitive α y + Real.cos α * atanPrimitive α y := by
    funext y
    unfold primitive logPrimitive atanPrimitive
    rw [quadratic_eq_denominator α y]
    ring
  rw [hfun]
  have heq := split_deriv_eq_integrand α hα x
  simpa only [heq] using hd

private lemma eq_add_const_of_same_deriv
    {f F P : ℝ → ℝ}
    (hF : ∀ x : ℝ, HasDerivAt F (f x) x)
    (hP : ∀ x : ℝ, HasDerivAt P (f x) x) :
    ∃ C : ℝ, ∀ x : ℝ, F x = P x + C := by
  let D : ℝ → ℝ := fun x => F x - P x
  have hD : ∀ x : ℝ, HasDerivAt D 0 x := by
    intro x
    simpa only [D, sub_self] using (hF x).sub (hP x)
  have hdiff : ∀ x : ℝ, DifferentiableAt ℝ D x :=
    fun x => (hD x).differentiableAt
  have hderiv : ∀ x : ℝ, deriv D x = 0 :=
    fun x => (hD x).deriv
  have hmono : Monotone D := monotone_of_deriv_nonneg hdiff (fun x => by
    rw [hderiv x])
  have hanti : Antitone D := antitone_of_deriv_nonpos hdiff (fun x => by
    rw [hderiv x])
  have hconst : ∀ x : ℝ, D x = D 0 := by
    intro x
    rcases le_total x 0 with hx | hx
    · exact le_antisymm (hmono hx) (hanti hx)
    · exact le_antisymm (hanti hx) (hmono hx)
  refine ⟨D 0, ?_⟩
  intro x
  have hx := hconst x
  dsimp only [D] at hx ⊢
  linarith

theorem gap1 (α : ℝ) (hα : Real.sin α ≠ 0) :
    AntiderivativesOn (integrand α) =
      AntiderivativesOn (rewrittenIntegrand α) := by
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · intro h x hx
    simpa only [integrand_eq_rewritten α x] using h x hx
  · intro h x hx
    simpa only [integrand_eq_rewritten α x] using h x hx
theorem gap2 (α : ℝ) (hα : Real.sin α ≠ 0) :
    AntiderivativesOn (integrand α) = SplitFamily α := by
  ext F
  simp only [AntiderivativesOn, SplitFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    let H : ℝ → ℝ := atanPrimitive α
    have hH : ∀ x ∈ branch, HasDerivAt H (atanIntegrand α x) x := by
      intro x hx
      simpa only [H] using hasDerivAt_atanPrimitive α hα x
    let G : ℝ → ℝ := fun x => 2 * (F x - Real.cos α * H x)
    have hG : ∀ x ∈ branch, HasDerivAt G (logIntegrand α x) x := by
      intro x hx
      have hd := ((hF x hx).sub ((hH x hx).const_mul (Real.cos α))).const_mul 2
      have heq :
          2 * (integrand α x - Real.cos α * atanIntegrand α x) =
            logIntegrand α x := by
        nlinarith [split_deriv_eq_integrand α hα x]
      simpa only [G, heq] using hd
    refine ⟨G, hG, H, hH, ?_⟩
    intro x hx
    dsimp only [G]
    ring
  · rintro ⟨G, hG, H, hH, hF⟩
    have hfun : F = fun x => (1 / 2 : ℝ) * G x + Real.cos α * H x := by
      funext x
      exact hF x (by simp [branch])
    intro x hx
    rw [hfun]
    have hd := ((hG x hx).const_mul (1 / 2 : ℝ)).add
      ((hH x hx).const_mul (Real.cos α))
    have heq :
        (1 / 2 : ℝ) * logIntegrand α x +
            Real.cos α * atanIntegrand α x = integrand α x :=
      split_deriv_eq_integrand α hα x
    simpa only [heq] using hd
theorem gap3 (α : ℝ) (hα : Real.sin α ≠ 0) :
    AntiderivativesOn (integrand α) = PrimitiveFamily α := by
  ext F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    have hP : ∀ x : ℝ, HasDerivAt (primitive α) (integrand α x) x :=
      hasDerivAt_primitive α hα
    obtain ⟨C, hC⟩ := eq_add_const_of_same_deriv
      (fun x => hF x (by simp [branch])) hP
    exact ⟨C, fun x hx => hC x⟩
  · rintro ⟨C, hC⟩
    have hfun : F = fun x => primitive α x + C := by
      funext x
      exact hC x (by simp [branch])
    intro x hx
    rw [hfun]
    exact (hasDerivAt_primitive α hα x).add_const C

end
end ProofGap.Exercise1841
