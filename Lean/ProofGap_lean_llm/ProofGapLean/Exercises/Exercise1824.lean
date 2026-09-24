import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1824

noncomputable section

def branch : Set ℝ := Set.univ
def expAtan (x : ℝ) := Real.exp (Real.arctan x)
def integrand (x : ℝ) :=
  x * expAtan x / Real.rpow (1 + x ^ 2) (3 / 2 : ℝ)
def firstChainIntegrand (x : ℝ) :=
  expAtan x *
    deriv (fun t : ℝ => -Real.rpow (1 + t ^ 2) (-1 / 2 : ℝ)) x
def secondChainIntegrand (x : ℝ) :=
  x / Real.sqrt (1 + x ^ 2) * deriv expAtan x
def auxiliaryIntegrand (x : ℝ) :=
  1 / Real.sqrt (1 + x ^ 2) * deriv expAtan x
def boundary₁ (x : ℝ) := -expAtan x / Real.sqrt (1 + x ^ 2)
def boundary₂ (x : ℝ) := x * expAtan x / Real.sqrt (1 + x ^ 2)
def primitive (x : ℝ) :=
  (x - 1) / (2 * Real.sqrt (1 + x ^ 2)) * expAtan x
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def FirstRelationFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn auxiliaryIntegrand,
    ∀ x ∈ branch, F x = boundary₁ x + G x}
def SecondRelationFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn auxiliaryIntegrand,
    ∀ x ∈ branch, F x = boundary₂ x - G x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private theorem base_pos (x : ℝ) : 0 < 1 + x ^ 2 := by
  positivity

private theorem sqrt_base_ne_zero (x : ℝ) :
    Real.sqrt (1 + x ^ 2) ≠ 0 := by
  exact ne_of_gt (Real.sqrt_pos.2 (base_pos x))

private theorem rpow_three_halves (x : ℝ) :
    Real.rpow (1 + x ^ 2) (3 / 2 : ℝ) =
      (1 + x ^ 2) * Real.sqrt (1 + x ^ 2) := by
  have hp := base_pos x
  have hradd :
      Real.rpow (1 + x ^ 2) (1 + 1 / 2 : ℝ) =
        Real.rpow (1 + x ^ 2) 1 * Real.rpow (1 + x ^ 2) (1 / 2 : ℝ) := by
    simpa only using
      (Real.rpow_add hp (1 : ℝ) (1 / 2 : ℝ))
  have hrone : Real.rpow (1 + x ^ 2) 1 = 1 + x ^ 2 := by
    simpa only using (Real.rpow_one (1 + x ^ 2))
  have hsqrt :
      Real.rpow (1 + x ^ 2) (1 / 2 : ℝ) = Real.sqrt (1 + x ^ 2) := by
    symm
    exact Real.sqrt_eq_rpow (1 + x ^ 2)
  calc
    Real.rpow (1 + x ^ 2) (3 / 2 : ℝ) =
        Real.rpow (1 + x ^ 2) (1 + 1 / 2 : ℝ) := by norm_num
    _ = Real.rpow (1 + x ^ 2) 1 *
        Real.rpow (1 + x ^ 2) (1 / 2 : ℝ) := hradd
    _ = (1 + x ^ 2) * Real.sqrt (1 + x ^ 2) := by
      rw [hrone, hsqrt]

private theorem rpow_neg_half (x : ℝ) :
    Real.rpow (1 + x ^ 2) (-1 / 2 : ℝ) =
      1 / Real.sqrt (1 + x ^ 2) := by
  have hp := base_pos x
  have hrneg :
      Real.rpow (1 + x ^ 2) (-(1 / 2 : ℝ)) =
        (Real.rpow (1 + x ^ 2) (1 / 2 : ℝ))⁻¹ := by
    simpa only using
      (Real.rpow_neg (le_of_lt hp) (1 / 2 : ℝ))
  have hsqrt :
      Real.rpow (1 + x ^ 2) (1 / 2 : ℝ) = Real.sqrt (1 + x ^ 2) := by
    symm
    exact Real.sqrt_eq_rpow (1 + x ^ 2)
  calc
    Real.rpow (1 + x ^ 2) (-1 / 2 : ℝ) =
        Real.rpow (1 + x ^ 2) (-(1 / 2 : ℝ)) := by ring
    _ = (Real.rpow (1 + x ^ 2) (1 / 2 : ℝ))⁻¹ := hrneg
    _ = (Real.sqrt (1 + x ^ 2))⁻¹ := by rw [hsqrt]
    _ = 1 / Real.sqrt (1 + x ^ 2) := by rw [one_div]

private theorem hasDerivAt_base (x : ℝ) :
    HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * x) x := by
  convert (hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2) using 1 <;>
    simp only [id_eq] <;> ring

private theorem hasDerivAt_sqrtBase (x : ℝ) :
    HasDerivAt
      (fun t : ℝ => Real.sqrt (1 + t ^ 2))
      (x / Real.sqrt (1 + x ^ 2)) x := by
  have hs :=
    (Real.hasDerivAt_sqrt (base_pos x).ne').comp x (hasDerivAt_base x)
  convert hs using 1
  field_simp [sqrt_base_ne_zero x]

private theorem hasDerivAt_negInvSqrt (x : ℝ) :
    HasDerivAt
      (fun t : ℝ => -1 / Real.sqrt (1 + t ^ 2))
      (x / ((1 + x ^ 2) * Real.sqrt (1 + x ^ 2))) x := by
  have hi := (hasDerivAt_sqrtBase x).inv (sqrt_base_ne_zero x)
  have hsq : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt (le_of_lt (base_pos x))
  convert hi.neg using 1
  · funext t
    rw [neg_div, one_div]
    change -(Real.sqrt (1 + t ^ 2))⁻¹ = -(Real.sqrt (1 + t ^ 2))⁻¹
    rfl
  · rw [hsq]
    field_simp [sqrt_base_ne_zero x]

private theorem hasDerivAt_invSqrt (x : ℝ) :
    HasDerivAt
      (fun t : ℝ => 1 / Real.sqrt (1 + t ^ 2))
      (-x / ((1 + x ^ 2) * Real.sqrt (1 + x ^ 2))) x := by
  have hi := (hasDerivAt_sqrtBase x).inv (sqrt_base_ne_zero x)
  have hsq : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt (le_of_lt (base_pos x))
  convert hi using 1
  · funext t
    simp
  · rw [hsq]
    field_simp [sqrt_base_ne_zero x]

private theorem hasDerivAt_negRpow (x : ℝ) :
    HasDerivAt
      (fun t : ℝ => -Real.rpow (1 + t ^ 2) (-1 / 2 : ℝ))
      (x / ((1 + x ^ 2) * Real.sqrt (1 + x ^ 2))) x := by
  have hfun :
      (fun t : ℝ => -Real.rpow (1 + t ^ 2) (-1 / 2 : ℝ)) =
        fun t : ℝ => -1 / Real.sqrt (1 + t ^ 2) := by
    funext t
    rw [rpow_neg_half t]
    simp only [div_eq_mul_inv, neg_mul, one_mul]
  rw [hfun]
  exact hasDerivAt_negInvSqrt x

private theorem hasDerivAt_expAtan (x : ℝ) :
    HasDerivAt expAtan (expAtan x / (1 + x ^ 2)) x := by
  unfold expAtan
  convert
    (Real.hasDerivAt_exp (Real.arctan x)).comp x
      (Real.hasDerivAt_arctan x) using 1 <;> ring

private theorem deriv_expAtan (x : ℝ) :
    deriv expAtan x = expAtan x / (1 + x ^ 2) :=
  (hasDerivAt_expAtan x).deriv

private theorem integrand_eq_firstChain (x : ℝ) :
    integrand x = firstChainIntegrand x := by
  unfold integrand firstChainIntegrand
  rw [(hasDerivAt_negRpow x).deriv, rpow_three_halves x]
  ring

private theorem integrand_eq_secondChain (x : ℝ) :
    integrand x = secondChainIntegrand x := by
  unfold integrand secondChainIntegrand
  rw [deriv_expAtan x, rpow_three_halves x]
  field_simp [sqrt_base_ne_zero x, (base_pos x).ne'] <;> ring

private theorem hasDerivAt_boundary₁ (x : ℝ) :
    HasDerivAt boundary₁ (integrand x - auxiliaryIntegrand x) x := by
  have hd := (hasDerivAt_expAtan x).mul (hasDerivAt_negInvSqrt x)
  have hsq : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt (le_of_lt (base_pos x))
  convert hd using 1
  · funext t
    change
      -expAtan t / Real.sqrt (1 + t ^ 2) =
        expAtan t * (-1 / Real.sqrt (1 + t ^ 2))
    ring
  · unfold integrand auxiliaryIntegrand
    rw [rpow_three_halves x, deriv_expAtan x]
    field_simp [sqrt_base_ne_zero x, (base_pos x).ne', hsq] <;> ring

private theorem hasDerivAt_boundary₂ (x : ℝ) :
    HasDerivAt boundary₂ (integrand x + auxiliaryIntegrand x) x := by
  have hprod :
      HasDerivAt (fun t : ℝ => t * expAtan t)
        (expAtan x + x * (expAtan x / (1 + x ^ 2))) x := by
    simpa only [id_eq, one_mul] using
      (hasDerivAt_id x).mul (hasDerivAt_expAtan x)
  have hd := hprod.mul (hasDerivAt_invSqrt x)
  have hsq : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt (le_of_lt (base_pos x))
  convert hd using 1
  · funext t
    change
      t * expAtan t / Real.sqrt (1 + t ^ 2) =
        (t * expAtan t) * (1 / Real.sqrt (1 + t ^ 2))
    ring
  · unfold integrand auxiliaryIntegrand
    rw [rpow_three_halves x, deriv_expAtan x]
    field_simp [sqrt_base_ne_zero x, (base_pos x).ne', hsq] <;> ring

private theorem primitive_eq_boundaries (x : ℝ) :
    primitive x = (boundary₁ x + boundary₂ x) / 2 := by
  unfold primitive boundary₁ boundary₂
  field_simp [sqrt_base_ne_zero x]
  ring

private theorem hasDerivAt_primitive (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have hd := ((hasDerivAt_boundary₁ x).add (hasDerivAt_boundary₂ x)).div_const 2
  convert hd using 1
  · funext t
    exact primitive_eq_boundaries t
  · ring

private theorem hasDerivAt_zero_is_constant
    {H : ℝ → ℝ} (hH : ∀ x, HasDerivAt H 0 x) :
    ∀ x, H x = H 0 := by
  have hcont : Continuous H :=
    continuous_iff_continuousAt.2 fun x => (hH x).continuousAt
  have hdiff : Differentiable ℝ H :=
    fun x => (hH x).differentiableAt
  intro x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · obtain ⟨c, hc, hslope⟩ :=
      exists_deriv_eq_slope H hx hcont.continuousOn hdiff.differentiableOn
    have hz : deriv H c = 0 := (hH c).deriv
    rw [hz] at hslope
    have hne : 0 - x ≠ 0 := by linarith
    field_simp [hne] at hslope
    linarith
  · simpa [hx]
  · obtain ⟨c, hc, hslope⟩ :=
      exists_deriv_eq_slope H hx hcont.continuousOn hdiff.differentiableOn
    have hz : deriv H c = 0 := (hH c).deriv
    rw [hz] at hslope
    have hne : x - 0 ≠ 0 := by linarith
    field_simp [hne] at hslope
    linarith

private theorem antiderivatives_differ_by_const
    {f F P : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (f x) x)
    (hP : ∀ x, HasDerivAt P (f x) x) :
    ∃ C : ℝ, ∀ x, F x = P x + C := by
  let H : ℝ → ℝ := fun x => F x - P x
  have hH : ∀ x, HasDerivAt H 0 x := by
    intro x
    dsimp [H]
    convert (hF x).sub (hP x) using 1 <;> ring
  refine ⟨H 0, ?_⟩
  intro x
  have hc := hasDerivAt_zero_is_constant hH x
  dsimp [H] at hc ⊢
  linarith

theorem gap1 :
    AntiderivativesOn integrand =
      AntiderivativesOn firstChainIntegrand := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      ∀ x ∈ branch, HasDerivAt F (firstChainIntegrand x) x
  constructor <;> intro h x hx
  · simpa only [integrand_eq_firstChain x] using h x hx
  · simpa only [integrand_eq_firstChain x] using h x hx
theorem gap2 :
    AntiderivativesOn firstChainIntegrand = FirstRelationFamily := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (firstChainIntegrand x) x) ↔
      ∃ G, (∀ x ∈ branch, HasDerivAt G (auxiliaryIntegrand x) x) ∧
        ∀ x ∈ branch, F x = boundary₁ x + G x
  constructor
  · intro hF
    refine ⟨fun x => F x - boundary₁ x, ?_, ?_⟩
    · intro x hx
      have hd := (hF x hx).sub (hasDerivAt_boundary₁ x)
      convert hd using 1
      rw [← integrand_eq_firstChain x]
      ring
    · intro x hx
      ring
  · rintro ⟨G, hG, hrel⟩
    have hfun : F = fun x => boundary₁ x + G x := by
      funext x
      exact hrel x (by simp [branch])
    intro x hx
    rw [hfun]
    have hd := (hasDerivAt_boundary₁ x).add (hG x hx)
    convert hd using 1
    rw [← integrand_eq_firstChain x]
    ring
theorem gap3 :
    AntiderivativesOn integrand = FirstRelationFamily := by
  calc
    AntiderivativesOn integrand =
        AntiderivativesOn firstChainIntegrand := gap1
    _ = FirstRelationFamily := gap2
theorem gap4 :
    AntiderivativesOn integrand =
      AntiderivativesOn secondChainIntegrand := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      ∀ x ∈ branch, HasDerivAt F (secondChainIntegrand x) x
  constructor <;> intro h x hx
  · simpa only [integrand_eq_secondChain x] using h x hx
  · simpa only [integrand_eq_secondChain x] using h x hx
theorem gap5 :
    AntiderivativesOn secondChainIntegrand = SecondRelationFamily := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (secondChainIntegrand x) x) ↔
      ∃ G, (∀ x ∈ branch, HasDerivAt G (auxiliaryIntegrand x) x) ∧
        ∀ x ∈ branch, F x = boundary₂ x - G x
  constructor
  · intro hF
    refine ⟨fun x => boundary₂ x - F x, ?_, ?_⟩
    · intro x hx
      have hd := (hasDerivAt_boundary₂ x).sub (hF x hx)
      convert hd using 1
      rw [← integrand_eq_secondChain x]
      ring
    · intro x hx
      ring
  · rintro ⟨G, hG, hrel⟩
    have hfun : F = fun x => boundary₂ x - G x := by
      funext x
      exact hrel x (by simp [branch])
    intro x hx
    rw [hfun]
    have hd := (hasDerivAt_boundary₂ x).sub (hG x hx)
    convert hd using 1
    rw [← integrand_eq_secondChain x]
    ring
theorem gap6 :
    AntiderivativesOn integrand = SecondRelationFamily := by
  calc
    AntiderivativesOn integrand =
        AntiderivativesOn secondChainIntegrand := gap4
    _ = SecondRelationFamily := gap5
theorem gap7 :
    AntiderivativesOn integrand = PrimitiveFamily := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C
  constructor
  · intro hF
    obtain ⟨C, hC⟩ := antiderivatives_differ_by_const
      (fun x => hF x (by simp [branch])) hasDerivAt_primitive
    exact ⟨C, fun x hx => hC x⟩
  · rintro ⟨C, hC⟩
    have hfun : F = fun x => primitive x + C := by
      funext x
      exact hC x (by simp [branch])
    intro x hx
    rw [hfun]
    exact (hasDerivAt_primitive x).add_const C

end
end ProofGap.Exercise1824
