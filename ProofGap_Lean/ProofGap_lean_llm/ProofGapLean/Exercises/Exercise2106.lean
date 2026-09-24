import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2106
noncomputable section

def domain : Set ℝ := Set.Ioi 0
def integrand (x : ℝ) := Real.sqrt x * Real.arctan (Real.sqrt x)
def powerDifferential (x : ℝ) :=
  Real.arctan (Real.sqrt x) * deriv (fun y : ℝ => y * Real.sqrt y) x
def rational (x : ℝ) := x / (1 + x)
def splitRational (x : ℝ) := 1 - 1 / (1 + x)
def primitive (x : ℝ) :=
  (2 / 3 : ℝ) * x * Real.sqrt x * Real.arctan (Real.sqrt x) -
    x / 3 + (1 / 3 : ℝ) * Real.log (1 + x)

def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ domain, HasDerivAt F (f x) x}
def ScaledFamily (c : ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family f, ∀ x ∈ domain, F x = c * A x}
def ByPartsFamily (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family f, ∀ x ∈ domain,
    F x = (2 / 3 : ℝ) * x * Real.sqrt x * Real.arctan (Real.sqrt x) -
      (1 / 3 : ℝ) * A x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private def boundary (x : ℝ) :=
  (2 / 3 : ℝ) * x * Real.sqrt x * Real.arctan (Real.sqrt x)

private def rationalPrimitive (x : ℝ) :=
  x - Real.log (1 + x)

private theorem hasDerivAt_of_eqOn_domain
    {F G : ℝ → ℝ} {f x : ℝ} (hx : x ∈ domain)
    (hFG : ∀ y ∈ domain, F y = G y) (hG : HasDerivAt G f x) :
    HasDerivAt F f x := by
  have he : F =ᶠ[nhds x] G := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact hFG y hy
  exact hG.congr_of_eventuallyEq he

private theorem hasDerivAt_mul_sqrt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt (fun y : ℝ => y * Real.sqrt y)
      ((3 / 2 : ℝ) * Real.sqrt x) x := by
  have hxpos : 0 < x := hx
  have hspos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hsquare : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (le_of_lt hxpos)
  have hs := Real.hasDerivAt_sqrt (ne_of_gt hxpos)
  convert (hasDerivAt_id x).mul hs using 1
  dsimp only [id]
  field_simp [hspos.ne']
  nlinarith [hsquare]

private theorem powerDifferential_eq_integrand (x : ℝ) (hx : x ∈ domain) :
    powerDifferential x = (3 / 2 : ℝ) * integrand x := by
  rw [powerDifferential, (hasDerivAt_mul_sqrt x hx).deriv]
  simp only [integrand]
  ring

private theorem hasDerivAt_boundary (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt boundary (integrand x + (1 / 3 : ℝ) * rational x) x := by
  have hxpos : 0 < x := hx
  have hspos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hsquare : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (le_of_lt hxpos)
  have hone : 1 + x ≠ 0 := by linarith
  have hs := Real.hasDerivAt_sqrt (ne_of_gt hxpos)
  have ha := (Real.hasDerivAt_arctan (Real.sqrt x)).comp x hs
  have hraw := ((hasDerivAt_mul_sqrt x hx).const_mul (2 / 3 : ℝ)).mul ha
  have hfun :
      (fun y : ℝ => (2 / 3 : ℝ) * (y * Real.sqrt y)) *
          (Real.arctan ∘ Real.sqrt) = boundary := by
    funext y
    simp only [Pi.mul_apply, Function.comp_apply, boundary]
    ring
  rw [hfun] at hraw
  convert hraw using 1
  simp only [Function.comp_apply, integrand, rational]
  field_simp [hspos.ne', hone]
  ring_nf
  nlinarith [hsquare]

private theorem rational_eq_splitRational (x : ℝ) (hx : x ∈ domain) :
    rational x = splitRational x := by
  have hxpos : 0 < x := hx
  have hone : 1 + x ≠ 0 := by linarith
  simp only [rational, splitRational]
  field_simp [hone]
  ring

private theorem family_rational_eq_splitRational :
    Family rational = Family splitRational := by
  ext A
  constructor
  · intro h x hx
    simpa only [← rational_eq_splitRational x hx] using h x hx
  · intro h x hx
    simpa only [rational_eq_splitRational x hx] using h x hx

private theorem hasDerivAt_rationalPrimitive (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt rationalPrimitive (splitRational x) x := by
  have hxpos : 0 < x := hx
  have hone : 1 + x ≠ 0 := by linarith
  simpa [rationalPrimitive, splitRational, div_eq_mul_inv] using
    (hasDerivAt_id x).sub
      ((Real.hasDerivAt_log hone).comp x
        ((hasDerivAt_const x 1).add (hasDerivAt_id x)))

private theorem split_antiderivative_is_translate
    {A : ℝ → ℝ} (hA : A ∈ Family splitRational) :
    ∃ C : ℝ, ∀ x ∈ domain, A x = rationalPrimitive x + C := by
  let H : ℝ → ℝ := fun y => A y - rationalPrimitive y
  have hdiff : DifferentiableOn ℝ H domain := by
    intro x hx
    exact ((hA x hx).sub (hasDerivAt_rationalPrimitive x hx)).differentiableAt.differentiableWithinAt
  have hzero : ∀ x ∈ domain, deriv H x = 0 := by
    intro x hx
    have h := ((hA x hx).sub (hasDerivAt_rationalPrimitive x hx)).deriv
    simpa [H] using h
  refine ⟨A 1 - rationalPrimitive 1, ?_⟩
  intro x hx
  have hone : (1 : ℝ) ∈ domain := by norm_num [domain]
  have hc : H x = H 1 :=
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi hdiff hzero hx hone
  dsimp [H] at hc
  linarith

theorem gap1 : Family integrand = ScaledFamily (2 / 3) powerDifferential := by
  ext F
  constructor
  · intro hF
    refine ⟨fun x => (3 / 2 : ℝ) * F x, ?_, ?_⟩
    · intro x hx
      have hpow := powerDifferential_eq_integrand x hx
      simpa only [hpow] using (hF x hx).const_mul (3 / 2 : ℝ)
    · intro x hx
      ring
  · rintro ⟨P, hP, hFP⟩
    intro x hx
    have hpow := powerDifferential_eq_integrand x hx
    have hscaled : HasDerivAt (fun y => (2 / 3 : ℝ) * P y) (integrand x) x := by
      convert (hP x hx).const_mul (2 / 3 : ℝ) using 1
      rw [hpow]
      ring
    exact hasDerivAt_of_eqOn_domain hx (fun y hy => hFP y hy) hscaled
theorem gap2 : ScaledFamily (2 / 3) powerDifferential = ByPartsFamily rational := by
  ext F
  constructor
  · rintro ⟨P, hP, hFP⟩
    refine ⟨fun x => 3 * boundary x - 2 * P x, ?_, ?_⟩
    · intro x hx
      have hb := hasDerivAt_boundary x hx
      have hp := hP x hx
      have hpow := powerDifferential_eq_integrand x hx
      convert (hb.const_mul 3).sub (hp.const_mul 2) using 1
      rw [hpow]
      ring
    · intro x hx
      rw [hFP x hx]
      simp only [boundary]
      ring
  · rintro ⟨A, hA, hFA⟩
    refine ⟨fun x => (3 / 2 : ℝ) * boundary x - (1 / 2 : ℝ) * A x, ?_, ?_⟩
    · intro x hx
      have hb := hasDerivAt_boundary x hx
      have ha := hA x hx
      have hpow := powerDifferential_eq_integrand x hx
      convert (hb.const_mul (3 / 2 : ℝ)).sub (ha.const_mul (1 / 2 : ℝ)) using 1
      rw [hpow]
      ring
    · intro x hx
      rw [hFA x hx]
      simp only [boundary]
      ring
theorem gap3 : Family integrand = ByPartsFamily rational := by
  exact gap1.trans gap2
theorem gap4 : Family integrand = ByPartsFamily splitRational := by
  rw [gap3]
  ext F
  constructor
  · rintro ⟨A, hA, hFA⟩
    refine ⟨A, ?_, hFA⟩
    rw [← family_rational_eq_splitRational]
    exact hA
  · rintro ⟨A, hA, hFA⟩
    refine ⟨A, ?_, hFA⟩
    rw [family_rational_eq_splitRational]
    exact hA
theorem gap5 : ByPartsFamily splitRational = Translates primitive := by
  ext F
  constructor
  · rintro ⟨A, hA, hFA⟩
    obtain ⟨C, hAC⟩ := split_antiderivative_is_translate hA
    refine ⟨-(C / 3), ?_⟩
    intro x hx
    rw [hFA x hx, hAC x hx]
    simp only [boundary, rationalPrimitive, primitive]
    ring
  · rintro ⟨C, hFC⟩
    refine ⟨fun x => rationalPrimitive x - 3 * C, ?_, ?_⟩
    · intro x hx
      simpa using (hasDerivAt_rationalPrimitive x hx).sub_const (3 * C)
    · intro x hx
      rw [hFC x hx]
      simp only [boundary, rationalPrimitive, primitive]
      ring
theorem gap6 : Family integrand = Translates primitive := by
  exact gap4.trans gap5

end
end ProofGap.Exercise2106
