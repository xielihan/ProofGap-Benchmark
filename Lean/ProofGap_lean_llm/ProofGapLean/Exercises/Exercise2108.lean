import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2108
noncomputable section

def domain : Set ℝ := Set.Ioo 0 1
def t (x : ℝ) := Real.sqrt x
def integrand (x : ℝ) := Real.arcsin (t x)
def residual (x : ℝ) := t x / Real.sqrt (1 - x)
def transformed (x : ℝ) :=
  t x ^ 2 / Real.sqrt (1 - t x ^ 2) * deriv t x
def splitTransformed (x : ℝ) :=
  (-Real.sqrt (1 - t x ^ 2) + 1 / Real.sqrt (1 - t x ^ 2)) * deriv t x
def residualPrimitiveT (x : ℝ) :=
  Real.arcsin (t x) - t x * Real.sqrt (1 - t x ^ 2)
def residualPrimitiveX (x : ℝ) :=
  Real.arcsin (Real.sqrt x) - Real.sqrt (x - x ^ 2)
def primitive (x : ℝ) :=
  (x - (1 / 2 : ℝ)) * Real.arcsin (Real.sqrt x) +
    (1 / 2 : ℝ) * Real.sqrt (x - x ^ 2)

def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ domain, HasDerivAt F (f x) x}
def ByPartsFamily :=
  {F : ℝ → ℝ | ∃ A ∈ Family residual, ∀ x ∈ domain,
    F x = x * Real.arcsin (Real.sqrt x) - (1 / 2 : ℝ) * A x}
def TwiceFamily (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family f, ∀ x ∈ domain, F x = 2 * A x}
def SplitFamily :=
  {F : ℝ → ℝ | ∃ A ∈ Family splitTransformed, ∀ x ∈ domain, F x = 2 * A x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem t_pos (x : ℝ) (hx : x ∈ domain) : 0 < t x := by
  exact Real.sqrt_pos.2 hx.1

private theorem t_sq (x : ℝ) (hx : x ∈ domain) : t x ^ 2 = x := by
  exact Real.sq_sqrt (le_of_lt hx.1)

private theorem one_sub_t_sq_pos (x : ℝ) (hx : x ∈ domain) :
    0 < 1 - t x ^ 2 := by
  rw [t_sq x hx]
  linarith [hx.2]

private theorem sqrt_one_sub_t_sq_pos (x : ℝ) (hx : x ∈ domain) :
    0 < Real.sqrt (1 - t x ^ 2) := by
  exact Real.sqrt_pos.2 (one_sub_t_sq_pos x hx)

private theorem t_mem_arcsin_domain (x : ℝ) (hx : x ∈ domain) :
    t x ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hp : 0 < t x := t_pos x hx
  have hs : t x ^ 2 = x := t_sq x hx
  have hxlt : x < 1 := hx.2
  constructor
  · linarith
  · by_contra hlt
    have hge : 1 ≤ t x := le_of_not_gt hlt
    have hplus : 0 ≤ t x + 1 := by linarith
    have hprod : 0 ≤ (t x - 1) * (t x + 1) :=
      mul_nonneg (sub_nonneg.mpr hge) hplus
    nlinarith [hprod]

private theorem hasDerivAt_t (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt t (1 / (2 * t x)) x := by
  simpa [t] using Real.hasDerivAt_sqrt (ne_of_gt hx.1)

private theorem t_deriv_relation (x : ℝ) (hx : x ∈ domain) :
    1 = 2 * t x * deriv t x := by
  have hd : deriv t x = 1 / (2 * t x) := (hasDerivAt_t x hx).deriv
  rw [hd]
  field_simp [ne_of_gt (t_pos x hx)]

private theorem hasDerivAt_integrand_formula (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt integrand
      ((1 / Real.sqrt (1 - t x ^ 2)) * (1 / (2 * t x))) x := by
  have hm := t_mem_arcsin_domain x hx
  have ha := Real.hasDerivAt_arcsin (ne_of_gt hm.1) (ne_of_lt hm.2)
  have ht := hasDerivAt_t x hx
  simpa [integrand, Function.comp_def] using ha.comp x ht

private theorem integrand_slope_identity (x : ℝ) (hx : x ∈ domain) :
    x * ((1 / Real.sqrt (1 - t x ^ 2)) * (1 / (2 * t x))) =
      (1 / 2 : ℝ) * residual x := by
  have ht0 : t x ≠ 0 := ne_of_gt (t_pos x hx)
  have hs0 : Real.sqrt (1 - t x ^ 2) ≠ 0 :=
    ne_of_gt (sqrt_one_sub_t_sq_pos x hx)
  simp only [residual]
  rw [show 1 - x = 1 - t x ^ 2 by rw [t_sq x hx]]
  field_simp [ht0, hs0] <;> nlinarith [t_sq x hx]

private theorem hasDerivAt_mul_integrand (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt (fun y => y * integrand y)
      (integrand x + (1 / 2 : ℝ) * residual x) x := by
  have h := (hasDerivAt_id x).mul (hasDerivAt_integrand_formula x hx)
  have hs := integrand_slope_identity x hx
  simpa only [Function.id_def, one_mul, hs] using h

private theorem hasDerivAt_of_eq_on_domain
    {F G : ℝ → ℝ} {d x : ℝ} (hx : x ∈ domain)
    (hG : HasDerivAt G d x)
    (hEq : ∀ y ∈ domain, F y = G y) : HasDerivAt F d x := by
  have hev : F =ᶠ[nhds x] G := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact hEq y hy
  exact hG.congr_of_eventuallyEq hev

private theorem residual_eq_two_transformed (x : ℝ) (hx : x ∈ domain) :
    residual x = 2 * transformed x := by
  simp only [residual, transformed]
  rw [show 1 - x = 1 - t x ^ 2 by rw [t_sq x hx]]
  calc
    t x / Real.sqrt (1 - t x ^ 2) =
        (t x / Real.sqrt (1 - t x ^ 2)) * 1 := by ring
    _ = (t x / Real.sqrt (1 - t x ^ 2)) *
        (2 * t x * deriv t x) := by rw [← t_deriv_relation x hx]
    _ = 2 * (t x ^ 2 / Real.sqrt (1 - t x ^ 2) * deriv t x) := by
      ring

private theorem transformed_eq_split (x : ℝ) (hx : x ∈ domain) :
    transformed x = splitTransformed x := by
  have hs : Real.sqrt (1 - t x ^ 2) ^ 2 = 1 - t x ^ 2 :=
    Real.sq_sqrt (le_of_lt (one_sub_t_sq_pos x hx))
  have hs0 : Real.sqrt (1 - t x ^ 2) ≠ 0 :=
    ne_of_gt (sqrt_one_sub_t_sq_pos x hx)
  have hcoeff :
      t x ^ 2 / Real.sqrt (1 - t x ^ 2) =
        -Real.sqrt (1 - t x ^ 2) + 1 / Real.sqrt (1 - t x ^ 2) := by
    field_simp [hs0] <;> nlinarith [hs]
  simp only [transformed, splitTransformed]
  rw [hcoeff]

private theorem hasDerivAt_residualPrimitiveT (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt residualPrimitiveT (residual x) x := by
  have ht := hasDerivAt_t x hx
  have ha := hasDerivAt_integrand_formula x hx
  have hinner := (hasDerivAt_const x (1 : ℝ)).sub (ht.pow 2)
  have hsqrt := (Real.hasDerivAt_sqrt
    (ne_of_gt (one_sub_t_sq_pos x hx))).comp x hinner
  have h := ha.sub (ht.mul hsqrt)
  have ht0 : t x ≠ 0 := ne_of_gt (t_pos x hx)
  have hs0 : Real.sqrt (1 - t x ^ 2) ≠ 0 :=
    ne_of_gt (sqrt_one_sub_t_sq_pos x hx)
  have hsquare : Real.sqrt (1 - t x ^ 2) ^ 2 = 1 - t x ^ 2 :=
    Real.sq_sqrt (le_of_lt (one_sub_t_sq_pos x hx))
  convert h using 1
  simp [Function.comp_apply]
  rw [residual]
  rw [show 1 - x = 1 - t x ^ 2 by rw [t_sq x hx]]
  field_simp [ht0, hs0] <;> nlinarith [hsquare]

private theorem family_eq_translates_of_primitive
    (f p : ℝ → ℝ) (hp : p ∈ Family f) : Family f = Translates p := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ domain, HasDerivAt F (f x) x at hF
    change ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C
    let c : ℝ := (1 / 2 : ℝ)
    have hc : c ∈ domain := by
      constructor <;> norm_num [domain, c]
    refine ⟨F c - p c, ?_⟩
    intro x hx
    have hdiff : DifferentiableOn ℝ (fun y => F y - p y) domain := by
      intro y hy
      exact ((hF y hy).sub (hp y hy)).differentiableAt.differentiableWithinAt
    have hzero : ∀ y ∈ domain, deriv (fun z => F z - p z) y = 0 := by
      intro y hy
      simpa using ((hF y hy).sub (hp y hy)).deriv
    have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero
      isPreconnected_Ioo hdiff hzero hc hx
    dsimp [c] at hconst ⊢
    linarith
  · rintro ⟨C, hEq⟩
    change ∀ x ∈ domain, HasDerivAt F (f x) x
    intro x hx
    have hmodel : HasDerivAt (fun y => p y + C) (f x) x :=
      (hp x hx).add_const C
    apply hasDerivAt_of_eq_on_domain hx hmodel
    exact hEq

private theorem residual_primitives_agree (x : ℝ) (hx : x ∈ domain) :
    residualPrimitiveT x = residualPrimitiveX x := by
  have hx0 : 0 ≤ x := le_of_lt hx.1
  have hmul : Real.sqrt x * Real.sqrt (1 - x) =
      Real.sqrt (x - x ^ 2) := by
    rw [← Real.sqrt_mul hx0]
    congr 1
    ring
  simp only [residualPrimitiveT, residualPrimitiveX, t]
  rw [Real.sq_sqrt hx0, hmul]

private theorem byparts_primitive_identity (x : ℝ) :
    x * Real.arcsin (Real.sqrt x) -
        (1 / 2 : ℝ) * residualPrimitiveX x = primitive x := by
  simp only [residualPrimitiveX, primitive]
  ring

theorem gap1 : Family integrand = ByPartsFamily := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ domain, HasDerivAt F (integrand x) x at hF
    change ∃ A ∈ Family residual, ∀ x ∈ domain,
      F x = x * Real.arcsin (Real.sqrt x) - (1 / 2 : ℝ) * A x
    let A : ℝ → ℝ := fun y => 2 * (y * integrand y - F y)
    refine ⟨A, ?_, ?_⟩
    · intro x hx
      have h := ((hasDerivAt_mul_integrand x hx).sub (hF x hx)).const_mul 2
      simpa [A] using h
    · intro x hx
      simp only [A, integrand, t]
      ring
  · rintro ⟨A, hA, hEq⟩
    change ∀ x ∈ domain, HasDerivAt F (integrand x) x
    intro x hx
    have hmodel : HasDerivAt
        (fun y => y * integrand y - (1 / 2 : ℝ) * A y)
        (integrand x) x := by
      have h := (hasDerivAt_mul_integrand x hx).sub
        ((hA x hx).const_mul (1 / 2 : ℝ))
      convert h using 1 <;> ring
    apply hasDerivAt_of_eq_on_domain hx hmodel
    intro y hy
    simpa [integrand, t] using hEq y hy
theorem gap2 (x : ℝ) (hx : x ∈ domain) : 1 = 2 * t x * deriv t x := by
  exact t_deriv_relation x hx
theorem gap3 : Family residual = TwiceFamily transformed := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ domain, HasDerivAt F (residual x) x at hF
    change ∃ A ∈ Family transformed, ∀ x ∈ domain, F x = 2 * A x
    let A : ℝ → ℝ := fun y => (1 / 2 : ℝ) * F y
    refine ⟨A, ?_, ?_⟩
    · intro x hx
      have h := (hF x hx).const_mul (1 / 2 : ℝ)
      rw [residual_eq_two_transformed x hx] at h
      simpa [A] using h
    · intro x hx
      simp [A]
  · rintro ⟨A, hA, hEq⟩
    change ∀ x ∈ domain, HasDerivAt F (residual x) x
    intro x hx
    have hmodel : HasDerivAt (fun y => 2 * A y) (residual x) x := by
      have h := (hA x hx).const_mul 2
      rw [residual_eq_two_transformed x hx]
      simpa using h
    apply hasDerivAt_of_eq_on_domain hx hmodel
    exact hEq
theorem gap4 : TwiceFamily transformed = SplitFamily := by
  ext F
  constructor
  · rintro ⟨A, hA, hEq⟩
    refine ⟨A, ?_, hEq⟩
    intro x hx
    rw [← transformed_eq_split x hx]
    exact hA x hx
  · rintro ⟨A, hA, hEq⟩
    refine ⟨A, ?_, hEq⟩
    intro x hx
    rw [transformed_eq_split x hx]
    exact hA x hx
theorem gap5 : Family residual = SplitFamily := by
  calc
    Family residual = TwiceFamily transformed := gap3
    _ = SplitFamily := gap4
theorem gap6 : Family residual = Translates residualPrimitiveT := by
  apply family_eq_translates_of_primitive
  intro x hx
  exact hasDerivAt_residualPrimitiveT x hx
theorem gap7 : Translates residualPrimitiveT = Translates residualPrimitiveX := by
  ext F
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [← residual_primitives_agree x hx]
    exact hC x hx
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [residual_primitives_agree x hx]
    exact hC x hx
theorem gap8 : Family residual = Translates residualPrimitiveX := by
  calc
    Family residual = Translates residualPrimitiveT := gap6
    _ = Translates residualPrimitiveX := gap7
theorem gap9 : Family integrand = Translates primitive := by
  rw [gap1]
  ext F
  constructor
  · rintro ⟨A, hA, hF⟩
    have hAT : A ∈ Translates residualPrimitiveX := by
      rw [← gap8]
      exact hA
    rcases hAT with ⟨C, hC⟩
    refine ⟨-(1 / 2 : ℝ) * C, ?_⟩
    intro x hx
    calc
      F x = x * Real.arcsin (Real.sqrt x) - (1 / 2 : ℝ) * A x := hF x hx
      _ = x * Real.arcsin (Real.sqrt x) -
          (1 / 2 : ℝ) * (residualPrimitiveX x + C) := by rw [hC x hx]
      _ = (x * Real.arcsin (Real.sqrt x) -
          (1 / 2 : ℝ) * residualPrimitiveX x) +
          (-(1 / 2 : ℝ) * C) := by ring
      _ = primitive x + (-(1 / 2 : ℝ) * C) := by
        rw [byparts_primitive_identity x]
  · rintro ⟨C, hF⟩
    let A : ℝ → ℝ := fun y => residualPrimitiveX y - 2 * C
    have hAT : A ∈ Translates residualPrimitiveX := by
      refine ⟨-2 * C, ?_⟩
      intro x hx
      simp [A]
      ring
    have hA : A ∈ Family residual := by
      rw [gap8]
      exact hAT
    refine ⟨A, hA, ?_⟩
    intro x hx
    calc
      F x = primitive x + C := hF x hx
      _ = (x * Real.arcsin (Real.sqrt x) -
          (1 / 2 : ℝ) * residualPrimitiveX x) + C := by
        rw [byparts_primitive_identity x]
      _ = x * Real.arcsin (Real.sqrt x) - (1 / 2 : ℝ) * A x := by
        simp only [A]
        ring

end
end ProofGap.Exercise2108
