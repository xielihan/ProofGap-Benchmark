import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2162

noncomputable section

def a (x : ℝ) := Real.arctan (Real.exp (x / 2))
def integrand (x : ℝ) :=
  a x / (Real.exp (x / 2) * (1 + Real.exp x))
def rewritten (x : ℝ) :=
  (Real.exp (-x / 2) - Real.exp (x / 2) / (1 + Real.exp x)) * a x
def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}
def FirstReductionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ,
      (∀ x, HasDerivAt G
        (a x * deriv (fun y : ℝ => Real.exp (-y / 2)) x) x) ∧
    ∃ H : ℝ → ℝ,
      (∀ x, HasDerivAt H (a x * deriv a x) x) ∧
    ∀ x, F x = -2 * G x - 2 * H x}
def SecondReductionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives (fun x => 1 / (1 + Real.exp x)),
    ∀ x,
      F x = -2 * Real.exp (-x / 2) * a x + G x - a x ^ 2}
def ThirdReductionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives
      (fun x => 1 - Real.exp x / (1 + Real.exp x)),
    ∀ x,
      F x = -2 * Real.exp (-x / 2) * a x + G x - a x ^ 2}
def primitive (x : ℝ) :=
  -2 * Real.exp (-x / 2) * a x +
    x - Real.log (1 + Real.exp x) - a x ^ 2

private def da_aux (x : ℝ) :=
  Real.exp (x / 2) / (2 * (1 + Real.exp x))

private def de_aux (x : ℝ) :=
  -Real.exp (-x / 2) / 2

private def q_aux (x : ℝ) :=
  1 / (1 + Real.exp x)

private def base_aux (x : ℝ) :=
  x - Real.log (1 + Real.exp x)

private lemma exp_half_sq_aux (x : ℝ) :
    Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
  calc
    Real.exp x = Real.exp (x / 2 + x / 2) := by
      congr 1
      ring
    _ = Real.exp (x / 2) * Real.exp (x / 2) := Real.exp_add _ _

private lemma exp_neg_half_aux (x : ℝ) :
    Real.exp (-x / 2) = 1 / Real.exp (x / 2) := by
  rw [show -x / 2 = -(x / 2) by ring, Real.exp_neg]
  simp only [one_div]

private lemma hasDerivAt_a_aux (x : ℝ) :
    HasDerivAt a (da_aux x) x := by
  have hhalf : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x :=
    (hasDerivAt_id x).div_const 2
  have h := (Real.hasDerivAt_arctan (Real.exp (x / 2))).comp x
    ((Real.hasDerivAt_exp (x / 2)).comp x hhalf)
  have hsquare : Real.exp (x / 2) ^ 2 = Real.exp x := by
    rw [pow_two, ← exp_half_sq_aux x]
  have hcoef :
      1 / (1 + Real.exp (x / 2) ^ 2) *
          (Real.exp (x / 2) * (1 / 2)) = da_aux x := by
    unfold da_aux
    rw [← hsquare]
    have hu : 1 + Real.exp (x / 2) ^ 2 ≠ 0 := by positivity
    field_simp [hu] <;> ring
  rw [← hcoef]
  simpa only [a, Function.comp_apply] using h

private lemma hasDerivAt_exp_neg_half_aux (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-y / 2)) (de_aux x) x := by
  have hlin : HasDerivAt (fun y : ℝ => -y / 2) (-1 / 2) x :=
    (hasDerivAt_id x).neg.div_const 2
  have h := (Real.hasDerivAt_exp (-x / 2)).comp x hlin
  have hcoef : Real.exp (-x / 2) * (-1 / 2) = de_aux x := by
    unfold de_aux
    ring
  rw [← hcoef]
  simpa only [Function.comp_apply] using h

private lemma hasDerivAt_base_aux (x : ℝ) :
    HasDerivAt base_aux (q_aux x) x := by
  have hs : HasDerivAt (fun y : ℝ => 1 + Real.exp y) (Real.exp x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add (Real.hasDerivAt_exp x) using 1 <;> simp
  have hlog := (Real.hasDerivAt_log (by positivity : 1 + Real.exp x ≠ 0)).comp x hs
  have h := (hasDerivAt_id x).sub hlog
  have hcoef : 1 - (1 + Real.exp x)⁻¹ * Real.exp x = q_aux x := by
    unfold q_aux
    have hx : 1 + Real.exp x ≠ 0 := by positivity
    field_simp [hx] <;> ring
  have hfun :
      (id - (Real.log ∘ (fun y : ℝ => 1 + Real.exp y))) = base_aux := by
    funext y
    rfl
  rw [hfun] at h
  simpa only [hcoef] using h

private lemma integrand_eq_rewritten_aux (x : ℝ) :
    integrand x = rewritten x := by
  unfold integrand rewritten
  rw [exp_half_sq_aux x, exp_neg_half_aux x]
  have ht : Real.exp (x / 2) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hu : 1 + Real.exp (x / 2) * Real.exp (x / 2) ≠ 0 := by positivity
  field_simp [ht, hu] <;> ring

private lemma first_derivative_identity_aux (x : ℝ) :
    -2 * (a x * de_aux x) - 2 * (a x * da_aux x) = integrand x := by
  unfold de_aux da_aux integrand
  rw [exp_half_sq_aux x, exp_neg_half_aux x]
  have ht : Real.exp (x / 2) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hu : 1 + Real.exp (x / 2) * Real.exp (x / 2) ≠ 0 := by positivity
  field_simp [ht, hu] <;> ring

private lemma second_derivative_identity_aux (x : ℝ) :
    -2 * (de_aux x * a x + Real.exp (-x / 2) * da_aux x) +
        q_aux x - 2 * a x * da_aux x = integrand x := by
  unfold de_aux da_aux q_aux integrand
  rw [exp_half_sq_aux x, exp_neg_half_aux x]
  have ht : Real.exp (x / 2) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hu : 1 + Real.exp (x / 2) * Real.exp (x / 2) ≠ 0 := by positivity
  field_simp [ht, hu] <;> ring

private lemma hasDerivAt_primitive_aux (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have he := hasDerivAt_exp_neg_half_aux x
  have ha := hasDerivAt_a_aux x
  have hb := hasDerivAt_base_aux x
  have h := (((he.mul ha).const_mul (-2)).add hb).sub (ha.pow 2)
  have hfun : primitive = fun y =>
      -2 * (Real.exp (-y / 2) * a y) + base_aux y - a y ^ 2 := by
    funext y
    simp [primitive, base_aux]
    ring
  rw [hfun]
  convert h using 1
  rw [← second_derivative_identity_aux x]
  ring

theorem gap1 :
    Antiderivatives integrand = Antiderivatives rewritten := by
  apply Set.ext
  intro F
  change
    (∀ x, HasDerivAt F (integrand x) x) ↔
      (∀ x, HasDerivAt F (rewritten x) x)
  constructor
  · intro h x
    rw [← integrand_eq_rewritten_aux x]
    exact h x
  · intro h x
    rw [integrand_eq_rewritten_aux x]
    exact h x
theorem gap2 :
    Antiderivatives integrand = FirstReductionFamily := by
  apply Set.ext
  intro F
  change
    (∀ x, HasDerivAt F (integrand x) x) ↔
      ∃ G : ℝ → ℝ,
        (∀ x, HasDerivAt G
          (a x * deriv (fun y : ℝ => Real.exp (-y / 2)) x) x) ∧
        ∃ H : ℝ → ℝ,
          (∀ x, HasDerivAt H (a x * deriv a x) x) ∧
          ∀ x, F x = -2 * G x - 2 * H x
  constructor
  · intro hF
    have hH : ∀ x, HasDerivAt (fun y : ℝ => a y ^ 2 / 2)
        (a x * deriv a x) x := by
      intro x
      have ha := hasDerivAt_a_aux x
      convert (ha.pow 2).div_const 2 using 1
      rw [ha.deriv]
      ring
    refine ⟨fun y => -F y / 2 - a y ^ 2 / 2, ?_,
      fun y => a y ^ 2 / 2, hH, ?_⟩
    · intro x
      have hd := ((hF x).neg.div_const 2).sub (hH x)
      convert hd using 1
      rw [(hasDerivAt_exp_neg_half_aux x).deriv,
        (hasDerivAt_a_aux x).deriv, ← first_derivative_identity_aux x]
      ring
    · intro x
      ring
  · rintro ⟨G, hG, H, hH, hFG⟩
    have hfun : F = fun y => -2 * G y - 2 * H y := funext hFG
    rw [hfun]
    intro x
    have hd := ((hG x).const_mul (-2)).sub ((hH x).const_mul 2)
    convert hd using 1
    rw [(hasDerivAt_exp_neg_half_aux x).deriv,
      (hasDerivAt_a_aux x).deriv, ← first_derivative_identity_aux x]
theorem gap3 :
    Antiderivatives integrand = SecondReductionFamily := by
  apply Set.ext
  intro F
  change
    (∀ x, HasDerivAt F (integrand x) x) ↔
      ∃ G ∈ Antiderivatives (fun x => 1 / (1 + Real.exp x)),
        ∀ x, F x = -2 * Real.exp (-x / 2) * a x + G x - a x ^ 2
  constructor
  · intro hF
    refine ⟨fun y => F y + 2 * (Real.exp (-y / 2) * a y) + a y ^ 2,
      ?_, ?_⟩
    · intro x
      have he := hasDerivAt_exp_neg_half_aux x
      have ha := hasDerivAt_a_aux x
      have hd := ((hF x).add ((he.mul ha).const_mul 2)).add (ha.pow 2)
      convert hd using 1
      rw [← second_derivative_identity_aux x]
      unfold q_aux
      ring
    · intro x
      ring
  · rintro ⟨G, hG, hFG⟩
    change ∀ x, HasDerivAt G (q_aux x) x at hG
    have hfun : F = fun y =>
        -2 * Real.exp (-y / 2) * a y + G y - a y ^ 2 := funext hFG
    rw [hfun]
    intro x
    have he := hasDerivAt_exp_neg_half_aux x
    have ha := hasDerivAt_a_aux x
    have hd := (((he.mul ha).const_mul (-2)).add (hG x)).sub (ha.pow 2)
    convert hd using 1
    · funext y
      change
        -2 * Real.exp (-y / 2) * a y + G y - a y ^ 2 =
          -2 * (Real.exp (-y / 2) * a y) + G y - a y ^ 2
      ring
    · rw [← second_derivative_identity_aux x]
      ring
theorem gap4 :
    Antiderivatives integrand = ThirdReductionFamily := by
  have hq : (fun x : ℝ => 1 / (1 + Real.exp x)) =
      (fun x : ℝ => 1 - Real.exp x / (1 + Real.exp x)) := by
    funext x
    have hx : 1 + Real.exp x ≠ 0 := by positivity
    field_simp [hx] <;> ring
  rw [gap3]
  unfold SecondReductionFamily ThirdReductionFamily
  rw [hq]
theorem gap5 :
    Antiderivatives integrand = PrimitiveFamily primitive := by
  apply Set.ext
  intro F
  change
    (∀ x, HasDerivAt F (integrand x) x) ↔
      ∃ C : ℝ, ∀ x, F x = primitive x + C
  constructor
  · intro hF
    let D : ℝ → ℝ := fun y => F y - primitive y
    have hD : ∀ x, HasDerivAt D 0 x := by
      intro x
      have hd := (hF x).sub (hasDerivAt_primitive_aux x)
      convert hd using 1
      ring
    have hdiff : Differentiable ℝ D := fun x => (hD x).differentiableAt
    have hderiv : ∀ x, deriv D x = 0 := fun x => (hD x).deriv
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hc := is_const_of_deriv_eq_zero hdiff hderiv x 0
    change F x - primitive x = F 0 - primitive 0 at hc
    calc
      F x = primitive x + (F x - primitive x) := by ring
      _ = primitive x + (F 0 - primitive 0) := by rw [hc]
  · rintro ⟨C, hF⟩
    have hfun : F = fun y => primitive y + C := funext hF
    rw [hfun]
    intro x
    exact (hasDerivAt_primitive_aux x).add_const C

end
end ProofGap.Exercise2162
