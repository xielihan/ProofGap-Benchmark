import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1775

noncomputable section

def subst (x : ℝ) : ℝ := Real.exp (x / 2)
def integrand (x : ℝ) : ℝ := 1 / (Real.exp (x / 2) + Real.exp x)
def intermediate (x : ℝ) : ℝ :=
  -2 / subst x - 2 * Real.log (subst x) + 2 * Real.log (1 + subst x)
def primitive (x : ℝ) : ℝ :=
  -2 * Real.exp (-x / 2) - x + 2 * Real.log (1 + Real.exp (x / 2))
def IsAntiderivative (F f : ℝ → ℝ) : Prop := ∀ x, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) := {F | IsAntiderivative F f}
def Translates (P : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x, F x = P x + C}

private theorem subst_hasDerivAt (x : ℝ) :
    HasDerivAt subst (subst x / 2) x := by
  simpa [subst, div_eq_mul_inv] using
    (Real.hasDerivAt_exp (x / 2)).comp x
      ((hasDerivAt_id x).div_const 2)

private theorem value_eq_zero_of_hasDerivAt_zero
    (f : ℝ → ℝ) (h : ∀ x, HasDerivAt f 0 x) (x : ℝ) :
    f x = f 0 := by
  have hf : Differentiable ℝ f := fun z => (h z).differentiableAt
  have hd : ∀ z, deriv f z = 0 := fun z => (h z).deriv
  exact is_const_of_deriv_eq_zero hf hd x 0

theorem gap1 (x : ℝ) :
    Real.exp x = subst x ^ 2 := by
  unfold subst
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

theorem gap2 (x : ℝ) :
    1 = 2 * deriv subst x / subst x := by
  have hs0 : subst x ≠ 0 := by
    simp [subst]
  rw [(subst_hasDerivAt x).deriv]
  field_simp [hs0]

theorem gap3 (x : ℝ) :
    integrand x =
      2 / (subst x ^ 2 * (1 + subst x)) * deriv subst x := by
  unfold integrand
  rw [gap1 x]
  change 1 / (subst x + subst x ^ 2) =
    2 / (subst x ^ 2 * (1 + subst x)) * deriv subst x
  have hderiv : deriv subst x = subst x / 2 :=
    (subst_hasDerivAt x).deriv
  rw [hderiv]
  have hspos : 0 < subst x := Real.exp_pos _
  have hs0 : subst x ≠ 0 := ne_of_gt hspos
  have h1 : 1 + subst x ≠ 0 :=
    ne_of_gt (add_pos zero_lt_one hspos)
  have hsum : subst x + subst x ^ 2 ≠ 0 := by
    rw [show subst x + subst x ^ 2 = subst x * (1 + subst x) by ring]
    exact mul_ne_zero hs0 h1
  field_simp [hs0, h1, hsum]

theorem gap4 (x : ℝ) :
    1 / (subst x ^ 2 * (1 + subst x)) =
      (1 - subst x) / subst x ^ 2 + 1 / (1 + subst x) := by
  have hs0 : subst x ≠ 0 := by
    simp [subst]
  have hspos : 0 < subst x := by
    exact Real.exp_pos _
  have h1 : 1 + subst x ≠ 0 := by
    exact ne_of_gt (add_pos zero_lt_one hspos)
  field_simp [hs0, h1]
  ring

theorem gap5 (x : ℝ) :
    HasDerivAt intermediate (integrand x) x := by
  have hs := subst_hasDerivAt x
  have hs0 : subst x ≠ 0 := by
    simp [subst]
  have hspos : 0 < subst x := by
    exact Real.exp_pos _
  have h1 : 1 + subst x ≠ 0 := by
    exact ne_of_gt (add_pos zero_lt_one hspos)
  have hdiv :
      HasDerivAt (fun y => -2 / subst y)
        (2 * (subst x / 2) / subst x ^ 2) x := by
    convert (hasDerivAt_const x (-2 : ℝ)).div hs hs0 using 1 <;> ring
  have hlogAt :
      HasDerivAt Real.log ((subst x)⁻¹) (subst x) :=
    Real.hasDerivAt_log hs0
  have hlog :
      HasDerivAt (fun y => Real.log (subst y))
        ((subst x)⁻¹ * (subst x / 2)) x := by
    simpa only [Function.comp_apply] using hlogAt.comp x hs
  have hadd :
      HasDerivAt (fun y => 1 + subst y) (0 + subst x / 2) x :=
    (hasDerivAt_const x 1).add hs
  have hlogOneAt :
      HasDerivAt Real.log ((1 + subst x)⁻¹) (1 + subst x) :=
    Real.hasDerivAt_log h1
  have hlogOne :
      HasDerivAt (fun y => Real.log (1 + subst y))
        ((1 + subst x)⁻¹ * (0 + subst x / 2)) x := by
    simpa only [Function.comp_apply] using hlogOneAt.comp x hadd
  let D :=
    (2 * (subst x / 2) / subst x ^ 2 -
      2 * ((subst x)⁻¹ * (subst x / 2))) +
      2 * ((1 + subst x)⁻¹ * (0 + subst x / 2))
  have htotal : HasDerivAt intermediate D x := by
    dsimp [D]
    unfold intermediate
    exact (hdiv.sub (hlog.const_mul 2)).add (hlogOne.const_mul 2)
  have hD : D = integrand x := by
    dsimp [D]
    rw [gap3 x, hs.deriv]
    field_simp [hs0, h1]
    ring
  rw [← hD]
  exact htotal

theorem gap6 (x : ℝ) :
    intermediate x = primitive x := by
  unfold intermediate primitive subst
  rw [Real.log_exp]
  have hneg : Real.exp (-x / 2) = (Real.exp (x / 2))⁻¹ := by
    rw [show -x / 2 = -(x / 2) by ring, Real.exp_neg]
  rw [hneg]
  simp only [div_eq_mul_inv]
  ring

theorem gap7 :
    Family integrand = Translates primitive := by
  have hip : intermediate = primitive := funext gap6
  have hp : IsAntiderivative primitive integrand := by
    intro x
    simpa only [hip] using gap5 x
  ext F
  constructor
  · intro hF
    change IsAntiderivative F integrand at hF
    change ∃ C, ∀ x, F x = primitive x + C
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hz : ∀ y, HasDerivAt (fun z => F z - primitive z) 0 y := by
      intro y
      simpa using (hF y).sub (hp y)
    have heq := value_eq_zero_of_hasDerivAt_zero
      (fun z => F z - primitive z) hz x
    calc
      F x = primitive x + (F x - primitive x) := by ring
      _ = primitive x + (F 0 - primitive 0) := by rw [heq]
  · rintro ⟨C, hC⟩
    change IsAntiderivative F integrand
    have hfun : F = fun x => primitive x + C := funext hC
    subst F
    intro x
    exact (hp x).add_const C

end

end ProofGap.Exercise1775
