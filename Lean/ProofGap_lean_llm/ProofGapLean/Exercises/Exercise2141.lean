import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2141

noncomputable section

def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}
def integrand (x : ℝ) := x * Real.log (4 + x ^ 4)
def SubstitutionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ,
    (∀ x,
      HasDerivAt G
        (Real.log (4 + x ^ 4) * deriv (fun y : ℝ => y ^ 2) x) x) ∧
    ∀ x, F x = 1 / 2 * G x}
def rationalIntegrand (x : ℝ) := x ^ 5 / (4 + x ^ 4)
def ReductionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives rationalIntegrand,
    ∀ x, F x = 1 / 2 * x ^ 2 * Real.log (4 + x ^ 4) - 2 * G x}
def simplifiedIntegrand (x : ℝ) := x - 4 * x / (4 + x ^ 4)
def SimplifiedFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives simplifiedIntegrand,
    ∀ x, F x = 1 / 2 * x ^ 2 * Real.log (4 + x ^ 4) - 2 * G x}
def primitive (x : ℝ) :=
  1 / 2 * x ^ 2 * Real.log (4 + x ^ 4) -
    x ^ 2 + 2 * Real.arctan (x ^ 2 / 2)

private theorem hasDerivAt_logQuartic (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.log (4 + y ^ 4))
      (4 * x ^ 3 / (4 + x ^ 4)) x := by
  have hpos : 0 < 4 + x ^ 4 := by positivity
  have hinner : HasDerivAt (fun y : ℝ => 4 + y ^ 4) (4 * x ^ 3) x := by
    convert (hasDerivAt_const x (4 : ℝ)).add ((hasDerivAt_id x).pow 4) using 1 <;>
      simp [id] <;> ring
  convert (Real.hasDerivAt_log hpos.ne').comp x hinner using 1 <;>
    simp [Function.comp_def, id, div_eq_mul_inv] <;> ring

private theorem hasDerivAt_halfSqLog (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => 1 / 2 * y ^ 2 * Real.log (4 + y ^ 4))
      (x * Real.log (4 + x ^ 4) + 2 * x ^ 5 / (4 + x ^ 4)) x := by
  have hsq : HasDerivAt (fun y : ℝ => 1 / 2 * y ^ 2) x x := by
    convert ((hasDerivAt_id x).pow 2).const_mul (1 / 2) using 1 <;>
      simp [id] <;> ring
  convert hsq.mul (hasDerivAt_logQuartic x) using 1 <;>
    simp [Function.comp_def, id, div_eq_mul_inv] <;> ring

private theorem hasDerivAt_primitive (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  unfold primitive integrand
  have hpos : 0 < 4 + x ^ 4 := by positivity
  have hinner : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
    convert ((hasDerivAt_id x).pow 2).div_const 2 using 1 <;>
      simp [id] <;> ring
  have ha := (Real.hasDerivAt_arctan (x ^ 2 / 2)).comp x hinner
  have hatpos : 0 < 1 + (x ^ 2 / 2) ^ 2 := by positivity
  convert
    ((hasDerivAt_halfSqLog x).sub ((hasDerivAt_id x).pow 2)).add
      (ha.const_mul 2) using 1 <;>
    simp [Function.comp_def, id] <;>
    field_simp [hpos.ne', hatpos.ne'] <;>
    ring

private theorem antiderivatives_eq_primitiveFamily_of_hasDeriv
    (f p : ℝ → ℝ) (hp : ∀ x, HasDerivAt p (f x) x) :
    Antiderivatives f = PrimitiveFamily p := by
  ext F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (f x) x at hF
    change ∃ C : ℝ, ∀ x, F x = p x + C
    have hq : ∀ y, HasDerivAt (fun z => F z - p z) 0 y := by
      intro y
      convert (hF y).sub (hp y) using 1 <;> ring
    have hdiff : Differentiable ℝ (fun z => F z - p z) :=
      fun y => (hq y).differentiableAt
    have hderiv : ∀ y, deriv (fun z => F z - p z) y = 0 :=
      fun y => (hq y).deriv
    refine ⟨F 0 - p 0, ?_⟩
    intro x
    have hc := is_const_of_deriv_eq_zero hdiff hderiv x 0
    linarith
  · intro hF
    change ∃ C : ℝ, ∀ x, F x = p x + C at hF
    rcases hF with ⟨C, hC⟩
    change ∀ x, HasDerivAt F (f x) x
    have hfun : F = fun y => p y + C := funext hC
    rw [hfun]
    intro x
    exact (hp x).add_const C

private theorem antiderivatives_eq_reduction :
    Antiderivatives integrand = ReductionFamily := by
  ext F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (integrand x) x at hF
    change ∃ G : ℝ → ℝ,
      (∀ x, HasDerivAt G (rationalIntegrand x) x) ∧
      ∀ x, F x = 1 / 2 * x ^ 2 * Real.log (4 + x ^ 4) - 2 * G x
    let G : ℝ → ℝ := fun y =>
      1 / 2 * (1 / 2 * y ^ 2 * Real.log (4 + y ^ 4)) - 1 / 2 * F y
    refine ⟨G, ?_, ?_⟩
    · intro x
      have hpos : 0 < 4 + x ^ 4 := by positivity
      dsimp [G]
      convert
        ((hasDerivAt_halfSqLog x).const_mul (1 / 2)).sub
          ((hF x).const_mul (1 / 2)) using 1
      unfold rationalIntegrand integrand
      field_simp [hpos.ne']
      ring
    · intro x
      dsimp [G]
      ring
  · intro hR
    change ∃ G : ℝ → ℝ,
      (∀ x, HasDerivAt G (rationalIntegrand x) x) ∧
      ∀ x, F x = 1 / 2 * x ^ 2 * Real.log (4 + x ^ 4) - 2 * G x at hR
    rcases hR with ⟨G, hG, hFG⟩
    change ∀ x, HasDerivAt F (integrand x) x
    have hfun : F = fun y =>
        1 / 2 * y ^ 2 * Real.log (4 + y ^ 4) - 2 * G y := funext hFG
    rw [hfun]
    intro x
    convert (hasDerivAt_halfSqLog x).sub ((hG x).const_mul 2) using 1
    unfold rationalIntegrand integrand
    ring

theorem gap1 :
    Antiderivatives integrand = SubstitutionFamily := by
  ext F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (integrand x) x at hF
    change ∃ G : ℝ → ℝ,
      (∀ x, HasDerivAt G
        (Real.log (4 + x ^ 4) * deriv (fun y : ℝ => y ^ 2) x) x) ∧
      ∀ x, F x = 1 / 2 * G x
    refine ⟨fun x => 2 * F x, ?_, ?_⟩
    · intro x
      have hd : deriv (fun y : ℝ => y ^ 2) x = 2 * x := by
        simpa using (((hasDerivAt_id x).pow 2).deriv)
      convert (hF x).const_mul 2 using 1
      rw [hd]
      unfold integrand
      ring
    · intro x
      ring
  · intro hS
    change ∃ G : ℝ → ℝ,
      (∀ x, HasDerivAt G
        (Real.log (4 + x ^ 4) * deriv (fun y : ℝ => y ^ 2) x) x) ∧
      ∀ x, F x = 1 / 2 * G x at hS
    rcases hS with ⟨G, hG, hFG⟩
    change ∀ x, HasDerivAt F (integrand x) x
    have hfun : F = fun y => 1 / 2 * G y := funext hFG
    rw [hfun]
    intro x
    have hd : deriv (fun y : ℝ => y ^ 2) x = 2 * x := by
      simpa using (((hasDerivAt_id x).pow 2).deriv)
    convert (hG x).const_mul (1 / 2) using 1
    rw [hd]
    unfold integrand
    ring
theorem gap2 :
    SubstitutionFamily = ReductionFamily := by
  exact gap1.symm.trans antiderivatives_eq_reduction
theorem gap3 :
    Antiderivatives integrand = ReductionFamily := by
  exact gap1.trans gap2
theorem gap4 :
    Antiderivatives integrand = SimplifiedFamily := by
  have hrs : rationalIntegrand = simplifiedIntegrand := by
    funext x
    unfold rationalIntegrand simplifiedIntegrand
    have hne : 4 + x ^ 4 ≠ 0 := by positivity
    field_simp [hne]
    ring
  rw [gap3]
  unfold ReductionFamily SimplifiedFamily
  rw [hrs]
theorem gap5 :
    SimplifiedFamily = PrimitiveFamily primitive := by
  rw [← gap4]
  exact antiderivatives_eq_primitiveFamily_of_hasDeriv
    integrand primitive hasDerivAt_primitive
theorem gap6 :
    Antiderivatives integrand = PrimitiveFamily primitive := by
  exact gap4.trans gap5

end
end ProofGap.Exercise2141
