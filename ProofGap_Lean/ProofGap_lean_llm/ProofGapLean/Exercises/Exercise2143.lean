import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2143

noncomputable section

def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}
def s (x : ℝ) := Real.sqrt (1 + x ^ 2)
def integrand (x : ℝ) := x * Real.log (1 + s x) / s x
def substitutionIntegrand (x : ℝ) :=
  Real.log (1 + s x) * deriv (fun y : ℝ => 1 + s y) x
def ByPartsFamily : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ,
    (∀ x, HasDerivAt G (x * deriv (fun y : ℝ => y) x / s x) x) ∧
    ∀ x, F x = (1 + s x) * Real.log (1 + s x) - G x}
def primitive (x : ℝ) :=
  (1 + s x) * Real.log (1 + s x) - s x

private theorem s_pos (x : ℝ) : 0 < s x := by
  unfold s
  apply Real.sqrt_pos.2
  nlinarith [sq_nonneg x]

private theorem hasDerivAt_s (x : ℝ) :
    HasDerivAt s (x / s x) x := by
  have hx : 0 < 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hinner :
      HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2) using 1 <;>
      simp [id] <;> ring
  unfold s
  convert (Real.hasDerivAt_sqrt (ne_of_gt hx)).comp x hinner using 1
  · field_simp [ne_of_gt (Real.sqrt_pos.2 hx)]
    <;> ring

private theorem hasDerivAt_one_add_s (x : ℝ) :
    HasDerivAt (fun y : ℝ => 1 + s y) (x / s x) x := by
  convert (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_s x) using 1 <;>
    ring

private theorem deriv_id_value (x : ℝ) :
    deriv (fun y : ℝ => y) x = 1 := by
  simpa using (hasDerivAt_id x).deriv

private theorem integrand_eq_substitutionIntegrand (x : ℝ) :
    integrand x = substitutionIntegrand x := by
  unfold integrand substitutionIntegrand
  rw [(hasDerivAt_one_add_s x).deriv]
  ring

private theorem hasDerivAt_primitive (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have hs := hasDerivAt_s x
  have ht := hasDerivAt_one_add_s x
  have htpos : 0 < 1 + s x := by
    nlinarith [s_pos x]
  have hlog :
      HasDerivAt (fun y : ℝ => Real.log (1 + s y))
        ((1 + s x)⁻¹ * (x / s x)) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_log (ne_of_gt htpos)).comp x ht
  have hprod := ht.mul hlog
  unfold primitive integrand
  convert hprod.sub hs using 1
  · field_simp [ne_of_gt (s_pos x), ne_of_gt htpos]
    <;> ring

private theorem functions_differ_by_constant
    {f g d : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (d x) x)
    (hg : ∀ x, HasDerivAt g (d x) x) :
    ∃ C : ℝ, ∀ x, f x = g x + C := by
  let h := fun x => f x - g x
  have hh : ∀ x, HasDerivAt h 0 x := by
    intro x
    simpa [h] using (hf x).sub (hg x)
  have hdiff : Differentiable ℝ h := fun x => (hh x).differentiableAt
  have hzero : ∀ x, deriv h x = 0 := fun x => (hh x).deriv
  refine ⟨f 0 - g 0, ?_⟩
  intro x
  have hc : h x = h 0 :=
    is_const_of_deriv_eq_zero hdiff hzero x 0
  dsimp [h] at hc
  linarith

theorem gap1 :
    Antiderivatives integrand = Antiderivatives substitutionIntegrand := by
  ext F
  simp only [Antiderivatives, Set.mem_setOf_eq,
    integrand_eq_substitutionIntegrand]
theorem gap2 :
    Antiderivatives integrand = ByPartsFamily := by
  ext F
  simp only [Antiderivatives, ByPartsFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    rcases functions_differ_by_constant hF hasDerivAt_primitive with ⟨C, hC⟩
    refine ⟨fun x => s x - C, ?_, ?_⟩
    · intro x
      simpa only [deriv_id_value, mul_one] using
        (hasDerivAt_s x).sub_const C
    · intro x
      rw [hC x]
      unfold primitive
      ring
  · rintro ⟨G, hG, hFG⟩
    have hG' : ∀ x, HasDerivAt G (x / s x) x := by
      intro x
      simpa only [deriv_id_value, mul_one] using hG x
    rcases functions_differ_by_constant hG' hasDerivAt_s with ⟨C, hGC⟩
    have hfun : F = fun x => primitive x - C := by
      funext x
      rw [hFG x, hGC x]
      unfold primitive
      ring
    rw [hfun]
    intro x
    exact (hasDerivAt_primitive x).sub_const C
theorem gap3 :
    ByPartsFamily = PrimitiveFamily primitive := by
  ext F
  simp only [ByPartsFamily, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨G, hG, hFG⟩
    have hG' : ∀ x, HasDerivAt G (x / s x) x := by
      intro x
      simpa only [deriv_id_value, mul_one] using hG x
    rcases functions_differ_by_constant hG' hasDerivAt_s with ⟨C, hGC⟩
    refine ⟨-C, ?_⟩
    intro x
    rw [hFG x, hGC x]
    unfold primitive
    ring
  · rintro ⟨C, hFC⟩
    refine ⟨fun x => s x - C, ?_, ?_⟩
    · intro x
      simpa only [deriv_id_value, mul_one] using
        (hasDerivAt_s x).sub_const C
    · intro x
      rw [hFC x]
      unfold primitive
      ring
theorem gap4 :
    Antiderivatives integrand = PrimitiveFamily primitive := by
  exact gap2.trans gap3

end
end ProofGap.Exercise2143
