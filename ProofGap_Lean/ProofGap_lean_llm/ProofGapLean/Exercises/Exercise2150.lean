import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise2150

noncomputable section

def branch : Set ℝ := Set.Ioi 1
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}
def l (x : ℝ) := Real.log |(x - 1) / (x + 1)|
def integrand (a b x : ℝ) :=
  (a * x ^ 2 + b) / (x ^ 2 - 1) * l x
def rewritten (a b x : ℝ) :=
  (a + (a + b) / (x ^ 2 - 1)) * l x
def ReductionFamily (a b : ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn (fun x => 2 * x / (x ^ 2 - 1)),
    ∃ H : ℝ → ℝ,
      (∀ x ∈ branch, HasDerivAt H (l x * deriv l x) x) ∧
    ∃ C : ℝ, ∀ x ∈ branch,
      F x = a * x * l x - a * G x + (a + b) / 2 * H x + C}
def primitive (a b x : ℝ) :=
  a * (x * l x - Real.log |x ^ 2 - 1|) +
    (a + b) / 4 * l x ^ 2

private theorem branch_gt_one {x : ℝ} (hx : x ∈ branch) : 1 < x := by
  simpa only [branch, Set.mem_Ioi] using hx

private theorem hasDerivAt_l {x : ℝ} (hx : x ∈ branch) :
    HasDerivAt l (2 / (x ^ 2 - 1)) x := by
  have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (branch_gt_one hx))
  have hxp : x + 1 ≠ 0 := by linarith [branch_gt_one hx]
  have hq : x ^ 2 - 1 ≠ 0 := by
    have h := branch_gt_one hx
    nlinarith [sq_nonneg (x - 1)]
  have hnum : HasDerivAt (fun y : ℝ => y - 1) 1 x := by
    simpa using (hasDerivAt_id x).sub_const 1
  have hden : HasDerivAt (fun y : ℝ => y + 1) 1 x := by
    simpa using (hasDerivAt_id x).add_const 1
  have hquot := hnum.div hden hxp
  have hlog :=
    (Real.hasDerivAt_log (div_ne_zero hx1 hxp)).comp x hquot
  unfold l
  simpa only [Function.comp_def, Real.log_abs] using (by
    convert hlog using 1 <;> field_simp [hx1, hxp, hq] <;> ring)

private theorem hasDerivAt_logQuadratic {x : ℝ} (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => Real.log |y ^ 2 - 1|)
      (2 * x / (x ^ 2 - 1)) x := by
  have hq : x ^ 2 - 1 ≠ 0 := by
    have h := branch_gt_one hx
    nlinarith [sq_nonneg (x - 1)]
  have hinner : HasDerivAt (fun y : ℝ => y ^ 2 - 1) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).sub_const 1 using 1 <;>
      simp only [id_eq] <;> ring
  have hlog := (Real.hasDerivAt_log hq).comp x hinner
  simpa only [Function.comp_def, Real.log_abs] using (by
    convert hlog using 1 <;> field_simp [hq] <;> ring)

private theorem integrand_eq_rewritten (a b x : ℝ) (hx : x ∈ branch) :
    integrand a b x = rewritten a b x := by
  have hq : x ^ 2 - 1 ≠ 0 := by
    have h := branch_gt_one hx
    nlinarith [sq_nonneg (x - 1)]
  unfold integrand rewritten
  field_simp [hq]
  ring

private theorem hasDerivAt_primitive (a b x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (primitive a b) (integrand a b x) x := by
  have hq : x ^ 2 - 1 ≠ 0 := by
    have h := branch_gt_one hx
    nlinarith [sq_nonneg (x - 1)]
  have hl := hasDerivAt_l hx
  have hxl := (hasDerivAt_id x).mul hl
  have hfirst := hxl.sub (hasDerivAt_logQuadratic hx)
  have hsquare := hl.pow 2
  have hraw :=
    (hfirst.const_mul a).add (hsquare.const_mul ((a + b) / 4))
  simp only [id_eq, one_mul, Nat.cast_ofNat, pow_one] at hraw
  unfold primitive
  convert hraw using 1
  unfold integrand
  field_simp [hq]
  ring

private theorem antiderivatives_eq_primitiveFamily
    {f p : ℝ → ℝ} (hp : ∀ x ∈ branch, HasDerivAt p (f x) x) :
    AntiderivativesOn f = PrimitiveFamily p := by
  ext F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    have htwo : (2 : ℝ) ∈ branch := by norm_num [branch]
    have hzero : ∀ x ∈ branch,
        HasDerivAt (fun y => F y - p y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (hp x hx)
    have hdiff : DifferentiableOn ℝ (fun y => F y - p y) branch :=
      fun x hx => (hzero x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ branch, deriv (fun y => F y - p y) x = 0 :=
      fun x hx => (hzero x hx).deriv
    refine ⟨F 2 - p 2, fun x hx => ?_⟩
    have hdiff' :
        DifferentiableOn ℝ (fun y => F y - p y) (Set.Ioi 1) := by
      simpa only [branch] using hdiff
    have hderiv' :
        ∀ y ∈ Set.Ioi (1 : ℝ), deriv (fun z => F z - p z) y = 0 := by
      simpa only [branch] using hderiv
    have hx' : x ∈ Set.Ioi (1 : ℝ) := by simpa only [branch] using hx
    have htwo' : (2 : ℝ) ∈ Set.Ioi (1 : ℝ) := by norm_num
    have hconst : F x - p x = F 2 - p 2 :=
      isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
        hdiff' hderiv' hx' htwo'
    linarith
  · rintro ⟨C, hFC⟩ x hx
    have heq : F =ᶠ[nhds x] fun y => p y + C :=
      Filter.Eventually.mono
        (by simpa only [branch] using isOpen_Ioi.mem_nhds hx)
        (fun y hy => hFC y (by simpa only [branch] using hy))
    exact ((hp x hx).add_const C).congr_of_eventuallyEq heq

theorem gap1 (a b : ℝ) :
    AntiderivativesOn (integrand a b) =
      AntiderivativesOn (rewritten a b) := by
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor <;> intro hF x hx
  · simpa only [integrand_eq_rewritten a b x hx] using hF x hx
  · simpa only [integrand_eq_rewritten a b x hx] using hF x hx

private theorem hasDerivAt_half_l_sq {x : ℝ} (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => (1 / 2 : ℝ) * l y ^ 2)
      (l x * deriv l x) x := by
  have hl := hasDerivAt_l hx
  have hld : deriv l x = 2 / (x ^ 2 - 1) := hl.deriv
  convert (hl.pow 2).const_mul (1 / 2 : ℝ) using 1 <;>
    simp only [Nat.cast_ofNat, pow_one] <;>
    rw [hld] <;>
    ring

theorem gap2 (a b : ℝ) :
    AntiderivativesOn (integrand a b) = ReductionFamily a b := by
  ext F
  constructor
  · intro hF
    have hFfamily : F ∈ PrimitiveFamily (primitive a b) := by
      rw [← antiderivatives_eq_primitiveFamily (hasDerivAt_primitive a b)]
      exact hF
    rcases hFfamily with ⟨C, hFC⟩
    refine ⟨(fun x => Real.log |x ^ 2 - 1|), ?_, ?_⟩
    · exact fun x hx => hasDerivAt_logQuadratic hx
    refine ⟨(fun x => (1 / 2 : ℝ) * l x ^ 2), ?_, C, ?_⟩
    · exact fun x hx => hasDerivAt_half_l_sq hx
    intro x hx
    rw [hFC x hx]
    unfold primitive
    ring
  · rintro ⟨G, hG, H, hH, C, hF⟩
    have hGfamily :
        G ∈ PrimitiveFamily (fun x => Real.log |x ^ 2 - 1|) := by
      rw [← antiderivatives_eq_primitiveFamily
        (fun x hx => hasDerivAt_logQuadratic hx)]
      exact hG
    have hHfamily :
        H ∈ PrimitiveFamily (fun x => (1 / 2 : ℝ) * l x ^ 2) := by
      rw [← antiderivatives_eq_primitiveFamily
        (fun x hx => hasDerivAt_half_l_sq hx)]
      exact hH
    rcases hGfamily with ⟨CG, hGC⟩
    rcases hHfamily with ⟨CH, hHC⟩
    rw [antiderivatives_eq_primitiveFamily (hasDerivAt_primitive a b)]
    refine ⟨C - a * CG + (a + b) / 2 * CH, ?_⟩
    intro x hx
    rw [hF x hx, hGC x hx, hHC x hx]
    unfold primitive
    ring
theorem gap3 (a b : ℝ) :
    AntiderivativesOn (integrand a b) =
      PrimitiveFamily (primitive a b) := by
  exact antiderivatives_eq_primitiveFamily (hasDerivAt_primitive a b)

end
end ProofGap.Exercise2150
