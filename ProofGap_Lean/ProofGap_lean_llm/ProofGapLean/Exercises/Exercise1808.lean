import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1808

noncomputable section

def branch : Set ℝ := Set.Ioo (-1 : ℝ) 1
def logRatio (x : ℝ) := Real.log ((1 + x) / (1 - x))
def integrand (x : ℝ) := x * logRatio x
def scaledIntegrand (x : ℝ) := logRatio x * deriv (fun t : ℝ => t ^ 2) x
def residual (x : ℝ) := x ^ 2 / (1 - x ^ 2)
def rewrittenResidual (x : ℝ) := 1 - 1 / (1 - x ^ 2)
def boundary (x : ℝ) := x ^ 2 / 2 * logRatio x
def primitive (x : ℝ) :=
  x - (1 - x ^ 2) / 2 * logRatio x
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def HalfFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn scaledIntegrand,
    ∀ x ∈ branch, F x = (1 / 2 : ℝ) * G x}
def ByPartsFamily (c : ℝ) (r : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn r, ∀ x ∈ branch, F x = boundary x + c * G x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private theorem branch_open : IsOpen branch := by
  simpa [branch] using
    (isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) 1))

private theorem zero_mem_branch : (0 : ℝ) ∈ branch := by
  norm_num [branch]

private theorem one_sub_sq_pos {x : ℝ} (hx : x ∈ branch) :
    0 < 1 - x ^ 2 := by
  change -1 < x ∧ x < 1 at hx
  have h₁ : 0 < 1 - x := by linarith
  have h₂ : 0 < 1 + x := by linarith
  nlinarith [mul_pos h₁ h₂]

private theorem hasDerivAt_sq (x : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
  convert (hasDerivAt_id x).pow 2 using 1 <;> simp [id] <;> ring

private theorem scaledIntegrand_eq (x : ℝ) :
    scaledIntegrand x = 2 * integrand x := by
  rw [scaledIntegrand, (hasDerivAt_sq x).deriv]
  simp only [integrand]
  ring

private theorem hasDerivAt_logRatio {x : ℝ} (hx : x ∈ branch) :
    HasDerivAt logRatio (2 / (1 - x ^ 2)) x := by
  have hx' : -1 < x ∧ x < 1 := by simpa [branch] using hx
  have hxm : 1 - x ≠ 0 := by linarith [hx'.2]
  have hxp : 1 + x ≠ 0 := by linarith [hx'.1]
  have hq : (1 + x) / (1 - x) ≠ 0 := div_ne_zero hxp hxm
  have hn : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    simpa using (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
  have hd : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
  have hquot := hn.div hd hxm
  change HasDerivAt (fun y : ℝ => Real.log ((1 + y) / (1 - y)))
    (2 / (1 - x ^ 2)) x
  convert (Real.hasDerivAt_log hq).comp x hquot using 1
  field_simp [hxm, hxp, ne_of_gt (one_sub_sq_pos hx)] <;> ring

private theorem hasDerivAt_boundary {x : ℝ} (hx : x ∈ branch) :
    HasDerivAt boundary (integrand x + residual x) x := by
  have hs : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
    convert (hasDerivAt_sq x).div_const 2 using 1 <;> norm_num <;> ring
  have hne : 1 - x ^ 2 ≠ 0 := ne_of_gt (one_sub_sq_pos hx)
  change HasDerivAt (fun y : ℝ => y ^ 2 / 2 * logRatio y)
    (integrand x + residual x) x
  convert hs.mul (hasDerivAt_logRatio hx) using 1
  simp only [integrand, residual]
  field_simp [hne] <;> ring

private theorem rewrittenResidual_eq_neg_residual {x : ℝ} (hx : x ∈ branch) :
    rewrittenResidual x = -residual x := by
  have hne : 1 - x ^ 2 ≠ 0 := ne_of_gt (one_sub_sq_pos hx)
  unfold rewrittenResidual residual
  field_simp [hne]
  ring

private def correction (x : ℝ) := x - (1 / 2 : ℝ) * logRatio x

private theorem hasDerivAt_correction {x : ℝ} (hx : x ∈ branch) :
    HasDerivAt correction (rewrittenResidual x) x := by
  have h := (hasDerivAt_id x).sub
    ((hasDerivAt_logRatio hx).const_mul (1 / 2 : ℝ))
  have hne : 1 - x ^ 2 ≠ 0 := ne_of_gt (one_sub_sq_pos hx)
  change HasDerivAt (fun y : ℝ => y - (1 / 2 : ℝ) * logRatio y)
    (rewrittenResidual x) x
  convert h using 1
  simp only [rewrittenResidual]
  field_simp [hne] <;> ring

private theorem hasDerivAt_primitive {x : ℝ} (hx : x ∈ branch) :
    HasDerivAt primitive (integrand x) x := by
  have h := (hasDerivAt_boundary hx).add (hasDerivAt_correction hx)
  convert h using 1
  · funext y
    simp only [Pi.add_apply, primitive, boundary, correction]
    ring
  · rw [rewrittenResidual_eq_neg_residual hx]
    ring

private theorem hasDerivAt_of_eqOn_branch
    {F G : ℝ → ℝ} {d x : ℝ} (hx : x ∈ branch)
    (hG : HasDerivAt G d x)
    (hEq : ∀ y ∈ branch, F y = G y) : HasDerivAt F d x := by
  apply hG.congr_of_eventuallyEq
  filter_upwards [branch_open.mem_nhds hx] with y hy
  exact hEq y hy

private theorem antiderivative_eq_add_const
    {f F P : ℝ → ℝ} (hF : F ∈ AntiderivativesOn f)
    (hP : P ∈ AntiderivativesOn f) :
    ∃ C : ℝ, ∀ x ∈ branch, F x = P x + C := by
  change (∀ x ∈ branch, HasDerivAt F (f x) x) at hF
  change (∀ x ∈ branch, HasDerivAt P (f x) x) at hP
  let D : ℝ → ℝ := fun x => F x - P x
  have hD : ∀ x ∈ branch, HasDerivAt D 0 x := by
    intro x hx
    simpa [D] using (hF x hx).sub (hP x hx)
  have hdiff : DifferentiableOn ℝ D branch := by
    intro x hx
    exact (hD x hx).differentiableAt.differentiableWithinAt
  have hzero : ∀ x ∈ branch, deriv D x = 0 := by
    intro x hx
    exact (hD x hx).deriv
  have hconv : Convex ℝ branch := by
    simpa [branch] using (convex_Ioo (-1 : ℝ) 1)
  have hpre : IsPreconnected branch := hconv.isPreconnected
  refine ⟨F 0 - P 0, ?_⟩
  intro x hx
  have heq : D x = D 0 :=
    branch_open.is_const_of_deriv_eq_zero hpre hdiff hzero hx zero_mem_branch
  dsimp [D] at heq
  linarith

theorem gap1 :
    AntiderivativesOn integrand = HalfFamily := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change ∃ G ∈ AntiderivativesOn scaledIntegrand,
      ∀ x ∈ branch, F x = (1 / 2 : ℝ) * G x
    refine ⟨fun x => 2 * F x, ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt (fun x => 2 * F x) (scaledIntegrand x) x
      intro x hx
      simpa [scaledIntegrand_eq] using (hF x hx).const_mul 2
    · intro x hx
      ring
  · rintro ⟨G, hG, hEq⟩
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    change ∀ x ∈ branch, HasDerivAt G (scaledIntegrand x) x at hG
    intro x hx
    have hd : HasDerivAt (fun y => (1 / 2 : ℝ) * G y) (integrand x) x := by
      convert (hG x hx).const_mul (1 / 2 : ℝ) using 1
      rw [scaledIntegrand_eq]
      ring
    exact hasDerivAt_of_eqOn_branch hx hd hEq
theorem gap2 :
    HalfFamily = ByPartsFamily (-1) residual := by
  ext F
  constructor
  · intro h
    have hF : F ∈ AntiderivativesOn integrand := by
      rw [gap1]
      exact h
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change ∃ G ∈ AntiderivativesOn residual,
      ∀ x ∈ branch, F x = boundary x + (-1 : ℝ) * G x
    refine ⟨fun x => boundary x - F x, ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt (fun x => boundary x - F x) (residual x) x
      intro x hx
      convert (hasDerivAt_boundary hx).sub (hF x hx) using 1 <;> ring
    · intro x hx
      ring
  · rintro ⟨G, hG, hEq⟩
    change ∀ x ∈ branch, HasDerivAt G (residual x) x at hG
    have hF : F ∈ AntiderivativesOn integrand := by
      change ∀ x ∈ branch, HasDerivAt F (integrand x) x
      intro x hx
      have hd : HasDerivAt (fun y => boundary y - G y) (integrand x) x := by
        convert (hasDerivAt_boundary hx).sub (hG x hx) using 1 <;> ring
      apply hasDerivAt_of_eqOn_branch hx hd
      intro y hy
      simpa using hEq y hy
    rw [← gap1]
    exact hF
theorem gap3 :
    AntiderivativesOn integrand = ByPartsFamily (-1) residual := by
  calc
    AntiderivativesOn integrand = HalfFamily := gap1
    _ = ByPartsFamily (-1) residual := gap2
theorem gap4 :
    AntiderivativesOn integrand = ByPartsFamily 1 rewrittenResidual := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change ∃ G ∈ AntiderivativesOn rewrittenResidual,
      ∀ x ∈ branch, F x = boundary x + (1 : ℝ) * G x
    refine ⟨fun x => F x - boundary x, ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt (fun x => F x - boundary x) (rewrittenResidual x) x
      intro x hx
      convert (hF x hx).sub (hasDerivAt_boundary hx) using 1
      rw [rewrittenResidual_eq_neg_residual hx]
      ring
    · intro x hx
      ring
  · rintro ⟨G, hG, hEq⟩
    change ∀ x ∈ branch, HasDerivAt G (rewrittenResidual x) x at hG
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    intro x hx
    have hd : HasDerivAt (fun y => boundary y + G y) (integrand x) x := by
      convert (hasDerivAt_boundary hx).add (hG x hx) using 1
      rw [rewrittenResidual_eq_neg_residual hx]
      ring
    apply hasDerivAt_of_eqOn_branch hx hd
    intro y hy
    simpa using hEq y hy
theorem gap5 :
    ByPartsFamily 1 rewrittenResidual = PrimitiveFamily := by
  ext F
  constructor
  · intro h
    have hF : F ∈ AntiderivativesOn integrand := by
      rw [gap4]
      exact h
    rcases antiderivative_eq_add_const hF
        (show primitive ∈ AntiderivativesOn integrand by
          intro x hx
          exact hasDerivAt_primitive hx) with ⟨C, hC⟩
    exact ⟨C, hC⟩
  · rintro ⟨C, hEq⟩
    have hF : F ∈ AntiderivativesOn integrand := by
      change ∀ x ∈ branch, HasDerivAt F (integrand x) x
      intro x hx
      have hd : HasDerivAt (fun y => primitive y + C) (integrand x) x :=
        (hasDerivAt_primitive hx).add_const C
      exact hasDerivAt_of_eqOn_branch hx hd hEq
    rw [← gap4]
    exact hF
theorem gap6 :
    AntiderivativesOn integrand = PrimitiveFamily := by
  calc
    AntiderivativesOn integrand = ByPartsFamily 1 rewrittenResidual := gap4
    _ = PrimitiveFamily := gap5

end
end ProofGap.Exercise1808
