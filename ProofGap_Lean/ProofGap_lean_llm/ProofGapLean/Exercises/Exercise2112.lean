import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2112
noncomputable section

def domain : Set ℝ := Set.Ioo (-1) 1
def integrand (x : ℝ) :=
  x * Real.arccos x / (Real.sqrt (1 - x ^ 2)) ^ 3
def differentialForm (x : ℝ) :=
  Real.arccos x * deriv (fun y : ℝ => 1 / Real.sqrt (1 - y ^ 2)) x
def residual (x : ℝ) := 1 / (1 - x ^ 2)
def primitive (x : ℝ) :=
  Real.arccos x / Real.sqrt (1 - x ^ 2) +
    (1 / 2 : ℝ) * Real.log ((1 + x) / (1 - x))

def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ domain, HasDerivAt F (f x) x}
def ByPartsFamily :=
  {F : ℝ → ℝ | ∃ A ∈ Family residual, ∀ x ∈ domain,
    F x = Real.arccos x / Real.sqrt (1 - x ^ 2) + A x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private def boundaryTerm (x : ℝ) :=
  Real.arccos x / Real.sqrt (1 - x ^ 2)

private def logPrimitive (x : ℝ) :=
  (1 / 2 : ℝ) * Real.log ((1 + x) / (1 - x))

private lemma one_sub_sq_pos {x : ℝ} (hx : x ∈ domain) :
    0 < 1 - x ^ 2 := by
  have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := by simpa [domain] using hx
  have hm : 0 < (1 - x) * (1 + x) :=
    mul_pos (by linarith [hx'.2]) (by linarith [hx'.1])
  nlinarith

private lemma hasDerivAt_recipSqrt {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt (fun y : ℝ => 1 / Real.sqrt (1 - y ^ 2))
      (x / (Real.sqrt (1 - x ^ 2)) ^ 3) x := by
  have hp := one_sub_sq_pos hx
  have hspos : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 hp
  have hu : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1 <;>
      simp [id] <;> ring
  have hs : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
      (-x / Real.sqrt (1 - x ^ 2)) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hp)).comp x hu using 1 <;>
      field_simp [ne_of_gt hspos] <;> ring
  convert hs.inv (ne_of_gt hspos) using 1
  · funext y
    simp [one_div]
  · field_simp [ne_of_gt hspos] <;> ring

private lemma hasDerivAt_boundaryTerm {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt boundaryTerm (differentialForm x - residual x) x := by
  have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := by simpa [domain] using hx
  have hp := one_sub_sq_pos hx
  have hspos : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 hp
  have hsquare : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hp)
  have hinv : 1 / (1 - x ^ 2) =
      1 / (Real.sqrt (1 - x ^ 2)) ^ 2 := by
    rw [hsquare]
  have ha : HasDerivAt Real.arccos
      (-1 / Real.sqrt (1 - x ^ 2)) x := by
    convert Real.hasDerivAt_arccos (ne_of_gt hx'.1) (ne_of_lt hx'.2) using 1
    ring
  have hg := hasDerivAt_recipSqrt hx
  have hprod := ha.mul hg
  convert hprod using 1
  · funext y
    simp [boundaryTerm, div_eq_mul_inv]
  · unfold differentialForm residual
    rw [hg.deriv, hinv]
    field_simp [ne_of_gt hspos]
    ring

private lemma hasDerivAt_logPrimitive {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt logPrimitive (residual x) x := by
  have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := by simpa [domain] using hx
  have hp := one_sub_sq_pos hx
  have hden : 1 - x ≠ 0 := by linarith [hx'.2]
  have hnum : 1 + x ≠ 0 := by linarith [hx'.1]
  have hn : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    convert (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x) using 1 <;> ring
  have hd : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x) using 1 <;> ring
  have hr : HasDerivAt (fun y : ℝ => (1 + y) / (1 - y))
      (2 / (1 - x) ^ 2) x := by
    convert hn.div hd hden using 1 <;> field_simp [hden] <;> ring
  have hrpos : 0 < (1 + x) / (1 - x) :=
    div_pos (by linarith [hx'.1]) (by linarith [hx'.2])
  have hlog : HasDerivAt
      (fun y : ℝ => Real.log ((1 + y) / (1 - y)))
      (2 / (1 - x ^ 2)) x := by
    convert (Real.hasDerivAt_log (ne_of_gt hrpos)).comp x hr using 1 <;>
      field_simp [hden, hnum, ne_of_gt hp, ne_of_gt hrpos] <;> ring
  convert hlog.const_mul (1 / 2 : ℝ) using 1 <;>
    simp [logPrimitive, residual] <;> ring

private lemma residual_antiderivative_eq (A : ℝ → ℝ)
    (hA : A ∈ Family residual) :
    ∃ C : ℝ, ∀ x ∈ domain, A x = logPrimitive x + C := by
  change ∀ x ∈ domain, HasDerivAt A (residual x) x at hA
  refine ⟨A 0 - logPrimitive 0, ?_⟩
  intro x hx
  have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := by simpa [domain] using hx
  have h0 : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  have hdiff : DifferentiableOn ℝ (fun y => A y - logPrimitive y)
      (Set.Ioo (-1 : ℝ) 1) := by
    intro y hy
    have hyd : y ∈ domain := by simpa [domain] using hy
    exact ((hA y hyd).sub (hasDerivAt_logPrimitive hyd)).differentiableAt.differentiableWithinAt
  have hzero : ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
      deriv (fun z => A z - logPrimitive z) y = 0 := by
    intro y hy
    have hyd : y ∈ domain := by simpa [domain] using hy
    have hd := (hA y hyd).sub (hasDerivAt_logPrimitive hyd)
    simpa using hd.deriv
  have heq : A x - logPrimitive x = A 0 - logPrimitive 0 :=
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      hdiff hzero hx' h0
  linarith

theorem gap1 : Family integrand = Family differentialForm := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ domain, HasDerivAt F (integrand x) x at hF
    change ∀ x ∈ domain, HasDerivAt F (differentialForm x) x
    intro x hx
    have hg := hasDerivAt_recipSqrt hx
    have heq : integrand x = differentialForm x := by
      unfold integrand differentialForm
      rw [hg.deriv]
      ring
    simpa [heq] using hF x hx
  · intro hF
    change ∀ x ∈ domain, HasDerivAt F (differentialForm x) x at hF
    change ∀ x ∈ domain, HasDerivAt F (integrand x) x
    intro x hx
    have hg := hasDerivAt_recipSqrt hx
    have heq : integrand x = differentialForm x := by
      unfold integrand differentialForm
      rw [hg.deriv]
      ring
    simpa [heq] using hF x hx
theorem gap2 : Family differentialForm = ByPartsFamily := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ domain, HasDerivAt F (differentialForm x) x at hF
    change ∃ A ∈ Family residual, ∀ x ∈ domain,
      F x = Real.arccos x / Real.sqrt (1 - x ^ 2) + A x
    refine ⟨fun y => F y - boundaryTerm y, ?_, ?_⟩
    · change ∀ x ∈ domain,
        HasDerivAt (fun y => F y - boundaryTerm y) (residual x) x
      intro x hx
      have hd := (hF x hx).sub (hasDerivAt_boundaryTerm hx)
      convert hd using 1 <;> ring
    · intro x hx
      simp [boundaryTerm]
  · intro hF
    change ∃ A ∈ Family residual, ∀ x ∈ domain,
      F x = Real.arccos x / Real.sqrt (1 - x ^ 2) + A x at hF
    rcases hF with ⟨A, hA, hEq⟩
    change ∀ x ∈ domain, HasDerivAt A (residual x) x at hA
    change ∀ x ∈ domain, HasDerivAt F (differentialForm x) x
    intro x hx
    have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := by simpa [domain] using hx
    have hd := (hasDerivAt_boundaryTerm hx).add (hA x hx)
    have hevent : F =ᶠ[nhds x] (boundaryTerm + A) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx'] with y hy
      simpa [boundaryTerm] using hEq y (by simpa [domain] using hy)
    have hdF := hd.congr_of_eventuallyEq hevent
    convert hdF using 1 <;> ring
theorem gap3 : ByPartsFamily = Translates primitive := by
  ext F
  constructor
  · intro hF
    change ∃ A ∈ Family residual, ∀ x ∈ domain,
      F x = Real.arccos x / Real.sqrt (1 - x ^ 2) + A x at hF
    rcases hF with ⟨A, hA, hEq⟩
    rcases residual_antiderivative_eq A hA with ⟨C, hAC⟩
    change ∃ C : ℝ, ∀ x ∈ domain, F x = primitive x + C
    refine ⟨C, ?_⟩
    intro x hx
    rw [hEq x hx, hAC x hx]
    simp [primitive, logPrimitive, add_assoc]
  · intro hF
    change ∃ C : ℝ, ∀ x ∈ domain, F x = primitive x + C at hF
    rcases hF with ⟨C, hEq⟩
    change ∃ A ∈ Family residual, ∀ x ∈ domain,
      F x = Real.arccos x / Real.sqrt (1 - x ^ 2) + A x
    refine ⟨fun y => logPrimitive y + C, ?_, ?_⟩
    · change ∀ x ∈ domain,
        HasDerivAt (fun y => logPrimitive y + C) (residual x) x
      intro x hx
      simpa using (hasDerivAt_logPrimitive hx).add_const C
    · intro x hx
      simpa [primitive, logPrimitive, add_assoc] using hEq x hx
theorem gap4 : Family integrand = Translates primitive := by
  exact gap1.trans (gap2.trans gap3)

end
end ProofGap.Exercise2112
