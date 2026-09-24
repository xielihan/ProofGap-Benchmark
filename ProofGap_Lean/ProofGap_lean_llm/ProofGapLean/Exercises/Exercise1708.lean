import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue

namespace ProofGap.Exercise1708

noncomputable section

def branch : Set ℝ := Set.Ioi 0
def integrand (x : ℝ) :=
  1 / ((Real.cosh x) ^ 2 * Real.cbrt ((Real.tanh x) ^ 2))
def substitutedIntegrand (x : ℝ) :=
  Real.rpow (Real.tanh x) (-2 / 3 : ℝ) * deriv Real.tanh x
def primitive (x : ℝ) := 3 * Real.cbrt (Real.tanh x)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private lemma tanh_eq_sinh_div_cosh_pointwise (x : ℝ) :
    Real.tanh x = Real.sinh x / Real.cosh x := by
  rw [Real.tanh_eq_sinh_div_cosh]

private lemma tanh_hasDerivAt (x : ℝ) :
    HasDerivAt Real.tanh (1 / (Real.cosh x) ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have hq := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  have hq' :
      HasDerivAt (fun y => Real.sinh y / Real.cosh y)
        (1 / (Real.cosh x) ^ 2) x := by
    convert hq using 1
    field_simp [hc]
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  have hfun : Real.tanh = fun y => Real.sinh y / Real.cosh y := by
    funext y
    exact tanh_eq_sinh_div_cosh_pointwise y
  rw [hfun]
  exact hq'

private lemma tanh_pos_of_pos (t : ℝ) (ht : 0 < t) : 0 < Real.tanh t := by
  have he : Real.exp (-t) < Real.exp t :=
    Real.exp_lt_exp.mpr (by linarith)
  have hs : 0 < Real.sinh t := by
    rw [Real.sinh_eq]
    linarith
  rw [tanh_eq_sinh_div_cosh_pointwise]
  exact div_pos hs (Real.cosh_pos t)

private lemma cbrt_eq_rpow_of_pos (t : ℝ) (ht : 0 < t) :
    Real.cbrt t = Real.rpow t (1 / 3 : ℝ) := by
  simp [Real.cbrt, ht, ht.le] <;> ring

private lemma cbrt_sq_eq_rpow (t : ℝ) (ht : 0 < t) :
    Real.cbrt (t ^ 2) = Real.rpow t (2 / 3 : ℝ) := by
  calc
    Real.cbrt (t ^ 2) = Real.rpow (t ^ 2) (1 / 3 : ℝ) :=
      cbrt_eq_rpow_of_pos (t ^ 2) (sq_pos_of_pos ht)
    _ = Real.exp (Real.log (t ^ 2) * (1 / 3 : ℝ)) :=
      Real.rpow_def_of_pos (pow_pos ht 2) (1 / 3 : ℝ)
    _ = Real.exp (Real.log (t * t) * (1 / 3 : ℝ)) := by
      rw [pow_two]
    _ = Real.exp ((Real.log t + Real.log t) * (1 / 3 : ℝ)) := by
      rw [Real.log_mul ht.ne' ht.ne']
    _ = Real.exp (Real.log t * (2 / 3 : ℝ)) := by
      congr 1
      ring
    _ = Real.rpow t (2 / 3 : ℝ) :=
      (Real.rpow_def_of_pos ht (2 / 3 : ℝ)).symm

private lemma rpow_neg_two_thirds (t : ℝ) (ht : 0 < t) :
    Real.rpow t (-2 / 3 : ℝ) =
      (Real.rpow t (2 / 3 : ℝ))⁻¹ := by
  calc
    Real.rpow t (-2 / 3 : ℝ) =
        Real.exp (Real.log t * (-2 / 3 : ℝ)) :=
      Real.rpow_def_of_pos ht (-2 / 3 : ℝ)
    _ = Real.exp (-(Real.log t * (2 / 3 : ℝ))) := by
      congr 1
      ring
    _ = (Real.exp (Real.log t * (2 / 3 : ℝ)))⁻¹ :=
      Real.exp_neg _
    _ = (Real.rpow t (2 / 3 : ℝ))⁻¹ :=
      congrArg (fun z : ℝ => z⁻¹)
        (Real.rpow_def_of_pos ht (2 / 3 : ℝ)).symm

private lemma integrand_eq_substitutedIntegrand (x : ℝ) (hx : x ∈ branch) :
    integrand x = substitutedIntegrand x := by
  have hxpos : 0 < x := by simpa [branch] using hx
  have ht : 0 < Real.tanh x := tanh_pos_of_pos x hxpos
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have hp : Real.rpow (Real.tanh x) (2 / 3 : ℝ) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos ht _)
  have hneg := rpow_neg_two_thirds (Real.tanh x) ht
  unfold integrand substitutedIntegrand
  rw [(tanh_hasDerivAt x).deriv, cbrt_sq_eq_rpow _ ht, hneg]
  field_simp [hc, hp] <;> ring

private lemma primitive_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (substitutedIntegrand x) x := by
  have hxpos : 0 < x := by simpa [branch] using hx
  have ht : 0 < Real.tanh x := tanh_pos_of_pos x hxpos
  have hexp : (1 / 3 : ℝ) - 1 = -2 / 3 := by ring
  have h :=
    ((Real.hasDerivAt_rpow_const (p := (1 / 3 : ℝ)) (Or.inl ht.ne')).comp x
      (tanh_hasDerivAt x)).const_mul 3
  have hpow :
      HasDerivAt
        (fun y => 3 * Real.rpow (Real.tanh y) (1 / 3 : ℝ))
        (substitutedIntegrand x) x := by
    convert h using 1
    rw [hexp]
    unfold substitutedIntegrand
    rw [(tanh_hasDerivAt x).deriv]
    ring_nf
    exact mul_comm _ _
  have heq :
      primitive =ᶠ[nhds x]
        (fun y => 3 * Real.rpow (Real.tanh y) (1 / 3 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hxpos] with y hy
    have hty : 0 < Real.tanh y := tanh_pos_of_pos y hy
    simpa [primitive] using
      congrArg (fun z : ℝ => 3 * z) (cbrt_eq_rpow_of_pos _ hty)
  exact hpow.congr_of_eventuallyEq heq

private lemma exists_add_const_of_same_deriv
    {F p d : ℝ → ℝ}
    (hF : ∀ x ∈ branch, HasDerivAt F (d x) x)
    (hp : ∀ x ∈ branch, HasDerivAt p (d x) x) :
    ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C := by
  let g : ℝ → ℝ := fun x => F x - p x
  have hg : ∀ x ∈ branch, HasDerivAt g 0 x := by
    intro x hx
    simpa [g] using (hF x hx).sub (hp x hx)
  have hdiff : DifferentiableOn ℝ g branch := by
    intro x hx
    exact (hg x hx).differentiableAt.differentiableWithinAt
  have hderiv : ∀ x ∈ branch, deriv g x = 0 := by
    intro x hx
    exact (hg x hx).deriv
  have hopen : IsOpen branch := by
    simpa [branch] using isOpen_Ioi
  have hpre : IsPreconnected branch := by
    simpa [branch] using isPreconnected_Ioi
  refine ⟨F 1 - p 1, ?_⟩
  intro x hx
  have hconst : g x = g 1 := by
    apply hopen.is_const_of_deriv_eq_zero hpre hdiff hderiv
    · exact hx
    · simpa [branch] using zero_lt_one
  dsimp [g] at hconst
  linarith

theorem gap1 :
    AntiderivativesOn integrand =
      AntiderivativesOn substitutedIntegrand := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      ∀ x ∈ branch, HasDerivAt F (substitutedIntegrand x) x
  constructor
  · intro hF x hx
    simpa only [integrand_eq_substitutedIntegrand x hx] using hF x hx
  · intro hF x hx
    simpa only [integrand_eq_substitutedIntegrand x hx] using hF x hx
theorem gap2 :
    AntiderivativesOn substitutedIntegrand = PrimitiveFamily primitive := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (substitutedIntegrand x) x) ↔
      ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C
  constructor
  · intro hF
    exact exists_add_const_of_same_deriv hF primitive_hasDerivAt
  · rintro ⟨C, hC⟩ x hx
    have hxpos : 0 < x := by simpa [branch] using hx
    have heq : F =ᶠ[nhds x] fun y => primitive y + C := by
      filter_upwards [isOpen_Ioi.mem_nhds hxpos] with y hy
      exact hC y (by simpa [branch] using hy)
    exact ((primitive_hasDerivAt x hx).add_const C).congr_of_eventuallyEq heq
theorem gap3 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  rw [gap1, gap2]

end
end ProofGap.Exercise1708
