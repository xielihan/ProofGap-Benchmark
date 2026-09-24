import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1711

noncomputable section

def branch : Set ℝ := Set.Ioi 0
def asinhLog (x : ℝ) := Real.log (x + Real.sqrt (1 + x ^ 2))
def integrand (x : ℝ) :=
  Real.sqrt (asinhLog x / (1 + x ^ 2))
def substitutedIntegrand (x : ℝ) :=
  Real.sqrt (asinhLog x) * deriv asinhLog x
def primitive (x : ℝ) :=
  (2 / 3 : ℝ) * Real.rpow (asinhLog x) (3 / 2 : ℝ)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem asinhLog_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < asinhLog x := by
  have hb : 0 ≤ 1 + x ^ 2 := by positivity
  have hs0 : 0 ≤ Real.sqrt (1 + x ^ 2) := Real.sqrt_nonneg _
  have hargpos : 0 < x + Real.sqrt (1 + x ^ 2) := by positivity
  unfold asinhLog
  rw [Real.log_pos_iff (le_of_lt hargpos)]
  have hsquare := Real.sq_sqrt hb
  have hsone : 1 ≤ Real.sqrt (1 + x ^ 2) := by
    nlinarith [sq_nonneg x]
  linarith

private theorem hasDerivAt_asinhLog_of_pos {x : ℝ} (hx : 0 < x) :
    HasDerivAt asinhLog (1 / Real.sqrt (1 + x ^ 2)) x := by
  have hspos : 0 < Real.sqrt (1 + x ^ 2) := by positivity
  have hargpos : 0 < x + Real.sqrt (1 + x ^ 2) := by positivity
  have hinner : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2) using 1 <;>
      simp only [id_eq] <;> ring
  have hsqrt : HasDerivAt (fun y : ℝ => Real.sqrt (1 + y ^ 2))
      (x / Real.sqrt (1 + x ^ 2)) x := by
    convert (Real.hasDerivAt_sqrt (show 1 + x ^ 2 ≠ 0 by positivity)).comp x hinner using 1 <;>
      field_simp <;> ring
  have hlog : HasDerivAt asinhLog
      ((x + Real.sqrt (1 + x ^ 2))⁻¹ *
        (1 + x / Real.sqrt (1 + x ^ 2))) x := by
    simpa only [asinhLog, Function.comp_apply, Pi.add_apply, id_eq] using
      ((Real.hasDerivAt_log hargpos.ne').comp x ((hasDerivAt_id x).add hsqrt))
  convert hlog using 1
  field_simp [hspos.ne', hargpos.ne']
  ring

private theorem hasDerivAt_primitive_of_pos {x : ℝ} (hx : 0 < x) :
    HasDerivAt primitive (substitutedIntegrand x) x := by
  have ha := asinhLog_pos_of_pos (x := x) hx
  have hda := hasDerivAt_asinhLog_of_pos (x := x) hx
  have hr : HasDerivAt
      (fun y => Real.rpow (asinhLog y) (3 / 2 : ℝ))
      ((3 / 2 : ℝ) * Real.rpow (asinhLog x) ((3 / 2 : ℝ) - 1) *
        (1 / Real.sqrt (1 + x ^ 2))) x := by
    simpa only [Function.comp_apply] using
      ((Real.hasDerivAt_rpow_const (Or.inl ha.ne')).comp x hda)
  have hcoef :
      (2 / 3 : ℝ) *
          ((3 / 2 : ℝ) * Real.rpow (asinhLog x) ((3 / 2 : ℝ) - 1) *
            (1 / Real.sqrt (1 + x ^ 2))) =
        Real.sqrt (asinhLog x) * (1 / Real.sqrt (1 + x ^ 2)) := by
    rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num]
    have hsqrt_asinh :
        Real.rpow (asinhLog x) (1 / 2 : ℝ) = Real.sqrt (asinhLog x) := by
      change asinhLog x ^ (1 / 2 : ℝ) = Real.sqrt (asinhLog x)
      exact (Real.sqrt_eq_rpow (asinhLog x)).symm
    rw [hsqrt_asinh]
    ring
  unfold substitutedIntegrand
  rw [hda.deriv, ← hcoef]
  simpa only [primitive] using hr.const_mul (2 / 3 : ℝ)

theorem gap1 :
    AntiderivativesOn integrand =
      AntiderivativesOn substitutedIntegrand := by
  have heq : ∀ x ∈ branch, integrand x = substitutedIntegrand x := by
    intro x hx
    have hda := hasDerivAt_asinhLog_of_pos (x := x) hx
    have ha := asinhLog_pos_of_pos (x := x) hx
    unfold integrand substitutedIntegrand
    rw [hda.deriv]
    rw [div_eq_mul_inv, Real.sqrt_mul ha.le]
    rw [Real.sqrt_inv (1 + x ^ 2)]
    simp only [one_div]
  ext F
  constructor
  · intro hF x hx
    simpa only [heq x hx] using hF x hx
  · intro hF x hx
    simpa only [heq x hx] using hF x hx
theorem gap2 :
    AntiderivativesOn substitutedIntegrand = PrimitiveFamily primitive := by
  ext F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    have hzero : ∀ x ∈ branch,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      convert (hF x hx).sub (hasDerivAt_primitive_of_pos (x := x) hx) using 1
      ring
    refine ⟨F 1 - primitive 1, ?_⟩
    intro x hx
    have hconst : F x - primitive x = F 1 - primitive 1 :=
      isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
        (fun y hy => (hzero y hy).differentiableAt.differentiableWithinAt)
        (fun y hy => (hzero y hy).deriv)
        hx (by norm_num [branch])
    linarith
  · rintro ⟨C, hC⟩ x hx
    have hp := hasDerivAt_primitive_of_pos (x := x) hx
    have hevent : F =ᶠ[nhds x] fun y => C + primitive y := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      simpa [add_comm] using hC y hy
    exact (hp.const_add C).congr_of_eventuallyEq hevent
theorem gap3 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  rw [gap1, gap2]

end
end ProofGap.Exercise1711
