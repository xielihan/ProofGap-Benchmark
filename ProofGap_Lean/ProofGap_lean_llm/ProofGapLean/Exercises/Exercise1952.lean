import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace ProofGap.Exercise1952

noncomputable section

def q (x : ℝ) := 1 + 2 * x - x ^ 2
def xOf (t : ℝ) := 1 + 1 / t
def xBranch : Set ℝ := {x | q x > 0 ∧ x ≠ 1}
def rightBranch : Set ℝ := {x | q x > 0 ∧ 1 < x}
def parameterBranch : Set ℝ := {t | 0 < t ∧ 2 * t ^ 2 - 1 > 0}
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def PrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}
def BranchwisePrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ u : Set ℝ, IsOpen u → IsPreconnected u → u ⊆ s →
    ∃ C : ℝ, ∀ x ∈ u, F x = p x + C}
def integrand (x : ℝ) := x / ((x - 1) ^ 2 * Real.sqrt (q x))
def part₁ (x : ℝ) := 1 / ((x - 1) ^ 2 * Real.sqrt (q x))
def part₂ (x : ℝ) := 1 / ((x - 1) * Real.sqrt (q x))
def DecompositionFamily : Set (ℝ → ℝ) :=
  {F | ∃ A ∈ AntiderivativesOn xBranch part₁,
    ∃ B ∈ AntiderivativesOn xBranch part₂,
    ∀ x ∈ xBranch, F x = A x + B x}
def sourceParamIntegrand (t : ℝ) := integrand (xOf t) * deriv xOf t
def AuxiliaryParamFamily : Set (ℝ → ℝ) :=
  {F | ∃ A ∈ AntiderivativesOn parameterBranch
      (fun t => t / Real.sqrt (2 * t ^ 2 - 1)),
    ∃ B ∈ AntiderivativesOn parameterBranch
      (fun t => 1 / Real.sqrt (2 * t ^ 2 - 1)),
    ∀ t ∈ parameterBranch, F t = -A t - B t}
def parameterPrimitive (t : ℝ) :=
  -1 / 2 * Real.sqrt (2 * t ^ 2 - 1) -
    1 / Real.sqrt 2 *
      Real.log |Real.sqrt 2 * t + Real.sqrt (2 * t ^ 2 - 1)|
def xPrimitive (x : ℝ) :=
  Real.sqrt (q x) / (2 * (1 - x)) -
    1 / Real.sqrt 2 *
      Real.log |(Real.sqrt 2 + Real.sqrt (q x)) / (1 - x)|

private def p1 (x : ℝ) := Real.sqrt (q x) / (2 * (1 - x))

private lemma q_hasDerivAt (x : ℝ) :
    HasDerivAt q (2 - 2 * x) x := by
  have hlin : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    convert (hasDerivAt_id x).const_mul 2 using 1 <;> ring
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;> simp [id] <;> ring
  convert (hasDerivAt_const x (1 : ℝ)).add (hlin.sub hsq) using 1
  · funext y
    simp only [Pi.add_apply, Pi.sub_apply]
    unfold q
    ring
  · ring

private lemma p1_hasDerivAt (x : ℝ) (hx : x ∈ xBranch) :
    HasDerivAt p1 (part₁ x) x := by
  have hq : 0 < q x := hx.1
  have hx1 : x ≠ 1 := hx.2
  have hs : Real.sqrt (q x) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have hs2 : Real.sqrt (q x) ^ 2 = q x := Real.sq_sqrt hq.le
  have hsder : HasDerivAt (fun y => Real.sqrt (q y))
      ((1 - x) / Real.sqrt (q x)) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x (q_hasDerivAt x) using 1 <;>
      ring
  have hden : HasDerivAt (fun y : ℝ => 2 * (1 - y)) (-2) x := by
    convert (hasDerivAt_const x (2 : ℝ)).mul
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)) using 1 <;>
        simp [id] <;> ring
  have hd0 : 2 * (1 - x) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hx1.symm)
  have h := hsder.div hden hd0
  have h' : HasDerivAt p1
      (((1 - x) / Real.sqrt (q x) * (2 * (1 - x)) -
        Real.sqrt (q x) * (-2)) / (2 * (1 - x)) ^ 2) x := by
    simpa [p1] using h
  convert h' using 1
  unfold part₁
  field_simp [hs, hx1]
  rw [hs2]
  unfold q
  ring

private lemma isOpen_xBranch : IsOpen xBranch := by
  rw [show xBranch = {x : ℝ | 0 < q x} ∩ {1}ᶜ by
    ext x
    simp [xBranch]]
  have hq : Continuous q := by
    unfold q
    fun_prop
  exact (isOpen_lt continuous_const hq).inter isOpen_compl_singleton

theorem gap1 :
    AntiderivativesOn xBranch integrand = DecompositionFamily := by
  ext F
  constructor
  · intro hF
    refine ⟨p1, ?_, (fun x => F x - p1 x), ?_, ?_⟩
    · intro x hx
      exact p1_hasDerivAt x hx
    · intro x hx
      have h := (hF x hx).sub (p1_hasDerivAt x hx)
      convert h using 1
      unfold integrand part₁ part₂
      have hq : 0 < q x := hx.1
      have hs : Real.sqrt (q x) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
      field_simp [hs, hx.2]
    · intro x hx
      ring
  · rintro ⟨A, hA, B, hB, hEq⟩
    intro x hx
    have h := (hA x hx).add (hB x hx)
    have hcoef : part₁ x + part₂ x = integrand x := by
      unfold integrand part₁ part₂
      have hq : 0 < q x := hx.1
      have hs : Real.sqrt (q x) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
      field_simp [hs, hx.2]
      ring
    have hevent : F =ᶠ[nhds x] (fun y => A y + B y) := by
      filter_upwards [isOpen_xBranch.mem_nhds hx] with y hy
      exact hEq y hy
    exact (h.congr_deriv hcoef).congr_of_eventuallyEq hevent
theorem gap2 (t : ℝ) (ht : t ∈ parameterBranch) :
    HasDerivAt xOf (-1 / t ^ 2) t := by
  have ht0 : t ≠ 0 := ht.1.ne'
  unfold xOf
  convert (hasDerivAt_const t (1 : ℝ)).add
    ((hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) ht0) using 1 <;>
    simp [id] <;> field_simp [ht0] <;> ring
theorem gap3 (t : ℝ) (ht : t ∈ parameterBranch) :
    Real.sqrt (q (xOf t)) = Real.sqrt (2 * t ^ 2 - 1) / t := by
  have ht0 : 0 < t := ht.1
  have hrad : 0 < 2 * t ^ 2 - 1 := ht.2
  have hq : q (xOf t) = (2 * t ^ 2 - 1) / t ^ 2 := by
    unfold q xOf
    field_simp [ht0.ne']
    ring
  rw [hq, Real.sqrt_div hrad.le, Real.sqrt_sq_eq_abs, abs_of_pos ht0]

private def paramA (t : ℝ) := (1 / 2 : ℝ) * Real.sqrt (2 * t ^ 2 - 1)

private lemma rad_hasDerivAt (t : ℝ) :
    HasDerivAt (fun y : ℝ => 2 * y ^ 2 - 1) (4 * t) t := by
  convert (((hasDerivAt_id t).pow 2).const_mul 2).sub
    (hasDerivAt_const t (1 : ℝ)) using 1 <;> simp [id] <;> ring

private lemma paramA_hasDerivAt (t : ℝ) (ht : t ∈ parameterBranch) :
    HasDerivAt paramA (t / Real.sqrt (2 * t ^ 2 - 1)) t := by
  have hr : 0 < 2 * t ^ 2 - 1 := ht.2
  have hs : Real.sqrt (2 * t ^ 2 - 1) ≠ 0 := (Real.sqrt_pos.2 hr).ne'
  have h := (Real.hasDerivAt_sqrt (ne_of_gt hr)).comp t (rad_hasDerivAt t)
  have hc := h.const_mul (1 / 2 : ℝ)
  unfold paramA
  convert hc using 1
  field_simp [hs]
  norm_num

private lemma sourceParamIntegrand_eq (t : ℝ) (ht : t ∈ parameterBranch) :
    sourceParamIntegrand t =
      -t / Real.sqrt (2 * t ^ 2 - 1) -
        1 / Real.sqrt (2 * t ^ 2 - 1) := by
  have ht0 : t ≠ 0 := ht.1.ne'
  have hs : Real.sqrt (2 * t ^ 2 - 1) ≠ 0 :=
    (Real.sqrt_pos.2 ht.2).ne'
  unfold sourceParamIntegrand integrand
  rw [(gap2 t ht).deriv, gap3 t ht]
  unfold xOf
  field_simp [ht0, hs]
  ring

private lemma isOpen_parameterBranch : IsOpen parameterBranch := by
  rw [show parameterBranch =
      {t : ℝ | 0 < t} ∩ {t : ℝ | 1 < 2 * t ^ 2} by
    ext t
    simp [parameterBranch]]
  exact (isOpen_lt continuous_const continuous_id).inter
    (isOpen_lt continuous_const (by fun_prop))
theorem gap4 :
    AntiderivativesOn parameterBranch sourceParamIntegrand =
      AuxiliaryParamFamily := by
  ext F
  constructor
  · intro hF
    refine ⟨paramA, ?_, (fun t => -F t - paramA t), ?_, ?_⟩
    · intro t ht
      exact paramA_hasDerivAt t ht
    · intro t ht
      have h := (hF t ht).neg.sub (paramA_hasDerivAt t ht)
      convert h using 1
      rw [sourceParamIntegrand_eq t ht]
      ring
    · intro t ht
      ring
  · rintro ⟨A, hA, B, hB, hEq⟩
    intro t ht
    have h := (hA t ht).neg.sub (hB t ht)
    have hcoef :
        -(t / Real.sqrt (2 * t ^ 2 - 1)) -
            1 / Real.sqrt (2 * t ^ 2 - 1) =
          sourceParamIntegrand t := by
      rw [sourceParamIntegrand_eq t ht]
      ring
    have hevent : F =ᶠ[nhds t] (fun y => -A y - B y) := by
      filter_upwards [isOpen_parameterBranch.mem_nhds ht] with y hy
      exact hEq y hy
    exact (h.congr_deriv hcoef).congr_of_eventuallyEq hevent

private lemma parameterBranch_eq_Ioi :
    parameterBranch = Set.Ioi (Real.sqrt (1 / 2 : ℝ)) := by
  ext t
  simp only [parameterBranch, Set.mem_setOf_eq, Set.mem_Ioi]
  have hr0 : 0 ≤ Real.sqrt (1 / 2 : ℝ) := Real.sqrt_nonneg _
  have hr2 : Real.sqrt (1 / 2 : ℝ) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  constructor
  · rintro ⟨ht, hsq⟩
    by_contra h
    have hle : t ≤ Real.sqrt (1 / 2 : ℝ) := le_of_not_gt h
    have hmul : 0 ≤ (Real.sqrt (1 / 2 : ℝ) - t) *
        (Real.sqrt (1 / 2 : ℝ) + t) :=
      mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hr0 ht.le)
    nlinarith
  · intro ht
    have ht0 : 0 < t := lt_of_le_of_lt hr0 ht
    have hmul : 0 < (t - Real.sqrt (1 / 2 : ℝ)) *
        (t + Real.sqrt (1 / 2 : ℝ)) :=
      mul_pos (sub_pos.mpr ht) (add_pos_of_pos_of_nonneg ht0 hr0)
    constructor
    · exact ht0
    · nlinarith

private lemma isPreconnected_parameterBranch : IsPreconnected parameterBranch := by
  rw [parameterBranch_eq_Ioi]
  exact isPreconnected_Ioi

private lemma parameterPrimitive_hasDerivAt (t : ℝ) (ht : t ∈ parameterBranch) :
    HasDerivAt parameterPrimitive (sourceParamIntegrand t) t := by
  have ht0 : 0 < t := ht.1
  have hr : 0 < 2 * t ^ 2 - 1 := ht.2
  have hR : Real.sqrt (2 * t ^ 2 - 1) ≠ 0 := (Real.sqrt_pos.2 hr).ne'
  have hR2 : Real.sqrt (2 * t ^ 2 - 1) ^ 2 = 2 * t ^ 2 - 1 :=
    Real.sq_sqrt hr.le
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := hs.ne'
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrad := (Real.hasDerivAt_sqrt (ne_of_gt hr)).comp t (rad_hasDerivAt t)
  have hg : HasDerivAt
      (fun y : ℝ => Real.sqrt 2 * y + Real.sqrt (2 * y ^ 2 - 1))
      (Real.sqrt 2 + 2 * t / Real.sqrt (2 * t ^ 2 - 1)) t := by
    have hlin : HasDerivAt (fun y : ℝ => Real.sqrt 2 * y) (Real.sqrt 2) t := by
      convert (hasDerivAt_id t).const_mul (Real.sqrt 2) using 1 <;> ring
    convert hlin.add hrad using 1
    field_simp [hR]
    ring
  have hgpos :
      0 < Real.sqrt 2 * t + Real.sqrt (2 * t ^ 2 - 1) := by positivity
  have hlog : HasDerivAt
      (fun y : ℝ =>
        Real.log |Real.sqrt 2 * y + Real.sqrt (2 * y ^ 2 - 1)|)
      (Real.sqrt 2 / Real.sqrt (2 * t ^ 2 - 1)) t := by
    have hc := (Real.hasDerivAt_log hgpos.ne').comp t hg
    simp only [Real.log_abs]
    convert hc using 1
    field_simp [hR, hgpos.ne']
    nlinarith [hs2]
  have hfirst := (paramA_hasDerivAt t ht).neg
  have hsecond := hlog.const_mul (-1 / Real.sqrt 2)
  have h := hfirst.add hsecond
  convert h using 1
  · funext y
    simp only [Pi.add_apply, Pi.neg_apply, paramA, parameterPrimitive]
    ring
  · rw [sourceParamIntegrand_eq t ht]
    field_simp [hs0]
    ring
theorem gap5 :
    AntiderivativesOn parameterBranch sourceParamIntegrand =
      PrimitiveFamilyOn parameterBranch parameterPrimitive := by
  ext F
  constructor
  · intro hF
    have hP : ∀ t ∈ parameterBranch,
        HasDerivAt parameterPrimitive (sourceParamIntegrand t) t :=
      parameterPrimitive_hasDerivAt
    have hFd : DifferentiableOn ℝ F parameterBranch :=
      fun t ht => (hF t ht).differentiableAt.differentiableWithinAt
    have hPd : DifferentiableOn ℝ parameterPrimitive parameterBranch :=
      fun t ht => (hP t ht).differentiableAt.differentiableWithinAt
    have heq : parameterBranch.EqOn (deriv F) (deriv parameterPrimitive) := by
      intro t ht
      rw [(hF t ht).deriv, (hP t ht).deriv]
    exact isOpen_parameterBranch.exists_eq_add_of_deriv_eq
      isPreconnected_parameterBranch hFd hPd heq
  · rintro ⟨C, hEq⟩
    intro t ht
    have hp := parameterPrimitive_hasDerivAt t ht
    have hpc := hp.add_const C
    have hevent : F =ᶠ[nhds t] (fun y => parameterPrimitive y + C) := by
      filter_upwards [isOpen_parameterBranch.mem_nhds ht] with y hy
      exact hEq y hy
    exact hpc.congr_of_eventuallyEq hevent

private def xLogArg (x : ℝ) :=
  (Real.sqrt 2 + Real.sqrt (q x)) / (1 - x)

private lemma xPrimitive_hasDerivAt (x : ℝ) (hx : x ∈ xBranch) :
    HasDerivAt xPrimitive (integrand x) x := by
  have hq : 0 < q x := hx.1
  have hx1 : x ≠ 1 := hx.2
  have hR : Real.sqrt (q x) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have hR2 : Real.sqrt (q x) ^ 2 = q x := Real.sq_sqrt hq.le
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := hs.ne'
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hRder : HasDerivAt (fun y => Real.sqrt (q y))
      ((1 - x) / Real.sqrt (q x)) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x (q_hasDerivAt x) using 1 <;>
      ring
  have hnum : HasDerivAt (fun y => Real.sqrt 2 + Real.sqrt (q y))
      ((1 - x) / Real.sqrt (q x)) x := by
    convert hRder.const_add (Real.sqrt 2) using 1 <;> simp
  have hden : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x) using 1 <;>
      simp [id]
  have hd0 : 1 - x ≠ 0 := sub_ne_zero.mpr hx1.symm
  have hg := hnum.div hden hd0
  have hnumpos : 0 < Real.sqrt 2 + Real.sqrt (q x) := by positivity
  have hg0 : xLogArg x ≠ 0 := by
    unfold xLogArg
    exact div_ne_zero hnumpos.ne' hd0
  have hlog : HasDerivAt (fun y => Real.log |xLogArg y|)
      (Real.sqrt 2 / (Real.sqrt (q x) * (1 - x))) x := by
    have hc := (Real.hasDerivAt_log hg0).comp x hg
    simp only [Real.log_abs]
    convert hc using 1
    unfold xLogArg
    field_simp [hR, hd0, hnumpos.ne']
    unfold q at hR2 ⊢
    nlinarith [hR2, hs2]
  have hfirst := p1_hasDerivAt x hx
  have hsecond := hlog.const_mul (-1 / Real.sqrt 2)
  have h := hfirst.add hsecond
  convert h using 1
  · funext y
    simp only [Pi.add_apply, p1, xLogArg, xPrimitive]
    ring
  · unfold integrand part₁
    have hxm : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
    have hom : 1 - x ≠ 0 := sub_ne_zero.mpr hx1.symm
    field_simp [hR, hxm, hom, hs0]
    ring
theorem gap6 :
    AntiderivativesOn xBranch integrand =
      BranchwisePrimitiveFamilyOn xBranch xPrimitive := by
  ext F
  constructor
  · intro hF
    intro u huOpen huPre huSub
    have hP : ∀ x ∈ u, HasDerivAt xPrimitive (integrand x) x :=
      fun x hx => xPrimitive_hasDerivAt x (huSub hx)
    have hFd : DifferentiableOn ℝ F u :=
      fun x hx => (hF x (huSub hx)).differentiableAt.differentiableWithinAt
    have hPd : DifferentiableOn ℝ xPrimitive u :=
      fun x hx => (hP x hx).differentiableAt.differentiableWithinAt
    have heq : u.EqOn (deriv F) (deriv xPrimitive) := by
      intro x hx
      rw [(hF x (huSub hx)).deriv, (hP x hx).deriv]
    exact huOpen.exists_eq_add_of_deriv_eq huPre hFd hPd heq
  · intro hF
    intro x hx
    rcases Metric.isOpen_iff.mp isOpen_xBranch x hx with ⟨ε, hε, hsub⟩
    rcases hF (Metric.ball x ε) Metric.isOpen_ball
      (convex_ball x ε).isPreconnected hsub with ⟨C, hEq⟩
    have hp := (xPrimitive_hasDerivAt x hx).add_const C
    have hevent : F =ᶠ[nhds x] (fun y => xPrimitive y + C) := by
      filter_upwards [Metric.ball_mem_nhds x hε] with y hy
      exact hEq y hy
    exact hp.congr_of_eventuallyEq hevent

end
end ProofGap.Exercise1952
