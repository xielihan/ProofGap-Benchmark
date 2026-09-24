import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1839

noncomputable section

def pole : ℝ := Real.sqrt (1 + Real.sqrt 2)
def branch : Set ℝ := Set.Ioo (-pole) pole
def integrand (x : ℝ) := x / (x ^ 4 - 2 * x ^ 2 - 1)
def substitutedIntegrand (x : ℝ) :=
  1 / ((x ^ 2 - 1) ^ 2 - (Real.sqrt 2) ^ 2) *
    deriv (fun t : ℝ => t ^ 2 - 1) x
def primitive (x : ℝ) :=
  1 / (4 * Real.sqrt 2) *
    Real.log |(x ^ 2 - (Real.sqrt 2 + 1)) /
      (x ^ 2 + Real.sqrt 2 - 1)|
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def HalfFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn substitutedIntegrand,
    ∀ x ∈ branch, F x = (1 / 2 : ℝ) * G x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private theorem substitutedIntegrand_eq (x : ℝ) :
    substitutedIntegrand x = 2 * integrand x := by
  have hd : HasDerivAt (fun t : ℝ => t ^ 2 - 1) (2 * x) x := by
    simpa using ((hasDerivAt_id x).pow 2).sub_const 1
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  rw [substitutedIntegrand, hd.deriv, hs]
  unfold integrand
  ring_nf

private theorem primitive_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (integrand x) x := by
  rcases hx with ⟨hx_left, hx_right⟩
  have hs_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hs_gt : 1 < Real.sqrt 2 := by
    nlinarith
  have hs_ne : Real.sqrt 2 ≠ 0 := by
    nlinarith
  have hp_nonneg : 0 ≤ pole := by
    unfold pole
    exact Real.sqrt_nonneg _
  have hp_sq : pole ^ 2 = 1 + Real.sqrt 2 := by
    unfold pole
    exact Real.sq_sqrt (by nlinarith)
  have hprod : 0 < (pole - x) * (pole + x) := by
    apply mul_pos <;> linarith
  have hx_sq_pole : x ^ 2 < pole ^ 2 := by
    nlinarith
  have hx_sq : x ^ 2 < Real.sqrt 2 + 1 := by
    nlinarith [hp_sq]
  have hnum_ne : x ^ 2 - (Real.sqrt 2 + 1) ≠ 0 := by
    nlinarith
  have hden_pos : 0 < x ^ 2 + Real.sqrt 2 - 1 := by
    nlinarith [sq_nonneg x]
  have hden_ne : x ^ 2 + Real.sqrt 2 - 1 ≠ 0 := ne_of_gt hden_pos
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_id x).pow 2
  have hnum :
      HasDerivAt
        (fun t : ℝ => t ^ 2 - (Real.sqrt 2 + 1)) (2 * x) x :=
    hsq.sub_const (Real.sqrt 2 + 1)
  have hden :
      HasDerivAt
        (fun t : ℝ => t ^ 2 + Real.sqrt 2 - 1) (2 * x) x := by
    exact (hsq.add_const (Real.sqrt 2)).sub_const 1
  have hquot :
      HasDerivAt
        (fun t : ℝ =>
          (t ^ 2 - (Real.sqrt 2 + 1)) /
            (t ^ 2 + Real.sqrt 2 - 1))
        (((2 * x) * (x ^ 2 + Real.sqrt 2 - 1) -
            (x ^ 2 - (Real.sqrt 2 + 1)) * (2 * x)) /
          (x ^ 2 + Real.sqrt 2 - 1) ^ 2) x :=
    hnum.div hden hden_ne
  have hquot_ne :
      (x ^ 2 - (Real.sqrt 2 + 1)) /
          (x ^ 2 + Real.sqrt 2 - 1) ≠ 0 :=
    div_ne_zero hnum_ne hden_ne
  have hlog :
      HasDerivAt
        (fun t : ℝ =>
          Real.log
            ((t ^ 2 - (Real.sqrt 2 + 1)) /
              (t ^ 2 + Real.sqrt 2 - 1)))
        ((((2 * x) * (x ^ 2 + Real.sqrt 2 - 1) -
              (x ^ 2 - (Real.sqrt 2 + 1)) * (2 * x)) /
            (x ^ 2 + Real.sqrt 2 - 1) ^ 2) /
          ((x ^ 2 - (Real.sqrt 2 + 1)) /
            (x ^ 2 + Real.sqrt 2 - 1))) x :=
    hquot.log hquot_ne
  have hfun :
      primitive =
        (fun t : ℝ =>
          (1 / (4 * Real.sqrt 2)) *
            Real.log
              ((t ^ 2 - (Real.sqrt 2 + 1)) /
                (t ^ 2 + Real.sqrt 2 - 1))) := by
    funext t
    rw [primitive, Real.log_abs]
  have hprim :
      HasDerivAt primitive
        ((1 / (4 * Real.sqrt 2)) *
          ((((2 * x) * (x ^ 2 + Real.sqrt 2 - 1) -
                (x ^ 2 - (Real.sqrt 2 + 1)) * (2 * x)) /
              (x ^ 2 + Real.sqrt 2 - 1) ^ 2) /
            ((x ^ 2 - (Real.sqrt 2 + 1)) /
              (x ^ 2 + Real.sqrt 2 - 1)))) x := by
    rw [hfun]
    exact hlog.const_mul (1 / (4 * Real.sqrt 2))
  have hfactor :
      x ^ 4 - 2 * x ^ 2 - 1 =
        (x ^ 2 - (Real.sqrt 2 + 1)) *
          (x ^ 2 + Real.sqrt 2 - 1) := by
    nlinarith [hs_sq]
  have heq :
      (1 / (4 * Real.sqrt 2)) *
          ((((2 * x) * (x ^ 2 + Real.sqrt 2 - 1) -
                (x ^ 2 - (Real.sqrt 2 + 1)) * (2 * x)) /
              (x ^ 2 + Real.sqrt 2 - 1) ^ 2) /
            ((x ^ 2 - (Real.sqrt 2 + 1)) /
              (x ^ 2 + Real.sqrt 2 - 1))) =
        integrand x := by
    unfold integrand
    rw [hfactor]
    field_simp [hs_ne, hnum_ne, hden_ne] <;> ring
  rw [heq] at hprim
  exact hprim

private theorem antiderivative_eq_primitive_add_const
    (F : ℝ → ℝ)
    (hF : ∀ x ∈ branch, HasDerivAt F (integrand x) x) :
    ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C := by
  let H : ℝ → ℝ := fun x => F x - primitive x
  have hzero : ∀ x ∈ branch, HasDerivAt H 0 x := by
    intro x hx
    simpa [H] using (hF x hx).sub (primitive_hasDerivAt x hx)
  have hdiff : DifferentiableOn ℝ H branch := by
    intro x hx
    exact (hzero x hx).differentiableAt.differentiableWithinAt
  have hderiv : ∀ x ∈ branch, deriv H x = 0 := by
    intro x hx
    exact (hzero x hx).deriv
  have hp : 0 < pole := by
    unfold pole
    apply Real.sqrt_pos.2
    nlinarith [Real.sqrt_nonneg 2]
  have hzero_mem : 0 ∈ branch := by
    change -pole < 0 ∧ 0 < pole
    exact ⟨neg_lt_zero.mpr hp, hp⟩
  refine ⟨F 0 - primitive 0, ?_⟩
  intro x hx
  have heq : H x = H 0 :=
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      hdiff hderiv hx hzero_mem
  dsimp [H] at heq
  linarith

theorem gap1 :
    AntiderivativesOn integrand = HalfFamily := by
  ext F
  constructor
  · intro hF
    refine ⟨fun y => 2 * F y, ?_, ?_⟩
    · intro x hx
      simpa only [substitutedIntegrand_eq] using
        (hF x hx).const_mul (2 : ℝ)
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hscaled :
        HasDerivAt (fun y => (1 / 2 : ℝ) * G y) (integrand x) x := by
      convert (hG x hx).const_mul (1 / 2 : ℝ) using 1
      rw [substitutedIntegrand_eq]
      ring
    have hopen : IsOpen branch := by
      unfold branch
      exact isOpen_Ioo
    have heq :
        Filter.EventuallyEq (nhds x) F
          (fun y => (1 / 2 : ℝ) * G y) := by
      apply Filter.mem_of_superset (hopen.mem_nhds hx)
      intro y hy
      exact hFG y hy
    exact hscaled.congr_of_eventuallyEq heq
theorem gap2 :
    HalfFamily = PrimitiveFamily := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    have hanti : F ∈ AntiderivativesOn integrand := by
      rw [gap1]
      exact ⟨G, hG, hFG⟩
    exact antiderivative_eq_primitive_add_const F hanti
  · rintro ⟨C, hC⟩
    rw [← gap1]
    intro x hx
    have hbase :
        HasDerivAt (fun y => primitive y + C) (integrand x) x :=
      (primitive_hasDerivAt x hx).add_const C
    have hopen : IsOpen branch := by
      unfold branch
      exact isOpen_Ioo
    have heq :
        Filter.EventuallyEq (nhds x) F
          (fun y => primitive y + C) := by
      apply Filter.mem_of_superset (hopen.mem_nhds hx)
      intro y hy
      exact hC y hy
    exact hbase.congr_of_eventuallyEq heq
theorem gap3 :
    AntiderivativesOn integrand = PrimitiveFamily := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1839
