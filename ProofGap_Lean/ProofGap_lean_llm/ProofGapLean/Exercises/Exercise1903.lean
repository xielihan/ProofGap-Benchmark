import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1903

noncomputable section

def integrand (x : ℝ) : ℝ := x ^ 3 / (x - 1) ^ 100
def domain : Set ℝ := {x | x ≠ 1}
def primitive (x : ℝ) : ℝ :=
  -1 / (96 * (x - 1) ^ 96) -
    3 / (97 * (x - 1) ^ 97) -
    3 / (98 * (x - 1) ^ 98) -
    1 / (99 * (x - 1) ^ 99)
def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

theorem gap1 (x : ℝ) (hx : x ∈ domain) :
    integrand x = (x - 1 + 1) ^ 3 / (x - 1) ^ 100 := by
  unfold integrand
  congr 1
  ring

theorem gap2 (x : ℝ) (hx : x ∈ domain) :
    (x - 1 + 1) ^ 3 / (x - 1) ^ 100 =
      1 / (x - 1) ^ 97 + 3 / (x - 1) ^ 98 +
        3 / (x - 1) ^ 99 + 1 / (x - 1) ^ 100 := by
  have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  field_simp [hx1]
  ring

theorem gap3 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  have hb := (hasDerivAt_id x).sub_const 1
  have h96 :=
    (hasDerivAt_const x (-1 : ℝ)).div
      ((hb.pow 96).const_mul 96)
      (mul_ne_zero (by norm_num) (pow_ne_zero 96 hx1))
  have h97 :=
    (hasDerivAt_const x (-3 : ℝ)).div
      ((hb.pow 97).const_mul 97)
      (mul_ne_zero (by norm_num) (pow_ne_zero 97 hx1))
  have h98 :=
    (hasDerivAt_const x (-3 : ℝ)).div
      ((hb.pow 98).const_mul 98)
      (mul_ne_zero (by norm_num) (pow_ne_zero 98 hx1))
  have h99 :=
    (hasDerivAt_const x (-1 : ℝ)).div
      ((hb.pow 99).const_mul 99)
      (mul_ne_zero (by norm_num) (pow_ne_zero 99 hx1))
  have hraw :=
    ((h96.add h97).add h98).add h99
  unfold primitive integrand
  convert hraw using 1
  · funext y
    simp [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  · norm_num [id_eq]
    field_simp [hx1]
    ring

theorem gap4 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  have hprimitive : IsAntiderivativeOn primitive integrand s := by
    intro x hx
    exact gap3 x (hdom hx)
  apply Set.ext
  intro F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand s at hF
    change ∃ C, ∀ x ∈ s, F x = primitive x + C
    have hzero : ∀ x ∈ s,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (hprimitive x hx)
    have hdiff : DifferentiableOn ℝ (fun y => F y - primitive y) s := by
      intro x hx
      exact (hzero x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ s, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      exact (hzero x hx).deriv
    by_cases hempty : s.Nonempty
    · obtain ⟨x₀, hx₀⟩ := hempty
      refine ⟨F x₀ - primitive x₀, ?_⟩
      intro x hx
      have heq : F x - primitive x = F x₀ - primitive x₀ :=
        IsOpen.is_const_of_deriv_eq_zero hopen hs hdiff hderiv hx hx₀
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact False.elim (hempty ⟨x, hx⟩)
  · rintro ⟨C, hC⟩
    change IsAntiderivativeOn F integrand s
    intro x hx
    apply ((hprimitive x hx).add_const C).congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hC y hy

end

end ProofGap.Exercise1903
