import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2087
noncomputable section

def U : Set ℝ := Set.Ioi 0
def f (x : ℝ) := 1 / Real.sqrt (Real.exp x - 1)
def rewritten (x : ℝ) :=
  1 / (Real.exp (x / 2) * Real.sqrt (1 - Real.exp (-x / 2) ^ 2))
def primitive (x : ℝ) := -2 * Real.arcsin (Real.exp (-x / 2))
def Family (g : ℝ → ℝ) := {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (g x) x}
def Substitution := {F : ℝ → ℝ |
  ∃ G ∈ Family (fun x => deriv (fun y => Real.exp (-y / 2)) x /
    Real.sqrt (1 - Real.exp (-x / 2) ^ 2)),
  ∃ C, ∀ x ∈ U, F x = -2 * G x + C}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ U, F x = p x + C}

private def arc (x : ℝ) := Real.arcsin (Real.exp (-x / 2))

private def q (x : ℝ) :=
  deriv (fun y => Real.exp (-y / 2)) x /
    Real.sqrt (1 - Real.exp (-x / 2) ^ 2)

private theorem exp_half_mul_exp_neg_half (x : ℝ) :
    Real.exp (x / 2) * Real.exp (-x / 2) = 1 := by
  calc
    Real.exp (x / 2) * Real.exp (-x / 2) =
        Real.exp (x / 2 + -x / 2) := (Real.exp_add _ _).symm
    _ = Real.exp 0 := by congr 1 <;> ring
    _ = 1 := Real.exp_zero

private theorem exp_neg_half_mul_exp_half (x : ℝ) :
    Real.exp (-x / 2) * Real.exp (x / 2) = 1 := by
  rw [mul_comm]
  exact exp_half_mul_exp_neg_half x

private theorem exp_eq_half_sq (x : ℝ) :
    Real.exp x = Real.exp (x / 2) ^ 2 := by
  calc
    Real.exp x = Real.exp (x / 2 + x / 2) := by congr 1 <;> ring
    _ = Real.exp (x / 2) * Real.exp (x / 2) := Real.exp_add _ _
    _ = Real.exp (x / 2) ^ 2 := by ring

private theorem denominator_eq (x : ℝ) (hx : x ∈ U) :
    Real.sqrt (Real.exp x - 1) =
      Real.exp (x / 2) * Real.sqrt (1 - Real.exp (-x / 2) ^ 2) := by
  have hx0 : 0 < x := hx
  have hbpos : 0 < Real.exp (-x / 2) := Real.exp_pos _
  have hblt : Real.exp (-x / 2) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hm : 0 < Real.exp (-x / 2) * (1 - Real.exp (-x / 2)) :=
    mul_pos hbpos (sub_pos.mpr hblt)
  have hrad2 : 0 ≤ 1 - Real.exp (-x / 2) ^ 2 := by
    nlinarith
  have hrad1 : 0 ≤ Real.exp x - 1 := by
    have := Real.one_lt_exp_iff.mpr hx0
    linarith
  have hs1 := Real.sq_sqrt hrad1
  have hs2 := Real.sq_sqrt hrad2
  have hprod := exp_half_mul_exp_neg_half x
  have hprodsq :
      Real.exp (x / 2) ^ 2 * Real.exp (-x / 2) ^ 2 = 1 := by
    calc
      Real.exp (x / 2) ^ 2 * Real.exp (-x / 2) ^ 2 =
          (Real.exp (x / 2) * Real.exp (-x / 2)) ^ 2 := by ring
      _ = 1 := by rw [hprod]; norm_num
  have hex := exp_eq_half_sq x
  have hrhs_sq :
      (Real.exp (x / 2) * Real.sqrt (1 - Real.exp (-x / 2) ^ 2)) ^ 2 =
        Real.exp x - 1 := by
    calc
      (Real.exp (x / 2) * Real.sqrt (1 - Real.exp (-x / 2) ^ 2)) ^ 2 =
          Real.exp (x / 2) ^ 2 *
            Real.sqrt (1 - Real.exp (-x / 2) ^ 2) ^ 2 := by ring
      _ = Real.exp (x / 2) ^ 2 * (1 - Real.exp (-x / 2) ^ 2) := by rw [hs2]
      _ = Real.exp (x / 2) ^ 2 -
          Real.exp (x / 2) ^ 2 * Real.exp (-x / 2) ^ 2 := by ring
      _ = Real.exp (x / 2) ^ 2 - 1 := by rw [hprodsq]
      _ = Real.exp x - 1 := by rw [hex]
  have hl_nonneg : 0 ≤ Real.sqrt (Real.exp x - 1) := Real.sqrt_nonneg _
  have hr_nonneg :
      0 ≤ Real.exp (x / 2) * Real.sqrt (1 - Real.exp (-x / 2) ^ 2) :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) (Real.sqrt_nonneg _)
  nlinarith

private theorem f_eq_rewritten (x : ℝ) (hx : x ∈ U) :
    f x = rewritten x := by
  simp only [f, rewritten, denominator_eq x hx]

private theorem hasDerivAt_exp_neg_half (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-y / 2))
      (Real.exp (-x / 2) * (-1 / 2)) x := by
  convert (Real.hasDerivAt_exp (-x / 2)).comp x
    ((hasDerivAt_id x).neg.div_const 2) using 1 <;> ring

private theorem hasDerivAt_arc (x : ℝ) (hx : x ∈ U) :
    HasDerivAt arc (q x) x := by
  have hx0 : 0 < x := hx
  have hlt : Real.exp (-x / 2) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hmem : Real.exp (-x / 2) ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · have := Real.exp_pos (-x / 2)
      linarith
    · exact hlt
  have hd := hasDerivAt_exp_neg_half x
  unfold q
  rw [hd.deriv]
  unfold arc
  simpa only [Function.comp_apply, one_mul, div_eq_mul_inv, mul_assoc,
    mul_comm, mul_left_comm] using
    (Real.hasDerivAt_arcsin (ne_of_gt hmem.1) (ne_of_lt hmem.2)).comp x hd

private theorem hasDerivAt_primitive (x : ℝ) (hx : x ∈ U) :
    HasDerivAt primitive (f x) x := by
  have hd := hasDerivAt_exp_neg_half x
  have hrecip : Real.exp (-x / 2) = 1 / Real.exp (x / 2) := by
    apply (eq_div_iff (ne_of_gt (Real.exp_pos (x / 2)))).2
    exact exp_neg_half_mul_exp_half x
  have hcoef : -2 * q x = rewritten x := by
    unfold q rewritten
    rw [hd.deriv]
    calc
      -2 * (Real.exp (-x / 2) * (-1 / 2) /
          Real.sqrt (1 - Real.exp (-x / 2) ^ 2)) =
          Real.exp (-x / 2) /
            Real.sqrt (1 - Real.exp (-x / 2) ^ 2) := by ring
      _ = (1 / Real.exp (x / 2)) /
            Real.sqrt (1 - Real.exp (-x / 2) ^ 2) := by rw [hrecip]
      _ = 1 / (Real.exp (x / 2) *
            Real.sqrt (1 - Real.exp (-x / 2) ^ 2)) := by rw [div_div]
  have h := (hasDerivAt_arc x hx).const_mul (-2)
  rw [hcoef, ← f_eq_rewritten x hx] at h
  simpa only [primitive, arc] using h

private theorem family_eq_translates_of_hasDerivAt
    (g p : ℝ → ℝ) (hp : ∀ x ∈ U, HasDerivAt p (g x) x) :
    Family g = Translates p := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ U, HasDerivAt F (g x) x at hF
    change ∃ C, ∀ x ∈ U, F x = p x + C
    let H : ℝ → ℝ := fun x => F x - p x
    have hdiff : DifferentiableOn ℝ H U := by
      intro x hx
      exact ((hF x hx).sub (hp x hx)).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ U, deriv H x = 0 := by
      intro x hx
      have hz := ((hF x hx).sub (hp x hx)).deriv
      simpa [H] using hz
    have hone : (1 : ℝ) ∈ U := by
      norm_num [U]
    refine ⟨F 1 - p 1, ?_⟩
    intro x hx
    have heq : H x = H 1 :=
      isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
        hdiff hderiv hx hone
    dsimp [H] at heq
    linarith
  · intro hF
    rcases hF with ⟨C, hC⟩
    change ∀ x ∈ U, HasDerivAt F (g x) x
    intro x hx
    have hevent : F =ᶠ[nhds x] fun y => p y + C :=
      Filter.mem_of_superset (isOpen_Ioi.mem_nhds hx) (fun y hy => hC y hy)
    exact ((hp x hx).add_const C).congr_of_eventuallyEq hevent

private theorem substitution_eq_translates :
    Substitution = Translates primitive := by
  have harc : arc ∈ Family q := by
    intro x hx
    exact hasDerivAt_arc x hx
  have hchar : Family q = Translates arc :=
    family_eq_translates_of_hasDerivAt q arc hasDerivAt_arc
  ext F
  constructor
  · intro hF
    rcases hF with ⟨G, hG, C, hFC⟩
    have hGq : G ∈ Family q := by
      simpa [q] using hG
    have hGt : G ∈ Translates arc := by
      rw [← hchar]
      exact hGq
    rcases hGt with ⟨D, hGD⟩
    refine ⟨C - 2 * D, ?_⟩
    intro x hx
    rw [hFC x hx, hGD x hx]
    simp only [primitive, arc]
    ring
  · intro hF
    rcases hF with ⟨C, hFC⟩
    refine ⟨arc, ?_, C, ?_⟩
    · simpa [q] using harc
    · intro x hx
      rw [hFC x hx]
      rfl

theorem gap1 : Family f = Family rewritten := by
  ext F
  change
    (∀ x ∈ U, HasDerivAt F (f x) x) ↔
      (∀ x ∈ U, HasDerivAt F (rewritten x) x)
  constructor
  · intro h x hx
    simpa only [f_eq_rewritten x hx] using h x hx
  · intro h x hx
    simpa only [f_eq_rewritten x hx] using h x hx
theorem gap2 : Family f = Substitution := by
  calc
    Family f = Translates primitive :=
      family_eq_translates_of_hasDerivAt f primitive hasDerivAt_primitive
    _ = Substitution := substitution_eq_translates.symm
theorem gap3 : Substitution = Translates primitive := by
  exact substitution_eq_translates
theorem gap4 : Family f = Translates primitive := by
  exact family_eq_translates_of_hasDerivAt f primitive hasDerivAt_primitive

end
end ProofGap.Exercise2087
