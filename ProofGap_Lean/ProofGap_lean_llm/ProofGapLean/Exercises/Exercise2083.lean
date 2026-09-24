import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2083
noncomputable section

def f (x : ℝ) := Real.exp (2 * x) / (1 + Real.exp x)
def primitive (x : ℝ) := Real.exp x - Real.log (1 + Real.exp x)
def Family (g : ℝ → ℝ) := {F : ℝ → ℝ | ∀ x, HasDerivAt F (g x) x}
def Split := {F : ℝ → ℝ |
  ∃ A ∈ Family (fun x => Real.exp x - 1),
  ∃ B ∈ Family (fun x => 1 / (1 + Real.exp x)),
  ∃ C, ∀ x, F x = A x + B x + C}
def Reduced := {F : ℝ → ℝ |
  ∃ G ∈ Family (fun x => 1 - Real.exp x / (1 + Real.exp x)),
  ∃ C, ∀ x, F x = Real.exp x - x + G x + C}
def Translates (p : ℝ → ℝ) := {F : ℝ → ℝ | ∃ C, ∀ x, F x = p x + C}

private theorem exp_den_ne (x : ℝ) : 1 + Real.exp x ≠ 0 := by
  linarith [Real.exp_pos x]

private theorem f_eq_split (x : ℝ) :
    f x = (Real.exp x - 1) + 1 / (1 + Real.exp x) := by
  unfold f
  rw [show (2 : ℝ) * x = x + x by ring, Real.exp_add]
  field_simp [exp_den_ne x] <;> ring

private theorem one_sub_exp_div_eq (x : ℝ) :
    1 - Real.exp x / (1 + Real.exp x) = 1 / (1 + Real.exp x) := by
  field_simp [exp_den_ne x] <;> ring

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (f x) x := by
  have hinner : HasDerivAt (fun t : ℝ => 1 + Real.exp t) (Real.exp x) x := by
    exact (Real.hasDerivAt_exp x).const_add 1
  have hlog : HasDerivAt (fun t : ℝ => Real.log (1 + Real.exp t))
      ((1 + Real.exp x)⁻¹ * Real.exp x) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_log (exp_den_ne x)).comp x hinner
  unfold primitive f
  convert (Real.hasDerivAt_exp x).sub hlog using 1
  rw [show (2 : ℝ) * x = x + x by ring, Real.exp_add]
  field_simp [exp_den_ne x] <;> ring

private theorem family_eq_translates (g p : ℝ → ℝ)
    (hp : ∀ x, HasDerivAt p (g x) x) :
    Family g = Translates p := by
  ext F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (g x) x at hF
    refine ⟨F 0 - p 0, ?_⟩
    have hd : ∀ y, HasDerivAt (fun t => F t - p t) 0 y := by
      intro y
      convert (hF y).sub (hp y) using 1 <;> simp
    intro x
    have hc := is_const_of_deriv_eq_zero
      (fun y => (hd y).differentiableAt)
      (fun y => (hd y).deriv) x 0
    linarith [hc]
  · rintro ⟨C, hFC⟩
    change ∀ x, HasDerivAt F (g x) x
    have hEq : F = fun t => p t + C := funext hFC
    intro x
    rw [hEq]
    exact (hp x).add_const C

theorem gap1 : Family f =
    Family (fun x => (Real.exp (2 * x) - 1 + 1) / (1 + Real.exp x)) := by
  apply congrArg Family
  funext x
  unfold f
  ring
theorem gap2 :
    Family (fun x => (Real.exp (2 * x) - 1 + 1) / (1 + Real.exp x)) =
      Split := by
  ext F
  constructor
  · intro hF
    have hFf : F ∈ Family f := by
      rw [gap1]
      exact hF
    change ∀ x, HasDerivAt F (f x) x at hFf
    refine ⟨fun t => Real.exp t - t, ?_,
      fun t => F t - (Real.exp t - t), ?_, 0, ?_⟩
    · intro x
      exact (Real.hasDerivAt_exp x).sub (hasDerivAt_id x)
    · intro x
      convert (hFf x).sub
          ((Real.hasDerivAt_exp x).sub (hasDerivAt_id x)) using 1
      rw [f_eq_split]
      ring
    · intro x
      ring
  · rintro ⟨A, hA, B, hB, C, hC⟩
    change ∀ x, HasDerivAt A (Real.exp x - 1) x at hA
    change ∀ x, HasDerivAt B (1 / (1 + Real.exp x)) x at hB
    have hFf : F ∈ Family f := by
      change ∀ x, HasDerivAt F (f x) x
      intro x
      have hEq : F = fun t => A t + B t + C := funext hC
      rw [hEq]
      simpa only [f_eq_split] using
        ((hA x).add (hB x)).add_const C
    rw [gap1] at hFf
    exact hFf
theorem gap3 : Family f = Split := by
  exact gap1.trans gap2
theorem gap4 : Family f = Reduced := by
  ext F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (f x) x at hF
    refine ⟨fun t => F t - (Real.exp t - t), ?_, 0, ?_⟩
    · intro x
      convert (hF x).sub
          ((Real.hasDerivAt_exp x).sub (hasDerivAt_id x)) using 1
      rw [f_eq_split]
      change 1 - Real.exp x / (1 + Real.exp x) =
        Real.exp x - 1 + 1 / (1 + Real.exp x) - (Real.exp x - 1)
      rw [one_sub_exp_div_eq]
      ring
    · intro x
      ring
  · rintro ⟨G, hG, C, hC⟩
    change ∀ x, HasDerivAt G
      (1 - Real.exp x / (1 + Real.exp x)) x at hG
    change ∀ x, HasDerivAt F (f x) x
    intro x
    have hEq : F = fun t => Real.exp t - t + G t + C := funext hC
    rw [hEq]
    simpa only [f_eq_split, one_sub_exp_div_eq] using
      (((Real.hasDerivAt_exp x).sub (hasDerivAt_id x)).add (hG x)).add_const C
theorem gap5 : Reduced = Translates primitive := by
  rw [← gap4]
  exact family_eq_translates f primitive primitive_hasDerivAt
theorem gap6 : Family f = Translates primitive := by
  exact gap4.trans gap5

end
end ProofGap.Exercise2083
