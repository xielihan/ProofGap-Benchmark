import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2082
noncomputable section

def f (x : ℝ) := 1 / (1 + Real.exp x) ^ 2
def primitive (x : ℝ) :=
  x - Real.log (1 + Real.exp x) + 1 / (1 + Real.exp x)
def Family (g : ℝ → ℝ) := {F : ℝ → ℝ | ∀ x, HasDerivAt F (g x) x}
def Split := {F : ℝ → ℝ |
  ∃ A ∈ Family (fun x => 1 / (1 + Real.exp x)),
  ∃ B ∈ Family (fun x => Real.exp x / (1 + Real.exp x) ^ 2),
  ∃ C, ∀ x, F x = A x - B x + C}
def Rewritten := {F : ℝ → ℝ |
  ∃ A ∈ Family (fun x => 1 - Real.exp x / (1 + Real.exp x)),
  ∃ B ∈ Family (fun x => deriv (fun y => 1 + Real.exp y) x /
    (1 + Real.exp x) ^ 2),
  ∃ C, ∀ x, F x = A x - B x + C}
def Translates (p : ℝ → ℝ) := {F : ℝ → ℝ | ∃ C, ∀ x, F x = p x + C}

private def splitLeft (x : ℝ) :=
  x - Real.log (1 + Real.exp x)

private def splitRight (x : ℝ) :=
  -(1 / (1 + Real.exp x))

private theorem one_add_exp_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => 1 + Real.exp y) (Real.exp x) x := by
  exact (Real.hasDerivAt_exp x).const_add 1

private theorem split_derivatives (x : ℝ) :
    HasDerivAt splitLeft (1 / (1 + Real.exp x)) x ∧
      HasDerivAt splitRight
        (Real.exp x / (1 + Real.exp x) ^ 2) x := by
  have hu : 1 + Real.exp x ≠ 0 :=
    ne_of_gt (add_pos zero_lt_one (Real.exp_pos x))
  have harg := one_add_exp_hasDerivAt x
  have hlog : HasDerivAt
      (fun y : ℝ => Real.log (1 + Real.exp y))
      (Real.exp x / (1 + Real.exp x)) x :=
    harg.log hu
  have hinv : HasDerivAt
      (fun y : ℝ => 1 / (1 + Real.exp y))
      (-Real.exp x / (1 + Real.exp x) ^ 2) x := by
    simpa [one_div] using harg.inv hu
  constructor
  · unfold splitLeft
    convert (hasDerivAt_id x).sub hlog using 1
    field_simp [hu]
    ring
  · unfold splitRight
    convert hinv.neg using 1 <;> ring

private theorem primitive_eq_split (x : ℝ) :
    primitive x = splitLeft x - splitRight x := by
  unfold primitive splitLeft splitRight
  ring

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (f x) x := by
  have hs := (split_derivatives x).1.sub (split_derivatives x).2
  have hfun : primitive = fun y => splitLeft y - splitRight y := by
    funext y
    exact primitive_eq_split y
  rw [hfun]
  unfold f
  have hu : 1 + Real.exp x ≠ 0 :=
    ne_of_gt (add_pos zero_lt_one (Real.exp_pos x))
  convert hs using 1
  field_simp [hu]
  ring

private theorem family_f_eq_translates :
    Family f = Translates primitive := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (f x) x at hF
    let d : ℝ → ℝ := fun x => F x - primitive x
    have hd : ∀ x, HasDerivAt d 0 x := by
      intro x
      simpa [d] using (hF x).sub (primitive_hasDerivAt x)
    have hdiff : Differentiable ℝ d := fun x => (hd x).differentiableAt
    have hderiv : ∀ x, deriv d x = 0 := fun x => (hd x).deriv
    change ∃ C, ∀ x, F x = primitive x + C
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hx : d x = d 0 :=
      is_const_of_deriv_eq_zero hdiff hderiv x 0
    change F x - primitive x = F 0 - primitive 0 at hx
    simpa [add_comm] using (sub_eq_iff_eq_add.mp hx)
  · intro hF
    change ∃ C, ∀ x, F x = primitive x + C at hF
    rcases hF with ⟨C, hC⟩
    have hfun : F = fun y => primitive y + C := funext hC
    change ∀ x, HasDerivAt F (f x) x
    intro x
    rw [hfun]
    convert (primitive_hasDerivAt x).add (hasDerivAt_const x C) using 1 <;> ring

private theorem rewritten_first :
    (fun x : ℝ => 1 - Real.exp x / (1 + Real.exp x)) =
      (fun x : ℝ => 1 / (1 + Real.exp x)) := by
  funext x
  have hu : 1 + Real.exp x ≠ 0 :=
    ne_of_gt (add_pos zero_lt_one (Real.exp_pos x))
  field_simp [hu]
  ring

private theorem rewritten_second :
    (fun x : ℝ => deriv (fun y : ℝ => 1 + Real.exp y) x /
      (1 + Real.exp x) ^ 2) =
      (fun x : ℝ => Real.exp x / (1 + Real.exp x) ^ 2) := by
  funext x
  rw [(one_add_exp_hasDerivAt x).deriv]

theorem gap1 : Family f =
    Family (fun x => (1 + Real.exp x - Real.exp x) / (1 + Real.exp x) ^ 2) := by
  apply congrArg Family
  funext x
  unfold f
  have hu : 1 + Real.exp x ≠ 0 :=
    ne_of_gt (add_pos zero_lt_one (Real.exp_pos x))
  field_simp [hu]
  ring
theorem gap2 :
    Family (fun x => (1 + Real.exp x - Real.exp x) / (1 + Real.exp x) ^ 2) =
      Split := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    have hf : F ∈ Family f := by
      rw [gap1]
      exact hF
    have ht : F ∈ Translates primitive := by
      rw [← family_f_eq_translates]
      exact hf
    rcases ht with ⟨C, hC⟩
    refine ⟨splitLeft, ?_, splitRight, ?_, C, ?_⟩
    · change ∀ x, HasDerivAt splitLeft
        (1 / (1 + Real.exp x)) x
      intro x
      exact (split_derivatives x).1
    · change ∀ x, HasDerivAt splitRight
        (Real.exp x / (1 + Real.exp x) ^ 2) x
      intro x
      exact (split_derivatives x).2
    · intro x
      rw [hC x, primitive_eq_split x]
  · intro hF
    rcases hF with ⟨A, hA, B, hB, C, hC⟩
    change ∀ x, HasDerivAt A (1 / (1 + Real.exp x)) x at hA
    change ∀ x, HasDerivAt B
      (Real.exp x / (1 + Real.exp x) ^ 2) x at hB
    have hfun : F = fun y => A y - B y + C := funext hC
    change ∀ x, HasDerivAt F
      ((1 + Real.exp x - Real.exp x) / (1 + Real.exp x) ^ 2) x
    intro x
    rw [hfun]
    have hu : 1 + Real.exp x ≠ 0 :=
      ne_of_gt (add_pos zero_lt_one (Real.exp_pos x))
    convert ((hA x).sub (hB x)).add (hasDerivAt_const x C) using 1
    field_simp [hu]
    ring
theorem gap3 : Family f = Split := by
  exact gap1.trans gap2
theorem gap4 : Family f = Rewritten := by
  calc
    Family f = Split := gap3
    _ = Rewritten := by
      unfold Split Rewritten
      rw [rewritten_first, rewritten_second]
theorem gap5 : Rewritten = Translates primitive := by
  calc
    Rewritten = Family f := gap4.symm
    _ = Translates primitive := family_f_eq_translates
theorem gap6 : Family f = Translates primitive := by
  exact family_f_eq_translates

end
end ProofGap.Exercise2082
