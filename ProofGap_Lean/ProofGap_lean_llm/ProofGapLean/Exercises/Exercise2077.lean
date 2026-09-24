import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2077
noncomputable section

def f (x : ℝ) := x ^ 2 * Real.exp x * Real.cos x
def g (x : ℝ) := Real.exp x * (2 * x * Real.cos x - x ^ 2 * Real.sin x)
def primitive (x : ℝ) :=
  Real.exp x / 2 *
    (x ^ 2 * (Real.sin x + Real.cos x) - 2 * x * Real.sin x +
      Real.sin x - Real.cos x)
def Family (h : ℝ → ℝ) := {F : ℝ → ℝ | ∀ x, HasDerivAt F (h x) x}
def Parts := {F : ℝ → ℝ | ∃ G ∈ Family g, ∃ C,
  ∀ x, F x = x ^ 2 * Real.exp x * Real.cos x - G x + C}
def SelfStep := {F : ℝ → ℝ |
  ∃ A ∈ Family (fun x => Real.exp x * Real.cos x),
  ∃ B ∈ Family (fun x => x * Real.exp x * Real.sin x),
  ∃ H ∈ Family f, ∃ C, ∀ x,
    F x = Real.exp x * (x ^ 2 * (Real.sin x + Real.cos x) -
      2 * x * Real.cos x) + 2 * A x - 4 * B x - H x + C}
def Reduced := {F : ℝ → ℝ |
  ∃ A ∈ Family (fun x => Real.exp x * Real.cos x),
  ∃ B ∈ Family (fun x => x * Real.exp x * Real.sin x),
  ∃ C, ∀ x, F x = Real.exp x / 2 *
    (x ^ 2 * (Real.sin x + Real.cos x) - 2 * x * Real.cos x) +
    A x - 2 * B x + C}
def Translates (p : ℝ → ℝ) := {F : ℝ → ℝ | ∃ C, ∀ x, F x = p x + C}

private theorem hasDerivAt_main (x : ℝ) :
    HasDerivAt f (f x + g x) x := by
  unfold f g
  convert ((((hasDerivAt_id x).pow 2).mul (Real.hasDerivAt_exp x)).mul
    (Real.hasDerivAt_cos x)) using 1 <;> simp <;> ring

private theorem family_eq_parts : Family f = Parts := by
  ext F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (f x) x at hF
    change ∃ G ∈ Family g, ∃ C, ∀ x,
      F x = x ^ 2 * Real.exp x * Real.cos x - G x + C
    refine ⟨fun x => f x - F x, ?_, 0, ?_⟩
    · change ∀ x, HasDerivAt (fun y => f y - F y) (g x) x
      intro x
      convert (hasDerivAt_main x).sub (hF x) using 1 <;> ring
    · intro x
      unfold f
      ring
  · rintro ⟨G, hG, C, hEq⟩
    change ∀ x, HasDerivAt F (f x) x
    have hfun : F = fun y => f y - G y + C := by
      funext y
      simpa [f] using hEq y
    rw [hfun]
    intro x
    convert ((hasDerivAt_main x).sub (hG x)).add
      (hasDerivAt_const x C) using 1 <;> ring

private theorem exists_eq_add_const {h F P : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (h x) x)
    (hP : ∀ x, HasDerivAt P (h x) x) :
    ∃ C, ∀ x, F x = P x + C := by
  let D : ℝ → ℝ := fun x => F x - P x
  have hD : ∀ x, HasDerivAt D 0 x := by
    intro x
    dsimp [D]
    convert (hF x).sub (hP x) using 1 <;> ring
  have hc : ∀ x, D x = D 0 := by
    intro x
    exact is_const_of_deriv_eq_zero
      (fun y => (hD y).differentiableAt)
      (fun y => (hD y).deriv) x 0
  refine ⟨F 0 - P 0, ?_⟩
  intro x
  calc
    F x = (F x - P x) + P x := by ring
    _ = (F 0 - P 0) + P x := by
      simpa [D] using congrArg (fun z => z + P x) (hc x)
    _ = P x + (F 0 - P 0) := by ring

private def integrationAuxA (x : ℝ) :=
  Real.exp x / 2 * (Real.sin x + Real.cos x)

private theorem hasDerivAt_integrationAuxA (x : ℝ) :
    HasDerivAt integrationAuxA (Real.exp x * Real.cos x) x := by
  unfold integrationAuxA
  have hsc := (Real.hasDerivAt_sin x).add (Real.hasDerivAt_cos x)
  convert ((Real.hasDerivAt_exp x).div_const 2).mul hsc using 1 <;>
    simp <;> ring

private def integrationAuxB (x : ℝ) :=
  Real.exp x / 2 *
    (x * (Real.sin x - Real.cos x) + Real.cos x)

private theorem hasDerivAt_integrationAuxB (x : ℝ) :
    HasDerivAt integrationAuxB (x * Real.exp x * Real.sin x) x := by
  unfold integrationAuxB
  have hsc := (Real.hasDerivAt_sin x).sub (Real.hasDerivAt_cos x)
  have hinner := ((hasDerivAt_id x).mul hsc).add (Real.hasDerivAt_cos x)
  convert ((Real.hasDerivAt_exp x).div_const 2).mul hinner using 1 <;>
    simp <;> ring

private theorem hasDerivAt_self_expr {A B H : ℝ → ℝ}
    (hA : ∀ x, HasDerivAt A (Real.exp x * Real.cos x) x)
    (hB : ∀ x, HasDerivAt B (x * Real.exp x * Real.sin x) x)
    (hH : ∀ x, HasDerivAt H (f x) x) (x : ℝ) :
    HasDerivAt
      (fun y => Real.exp y *
          (y ^ 2 * (Real.sin y + Real.cos y) - 2 * y * Real.cos y) +
        2 * A y - 4 * B y - H y)
      (f x) x := by
  have hsc := (Real.hasDerivAt_sin x).add (Real.hasDerivAt_cos x)
  have hinner :=
    (((hasDerivAt_id x).pow 2).mul hsc).sub
      (((hasDerivAt_id x).const_mul 2).mul (Real.hasDerivAt_cos x))
  have hbase := (Real.hasDerivAt_exp x).mul hinner
  have hd := (((hbase.add ((hA x).const_mul 2)).sub
    ((hB x).const_mul 4)).sub (hH x))
  convert hd using 1 <;> simp [f] <;> ring

private theorem family_eq_selfStep : Family f = SelfStep := by
  ext F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (f x) x at hF
    let R : ℝ → ℝ := fun y => Real.exp y *
        (y ^ 2 * (Real.sin y + Real.cos y) - 2 * y * Real.cos y) +
      2 * integrationAuxA y - 4 * integrationAuxB y - F y
    have hR : ∀ x, HasDerivAt R (f x) x := by
      intro x
      dsimp [R]
      exact hasDerivAt_self_expr hasDerivAt_integrationAuxA
        hasDerivAt_integrationAuxB hF x
    obtain ⟨C, hC⟩ := exists_eq_add_const hF hR
    change ∃ A ∈ Family (fun x => Real.exp x * Real.cos x),
      ∃ B ∈ Family (fun x => x * Real.exp x * Real.sin x),
      ∃ H ∈ Family f, ∃ C, ∀ x,
        F x = Real.exp x *
          (x ^ 2 * (Real.sin x + Real.cos x) - 2 * x * Real.cos x) +
          2 * A x - 4 * B x - H x + C
    refine ⟨integrationAuxA, hasDerivAt_integrationAuxA,
      integrationAuxB, hasDerivAt_integrationAuxB, F, hF, C, ?_⟩
    intro x
    simpa [R] using hC x
  · rintro ⟨A, hA, B, hB, H, hH, C, hEq⟩
    change ∀ x, HasDerivAt F (f x) x
    let R : ℝ → ℝ := fun y => Real.exp y *
        (y ^ 2 * (Real.sin y + Real.cos y) - 2 * y * Real.cos y) +
      2 * A y - 4 * B y - H y
    have hR : ∀ x, HasDerivAt R (f x) x := by
      intro x
      dsimp [R]
      exact hasDerivAt_self_expr hA hB hH x
    have hfun : F = fun y => R y + C := by
      funext y
      simpa [R] using hEq y
    rw [hfun]
    intro x
    convert (hR x).add (hasDerivAt_const x C) using 1 <;> ring

private theorem hasDerivAt_reduced_expr {A B : ℝ → ℝ}
    (hA : ∀ x, HasDerivAt A (Real.exp x * Real.cos x) x)
    (hB : ∀ x, HasDerivAt B (x * Real.exp x * Real.sin x) x)
    (x : ℝ) :
    HasDerivAt
      (fun y => Real.exp y / 2 *
          (y ^ 2 * (Real.sin y + Real.cos y) - 2 * y * Real.cos y) +
        A y - 2 * B y)
      (f x) x := by
  have hsc := (Real.hasDerivAt_sin x).add (Real.hasDerivAt_cos x)
  have hinner :=
    (((hasDerivAt_id x).pow 2).mul hsc).sub
      (((hasDerivAt_id x).const_mul 2).mul (Real.hasDerivAt_cos x))
  have hbase := ((Real.hasDerivAt_exp x).div_const 2).mul hinner
  have hd := (hbase.add (hA x)).sub ((hB x).const_mul 2)
  convert hd using 1 <;> simp [f] <;> ring

private theorem family_eq_reduced : Family f = Reduced := by
  ext F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (f x) x at hF
    let R : ℝ → ℝ := fun y => Real.exp y / 2 *
        (y ^ 2 * (Real.sin y + Real.cos y) - 2 * y * Real.cos y) +
      integrationAuxA y - 2 * integrationAuxB y
    have hR : ∀ x, HasDerivAt R (f x) x := by
      intro x
      dsimp [R]
      exact hasDerivAt_reduced_expr hasDerivAt_integrationAuxA
        hasDerivAt_integrationAuxB x
    obtain ⟨C, hC⟩ := exists_eq_add_const hF hR
    change ∃ A ∈ Family (fun x => Real.exp x * Real.cos x),
      ∃ B ∈ Family (fun x => x * Real.exp x * Real.sin x),
      ∃ C, ∀ x, F x = Real.exp x / 2 *
        (x ^ 2 * (Real.sin x + Real.cos x) - 2 * x * Real.cos x) +
        A x - 2 * B x + C
    refine ⟨integrationAuxA, hasDerivAt_integrationAuxA,
      integrationAuxB, hasDerivAt_integrationAuxB, C, ?_⟩
    intro x
    simpa [R] using hC x
  · rintro ⟨A, hA, B, hB, C, hEq⟩
    change ∀ x, HasDerivAt F (f x) x
    let R : ℝ → ℝ := fun y => Real.exp y / 2 *
        (y ^ 2 * (Real.sin y + Real.cos y) - 2 * y * Real.cos y) +
      A y - 2 * B y
    have hR : ∀ x, HasDerivAt R (f x) x := by
      intro x
      dsimp [R]
      exact hasDerivAt_reduced_expr hA hB x
    have hfun : F = fun y => R y + C := by
      funext y
      simpa [R] using hEq y
    rw [hfun]
    intro x
    convert (hR x).add (hasDerivAt_const x C) using 1 <;> ring

private theorem hasDerivAt_primitive (x : ℝ) :
    HasDerivAt primitive (f x) x := by
  have hsc := (Real.hasDerivAt_sin x).add (Real.hasDerivAt_cos x)
  have hfirst := ((hasDerivAt_id x).pow 2).mul hsc
  have hsecond :=
    ((hasDerivAt_id x).const_mul 2).mul (Real.hasDerivAt_sin x)
  have hinner := ((hfirst.sub hsecond).add
    (Real.hasDerivAt_sin x)).sub (Real.hasDerivAt_cos x)
  unfold primitive f
  convert ((Real.hasDerivAt_exp x).div_const 2).mul hinner using 1 <;>
    simp <;> ring

private theorem family_eq_translates_primitive :
    Family f = Translates primitive := by
  ext F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (f x) x at hF
    change ∃ C, ∀ x, F x = primitive x + C
    exact exists_eq_add_const hF hasDerivAt_primitive
  · rintro ⟨C, hEq⟩
    change ∀ x, HasDerivAt F (f x) x
    have hfun : F = fun y => primitive y + C := by
      funext y
      exact hEq y
    rw [hfun]
    intro x
    convert (hasDerivAt_primitive x).add
      (hasDerivAt_const x C) using 1 <;> ring

theorem gap1 : Family f =
    Family (fun x => x ^ 2 * Real.cos x * deriv Real.exp x) := by
  ext F
  change (∀ x, HasDerivAt F (f x) x) ↔
    (∀ x, HasDerivAt F (x ^ 2 * Real.cos x * deriv Real.exp x) x)
  constructor
  · intro h x
    have he : deriv Real.exp x = Real.exp x :=
      (Real.hasDerivAt_exp x).deriv
    simpa [f, he, mul_comm, mul_left_comm, mul_assoc] using h x
  · intro h x
    have he : deriv Real.exp x = Real.exp x :=
      (Real.hasDerivAt_exp x).deriv
    simpa [f, he, mul_comm, mul_left_comm, mul_assoc] using h x
theorem gap2 : Family (fun x => x ^ 2 * Real.cos x * deriv Real.exp x) =
    Parts := by
  calc
    Family (fun x => x ^ 2 * Real.cos x * deriv Real.exp x) = Family f := gap1.symm
    _ = Parts := family_eq_parts
theorem gap3 : Family f = Parts := by
  exact family_eq_parts
theorem gap4 : Family f = Parts := by
  exact family_eq_parts
theorem gap5 : Family f = SelfStep := by
  exact family_eq_selfStep
theorem gap6 : Family f = Reduced := by
  exact family_eq_reduced
theorem gap7 : Family f = Translates primitive := by
  exact family_eq_translates_primitive

end
end ProofGap.Exercise2077
