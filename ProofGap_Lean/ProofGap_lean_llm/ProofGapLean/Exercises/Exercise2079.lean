import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2079
noncomputable section

def f (x : ℝ) := (x - Real.sin x) ^ 3
def expanded (x : ℝ) :=
  x ^ 3 - 3 * x ^ 2 * Real.sin x + 3 * x * Real.sin x ^ 2 - Real.sin x ^ 3
def primitive (x : ℝ) :=
  x ^ 4 / 4 + 3 * x ^ 2 / 4 + 3 * x ^ 2 * Real.cos x -
    x * (6 * Real.sin x + 3 / 4 * Real.sin (2 * x)) -
    (5 * Real.cos x + 3 / 8 * Real.cos (2 * x)) -
    Real.cos x ^ 3 / 3
def Family (g : ℝ → ℝ) := {F : ℝ → ℝ | ∀ x, HasDerivAt F (g x) x}
def Step2 := {F : ℝ → ℝ |
  ∃ A ∈ Family (fun x => x ^ 2 * deriv Real.cos x),
  ∃ B ∈ Family (fun x => x * (1 - Real.cos (2 * x))),
  ∃ C ∈ Family (fun x => (1 - Real.cos x ^ 2) * deriv Real.cos x),
  ∃ C₀, ∀ x, F x = x ^ 4 / 4 + 3 * A x + 3 / 2 * B x + C x + C₀}
def Step3 := {F : ℝ → ℝ |
  ∃ A ∈ Family (fun x => x * Real.cos x),
  ∃ B ∈ Family (fun x => x * deriv (fun y => Real.sin (2 * y)) x),
  ∃ C, ∀ x, F x = x ^ 4 / 4 + 3 * x ^ 2 * Real.cos x - 6 * A x +
    3 * x ^ 2 / 4 - 3 / 4 * B x + Real.cos x - Real.cos x ^ 3 / 3 + C}
def Step4 := {F : ℝ → ℝ |
  ∃ A ∈ Family (fun x => x * deriv Real.sin x),
  ∃ B ∈ Family (fun x => Real.sin (2 * x)), ∃ C, ∀ x,
  F x = x ^ 4 / 4 + 3 * x ^ 2 / 4 + 3 * x ^ 2 * Real.cos x -
    6 * A x - 3 / 4 * x * Real.sin (2 * x) + 3 / 4 * B x +
    Real.cos x - Real.cos x ^ 3 / 3 + C}
def ExpandedPrimitive := {F : ℝ → ℝ | ∃ C, ∀ x,
  F x = x ^ 4 / 4 + 3 * x ^ 2 / 4 + 3 * x ^ 2 * Real.cos x -
    6 * x * Real.sin x - 6 * Real.cos x -
    3 / 4 * x * Real.sin (2 * x) + Real.cos x -
    3 / 8 * Real.cos (2 * x) - Real.cos x ^ 3 / 3 + C}
def Translates (p : ℝ → ℝ) := {F : ℝ → ℝ | ∃ C, ∀ x, F x = p x + C}

private theorem hasDerivAt_sin_two (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin (2 * y))
      (2 * Real.cos (2 * x)) x := by
  convert (Real.hasDerivAt_sin (2 * x)).comp x
    ((hasDerivAt_id x).const_mul 2) using 1 <;> ring

private theorem hasDerivAt_cos_two (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.cos (2 * y))
      (-2 * Real.sin (2 * x)) x := by
  convert (Real.hasDerivAt_cos (2 * x)).comp x
    ((hasDerivAt_id x).const_mul 2) using 1 <;> ring

private theorem same_deriv_eq_add_const
    {F P g : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (g x) x)
    (hP : ∀ x, HasDerivAt P (g x) x) :
    ∀ x, F x = P x + (F 0 - P 0) := by
  intro x
  have hD : ∀ y, HasDerivAt (fun z => F z - P z) 0 y := by
    intro y
    convert (hF y).sub (hP y) using 1 <;> ring
  have hEq := is_const_of_deriv_eq_zero
    (fun y => (hD y).differentiableAt)
    (fun y => (hD y).deriv) x 0
  linarith [hEq]

private def auxA2 (x : ℝ) :=
  x ^ 2 * Real.cos x - 2 * (x * Real.sin x) - 2 * Real.cos x

private theorem auxA2_hasDerivAt (x : ℝ) :
    HasDerivAt auxA2 (x ^ 2 * deriv Real.cos x) x := by
  change HasDerivAt
    (fun y : ℝ => y ^ 2 * Real.cos y - 2 * (y * Real.sin y) -
      2 * Real.cos y) (x ^ 2 * deriv Real.cos x) x
  convert (((((hasDerivAt_id x).pow 2).mul (Real.hasDerivAt_cos x)).sub
    (((hasDerivAt_id x).mul (Real.hasDerivAt_sin x)).const_mul 2)).sub
    ((Real.hasDerivAt_cos x).const_mul 2)) using 1
  rw [(Real.hasDerivAt_cos x).deriv]
  simp only [id_eq, Pi.pow_apply]
  ring

private def auxB2 (x : ℝ) :=
  x ^ 2 / 2 - (x * Real.sin (2 * x)) / 2 - Real.cos (2 * x) / 4

private theorem auxB2_hasDerivAt (x : ℝ) :
    HasDerivAt auxB2 (x * (1 - Real.cos (2 * x))) x := by
  change HasDerivAt
    (fun y : ℝ => y ^ 2 / 2 - (y * Real.sin (2 * y)) / 2 -
      Real.cos (2 * y) / 4) (x * (1 - Real.cos (2 * x))) x
  convert (((((hasDerivAt_id x).pow 2).div_const 2).sub
    (((hasDerivAt_id x).mul (hasDerivAt_sin_two x)).div_const 2)).sub
    ((hasDerivAt_cos_two x).div_const 4)) using 1
  simp only [id_eq, Pi.pow_apply]
  ring

private def auxC2 (x : ℝ) := Real.cos x - Real.cos x ^ 3 / 3

private theorem auxC2_hasDerivAt (x : ℝ) :
    HasDerivAt auxC2
      ((1 - Real.cos x ^ 2) * deriv Real.cos x) x := by
  change HasDerivAt
    (fun y : ℝ => Real.cos y - Real.cos y ^ 3 / 3)
    ((1 - Real.cos x ^ 2) * deriv Real.cos x) x
  convert (Real.hasDerivAt_cos x).sub
    (((Real.hasDerivAt_cos x).pow 3).div_const 3) using 1
  rw [(Real.hasDerivAt_cos x).deriv]
  ring

private def auxP2 (A B C : ℝ → ℝ) (x : ℝ) :=
  x ^ 4 / 4 + 3 * A x + 3 / 2 * B x + C x

private theorem auxP2_hasDerivAt
    {A B C : ℝ → ℝ}
    (hA : ∀ x, HasDerivAt A (x ^ 2 * deriv Real.cos x) x)
    (hB : ∀ x, HasDerivAt B (x * (1 - Real.cos (2 * x))) x)
    (hC : ∀ x, HasDerivAt C
      ((1 - Real.cos x ^ 2) * deriv Real.cos x) x) :
    ∀ x, HasDerivAt (auxP2 A B C) (f x) x := by
  intro x
  have hcos : deriv Real.cos x = -Real.sin x :=
    (Real.hasDerivAt_cos x).deriv
  have hsquare : 1 - Real.cos x ^ 2 = Real.sin x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hdouble : 1 - Real.cos (2 * x) = 2 * Real.sin x ^ 2 := by
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq x]
  change HasDerivAt
    (fun y : ℝ => y ^ 4 / 4 + 3 * A y + 3 / 2 * B y + C y)
    (f x) x
  convert (((((hasDerivAt_id x).pow 4).div_const 4).add
    ((hA x).const_mul 3)).add
    ((hB x).const_mul (3 / 2))).add (hC x) using 1
  rw [hcos, hsquare, hdouble]
  simp only [f, id_eq, Pi.pow_apply]
  ring

private def auxA3 (x : ℝ) := x * Real.sin x + Real.cos x

private theorem auxA3_hasDerivAt (x : ℝ) :
    HasDerivAt auxA3 (x * Real.cos x) x := by
  change HasDerivAt
    (fun y : ℝ => y * Real.sin y + Real.cos y)
    (x * Real.cos x) x
  convert ((hasDerivAt_id x).mul (Real.hasDerivAt_sin x)).add
    (Real.hasDerivAt_cos x) using 1
  simp only [id_eq, Pi.pow_apply]
  ring

private def auxB3 (x : ℝ) :=
  x * Real.sin (2 * x) + Real.cos (2 * x) / 2

private theorem auxB3_hasDerivAt (x : ℝ) :
    HasDerivAt auxB3
      (x * deriv (fun y : ℝ => Real.sin (2 * y)) x) x := by
  change HasDerivAt
    (fun y : ℝ => y * Real.sin (2 * y) + Real.cos (2 * y) / 2)
    (x * deriv (fun y : ℝ => Real.sin (2 * y)) x) x
  convert ((hasDerivAt_id x).mul (hasDerivAt_sin_two x)).add
    ((hasDerivAt_cos_two x).div_const 2) using 1
  rw [(hasDerivAt_sin_two x).deriv]
  simp only [id_eq, Pi.pow_apply]
  ring

private def auxP3 (A B : ℝ → ℝ) (x : ℝ) :=
  x ^ 4 / 4 + 3 * x ^ 2 * Real.cos x - 6 * A x +
    3 * x ^ 2 / 4 - 3 / 4 * B x + Real.cos x -
    Real.cos x ^ 3 / 3

private theorem auxP3_hasDerivAt
    {A B : ℝ → ℝ}
    (hA : ∀ x, HasDerivAt A (x * Real.cos x) x)
    (hB : ∀ x, HasDerivAt B
      (x * deriv (fun y : ℝ => Real.sin (2 * y)) x) x) :
    ∀ x, HasDerivAt (auxP3 A B) (f x) x := by
  intro x
  have hsinTwo : deriv (fun y : ℝ => Real.sin (2 * y)) x =
      2 * Real.cos (2 * x) := (hasDerivAt_sin_two x).deriv
  have hunit : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hdouble : Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2 := by
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq x]
  change HasDerivAt
    (fun y : ℝ => y ^ 4 / 4 + 3 * y ^ 2 * Real.cos y - 6 * A y +
      3 * y ^ 2 / 4 - 3 / 4 * B y + Real.cos y -
      Real.cos y ^ 3 / 3) (f x) x
  have h0 := ((hasDerivAt_id x).pow 4).div_const 4
  have h1 := h0.add
    ((((hasDerivAt_id x).pow 2).mul (Real.hasDerivAt_cos x)).const_mul 3)
  have h2 := h1.sub ((hA x).const_mul 6)
  have h3 := h2.add
    ((((hasDerivAt_id x).pow 2).const_mul 3).div_const 4)
  have h4 := h3.sub ((hB x).const_mul (3 / 4))
  have h5 := h4.add (Real.hasDerivAt_cos x)
  have h6 := h5.sub (((Real.hasDerivAt_cos x).pow 3).div_const 3)
  convert h6 using 1
  · funext y
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
    ring
  · rw [hsinTwo, hdouble]
    simp only [f, id_eq, Pi.pow_apply]
    rw [hunit]
    ring

private def auxB4 (x : ℝ) := -Real.cos (2 * x) / 2

private theorem auxB4_hasDerivAt (x : ℝ) :
    HasDerivAt auxB4 (Real.sin (2 * x)) x := by
  change HasDerivAt
    (fun y : ℝ => -Real.cos (2 * y) / 2) (Real.sin (2 * x)) x
  convert (hasDerivAt_cos_two x).neg.div_const 2 using 1
  ring

private def auxP4 (A B : ℝ → ℝ) (x : ℝ) :=
  x ^ 4 / 4 + 3 * x ^ 2 / 4 + 3 * x ^ 2 * Real.cos x -
    6 * A x - 3 / 4 * x * Real.sin (2 * x) + 3 / 4 * B x +
    Real.cos x - Real.cos x ^ 3 / 3

private theorem auxP4_hasDerivAt
    {A B : ℝ → ℝ}
    (hA : ∀ x, HasDerivAt A (x * deriv Real.sin x) x)
    (hB : ∀ x, HasDerivAt B (Real.sin (2 * x)) x) :
    ∀ x, HasDerivAt (auxP4 A B) (f x) x := by
  intro x
  have hsin : deriv Real.sin x = Real.cos x :=
    (Real.hasDerivAt_sin x).deriv
  have hunit : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hdouble : Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2 := by
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq x]
  change HasDerivAt
    (fun y : ℝ => y ^ 4 / 4 + 3 * y ^ 2 / 4 +
      3 * y ^ 2 * Real.cos y - 6 * A y -
      3 / 4 * y * Real.sin (2 * y) + 3 / 4 * B y +
      Real.cos y - Real.cos y ^ 3 / 3) (f x) x
  have h0 := ((hasDerivAt_id x).pow 4).div_const 4
  have h1 := h0.add
    ((((hasDerivAt_id x).pow 2).const_mul 3).div_const 4)
  have h2 := h1.add
    ((((hasDerivAt_id x).pow 2).mul (Real.hasDerivAt_cos x)).const_mul 3)
  have h3 := h2.sub ((hA x).const_mul 6)
  have h4 := h3.sub
    (((hasDerivAt_id x).const_mul (3 / 4)).mul
      (hasDerivAt_sin_two x))
  have h5 := h4.add ((hB x).const_mul (3 / 4))
  have h6 := h5.add (Real.hasDerivAt_cos x)
  have h7 := h6.sub (((Real.hasDerivAt_cos x).pow 3).div_const 3)
  convert h7 using 1
  · funext y
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
    ring
  · rw [hsin, hdouble]
    simp only [f, id_eq, Pi.pow_apply]
    rw [hunit]
    ring

private def auxP5 (x : ℝ) :=
  x ^ 4 / 4 + 3 * x ^ 2 / 4 + 3 * x ^ 2 * Real.cos x -
    6 * x * Real.sin x - 6 * Real.cos x -
    3 / 4 * x * Real.sin (2 * x) + Real.cos x -
    3 / 8 * Real.cos (2 * x) - Real.cos x ^ 3 / 3

private theorem auxP5_eq_auxP4 : auxP5 = auxP4 auxA3 auxB4 := by
  funext x
  simp only [auxP5, auxP4, auxA3, auxB4]
  ring

private theorem auxP5_hasDerivAt (x : ℝ) :
    HasDerivAt auxP5 (f x) x := by
  rw [auxP5_eq_auxP4]
  apply auxP4_hasDerivAt
  · intro y
    convert auxA3_hasDerivAt y using 1
    rw [(Real.hasDerivAt_sin y).deriv]
  · exact auxB4_hasDerivAt

private theorem auxP5_eq_primitive (x : ℝ) : auxP5 x = primitive x := by
  simp only [auxP5, primitive]
  ring

theorem gap1 : Family f = Family expanded := by
  apply Set.ext
  intro F
  simp only [Family, Set.mem_setOf_eq]
  constructor
  · intro h x
    convert h x using 1
    simp only [f, expanded]
    ring
  · intro h x
    convert h x using 1
    simp only [f, expanded]
    ring
theorem gap2 : Family f = Step2 := by
  apply Set.ext
  intro F
  simp only [Family, Step2, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨auxA2, auxA2_hasDerivAt, auxB2, auxB2_hasDerivAt,
      auxC2, auxC2_hasDerivAt, F 0 - auxP2 auxA2 auxB2 auxC2 0, ?_⟩
    intro x
    simpa only [auxP2] using
      same_deriv_eq_add_const hF
        (auxP2_hasDerivAt auxA2_hasDerivAt auxB2_hasDerivAt auxC2_hasDerivAt) x
  · rintro ⟨A, hA, B, hB, C, hC, C₀, hF⟩ x
    have hEq : F = fun y => auxP2 A B C y + C₀ := by
      funext y
      simpa only [auxP2] using hF y
    rw [hEq]
    exact (auxP2_hasDerivAt hA hB hC x).add_const C₀
theorem gap3 : Family f = Step3 := by
  apply Set.ext
  intro F
  simp only [Family, Step3, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨auxA3, auxA3_hasDerivAt, auxB3, auxB3_hasDerivAt,
      F 0 - auxP3 auxA3 auxB3 0, ?_⟩
    intro x
    simpa only [auxP3] using
      same_deriv_eq_add_const hF
        (auxP3_hasDerivAt auxA3_hasDerivAt auxB3_hasDerivAt) x
  · rintro ⟨A, hA, B, hB, C, hF⟩ x
    have hEq : F = fun y => auxP3 A B y + C := by
      funext y
      simpa only [auxP3] using hF y
    rw [hEq]
    exact (auxP3_hasDerivAt hA hB x).add_const C
theorem gap4 : Family f = Step4 := by
  apply Set.ext
  intro F
  simp only [Family, Step4, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨auxA3, ?_, auxB4, auxB4_hasDerivAt,
      F 0 - auxP4 auxA3 auxB4 0, ?_⟩
    · intro x
      convert auxA3_hasDerivAt x using 1
      rw [(Real.hasDerivAt_sin x).deriv]
    · intro x
      simpa only [auxP4] using
        same_deriv_eq_add_const hF
          (auxP4_hasDerivAt
            (fun y => by
              convert auxA3_hasDerivAt y using 1
              rw [(Real.hasDerivAt_sin y).deriv])
            auxB4_hasDerivAt) x
  · rintro ⟨A, hA, B, hB, C, hF⟩ x
    have hEq : F = fun y => auxP4 A B y + C := by
      funext y
      simpa only [auxP4] using hF y
    rw [hEq]
    exact (auxP4_hasDerivAt hA hB x).add_const C
theorem gap5 : Family f = ExpandedPrimitive := by
  apply Set.ext
  intro F
  simp only [Family, ExpandedPrimitive, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨F 0 - auxP5 0, ?_⟩
    intro x
    simpa only [auxP5] using
      same_deriv_eq_add_const hF auxP5_hasDerivAt x
  · rintro ⟨C, hF⟩ x
    have hEq : F = fun y => auxP5 y + C := by
      funext y
      simpa only [auxP5] using hF y
    rw [hEq]
    exact (auxP5_hasDerivAt x).add_const C
theorem gap6 : Family f = Translates primitive := by
  rw [gap5]
  apply Set.ext
  intro F
  simp only [ExpandedPrimitive, Translates, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x
    calc
      F x = auxP5 x + C := by simpa only [auxP5] using hF x
      _ = primitive x + C := by rw [auxP5_eq_primitive]
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x
    calc
      F x = primitive x + C := hF x
      _ = auxP5 x + C := by rw [auxP5_eq_primitive]
      _ = x ^ 4 / 4 + 3 * x ^ 2 / 4 + 3 * x ^ 2 * Real.cos x -
          6 * x * Real.sin x - 6 * Real.cos x -
          3 / 4 * x * Real.sin (2 * x) + Real.cos x -
          3 / 8 * Real.cos (2 * x) - Real.cos x ^ 3 / 3 + C := by
            rfl

end
end ProofGap.Exercise2079
