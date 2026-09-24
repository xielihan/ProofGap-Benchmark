import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2078
noncomputable section

def f (x : ℝ) := x * Real.exp x * Real.sin x ^ 2
def oscillatory (x : ℝ) := x * Real.exp x * Real.cos (2 * x)
def aux (x : ℝ) := Real.exp x * (Real.cos (2 * x) - 2 * x * Real.sin (2 * x))
def primitive (x : ℝ) :=
  Real.exp x * ((x - 1) / 2 -
    x / 10 * (2 * Real.sin (2 * x) + Real.cos (2 * x)) +
    (1 / 50 : ℝ) * (4 * Real.sin (2 * x) - 3 * Real.cos (2 * x)))
def Family (g : ℝ → ℝ) := {F : ℝ → ℝ | ∀ x, HasDerivAt F (g x) x}
def HalfAngle := {F : ℝ → ℝ |
  ∃ G ∈ Family (fun x => x * Real.exp x * (1 - Real.cos (2 * x))),
  ∃ C, ∀ x, F x = G x / 2 + C}
def Split := {F : ℝ → ℝ |
  ∃ A ∈ Family (fun x => x * Real.exp x), ∃ B ∈ Family oscillatory,
  ∃ C, ∀ x, F x = A x / 2 - B x / 2 + C}
def FirstParts := {F : ℝ → ℝ | ∃ G ∈ Family oscillatory, ∃ C, ∀ x,
  F x = Real.exp x * (x - 1) / 2 - G x / 2 + C}
def SecondParts := {F : ℝ → ℝ | ∃ G ∈ Family aux, ∃ C, ∀ x,
  F x = Real.exp x * (x - 1) / 2 -
    x * Real.exp x * Real.cos (2 * x) / 2 + G x / 2 + C}
def Coupled := {F : ℝ → ℝ |
  ∃ G ∈ Family (fun x => x * Real.exp x * Real.sin (2 * x)), ∃ C, ∀ x,
  F x = Real.exp x * (x - 1) / 2 -
    x * Real.exp x * Real.cos (2 * x) / 2 +
    Real.exp x / 10 * (Real.cos (2 * x) + 2 * Real.sin (2 * x)) - G x + C}
def ReverseCoupled := {G : ℝ → ℝ | ∃ F ∈ Family f, ∃ C, ∀ x,
  G x = x * Real.exp x * Real.sin (2 * x) -
    Real.exp x / 5 * (Real.sin (2 * x) - 2 * Real.cos (2 * x)) -
    2 * (x - 1) * Real.exp x + 4 * F x + C}
def Translates (p : ℝ → ℝ) := {F : ℝ → ℝ | ∃ C, ∀ x, F x = p x + C}

private theorem f_eq_half (x : ℝ) :
    f x = x * Real.exp x * (1 - Real.cos (2 * x)) / 2 := by
  unfold f
  rw [Real.cos_two_mul]
  rw [← Real.sin_sq_add_cos_sq x]
  ring

private theorem two_f (x : ℝ) :
    2 * f x = x * Real.exp x * (1 - Real.cos (2 * x)) := by
  rw [f_eq_half]
  ring

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

private theorem hasDerivAt_base (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp y * (y - 1))
      (x * Real.exp x) x := by
  convert (Real.hasDerivAt_exp x).mul
    ((hasDerivAt_id x).sub_const 1) using 1 <;>
    simp [id_eq] <;> ring

private theorem hasDerivAt_cos_product (x : ℝ) :
    HasDerivAt (fun y : ℝ => y * Real.exp y * Real.cos (2 * y))
      (oscillatory x + aux x) x := by
  convert ((hasDerivAt_id x).mul (Real.hasDerivAt_exp x)).mul
    (hasDerivAt_cos_two x) using 1 <;>
    simp [id_eq, oscillatory, aux] <;> ring

private theorem hasDerivAt_sin_product (x : ℝ) :
    HasDerivAt (fun y : ℝ => y * Real.exp y * Real.sin (2 * y))
      (Real.exp x * Real.sin (2 * x) +
        x * Real.exp x * Real.sin (2 * x) +
        2 * x * Real.exp x * Real.cos (2 * x)) x := by
  convert ((hasDerivAt_id x).mul (Real.hasDerivAt_exp x)).mul
    (hasDerivAt_sin_two x) using 1 <;>
    simp [id_eq] <;> ring

private theorem hasDerivAt_kernel (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => Real.exp y / 5 *
        (Real.cos (2 * y) + 2 * Real.sin (2 * y)))
      (Real.exp x * Real.cos (2 * x)) x := by
  convert (Real.hasDerivAt_exp x).div_const 5 |>.mul
    ((hasDerivAt_cos_two x).add
      ((hasDerivAt_sin_two x).const_mul 2)) using 1 <;>
    simp [id_eq] <;> ring

private def reverseBase (x : ℝ) :=
  x * Real.exp x * Real.sin (2 * x) -
    Real.exp x / 5 * (Real.sin (2 * x) - 2 * Real.cos (2 * x)) -
    2 * (x - 1) * Real.exp x

private theorem hasDerivAt_reverseBase (x : ℝ) :
    HasDerivAt reverseBase
      (x * Real.exp x * Real.sin (2 * x) - 4 * f x) x := by
  have hmiddle : HasDerivAt
      (fun y : ℝ => Real.exp y / 5 *
        (Real.sin (2 * y) - 2 * Real.cos (2 * y)))
      (Real.exp x * Real.sin (2 * x)) x := by
    convert (Real.hasDerivAt_exp x).div_const 5 |>.mul
      ((hasDerivAt_sin_two x).sub
        ((hasDerivAt_cos_two x).const_mul 2)) using 1 <;>
      simp [id_eq] <;> ring
  have hraw : HasDerivAt
      (fun y : ℝ =>
        y * Real.exp y * Real.sin (2 * y) -
          Real.exp y / 5 * (Real.sin (2 * y) - 2 * Real.cos (2 * y)) -
          2 * (Real.exp y * (y - 1)))
      ((Real.exp x * Real.sin (2 * x) +
          x * Real.exp x * Real.sin (2 * x) +
          2 * x * Real.exp x * Real.cos (2 * x)) -
        Real.exp x * Real.sin (2 * x) - 2 * (x * Real.exp x)) x :=
    ((hasDerivAt_sin_product x).sub hmiddle).sub
      ((hasDerivAt_base x).const_mul 2)
  have hfun : reverseBase = fun y : ℝ =>
      y * Real.exp y * Real.sin (2 * y) -
        Real.exp y / 5 * (Real.sin (2 * y) - 2 * Real.cos (2 * y)) -
        2 * (Real.exp y * (y - 1)) := by
    funext y
    unfold reverseBase
    ring
  have hderiv :
      (Real.exp x * Real.sin (2 * x) +
          x * Real.exp x * Real.sin (2 * x) +
          2 * x * Real.exp x * Real.cos (2 * x)) -
        Real.exp x * Real.sin (2 * x) - 2 * (x * Real.exp x) =
      x * Real.exp x * Real.sin (2 * x) - 4 * f x := by
    rw [f_eq_half]
    ring_nf
  rw [hfun, ← hderiv]
  exact hraw

private theorem hasDerivAt_primitive (x : ℝ) :
    HasDerivAt primitive (f x) x := by
  have ht : HasDerivAt (fun y : ℝ => (y - 1) / 2) (1 / 2 : ℝ) x := by
    simpa only [id_eq] using
      ((hasDerivAt_id x).sub_const 1).div_const 2
  have hlin : HasDerivAt (fun y : ℝ => y / 10) (1 / 10 : ℝ) x := by
    simpa only [id_eq] using (hasDerivAt_id x).div_const 10
  have htrigRaw : HasDerivAt
      (fun y : ℝ => 2 * Real.sin (2 * y) + Real.cos (2 * y))
      (2 * (2 * Real.cos (2 * x)) + (-2 * Real.sin (2 * x))) x :=
    ((hasDerivAt_sin_two x).const_mul 2).add
      (hasDerivAt_cos_two x)
  have htrig : HasDerivAt
      (fun y : ℝ => 2 * Real.sin (2 * y) + Real.cos (2 * y))
      (4 * Real.cos (2 * x) - 2 * Real.sin (2 * x)) x := by
    have heq :
        2 * (2 * Real.cos (2 * x)) + (-2 * Real.sin (2 * x)) =
          4 * Real.cos (2 * x) - 2 * Real.sin (2 * x) := by
      ring
    rw [← heq]
    exact htrigRaw
  have hu : HasDerivAt
      (fun y : ℝ => y / 10 *
        (2 * Real.sin (2 * y) + Real.cos (2 * y)))
      ((1 / 10 : ℝ) * (2 * Real.sin (2 * x) + Real.cos (2 * x)) +
        x / 10 * (4 * Real.cos (2 * x) - 2 * Real.sin (2 * x))) x :=
    hlin.mul htrig
  have hvRaw : HasDerivAt
      (fun y : ℝ => 4 * Real.sin (2 * y) - 3 * Real.cos (2 * y))
      (4 * (2 * Real.cos (2 * x)) - 3 * (-2 * Real.sin (2 * x))) x :=
    ((hasDerivAt_sin_two x).const_mul 4).sub
      ((hasDerivAt_cos_two x).const_mul 3)
  have hvTrig : HasDerivAt
      (fun y : ℝ => 4 * Real.sin (2 * y) - 3 * Real.cos (2 * y))
      (8 * Real.cos (2 * x) + 6 * Real.sin (2 * x)) x := by
    have heq :
        4 * (2 * Real.cos (2 * x)) - 3 * (-2 * Real.sin (2 * x)) =
          8 * Real.cos (2 * x) + 6 * Real.sin (2 * x) := by
      ring
    rw [← heq]
    exact hvRaw
  have hv : HasDerivAt
      (fun y : ℝ => (1 / 50 : ℝ) *
        (4 * Real.sin (2 * y) - 3 * Real.cos (2 * y)))
      ((1 / 50 : ℝ) *
        (8 * Real.cos (2 * x) + 6 * Real.sin (2 * x))) x :=
    hvTrig.const_mul (1 / 50 : ℝ)
  have hprod : HasDerivAt
      (fun y : ℝ => Real.exp y *
        (((y - 1) / 2 - y / 10 *
          (2 * Real.sin (2 * y) + Real.cos (2 * y))) +
          (1 / 50 : ℝ) *
            (4 * Real.sin (2 * y) - 3 * Real.cos (2 * y))))
      (Real.exp x *
          (((x - 1) / 2 - x / 10 *
            (2 * Real.sin (2 * x) + Real.cos (2 * x))) +
            (1 / 50 : ℝ) *
              (4 * Real.sin (2 * x) - 3 * Real.cos (2 * x))) +
        Real.exp x *
          (((1 / 2 : ℝ) -
            ((1 / 10 : ℝ) *
                (2 * Real.sin (2 * x) + Real.cos (2 * x)) +
              x / 10 *
                (4 * Real.cos (2 * x) - 2 * Real.sin (2 * x)))) +
            (1 / 50 : ℝ) *
              (8 * Real.cos (2 * x) + 6 * Real.sin (2 * x)))) x :=
    (Real.hasDerivAt_exp x).mul ((ht.sub hu).add hv)
  have hderiv :
      Real.exp x *
          (((x - 1) / 2 - x / 10 *
            (2 * Real.sin (2 * x) + Real.cos (2 * x))) +
            (1 / 50 : ℝ) *
              (4 * Real.sin (2 * x) - 3 * Real.cos (2 * x))) +
        Real.exp x *
          (((1 / 2 : ℝ) -
            ((1 / 10 : ℝ) *
                (2 * Real.sin (2 * x) + Real.cos (2 * x)) +
              x / 10 *
                (4 * Real.cos (2 * x) - 2 * Real.sin (2 * x)))) +
            (1 / 50 : ℝ) *
              (8 * Real.cos (2 * x) + 6 * Real.sin (2 * x))) = f x := by
    rw [f_eq_half]
    ring_nf
  rw [← hderiv]
  simpa only [primitive] using hprod

private theorem family_eq_translates (p g : ℝ → ℝ)
    (hp : ∀ x, HasDerivAt p (g x) x) :
    Family g = Translates p := by
  apply Set.ext
  intro F
  change (∀ x, HasDerivAt F (g x) x) ↔ ∃ C, ∀ x, F x = p x + C
  constructor
  · intro hF
    have hzero : ∀ x, HasDerivAt (fun y => F y - p y) 0 x := by
      intro x
      convert (hF x).sub (hp x) using 1 <;> ring
    have hconst : ∀ x, F x - p x = F 0 - p 0 := by
      intro x
      exact is_const_of_deriv_eq_zero
        (fun y => (hzero y).differentiableAt)
        (fun y => (hzero y).deriv) x 0
    refine ⟨F 0 - p 0, ?_⟩
    intro x
    have hx := hconst x
    linarith
  · rintro ⟨C, hFC⟩
    rw [show F = fun y => p y + C from funext hFC]
    intro x
    exact (hp x).add_const C

theorem gap1 : Family f = HalfAngle := by
  apply Set.ext
  intro F
  change (∀ x, HasDerivAt F (f x) x) ↔
    ∃ G, (∀ x, HasDerivAt G (x * Real.exp x * (1 - Real.cos (2 * x))) x) ∧
      ∃ C, ∀ x, F x = G x / 2 + C
  constructor
  · intro hF
    refine ⟨fun y => 2 * F y, ?_, 0, ?_⟩
    · intro x
      simpa only [two_f] using (hF x).const_mul 2
    · intro x
      ring
  · rintro ⟨G, hG, C, hFC⟩
    rw [show F = fun y => G y / 2 + C from funext hFC]
    intro x
    convert ((hG x).div_const 2).add_const C using 1
    rw [← two_f x]
    ring
theorem gap2 : HalfAngle = Split := by
  apply Set.ext
  intro F
  change
    (∃ G, (∀ x, HasDerivAt G (x * Real.exp x * (1 - Real.cos (2 * x))) x) ∧
      ∃ C, ∀ x, F x = G x / 2 + C) ↔
    (∃ A, (∀ x, HasDerivAt A (x * Real.exp x) x) ∧
      ∃ B, (∀ x, HasDerivAt B (oscillatory x) x) ∧
        ∃ C, ∀ x, F x = A x / 2 - B x / 2 + C)
  constructor
  · rintro ⟨G, hG, C, hFC⟩
    refine ⟨fun y => Real.exp y * (y - 1), hasDerivAt_base,
      fun y => Real.exp y * (y - 1) - G y, ?_, C, ?_⟩
    · intro x
      convert (hasDerivAt_base x).sub (hG x) using 1 <;>
        dsimp [oscillatory] <;> ring
    · intro x
      rw [hFC x]
      ring
  · rintro ⟨A, hA, B, hB, C, hFC⟩
    refine ⟨fun y => A y - B y, ?_, C, ?_⟩
    · intro x
      convert (hA x).sub (hB x) using 1 <;>
        dsimp [oscillatory] <;> ring
    · intro x
      rw [hFC x]
      ring
theorem gap3 : Family f = Split := by
  rw [gap1, gap2]
theorem gap4 : Family f = FirstParts := by
  apply Set.ext
  intro F
  change (∀ x, HasDerivAt F (f x) x) ↔
    ∃ G, (∀ x, HasDerivAt G (oscillatory x) x) ∧
      ∃ C, ∀ x, F x = Real.exp x * (x - 1) / 2 - G x / 2 + C
  constructor
  · intro hF
    refine ⟨fun y => Real.exp y * (y - 1) - 2 * F y, ?_, 0, ?_⟩
    · intro x
      convert (hasDerivAt_base x).sub ((hF x).const_mul 2) using 1 <;>
        dsimp [oscillatory] <;> rw [two_f] <;> ring
    · intro x
      ring
  · rintro ⟨G, hG, C, hFC⟩
    rw [show F = fun y => Real.exp y * (y - 1) / 2 - G y / 2 + C from funext hFC]
    intro x
    have h := ((hasDerivAt_base x).div_const 2).sub ((hG x).div_const 2)
    convert h.add_const C using 1
    rw [f_eq_half]
    dsimp [oscillatory]
    ring
theorem gap5 : FirstParts = SecondParts := by
  apply Set.ext
  intro F
  change
    (∃ G, (∀ x, HasDerivAt G (oscillatory x) x) ∧
      ∃ C, ∀ x, F x = Real.exp x * (x - 1) / 2 - G x / 2 + C) ↔
    (∃ G, (∀ x, HasDerivAt G (aux x) x) ∧
      ∃ C, ∀ x, F x = Real.exp x * (x - 1) / 2 -
        x * Real.exp x * Real.cos (2 * x) / 2 + G x / 2 + C)
  constructor
  · rintro ⟨G, hG, C, hFC⟩
    refine ⟨fun y => y * Real.exp y * Real.cos (2 * y) - G y, ?_, C, ?_⟩
    · intro x
      convert (hasDerivAt_cos_product x).sub (hG x) using 1 <;>
        dsimp [oscillatory, aux] <;> ring
    · intro x
      rw [hFC x]
      ring
  · rintro ⟨G, hG, C, hFC⟩
    refine ⟨fun y => y * Real.exp y * Real.cos (2 * y) - G y, ?_, C, ?_⟩
    · intro x
      convert (hasDerivAt_cos_product x).sub (hG x) using 1 <;>
        dsimp [oscillatory, aux] <;> ring
    · intro x
      rw [hFC x]
      ring
theorem gap6 : Family f = SecondParts := by
  rw [gap4, gap5]
theorem gap7 : Family f = Coupled := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    have hS : F ∈ SecondParts := by
      rw [← gap6]
      exact hF
    rcases hS with ⟨H, hH, C, hFC⟩
    change F ∈ Coupled
    refine ⟨fun y => (Real.exp y / 5 *
      (Real.cos (2 * y) + 2 * Real.sin (2 * y)) - H y) / 2, ?_, C, ?_⟩
    · intro x
      convert ((hasDerivAt_kernel x).sub (hH x)).div_const 2 using 1 <;>
        dsimp [aux] <;> ring
    · intro x
      rw [hFC x]
      ring
  · intro hF
    change F ∈ Coupled at hF
    rcases hF with ⟨G, hG, C, hFC⟩
    have hS : F ∈ SecondParts := by
      refine ⟨fun y => Real.exp y / 5 *
        (Real.cos (2 * y) + 2 * Real.sin (2 * y)) - 2 * G y, ?_, C, ?_⟩
      · intro x
        convert (hasDerivAt_kernel x).sub ((hG x).const_mul 2) using 1 <;>
          dsimp [aux] <;> ring
      · intro x
        rw [hFC x]
        ring
    rw [gap6]
    exact hS
theorem gap8 : Family (fun x => x * Real.exp x * Real.sin (2 * x)) =
    ReverseCoupled := by
  apply Set.ext
  intro G
  change
    (∀ x, HasDerivAt G (x * Real.exp x * Real.sin (2 * x)) x) ↔
    ∃ F, (∀ x, HasDerivAt F (f x) x) ∧ ∃ C, ∀ x,
      G x = reverseBase x + 4 * F x + C
  constructor
  · intro hG
    refine ⟨fun y => (G y - reverseBase y) / 4, ?_, 0, ?_⟩
    · intro x
      convert ((hG x).sub (hasDerivAt_reverseBase x)).div_const 4 using 1
      ring
    · intro x
      ring
  · rintro ⟨F, hF, C, hGF⟩
    rw [show G = fun y => reverseBase y + 4 * F y + C from funext hGF]
    intro x
    convert (hasDerivAt_reverseBase x).add ((hF x).const_mul 4) |>.add_const C using 1
    ring
theorem gap9 : Family f = Translates primitive := by
  exact family_eq_translates primitive f hasDerivAt_primitive

end
end ProofGap.Exercise2078
