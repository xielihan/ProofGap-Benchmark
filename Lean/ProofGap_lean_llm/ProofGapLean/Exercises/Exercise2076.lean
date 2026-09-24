import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2076
noncomputable section

def f (x : ℝ) := x * Real.exp x * Real.sin x
def g₁ (x : ℝ) := Real.exp x * (Real.sin x + x * Real.cos x)
def g₂ (x : ℝ) := Real.exp x * (2 * Real.cos x - x * Real.sin x)
def h (x : ℝ) := Real.exp x * Real.cos x
def primitive (x : ℝ) :=
  Real.exp x / 2 * (x * (Real.sin x - Real.cos x) + Real.cos x)
def Family (g : ℝ → ℝ) := {F : ℝ → ℝ | ∀ x, HasDerivAt F (g x) x}
def Parts1 := {F : ℝ → ℝ | ∃ G ∈ Family g₁, ∃ C,
  ∀ x, F x = x * Real.exp x * Real.sin x - G x + C}
def Parts2 := {F : ℝ → ℝ | ∃ G ∈ Family g₂, ∃ C,
  ∀ x, F x = Real.exp x * (x * Real.sin x - Real.sin x - x * Real.cos x) + G x + C}
def SelfStep := {F : ℝ → ℝ | ∃ G ∈ Family h, ∃ H ∈ Family f, ∃ C,
  ∀ x, F x = Real.exp x * (x * Real.sin x - Real.sin x - x * Real.cos x) +
    2 * G x - H x + C}
def Reduced := {F : ℝ → ℝ | ∃ G ∈ Family h, ∃ C,
  ∀ x, F x = Real.exp x / 2 *
    (x * Real.sin x - Real.sin x - x * Real.cos x) + G x + C}
def Expanded := {F : ℝ → ℝ | ∃ C, ∀ x,
  F x = Real.exp x / 2 * (x * Real.sin x - Real.sin x - x * Real.cos x) +
    Real.exp x / 2 * (Real.sin x + Real.cos x) + C}
def Translates (p : ℝ → ℝ) := {F : ℝ → ℝ | ∃ C, ∀ x, F x = p x + C}

private def auxA (x : ℝ) :=
  Real.exp x * (x * Real.sin x - Real.sin x - x * Real.cos x)

private def auxQ (x : ℝ) :=
  Real.exp x / 2 * (Real.sin x + Real.cos x)

private def auxB (x : ℝ) :=
  Real.exp x / 2 * (x * Real.sin x - Real.sin x - x * Real.cos x)

private theorem hasDerivAt_f (x : ℝ) :
    HasDerivAt f (f x + g₁ x) x := by
  unfold f g₁
  convert (((hasDerivAt_id x).mul (Real.hasDerivAt_exp x)).mul
    (Real.hasDerivAt_sin x)) using 1 <;>
    (try funext y) <;>
    simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, id_eq] <;>
    ring_nf

private theorem hasDerivAt_auxA (x : ℝ) :
    HasDerivAt auxA (2 * f x - 2 * h x) x := by
  unfold auxA f h
  convert (Real.hasDerivAt_exp x).mul
    ((((hasDerivAt_id x).mul (Real.hasDerivAt_sin x)).sub
      (Real.hasDerivAt_sin x)).sub
      ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x))) using 1 <;>
    (try funext y) <;>
    simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, id_eq] <;>
    ring_nf

private theorem hasDerivAt_auxQ (x : ℝ) :
    HasDerivAt auxQ (h x) x := by
  unfold auxQ h
  convert ((Real.hasDerivAt_exp x).mul
    ((Real.hasDerivAt_sin x).add (Real.hasDerivAt_cos x))).const_mul
      (1 / 2 : ℝ) using 1 <;>
    (try funext y) <;>
    simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, id_eq] <;>
    ring_nf

private theorem hasDerivAt_auxB (x : ℝ) :
    HasDerivAt auxB (f x - h x) x := by
  have hfun : auxB = fun y => (1 / 2 : ℝ) * auxA y := by
    funext y
    unfold auxA auxB
    ring_nf
  rw [hfun]
  convert (hasDerivAt_auxA x).const_mul (1 / 2 : ℝ) using 1 <;>
    ring_nf

private theorem family_eq_translates_of_hasDerivAt
    {q p : ℝ → ℝ} (hp : ∀ x, HasDerivAt p (q x) x) :
    Family q = Translates p := by
  ext F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (q x) x at hF
    let d : ℝ → ℝ := fun x => F x - p x
    have hd : ∀ x, HasDerivAt d 0 x := by
      intro x
      dsimp [d]
      convert (hF x).sub (hp x) using 1 <;> ring
    have hconst : ∀ x, d x = d 0 := by
      intro x
      exact is_const_of_deriv_eq_zero
        (fun y => (hd y).differentiableAt)
        (fun y => (hd y).deriv) x 0
    change ∃ C, ∀ x, F x = p x + C
    refine ⟨d 0, ?_⟩
    intro x
    have hx : F x - p x = F 0 - p 0 := by
      simpa [d] using hconst x
    dsimp [d]
    calc
      F x = p x + (F x - p x) := by ring
      _ = p x + (F 0 - p 0) := by rw [hx]
  · rintro ⟨C, hFC⟩
    have hfun : F = fun x => p x + C := funext hFC
    subst F
    change ∀ x, HasDerivAt (fun y => p y + C) (q x) x
    intro x
    exact (hp x).add_const C

theorem gap1 : Family f =
    Family (fun x => x * Real.sin x * deriv Real.exp x) := by
  ext F
  change (∀ x, HasDerivAt F (f x) x) ↔
    (∀ x, HasDerivAt F (x * Real.sin x * deriv Real.exp x) x)
  constructor
  · intro hF x
    have he : deriv Real.exp x = Real.exp x :=
      (Real.hasDerivAt_exp x).deriv
    convert hF x using 1
    rw [he]
    unfold f
    ring
  · intro hF x
    have he : deriv Real.exp x = Real.exp x :=
      (Real.hasDerivAt_exp x).deriv
    convert hF x using 1
    rw [he]
    unfold f
    ring
theorem gap2 : Family (fun x => x * Real.sin x * deriv Real.exp x) = Parts1 := by
  ext F
  change (F ∈ Family (fun x => x * Real.sin x * deriv Real.exp x)) ↔
    (∃ G ∈ Family g₁, ∃ C, ∀ x, F x = f x - G x + C)
  constructor
  · intro hF
    have hf : F ∈ Family f := by
      rw [gap1]
      exact hF
    change ∀ x, HasDerivAt F (f x) x at hf
    refine ⟨fun x => f x - F x, ?_, 0, ?_⟩
    · change ∀ x, HasDerivAt (fun y => f y - F y) (g₁ x) x
      intro x
      convert (hasDerivAt_f x).sub (hf x) using 1 <;> ring
    · intro x
      ring
  · rintro ⟨G, hG, C, hEq⟩
    change ∀ x, HasDerivAt G (g₁ x) x at hG
    have hF_eq : F = fun x => f x - G x + C := funext hEq
    subst F
    rw [← gap1]
    change ∀ x, HasDerivAt (fun y => f y - G y + C) (f x) x
    intro x
    convert ((hasDerivAt_f x).sub (hG x)).add_const C using 1 <;> ring
theorem gap3 : Family f = Parts1 := by
  exact gap1.trans gap2
theorem gap4 : Family f = Parts1 := by
  exact gap3
theorem gap5 : Parts1 = Parts2 := by
  rw [← gap3]
  ext F
  change (F ∈ Family f) ↔
    (∃ G ∈ Family g₂, ∃ C, ∀ x, F x = auxA x + G x + C)
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (f x) x at hF
    refine ⟨fun x => F x - auxA x, ?_, 0, ?_⟩
    · change ∀ x, HasDerivAt (fun y => F y - auxA y) (g₂ x) x
      intro x
      convert (hF x).sub (hasDerivAt_auxA x) using 1 <;>
        simp only [f, g₂, h] <;> ring
    · intro x
      ring
  · rintro ⟨G, hG, C, hEq⟩
    change ∀ x, HasDerivAt G (g₂ x) x at hG
    have hF_eq : F = fun x => auxA x + G x + C := funext hEq
    subst F
    change ∀ x, HasDerivAt (fun y => auxA y + G y + C) (f x) x
    intro x
    convert ((hasDerivAt_auxA x).add (hG x)).add_const C using 1 <;>
      simp only [f, g₂, h] <;> ring
theorem gap6 : Family f = Parts2 := by
  exact gap3.trans gap5
theorem gap7 : Family f = SelfStep := by
  ext F
  change (F ∈ Family f) ↔
    (∃ G ∈ Family h, ∃ H ∈ Family f, ∃ C,
      ∀ x, F x = auxA x + 2 * G x - H x + C)
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (f x) x at hF
    refine ⟨auxQ, ?_, fun x => auxA x + 2 * auxQ x - F x, ?_, 0, ?_⟩
    · change ∀ x, HasDerivAt auxQ (h x) x
      exact hasDerivAt_auxQ
    · change ∀ x,
        HasDerivAt (fun y => auxA y + 2 * auxQ y - F y) (f x) x
      intro x
      convert ((hasDerivAt_auxA x).add
        ((hasDerivAt_auxQ x).const_mul 2)).sub (hF x) using 1 <;> ring
    · intro x
      ring
  · rintro ⟨G, hG, H, hH, C, hEq⟩
    change ∀ x, HasDerivAt G (h x) x at hG
    change ∀ x, HasDerivAt H (f x) x at hH
    have hF_eq : F = fun x => auxA x + 2 * G x - H x + C := funext hEq
    subst F
    change ∀ x,
      HasDerivAt (fun y => auxA y + 2 * G y - H y + C) (f x) x
    intro x
    convert (((hasDerivAt_auxA x).add ((hG x).const_mul 2)).sub
      (hH x)).add_const C using 1 <;> ring
theorem gap8 : Family f = Reduced := by
  ext F
  change (F ∈ Family f) ↔
    (∃ G ∈ Family h, ∃ C, ∀ x, F x = auxB x + G x + C)
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (f x) x at hF
    refine ⟨fun x => F x - auxB x, ?_, 0, ?_⟩
    · change ∀ x, HasDerivAt (fun y => F y - auxB y) (h x) x
      intro x
      convert (hF x).sub (hasDerivAt_auxB x) using 1 <;> ring
    · intro x
      ring
  · rintro ⟨G, hG, C, hEq⟩
    change ∀ x, HasDerivAt G (h x) x at hG
    have hF_eq : F = fun x => auxB x + G x + C := funext hEq
    subst F
    change ∀ x, HasDerivAt (fun y => auxB y + G y + C) (f x) x
    intro x
    convert ((hasDerivAt_auxB x).add (hG x)).add_const C using 1 <;> ring
theorem gap9 : Reduced = Expanded := by
  ext F
  change (∃ G ∈ Family h, ∃ C, ∀ x, F x = auxB x + G x + C) ↔
    (∃ C, ∀ x, F x = auxB x + auxQ x + C)
  have ht : Family h = Translates auxQ :=
    family_eq_translates_of_hasDerivAt hasDerivAt_auxQ
  constructor
  · rintro ⟨G, hG, C, hEq⟩
    have hGt : G ∈ Translates auxQ := by
      rw [← ht]
      exact hG
    change ∃ D, ∀ x, G x = auxQ x + D at hGt
    rcases hGt with ⟨D, hGD⟩
    refine ⟨D + C, ?_⟩
    intro x
    rw [hEq x, hGD x]
    ring
  · rintro ⟨C, hEq⟩
    refine ⟨fun x => auxQ x + C, ?_, 0, ?_⟩
    · change ∀ x, HasDerivAt (fun y => auxQ y + C) (h x) x
      intro x
      exact (hasDerivAt_auxQ x).add_const C
    · intro x
      rw [hEq x]
      ring
theorem gap10 : Expanded = Translates primitive := by
  ext F
  change (∃ C, ∀ x, F x = auxB x + auxQ x + C) ↔
    (∃ C, ∀ x, F x = primitive x + C)
  have hp : ∀ x, auxB x + auxQ x = primitive x := by
    intro x
    unfold auxB auxQ primitive
    ring
  constructor
  · rintro ⟨C, hEq⟩
    refine ⟨C, ?_⟩
    intro x
    calc
      F x = auxB x + auxQ x + C := hEq x
      _ = primitive x + C := by rw [hp x]
  · rintro ⟨C, hEq⟩
    refine ⟨C, ?_⟩
    intro x
    calc
      F x = primitive x + C := hEq x
      _ = auxB x + auxQ x + C := by rw [hp x]
theorem gap11 : Family f = Translates primitive := by
  calc
    Family f = Reduced := gap8
    _ = Expanded := gap9
    _ = Translates primitive := gap10

end
end ProofGap.Exercise2076
