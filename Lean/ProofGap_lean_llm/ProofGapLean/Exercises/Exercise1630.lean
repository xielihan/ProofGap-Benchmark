import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1630

noncomputable section

def factored (x : ℝ) : ℝ := (1 - x) * (1 - 2 * x) * (1 - 3 * x)
def expanded (x : ℝ) : ℝ := 1 - 6 * x + 11 * x ^ 2 - 6 * x ^ 3
def primitive (x : ℝ) : ℝ :=
  x - 3 * x ^ 2 + (11 / 3) * x ^ 3 - (3 / 2) * x ^ 4
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (expanded x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert h1.mul h1 using 1
    · funext y
      simp [pow_two]
    · ring
  have h3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    convert h2.mul h1 using 1 <;> ring
  have h4 : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by
    convert h3.mul h1 using 1 <;> ring
  unfold primitive expanded
  convert
    (((h1.sub ((hasDerivAt_const x (3 : ℝ)).mul h2)).add
      ((hasDerivAt_const x (11 / 3 : ℝ)).mul h3)).sub
      ((hasDerivAt_const x (3 / 2 : ℝ)).mul h4)) using 1 <;>
    norm_num <;> ring

theorem gap1 : Antiderivatives factored = Antiderivatives expanded := by
  have h : factored = expanded := by
    funext x
    unfold factored expanded
    ring
  rw [h]

theorem gap2 : Antiderivatives expanded = PrimitiveFamily primitive := by
  ext F
  change
    (Differentiable ℝ F ∧ ∀ x, deriv F x = expanded x) ↔
      ∃ C : ℝ, ∀ x, F x = primitive x + C
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    have hpdiff : Differentiable ℝ primitive :=
      fun x => (primitive_hasDerivAt x).differentiableAt
    have hdiff : Differentiable ℝ (fun x => F x - primitive x) :=
      hFdiff.sub hpdiff
    have hzero (x : ℝ) :
        HasDerivAt (fun t => F t - primitive t) 0 x := by
      have hFx := (hFdiff x).hasDerivAt
      rw [hFderiv x] at hFx
      simpa using hFx.sub (primitive_hasDerivAt x)
    have hderivzero (x : ℝ) :
        deriv (fun t => F t - primitive t) x = 0 :=
      (hzero x).deriv
    have hconst := is_const_of_deriv_eq_zero hdiff hderivzero
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hc : F x - primitive x = F 0 - primitive 0 := by
      exact hconst x 0
    calc
      F x = primitive x + (F x - primitive x) := by ring
      _ = primitive x + (F 0 - primitive 0) := by rw [hc]
  · rintro ⟨C, hC⟩
    have hfun : F = fun x => primitive x + C := funext hC
    subst F
    constructor
    · intro x
      exact ((primitive_hasDerivAt x).add_const C).differentiableAt
    · intro x
      exact ((primitive_hasDerivAt x).add_const C).deriv

theorem gap3 : Antiderivatives factored = PrimitiveFamily primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1630
