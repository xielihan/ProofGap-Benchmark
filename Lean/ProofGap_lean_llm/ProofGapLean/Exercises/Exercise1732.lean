import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1732

noncomputable section

def u (x : ℝ) : ℝ := 1 + x ^ 2
def original (x : ℝ) : ℝ := x ^ 3 * Real.cbrt (u x)
def substituted (x : ℝ) : ℝ :=
  (1 / 2) * (Real.rpow (u x) (4 / 3) - Real.rpow (u x) (1 / 3)) * (2 * x)
def powers (x : ℝ) : ℝ :=
  x * (Real.rpow (u x) (4 / 3) - Real.rpow (u x) (1 / 3))
def primitive₁ (x : ℝ) : ℝ :=
  (3 / 14) * Real.rpow (u x) (7 / 3) -
    (3 / 8) * Real.rpow (u x) (4 / 3)
def primitive₂ (x : ℝ) : ℝ :=
  ((12 * x ^ 2 - 9) / 56) * Real.rpow (u x) (4 / 3)
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem u_pos (x : ℝ) : 0 < u x := by
  unfold u
  nlinarith [sq_nonneg x]

private theorem u_hasDerivAt (x : ℝ) :
    HasDerivAt u (2 * x) x := by
  unfold u
  convert (hasDerivAt_const x 1).add ((hasDerivAt_id x).pow 2) using 1 <;>
    simp only [id_eq] <;>
    ring

private theorem rpow_four_thirds (x : ℝ) :
    Real.rpow (u x) (4 / 3) =
      u x * Real.rpow (u x) (1 / 3) := by
  change (u x) ^ (4 / 3 : ℝ) =
    u x * (u x) ^ (1 / 3 : ℝ)
  calc
    (u x) ^ (4 / 3 : ℝ) = (u x) ^ (1 + 1 / 3 : ℝ) := by
      congr 1
      ring
    _ = (u x) ^ (1 : ℝ) * (u x) ^ (1 / 3 : ℝ) := by
      exact Real.rpow_add (u_pos x) 1 (1 / 3)
    _ = u x * (u x) ^ (1 / 3 : ℝ) := by rw [Real.rpow_one]

private theorem rpow_seven_thirds (x : ℝ) :
    Real.rpow (u x) (7 / 3) =
      u x * Real.rpow (u x) (4 / 3) := by
  change (u x) ^ (7 / 3 : ℝ) =
    u x * (u x) ^ (4 / 3 : ℝ)
  calc
    (u x) ^ (7 / 3 : ℝ) = (u x) ^ (1 + 4 / 3 : ℝ) := by
      congr 1
      ring
    _ = (u x) ^ (1 : ℝ) * (u x) ^ (4 / 3 : ℝ) := by
      exact Real.rpow_add (u_pos x) 1 (4 / 3)
    _ = u x * (u x) ^ (4 / 3 : ℝ) := by rw [Real.rpow_one]

private theorem original_eq_powers (x : ℝ) :
    original x = powers x := by
  unfold original powers Real.cbrt
  rw [rpow_four_thirds]
  unfold u
  ring

private theorem substituted_eq_powers (x : ℝ) :
    substituted x = powers x := by
  unfold substituted powers
  ring

private theorem primitive₁_hasDerivAt (x : ℝ) :
    HasDerivAt primitive₁ (powers x) x := by
  have hr7 :
      HasDerivAt (fun y : ℝ => Real.rpow (u y) (7 / 3))
        (((7 / 3) * Real.rpow (u x) (4 / 3)) * (2 * x)) x := by
    change HasDerivAt (fun y : ℝ => (u y) ^ (7 / 3 : ℝ))
      (((7 / 3 : ℝ) * (u x) ^ (4 / 3 : ℝ)) * (2 * x)) x
    have he : (7 / 3 : ℝ) - 1 = 4 / 3 := by ring
    simpa only [he, Function.comp_def] using
      (Real.hasDerivAt_rpow_const (p := (7 / 3 : ℝ))
        (Or.inl (ne_of_gt (u_pos x)))).comp x (u_hasDerivAt x)
  have hr4 :
      HasDerivAt (fun y : ℝ => Real.rpow (u y) (4 / 3))
        (((4 / 3) * Real.rpow (u x) (1 / 3)) * (2 * x)) x := by
    change HasDerivAt (fun y : ℝ => (u y) ^ (4 / 3 : ℝ))
      (((4 / 3 : ℝ) * (u x) ^ (1 / 3 : ℝ)) * (2 * x)) x
    have he : (4 / 3 : ℝ) - 1 = 1 / 3 := by ring
    simpa only [he, Function.comp_def] using
      (Real.hasDerivAt_rpow_const (p := (4 / 3 : ℝ))
        (Or.inl (ne_of_gt (u_pos x)))).comp x (u_hasDerivAt x)
  unfold primitive₁ powers
  convert
    (hr7.const_mul (3 / 14 : ℝ)).sub
      (hr4.const_mul (3 / 8 : ℝ)) using 1
  ring

theorem gap1 : Antiderivatives original = Antiderivatives substituted := by
  have hfun : original = substituted := by
    funext x
    exact (original_eq_powers x).trans (substituted_eq_powers x).symm
  rw [hfun]

theorem gap2 : Antiderivatives substituted = Antiderivatives powers := by
  have hfun : substituted = powers := by
    funext x
    exact substituted_eq_powers x
  rw [hfun]

theorem gap3 : Antiderivatives original = Antiderivatives powers := by
  exact gap1.trans gap2

theorem gap4 : Antiderivatives original = PrimitiveFamily primitive₁ := by
  rw [gap3]
  ext F
  simp only [Antiderivatives, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    have hzero : ∀ x, HasDerivAt (fun y => F y - primitive₁ y) 0 x := by
      intro x
      have hF : HasDerivAt F (powers x) x := by
        simpa only [hFderiv x] using (hFdiff x).hasDerivAt
      simpa using hF.sub (primitive₁_hasDerivAt x)
    have hdiff : Differentiable ℝ (fun y => F y - primitive₁ y) :=
      fun x => (hzero x).differentiableAt
    have hconst :=
      is_const_of_deriv_eq_zero hdiff (fun x => (hzero x).deriv)
    refine ⟨F 0 - primitive₁ 0, ?_⟩
    intro x
    have hc : F x - primitive₁ x = F 0 - primitive₁ 0 :=
      hconst x 0
    linarith
  · rintro ⟨C, hFC⟩
    have hfun : F = fun x => primitive₁ x + C := funext hFC
    rw [hfun]
    constructor
    · intro x
      exact ((primitive₁_hasDerivAt x).add_const C).differentiableAt
    · intro x
      exact ((primitive₁_hasDerivAt x).add_const C).deriv

theorem gap5 : PrimitiveFamily primitive₁ = PrimitiveFamily primitive₂ := by
  have hp : primitive₁ = primitive₂ := by
    funext x
    unfold primitive₁ primitive₂
    rw [rpow_seven_thirds]
    unfold u
    ring
  rw [hp]

theorem gap6 : Antiderivatives original = PrimitiveFamily primitive₂ := by
  exact gap4.trans gap5

end
end ProofGap.Exercise1732
