import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1657

noncomputable section

def integrand (x : ℝ) : ℝ := Real.cbrt (1 - 3 * x)
def primitive₁ (x : ℝ) : ℝ :=
  -(1 / 3) * (3 / 4) * (Real.cbrt (1 - 3 * x)) ^ 4
def primitive₂ (x : ℝ) : ℝ :=
  -(1 / 4) * (Real.cbrt (1 - 3 * x)) ^ 4
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem cbrt_pos_of_neg {x : ℝ} (hx : x < 0) :
    0 < Real.cbrt x := by
  unfold Real.cbrt
  change 0 < x ^ (1 / 3 : ℝ)
  rw [Real.rpow_def_of_neg hx]
  rw [show (1 / 3 : ℝ) * Real.pi = Real.pi / 3 by ring,
    Real.cos_pi_div_three]
  positivity

private theorem rpow_third_sub_one_neg {x : ℝ} (hx : x < 0) :
    x ^ ((1 / 3 : ℝ) - 1) < 0 := by
  rw [Real.rpow_def_of_neg hx]
  have hcos :
      Real.cos (((1 / 3 : ℝ) - 1) * Real.pi) = -1 / 2 := by
    rw [show ((1 / 3 : ℝ) - 1) * Real.pi =
        -(2 * Real.pi / 3) by ring, Real.cos_neg]
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  rw [hcos]
  exact mul_neg_of_pos_of_neg (Real.exp_pos _) (by norm_num)

private theorem deriv_primitive_two_one_neg : deriv primitive₂ 1 < 0 := by
  have hsub : HasDerivAt (fun z : ℝ => 1 - 3 * z) (-3) 1 := by
    convert (hasDerivAt_const (x := (1 : ℝ)) (1 : ℝ)).sub
      ((hasDerivAt_const (x := (1 : ℝ)) (3 : ℝ)).mul (hasDerivAt_id 1)) using 1 <;>
      norm_num <;> ring
  have hroot :
      HasDerivAt (fun z : ℝ => Real.cbrt (1 - 3 * z))
        ((-3 : ℝ) * (1 / 3 : ℝ) *
          (-2 : ℝ) ^ ((1 / 3 : ℝ) - 1)) 1 := by
    unfold Real.cbrt
    convert hsub.rpow_const (p := (1 / 3 : ℝ))
      (Or.inl (by norm_num)) using 1 <;> norm_num <;> ring
  have hprim : HasDerivAt primitive₂
      (-(1 / 4 : ℝ) *
        (4 * (Real.cbrt (-2)) ^ 3 *
          ((-3 : ℝ) * (1 / 3 : ℝ) *
            (-2 : ℝ) ^ ((1 / 3 : ℝ) - 1)))) 1 := by
    unfold primitive₂
    convert (hroot.fun_pow 4).const_mul (-(1 / 4 : ℝ)) using 1 <;>
      norm_num <;> ring
  rw [hprim.deriv]
  have hcpos : 0 < Real.cbrt (-2) := cbrt_pos_of_neg (by norm_num)
  have hrneg : (-2 : ℝ) ^ ((1 / 3 : ℝ) - 1) < 0 :=
    rpow_third_sub_one_neg (by norm_num)
  have hdpos : 0 <
      ((-3 : ℝ) * (1 / 3 : ℝ) *
        (-2 : ℝ) ^ ((1 / 3 : ℝ) - 1)) := by
    norm_num
    convert hrneg using 1 <;> ring
  exact mul_neg_of_neg_of_pos (by norm_num)
    (mul_pos (mul_pos (by norm_num) (pow_pos hcpos 3)) hdpos)

private theorem primitive_family_eq :
    PrimitiveFamily primitive₁ = PrimitiveFamily primitive₂ := by
  have hp : primitive₁ = primitive₂ := by
    funext x
    unfold primitive₁ primitive₂
    ring
  rw [hp]

private theorem antiderivatives_ne_primitive_two :
    Antiderivatives integrand ≠ PrimitiveFamily primitive₂ := by
  intro heq
  have hmemP : primitive₂ ∈ PrimitiveFamily primitive₂ := by
    refine ⟨0, ?_⟩
    intro x
    simp
  have hmemA : primitive₂ ∈ Antiderivatives integrand := by
    rw [heq]
    exact hmemP
  have hder := hmemA.2 1
  have hneg := deriv_primitive_two_one_neg
  have hpos : 0 < integrand 1 := by
    unfold integrand
    norm_num
    exact cbrt_pos_of_neg (by norm_num)
  rw [hder] at hneg
  linarith

theorem gap1 : Antiderivatives integrand ≠ PrimitiveFamily primitive₁ := by
  intro heq
  exact antiderivatives_ne_primitive_two (heq.trans primitive_family_eq)

theorem gap2 : PrimitiveFamily primitive₁ = PrimitiveFamily primitive₂ := by
  have hp : primitive₁ = primitive₂ := by
    funext x
    unfold primitive₁ primitive₂
    ring
  rw [hp]

theorem gap3 : Antiderivatives integrand ≠ PrimitiveFamily primitive₂ := by
  exact antiderivatives_ne_primitive_two

end
end ProofGap.Exercise1657
