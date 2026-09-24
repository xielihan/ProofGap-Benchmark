import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1766

noncomputable section

def subst (x : ℝ) : ℝ := 1 - x
def q (x : ℝ) : ℝ :=
  Real.sign (subst x) * Real.rpow |subst x| (1 / 3 : ℝ)
def integrand (x : ℝ) : ℝ := x ^ 2 * q x
def intermediate (x : ℝ) : ℝ :=
  -(3 / 4 : ℝ) * q x ^ 4 + (6 / 7 : ℝ) * q x ^ 7 - (3 / 10 : ℝ) * q x ^ 10
def primitive (x : ℝ) : ℝ :=
  -(3 / 140 : ℝ) * (9 + 12 * x + 14 * x ^ 2) * q x ^ 4
def IsAntiderivative (F f : ℝ → ℝ) : Prop := ∀ x, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) := {F | IsAntiderivative F f}
def Translates (P : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x, F x = P x + C}

private def base4 (x : ℝ) : ℝ :=
  Real.rpow |subst x| (4 / 3 : ℝ)

private theorem abs_root_cube (u : ℝ) :
    (Real.rpow |u| (1 / 3 : ℝ)) ^ 3 = |u| := by
  have h := Real.rpow_inv_natCast_pow (x := |u|) (n := 3)
    (abs_nonneg u) (by norm_num)
  norm_num at h ⊢
  exact h

private theorem q_cube (x : ℝ) : q x ^ 3 = subst x := by
  unfold q
  rw [mul_pow, abs_root_cube]
  rcases lt_trichotomy (subst x) 0 with h | h | h
  · simp [Real.sign_of_neg h, abs_of_neg h]
    norm_num
  · simp [h]
  · simp [Real.sign_of_pos h, abs_of_pos h]

private theorem q_four (x : ℝ) : q x ^ 4 = base4 x := by
  unfold q base4
  rw [mul_pow]
  have hr : (Real.rpow |subst x| (1 / 3 : ℝ)) ^ 4 =
      Real.rpow |subst x| (4 / 3 : ℝ) := by
    calc
      (Real.rpow |subst x| (1 / 3 : ℝ)) ^ 4 =
          Real.rpow |subst x| ((1 / 3 : ℝ) * (4 : ℕ)) :=
        (Real.rpow_mul_natCast (abs_nonneg (subst x)) (1 / 3 : ℝ) 4).symm
      _ = Real.rpow |subst x| (4 / 3 : ℝ) := by norm_num
  rw [hr]
  rcases lt_trichotomy (subst x) 0 with h | h | h
  · simp [Real.sign_of_neg h]
    norm_num
  · simp [h, Real.zero_rpow]
  · simp [Real.sign_of_pos h]

private theorem abs_rpow_neg_two_thirds_mul (u : ℝ) :
    Real.rpow |u| (-2 / 3 : ℝ) * u =
      Real.sign u * Real.rpow |u| (1 / 3 : ℝ) := by
  rcases lt_trichotomy u 0 with h | h | h
  · have hpos : 0 < -u := by linarith
    have hr : Real.rpow (-u) (-2 / 3 : ℝ) * (-u) =
        Real.rpow (-u) (1 / 3 : ℝ) := by
      calc
        Real.rpow (-u) (-2 / 3 : ℝ) * (-u) =
            Real.rpow (-u) ((-2 / 3 : ℝ) + 1) :=
          (Real.rpow_add_one hpos.ne' (-2 / 3 : ℝ)).symm
        _ = Real.rpow (-u) (1 / 3 : ℝ) := by norm_num
    rw [abs_of_neg h, Real.sign_of_neg h]
    calc
      Real.rpow (-u) (-2 / 3 : ℝ) * u =
          -(Real.rpow (-u) (-2 / 3 : ℝ) * (-u)) := by ring
      _ = -Real.rpow (-u) (1 / 3 : ℝ) := by rw [hr]
      _ = (-1 : ℝ) * Real.rpow (-u) (1 / 3 : ℝ) := by ring
  · subst u
    norm_num [Real.zero_rpow]
  · have hr : Real.rpow u (-2 / 3 : ℝ) * u =
        Real.rpow u (1 / 3 : ℝ) := by
      calc
        Real.rpow u (-2 / 3 : ℝ) * u =
            Real.rpow u ((-2 / 3 : ℝ) + 1) :=
          (Real.rpow_add_one h.ne' (-2 / 3 : ℝ)).symm
        _ = Real.rpow u (1 / 3 : ℝ) := by norm_num
    rw [abs_of_pos h, Real.sign_of_pos h, one_mul, hr]

private theorem hasDerivAt_subst (x : ℝ) : HasDerivAt subst (-1) x := by
  unfold subst
  convert (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub (hasDerivAt_id x) using 1 <;>
    norm_num

private theorem hasDerivAt_base4 (x : ℝ) :
    HasDerivAt base4 (-(4 / 3 : ℝ) * q x) x := by
  have h := (hasDerivAt_abs_rpow (subst x)
    (p := (4 / 3 : ℝ)) (by norm_num)).comp x (hasDerivAt_subst x)
  unfold base4
  convert h using 1
  unfold q
  change -(4 / 3 : ℝ) *
      (Real.sign (subst x) * Real.rpow |subst x| (1 / 3 : ℝ)) =
    (4 / 3 : ℝ) * Real.rpow |subst x| ((4 / 3 : ℝ) - 2) * subst x * (-1)
  rw [show (4 / 3 : ℝ) - 2 = -2 / 3 by norm_num]
  rw [← abs_rpow_neg_two_thirds_mul]
  ring

private theorem hasDerivAt_q_four (x : ℝ) :
    HasDerivAt (fun y : ℝ => q y ^ 4) (-(4 / 3 : ℝ) * q x) x := by
  have heq : (fun y : ℝ => q y ^ 4) = base4 := by
    funext y
    exact q_four y
  rw [heq]
  exact hasDerivAt_base4 x

private theorem hasDerivAt_q_seven (x : ℝ) :
    HasDerivAt (fun y : ℝ => q y ^ 7) (-(7 / 3 : ℝ) * q x ^ 4) x := by
  have heq : (fun y : ℝ => q y ^ 7) =
      fun y : ℝ => subst y * q y ^ 4 := by
    funext y
    rw [← q_cube y]
    ring
  rw [heq]
  have h := (hasDerivAt_subst x).mul (hasDerivAt_q_four x)
  convert h using 1
  rw [← q_cube x]
  ring

private theorem hasDerivAt_q_ten (x : ℝ) :
    HasDerivAt (fun y : ℝ => q y ^ 10) (-(10 / 3 : ℝ) * q x ^ 7) x := by
  have heq : (fun y : ℝ => q y ^ 10) =
      fun y : ℝ => subst y * q y ^ 7 := by
    funext y
    rw [← q_cube y]
    ring
  rw [heq]
  have h := (hasDerivAt_subst x).mul (hasDerivAt_q_seven x)
  convert h using 1
  rw [← q_cube x]
  ring

private theorem eq_const_of_deriv_eq_zero
    (g : ℝ → ℝ) (hzero : ∀ x, HasDerivAt g 0 x) (x : ℝ) :
    g x = g 0 := by
  have hdiff : Differentiable ℝ g := fun y => (hzero y).differentiableAt
  exact is_const_of_deriv_eq_zero hdiff (fun y => (hzero y).deriv) x 0

theorem gap1 (x : ℝ) :
    x = 1 - subst x := by
  simp [subst]

theorem gap2 (x : ℝ) :
    deriv subst x = -1 := by
  have h : HasDerivAt subst (-1) x := by
    unfold subst
    convert (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub (hasDerivAt_id x) using 1 <;>
      norm_num
  exact h.deriv

theorem gap3 (x : ℝ) :
    integrand x = (1 - subst x) ^ 2 * q x := by
  change x ^ 2 * q x = (1 - subst x) ^ 2 * q x
  exact congrArg
    (fun z : ℝ => z ^ 2 * q x)
    (gap1 x)

theorem gap4 (x : ℝ) :
    (1 - subst x) ^ 2 * q x =
      q x - 2 * q x ^ 4 + q x ^ 7 := by
  rw [← gap1 x]
  have hx : x = 1 - q x ^ 3 := by
    rw [q_cube]
    simp [subst]
  change x ^ 2 * q x = q x - 2 * q x ^ 4 + q x ^ 7
  calc
    x ^ 2 * q x = (1 - q x ^ 3) ^ 2 * q x :=
      congrArg (fun z : ℝ => z ^ 2 * q x) hx
    _ = q x - 2 * q x ^ 4 + q x ^ 7 := by ring

theorem gap5 (x : ℝ) :
    HasDerivAt intermediate (integrand x) x := by
  have hraw :=
    ((hasDerivAt_q_four x).const_mul (-(3 / 4 : ℝ))).add
      ((hasDerivAt_q_seven x).const_mul (6 / 7 : ℝ)) |>.sub
      ((hasDerivAt_q_ten x).const_mul (3 / 10 : ℝ))
  unfold intermediate
  convert hraw using 1
  rw [gap3, gap4]
  ring

theorem gap6 (x : ℝ) :
    intermediate x = primitive x := by
  have hx : x = 1 - q x ^ 3 := by
    rw [q_cube]
    simp [subst]
  have hpoly : 9 + 12 * x + 14 * x ^ 2 =
      9 + 12 * (1 - q x ^ 3) + 14 * (1 - q x ^ 3) ^ 2 :=
    congrArg (fun z : ℝ => 9 + 12 * z + 14 * z ^ 2) hx
  unfold intermediate primitive
  rw [hpoly]
  ring

theorem gap7 :
    Family integrand = Translates primitive := by
  have hprimitive : ∀ x, HasDerivAt primitive (integrand x) x := by
    intro x
    have heq : intermediate = primitive := by
      funext y
      exact gap6 y
    rw [← heq]
    exact gap5 x
  ext F
  constructor
  · intro hF
    change IsAntiderivative F integrand at hF
    change ∃ C, ∀ x, F x = primitive x + C
    have hzero : ∀ x, HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x
      simpa using (hF x).sub (hprimitive x)
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hc := eq_const_of_deriv_eq_zero
      (fun y => F y - primitive y) hzero x
    linarith
  · rintro ⟨C, hC⟩
    change IsAntiderivative F integrand
    have hEq : F = fun y => primitive y + C := by
      funext y
      exact hC y
    intro x
    rw [hEq]
    exact (hprimitive x).add_const C

end

end ProofGap.Exercise1766
