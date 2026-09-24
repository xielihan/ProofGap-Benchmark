import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1770

noncomputable section

def subst (x : ℝ) : ℝ := 2 - 5 * x ^ 3
def q (x : ℝ) : ℝ :=
  Real.sign (subst x) * Real.rpow |subst x| (1 / 3 : ℝ)
def integrand (x : ℝ) : ℝ := x ^ 5 * q x ^ 2
def intermediate (x : ℝ) : ℝ :=
  -(2 / 125 : ℝ) * q x ^ 5 + (1 / 200 : ℝ) * q x ^ 8
def primitive (x : ℝ) : ℝ :=
  -(6 + 25 * x ^ 3) / 1000 * q x ^ 5
def IsAntiderivative (F f : ℝ → ℝ) : Prop := ∀ x, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) := {F | IsAntiderivative F f}
def Translates (P : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x, F x = P x + C}

private def signedFive (u : ℝ) : ℝ :=
  u * Real.rpow |u| (2 / 3 : ℝ)

private theorem coe_sign_eq_real_sign (u : ℝ) :
    ((SignType.sign u : SignType) : ℝ) = Real.sign u := by
  rcases lt_trichotomy u 0 with h | h | h
  · rw [_root_.sign_neg h, Real.sign_of_neg h]
    rfl
  · subst u
    simp
  · rw [_root_.sign_pos h, Real.sign_of_pos h]
    rfl

private theorem mul_real_sign (u : ℝ) : u * Real.sign u = |u| := by
  rcases lt_trichotomy u 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]
    ring
  · subst u
    simp
  · rw [Real.sign_of_pos h, abs_of_pos h]
    ring

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

private theorem q_two (x : ℝ) :
    q x ^ 2 = Real.rpow |subst x| (2 / 3 : ℝ) := by
  unfold q
  rw [mul_pow]
  have hr : (Real.rpow |subst x| (1 / 3 : ℝ)) ^ 2 =
      Real.rpow |subst x| (2 / 3 : ℝ) := by
    calc
      (Real.rpow |subst x| (1 / 3 : ℝ)) ^ 2 =
          Real.rpow |subst x| ((1 / 3 : ℝ) * (2 : ℕ)) :=
        (Real.rpow_mul_natCast (abs_nonneg (subst x)) (1 / 3 : ℝ) 2).symm
      _ = Real.rpow |subst x| (2 / 3 : ℝ) := by norm_num
  rw [hr]
  rcases lt_trichotomy (subst x) 0 with h | h | h
  · simp [Real.sign_of_neg h]
  · simp [h, Real.zero_rpow]
  · simp [Real.sign_of_pos h]

private theorem hasDerivAt_subst (x : ℝ) :
    HasDerivAt subst (-15 * x ^ 2) x := by
  unfold subst
  convert (hasDerivAt_const x (2 : ℝ)).sub
    (((hasDerivAt_id x).pow 3).const_mul 5) using 1 <;>
    simp only [id] <;>
    ring

private theorem hasDerivAt_signedFive (u : ℝ) :
    HasDerivAt signedFive
      ((5 / 3 : ℝ) * Real.rpow |u| (2 / 3 : ℝ)) u := by
  by_cases hu : u = 0
  · subst u
    apply hasDerivAt_of_hasDerivAt_of_ne
      (f := signedFive)
      (g := fun y : ℝ => (5 / 3 : ℝ) * Real.rpow |y| (2 / 3 : ℝ))
      (x := (0 : ℝ))
    · intro y hy
      have habs := hasDerivAt_abs hy
      have hp := habs.rpow_const
        (p := (2 / 3 : ℝ)) (Or.inl (abs_ne_zero.mpr hy))
      have hraw := (hasDerivAt_id y).mul hp
      unfold signedFive
      convert hraw using 1
      have habspos : 0 < |y| := abs_pos.mpr hy
      have hr : (|y| ^ (-1 / 3 : ℝ)) * |y| =
          |y| ^ (2 / 3 : ℝ) := by
        calc
          (|y| ^ (-1 / 3 : ℝ)) * |y| =
              |y| ^ ((-1 / 3 : ℝ) + 1) :=
            (Real.rpow_add_one habspos.ne' (-1 / 3 : ℝ)).symm
          _ = |y| ^ (2 / 3 : ℝ) := by norm_num
      rw [Real.rpow_eq_pow]
      simp only [id]
      rw [coe_sign_eq_real_sign]
      rw [show (2 / 3 : ℝ) - 1 = -1 / 3 by norm_num]
      rw [show y * (Real.sign y * (2 / 3 : ℝ) * (|y| ^ (-1 / 3 : ℝ))) =
          (y * Real.sign y) * (2 / 3 : ℝ) * (|y| ^ (-1 / 3 : ℝ)) by ring]
      rw [mul_real_sign]
      rw [show |y| * (2 / 3 : ℝ) * (|y| ^ (-1 / 3 : ℝ)) =
          (2 / 3 : ℝ) * ((|y| ^ (-1 / 3 : ℝ)) * |y|) by ring]
      rw [hr]
      ring
    · unfold signedFive
      simpa only [Real.rpow_eq_pow] using continuousAt_id.mul
        (continuous_abs.continuousAt.rpow_const (Or.inr (by norm_num)))
    · simpa only [Real.rpow_eq_pow] using continuousAt_const.mul
        (continuous_abs.continuousAt.rpow_const (Or.inr (by norm_num)))
  · have habs := hasDerivAt_abs hu
    have hp := habs.rpow_const
      (p := (2 / 3 : ℝ)) (Or.inl (abs_ne_zero.mpr hu))
    have hraw := (hasDerivAt_id u).mul hp
    unfold signedFive
    convert hraw using 1
    have habspos : 0 < |u| := abs_pos.mpr hu
    have hr : (|u| ^ (-1 / 3 : ℝ)) * |u| =
        |u| ^ (2 / 3 : ℝ) := by
      calc
        (|u| ^ (-1 / 3 : ℝ)) * |u| =
            |u| ^ ((-1 / 3 : ℝ) + 1) :=
          (Real.rpow_add_one habspos.ne' (-1 / 3 : ℝ)).symm
        _ = |u| ^ (2 / 3 : ℝ) := by norm_num
    rw [Real.rpow_eq_pow]
    simp only [id]
    rw [coe_sign_eq_real_sign]
    rw [show (2 / 3 : ℝ) - 1 = -1 / 3 by norm_num]
    rw [show u * (Real.sign u * (2 / 3 : ℝ) * (|u| ^ (-1 / 3 : ℝ))) =
        (u * Real.sign u) * (2 / 3 : ℝ) * (|u| ^ (-1 / 3 : ℝ)) by ring]
    rw [mul_real_sign]
    rw [show |u| * (2 / 3 : ℝ) * (|u| ^ (-1 / 3 : ℝ)) =
        (2 / 3 : ℝ) * ((|u| ^ (-1 / 3 : ℝ)) * |u|) by ring]
    rw [hr]
    ring

private theorem q_five_eq (x : ℝ) : q x ^ 5 = signedFive (subst x) := by
  unfold signedFive
  rw [show q x ^ 5 = q x ^ 3 * q x ^ 2 by ring, q_cube, q_two]

private theorem hasDerivAt_q_five (x : ℝ) :
    HasDerivAt (fun y : ℝ => q y ^ 5) (-25 * x ^ 2 * q x ^ 2) x := by
  have heq : (fun y : ℝ => q y ^ 5) = fun y => signedFive (subst y) := by
    funext y
    exact q_five_eq y
  rw [heq]
  have h := (hasDerivAt_signedFive (subst x)).comp x (hasDerivAt_subst x)
  convert h using 1
  rw [q_two]
  ring

private theorem hasDerivAt_q_eight (x : ℝ) :
    HasDerivAt (fun y : ℝ => q y ^ 8) (-40 * x ^ 2 * q x ^ 5) x := by
  have heq : (fun y : ℝ => q y ^ 8) =
      fun y : ℝ => subst y * q y ^ 5 := by
    funext y
    rw [← q_cube y]
    ring
  rw [heq]
  have h := (hasDerivAt_subst x).mul (hasDerivAt_q_five x)
  convert h using 1
  rw [← q_cube x]
  ring

private theorem eq_const_of_deriv_eq_zero
    (g : ℝ → ℝ) (hzero : ∀ x, HasDerivAt g 0 x) (x : ℝ) :
    g x = g 0 := by
  have hdiff : Differentiable ℝ g := fun y => (hzero y).differentiableAt
  exact is_const_of_deriv_eq_zero hdiff (fun y => (hzero y).deriv) x 0

theorem gap1 (x : ℝ) :
    x ^ 3 = (1 / 5 : ℝ) * (2 - subst x) := by
  unfold subst
  ring

theorem gap2 (x : ℝ) :
    x ^ 5 = (1 / 3 : ℝ) * x ^ 3 * deriv (fun y : ℝ => y ^ 3) x := by
  have hd : deriv (fun y : ℝ => y ^ 3) x = 3 * x ^ 2 := by
    simpa using ((hasDerivAt_id x).pow 3).deriv
  rw [hd]
  ring

theorem gap3 (x : ℝ) :
    (1 / 3 : ℝ) * x ^ 3 * deriv (fun y : ℝ => y ^ 3) x =
      -(1 / 75 : ℝ) * (2 - subst x) * deriv subst x := by
  have hd : deriv (fun y : ℝ => y ^ 3) x = 3 * x ^ 2 := by
    simpa using ((hasDerivAt_id x).pow 3).deriv
  have hs : HasDerivAt subst (-15 * x ^ 2) x := by
    change HasDerivAt (fun y : ℝ => 2 - 5 * y ^ 3) (-15 * x ^ 2) x
    convert (hasDerivAt_const x (2 : ℝ)).sub
      (((hasDerivAt_id x).pow 3).const_mul 5) using 1 <;>
      simp only [id] <;>
      ring
  rw [hd, hs.deriv]
  unfold subst
  ring

theorem gap4 (x : ℝ) :
    x ^ 5 = -(1 / 75 : ℝ) * (2 - subst x) * deriv subst x := by
  rw [gap2, gap3]

theorem gap5 (x : ℝ) :
    integrand x =
      -(1 / 75 : ℝ) * (2 * q x ^ 2 - q x ^ 5) * deriv subst x := by
  unfold integrand
  rw [gap4, (hasDerivAt_subst x).deriv]
  rw [← q_cube x]
  ring

theorem gap6 (x : ℝ) :
    2 * q x ^ 2 - q x ^ 5 = q x ^ 2 * (2 - subst x) := by
  rw [← q_cube x]
  ring

theorem gap7 (x : ℝ) :
    HasDerivAt intermediate (integrand x) x := by
  have hraw :=
    ((hasDerivAt_q_five x).const_mul (-(2 / 125 : ℝ))).add
      ((hasDerivAt_q_eight x).const_mul (1 / 200 : ℝ))
  unfold intermediate
  convert hraw using 1
  rw [gap5, (hasDerivAt_subst x).deriv]
  ring

theorem gap8 (x : ℝ) :
    intermediate x = primitive x := by
  have hx3 : x ^ 3 = (1 / 5 : ℝ) * (2 - q x ^ 3) := by
    rw [q_cube]
    unfold subst
    ring
  unfold intermediate primitive
  have hpoly : 6 + 25 * x ^ 3 =
      6 + 25 * ((1 / 5 : ℝ) * (2 - q x ^ 3)) :=
    congrArg (fun z : ℝ => 6 + 25 * z) hx3
  rw [hpoly]
  ring

theorem gap9 :
    Family integrand = Translates primitive := by
  have hprimitive : ∀ x, HasDerivAt primitive (integrand x) x := by
    intro x
    have heq : intermediate = primitive := by
      funext y
      exact gap8 y
    rw [← heq]
    exact gap7 x
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

end ProofGap.Exercise1770
