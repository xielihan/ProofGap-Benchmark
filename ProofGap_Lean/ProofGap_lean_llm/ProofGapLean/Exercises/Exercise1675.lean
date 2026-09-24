import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1675

noncomputable section

def integrand (x : ℝ) : ℝ := x ^ 2 * Real.cbrt (1 + x ^ 3)
def inner (x : ℝ) : ℝ := 1 + x ^ 3
def primitive (x : ℝ) : ℝ := (1 / 4 : ℝ) * (Real.cbrt (inner x)) ^ 4

def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

private theorem cbrt_cubed_of_nonneg (x : ℝ) (hx : 0 ≤ x) :
    (Real.cbrt x) ^ 3 = x := by
  unfold Real.cbrt
  rw [← Real.rpow_natCast]
  calc
    (x ^ (1 / 3 : ℝ)) ^ (3 : ℝ) =
        x ^ ((1 / 3 : ℝ) * 3) := (Real.rpow_mul hx _ _).symm
    _ = x := by norm_num

private theorem cbrt_pos_of_pos {x : ℝ} (hx : 0 < x) :
    0 < Real.cbrt x := by
  unfold Real.cbrt
  exact Real.rpow_pos_of_pos hx _

private theorem rpow_third_sub_one_eq {x : ℝ} (hx : 0 < x) :
    x ^ ((1 / 3 : ℝ) - 1) = 1 / (Real.cbrt x) ^ 2 := by
  have hcpos := cbrt_pos_of_pos hx
  have hcubed := cbrt_cubed_of_nonneg x hx.le
  rw [Real.rpow_sub hx, Real.rpow_one]
  change Real.cbrt x / x = 1 / (Real.cbrt x) ^ 2
  field_simp [hcpos.ne']
  nlinarith [hcubed]

private theorem hasDerivAt_primitive_of_pos (x : ℝ)
    (hx : 0 < inner x) :
    HasDerivAt primitive (integrand x) x := by
  have hinner : HasDerivAt inner (3 * x ^ 2) x := by
    unfold inner
    convert (hasDerivAt_const x 1).add ((hasDerivAt_id x).fun_pow 3) using 1 <;>
      simp [id] <;> ring
  have hroot :
      HasDerivAt (fun z : ℝ => Real.cbrt (inner z))
        ((3 * x ^ 2) * (1 / 3 : ℝ) *
          (inner x) ^ ((1 / 3 : ℝ) - 1)) x := by
    unfold Real.cbrt
    convert hinner.rpow_const (p := (1 / 3 : ℝ))
      (Or.inl hx.ne') using 1 <;> ring
  have hprim : HasDerivAt primitive
      ((1 / 4 : ℝ) *
        (4 * (Real.cbrt (inner x)) ^ 3 *
          ((3 * x ^ 2) * (1 / 3 : ℝ) *
            (inner x) ^ ((1 / 3 : ℝ) - 1)))) x := by
    unfold primitive
    convert (hroot.fun_pow 4).const_mul (1 / 4 : ℝ) using 1 <;> ring
  apply hprim.congr_deriv
  unfold integrand
  have hcpos := cbrt_pos_of_pos hx
  have hcubed := cbrt_cubed_of_nonneg (inner x) hx.le
  rw [rpow_third_sub_one_eq hx]
  field_simp [hcpos.ne']
  simpa [inner] using
    (mul_comm (Real.cbrt (inner x)) (x ^ 2))

theorem gap1 (x : ℝ) :
    integrand x = (1 / 3 : ℝ) * Real.cbrt (inner x) * deriv inner x := by
  have h1 : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert h1.mul h1 using 1
    · funext y
      simp [pow_two]
    · ring
  have h3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    convert h2.mul h1 using 1 <;> ring
  have hinner : HasDerivAt inner (3 * x ^ 2) x := by
    convert (hasDerivAt_const x 1).add h3 using 1 <;> ring
  rw [hinner.deriv]
  unfold integrand inner
  ring

theorem gap2 (x : ℝ) (hx : -1 < x) :
    HasDerivAt primitive (integrand x) x := by
  exact hasDerivAt_primitive_of_pos x (by
    have hquad : 0 < x ^ 2 - x + 1 := by
      nlinarith [sq_nonneg (x - 1 / 2)]
    have hprod := mul_pos (by linarith : 0 < x + 1) hquad
    unfold inner
    calc
      0 < (x + 1) * (x ^ 2 - x + 1) := hprod
      _ = 1 + x ^ 3 := by ring)

theorem gap3 :
    Family integrand (Set.Ioi (-1)) =
      Translates primitive (Set.Ioi (-1)) := by
  ext F
  constructor
  · intro hF
    have hFd : DifferentiableOn ℝ F (Set.Ioi (-1)) := by
      intro x hx
      exact (hF x hx).differentiableAt.differentiableWithinAt
    have hPd : DifferentiableOn ℝ primitive (Set.Ioi (-1)) := by
      intro x hx
      exact (gap2 x hx).differentiableAt.differentiableWithinAt
    have hderiv : Set.EqOn (deriv F) (deriv primitive) (Set.Ioi (-1)) := by
      intro x hx
      rw [(hF x hx).deriv, (gap2 x hx).deriv]
    rcases isOpen_Ioi.exists_eq_add_of_deriv_eq isPreconnected_Ioi
      hFd hPd hderiv with ⟨C, hC⟩
    exact ⟨C, hC⟩
  · rintro ⟨C, hC⟩
    intro x hx
    have hevent : F =ᶠ[nhds x] fun y => primitive y + C := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      exact hC y hy
    exact ((gap2 x hx).add_const C).congr_of_eventuallyEq hevent

end

end ProofGap.Exercise1675
