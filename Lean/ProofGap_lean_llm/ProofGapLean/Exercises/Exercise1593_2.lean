import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1593_2

noncomputable section

def y (x : ℝ) := Real.tan x - Real.sin x
def axis (_x : ℝ) : ℝ := 0
def sec (x : ℝ) := 1 / Real.cos x
def iterDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (iterDeriv n f)
def ContactOrder (f g : ℝ → ℝ) (x₀ : ℝ) (m : ℕ) : Prop :=
  (∀ k ≤ m, iterDeriv k f x₀ = iterDeriv k g x₀) ∧
    iterDeriv (m + 1) f x₀ ≠ iterDeriv (m + 1) g x₀

private theorem sec_sq_eq_one_add_tan_sq (x : ℝ)
    (hx : Real.cos x ≠ 0) :
    sec x ^ 2 = 1 + Real.tan x ^ 2 := by
  rw [sec, Real.tan_eq_sin_div_cos]
  field_simp [hx]
  nlinarith [Real.sin_sq_add_cos_sq x]

theorem gap1 (x : ℝ) (hx : Real.cos x ≠ 0) :
    deriv y x = sec x ^ 2 - Real.cos x := by
  have hderiv : HasDerivAt y (sec x ^ 2 - Real.cos x) x := by
    convert (Real.hasDerivAt_tan hx).sub (Real.hasDerivAt_sin x) using 1 <;>
      simp [y, sec]
  exact hderiv.deriv
theorem gap2 (x : ℝ) (hx : Real.cos x ≠ 0) :
    deriv (deriv y) x = 2 * sec x ^ 2 * Real.tan x + Real.sin x := by
  have hcos : ∀ᶠ z in nhds x, Real.cos z ≠ 0 :=
    Real.continuous_cos.continuousAt.eventually_ne hx
  have heq :
      deriv y =ᶠ[nhds x]
        (fun z : ℝ => 1 + Real.tan z ^ 2 - Real.cos z) := by
    filter_upwards [hcos] with z hz
    rw [gap1 z hz, sec_sq_eq_one_add_tan_sq z hz]
  have hderiv :
      HasDerivAt (fun z : ℝ => 1 + Real.tan z ^ 2 - Real.cos z)
        (2 * sec x ^ 2 * Real.tan x + Real.sin x) x := by
    convert
      ((hasDerivAt_const x (1 : ℝ)).add
          ((Real.hasDerivAt_tan hx).pow 2)).sub
        (Real.hasDerivAt_cos x) using 1 <;>
      (try simp [sec]) <;> ring
  calc
    deriv (deriv y) x =
        deriv (fun z : ℝ => 1 + Real.tan z ^ 2 - Real.cos z) x :=
      heq.deriv_eq
    _ = 2 * sec x ^ 2 * Real.tan x + Real.sin x := hderiv.deriv
theorem gap3 (x : ℝ) (hx : Real.cos x ≠ 0) :
    deriv (deriv (deriv y)) x =
      4 * sec x ^ 2 * Real.tan x ^ 2 + 2 * sec x ^ 4 + Real.cos x := by
  have hcos : ∀ᶠ z in nhds x, Real.cos z ≠ 0 :=
    Real.continuous_cos.continuousAt.eventually_ne hx
  have heq :
      deriv (deriv y) =ᶠ[nhds x]
        (fun z : ℝ =>
          2 * (1 + Real.tan z ^ 2) * Real.tan z + Real.sin z) := by
    filter_upwards [hcos] with z hz
    rw [gap2 z hz, sec_sq_eq_one_add_tan_sq z hz]
  have hd : 1 / Real.cos x ^ 2 = sec x ^ 2 := by
    simp [sec]
  have hrel : sec x ^ 2 = 1 + Real.tan x ^ 2 :=
    sec_sq_eq_one_add_tan_sq x hx
  have hrel4 : sec x ^ 4 = (1 + Real.tan x ^ 2) ^ 2 := by
    calc
      sec x ^ 4 = (sec x ^ 2) ^ 2 := by ring
      _ = (1 + Real.tan x ^ 2) ^ 2 := by rw [hrel]
  have hraw :=
    ((((hasDerivAt_const x (2 : ℝ)).mul
          ((hasDerivAt_const x (1 : ℝ)).add
            ((Real.hasDerivAt_tan hx).pow 2))).mul
        (Real.hasDerivAt_tan hx)).add
      (Real.hasDerivAt_sin x))
  have hderiv :
      HasDerivAt
        (fun z : ℝ =>
          2 * (1 + Real.tan z ^ 2) * Real.tan z + Real.sin z)
        (4 * sec x ^ 2 * Real.tan x ^ 2 +
          2 * sec x ^ 4 + Real.cos x) x := by
    convert hraw using 1 <;>
      (try simp [hd, hrel, hrel4]) <;> ring
  calc
    deriv (deriv (deriv y)) x =
        deriv
          (fun z : ℝ =>
            2 * (1 + Real.tan z ^ 2) * Real.tan z + Real.sin z) x :=
      heq.deriv_eq
    _ = 4 * sec x ^ 2 * Real.tan x ^ 2 +
          2 * sec x ^ 4 + Real.cos x := hderiv.deriv
theorem gap4 : deriv y 0 = deriv (deriv y) 0 := by
  rw [gap1 0 (by norm_num), gap2 0 (by norm_num)]
  norm_num [sec]
theorem gap5 : deriv (deriv y) 0 = 0 := by
  rw [gap2 0 (by norm_num)]
  norm_num [sec]
theorem gap6 : deriv y 0 = 0 := by
  rw [gap1 0 (by norm_num)]
  norm_num [sec]
theorem gap7 : deriv (deriv (deriv y)) 0 = 3 := by
  rw [gap3 0 (by norm_num)]
  norm_num [sec]
theorem gap8 : (3 : ℝ) ≠ 0 := by
  norm_num
theorem gap9 : deriv (deriv (deriv y)) 0 ≠ 0 := by
  rw [gap7]
  exact gap8
theorem gap10 : ContactOrder y axis 0 2 := by
  have haxis : deriv axis = axis := by
    funext x
    exact (hasDerivAt_const x (0 : ℝ)).deriv
  constructor
  · intro k hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl | rfl
    · simp [iterDeriv, y, axis]
    · simp only [iterDeriv]
      rw [haxis]
      simpa [axis] using gap6
    · simp only [iterDeriv]
      rw [haxis, haxis]
      simpa [axis] using gap5
  · simp only [iterDeriv]
    rw [haxis, haxis, haxis]
    simpa [axis] using gap9

end
end ProofGap.Exercise1593_2
