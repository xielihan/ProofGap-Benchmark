import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1902_3

noncomputable section

def q (a b c x : ℝ) : ℝ := a * x ^ 2 + 2 * b * x + c
def numerator (α β γ x : ℝ) : ℝ := α * x ^ 2 + 2 * β * x + γ
def integrand (a b c α β γ x : ℝ) : ℝ :=
  numerator α β γ x / q a b c x ^ 2
def shift (b c x : ℝ) : ℝ := x + c / (2 * b)
def domain (b c : ℝ) : Set ℝ := {x | shift b c x ≠ 0}
def tailCoefficient (b c α β γ : ℝ) : ℝ :=
  α * c ^ 2 / (4 * b ^ 2) - β * c / b + γ
def rationalPrimitive (b c α β γ x : ℝ) : ℝ :=
  α / (4 * b ^ 2) * x -
    tailCoefficient b c α β γ / (4 * b ^ 2 * shift b c x)

theorem gap1 (a b c α β γ x : ℝ) (ha : a = 0) (hb : b ≠ 0)
    (hx : x ∈ domain b c) :
    integrand a b c α β γ x =
      (α * shift b c x ^ 2 - α * c / b * shift b c x +
          α * c ^ 2 / (4 * b ^ 2) +
          2 * β * shift b c x - β * c / b + γ) /
        (4 * b ^ 2 * shift b c x ^ 2) := by
  have hq : q a b c x = 2 * b * shift b c x := by
    unfold q shift
    rw [ha]
    field_simp [hb] <;> ring
  have hn :
      numerator α β γ x =
        α * shift b c x ^ 2 - α * c / b * shift b c x +
          α * c ^ 2 / (4 * b ^ 2) + 2 * β * shift b c x -
          β * c / b + γ := by
    unfold numerator shift
    field_simp [hb] <;> ring
  unfold integrand
  rw [hq, hn]
  congr 1
  ring

theorem gap2 (a b c α β γ x : ℝ) (ha : a = 0) (hb : b ≠ 0)
    (hx : x ∈ domain b c) :
    integrand a b c α β γ x =
      α / (4 * b ^ 2) +
        (2 * β - α * c / b) / (4 * b ^ 2 * shift b c x) +
        tailCoefficient b c α β γ / (4 * b ^ 2 * shift b c x ^ 2) := by
  have hs : shift b c x ≠ 0 := by
    simpa [domain] using hx
  rw [gap1 a b c α β γ x ha hb hx]
  unfold tailCoefficient
  field_simp [hb, hs] <;> ring

theorem gap3 (b c α β : ℝ) (hb : b ≠ 0) :
    2 * β - α * c / b = 0 ↔ α * c = 2 * b * β := by
  constructor
  · intro h
    field_simp [hb] at h
    nlinarith
  · intro h
    field_simp [hb]
    nlinarith

theorem gap4 (a b c α β γ x : ℝ) (ha : a = 0) (hb : b ≠ 0)
    (hrel : α * c = 2 * b * β) (hx : x ∈ domain b c) :
    HasDerivAt (rationalPrimitive b c α β γ)
      (integrand a b c α β γ x) x := by
  have hs : shift b c x ≠ 0 := by
    simpa [domain] using hx
  have hzero : 2 * β - α * c / b = 0 :=
    (gap3 b c α β hb).2 hrel
  have hint := gap2 a b c α β γ x ha hb hx
  rw [hzero] at hint
  simp only [zero_div, add_zero] at hint
  have hshift : HasDerivAt (shift b c) 1 x := by
    simpa [shift] using
      (hasDerivAt_id x).add (hasDerivAt_const x (c / (2 * b)))
  have hlinear :
      HasDerivAt (fun y : ℝ => α / (4 * b ^ 2) * y)
        (α / (4 * b ^ 2)) x := by
    simpa using
      (hasDerivAt_const x (α / (4 * b ^ 2))).mul (hasDerivAt_id x)
  have hden :
      HasDerivAt (fun y : ℝ => 4 * b ^ 2 * shift b c y)
        (4 * b ^ 2) x := by
    simpa using (hasDerivAt_const x (4 * b ^ 2)).mul hshift
  have hK : 4 * b ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hb)
  have hden_ne : 4 * b ^ 2 * shift b c x ≠ 0 :=
    mul_ne_zero hK hs
  have htail :
      HasDerivAt
        (fun y : ℝ =>
          tailCoefficient b c α β γ / (4 * b ^ 2 * shift b c y))
        (-tailCoefficient b c α β γ * (4 * b ^ 2) /
          (4 * b ^ 2 * shift b c x) ^ 2) x := by
    convert
      (hasDerivAt_const x (tailCoefficient b c α β γ)).div hden hden_ne
        using 1 <;> ring
  have hp :
      HasDerivAt (rationalPrimitive b c α β γ)
        (α / (4 * b ^ 2) -
          (-tailCoefficient b c α β γ * (4 * b ^ 2) /
            (4 * b ^ 2 * shift b c x) ^ 2)) x := by
    simpa only [rationalPrimitive] using hlinear.sub htail
  rw [hint]
  convert hp using 1
  field_simp [hb, hs, hden_ne] <;> ring

theorem gap5 (a b c α β γ : ℝ) (ha : a = 0)
    (hrel : α * c = 2 * b * β) :
    a * γ + c * α = 2 * b * β := by
  rw [ha, zero_mul, zero_add]
  simpa [mul_comm] using hrel

theorem gap6 (a b c α β γ : ℝ) (ha : a = 0) (hb : b ≠ 0)
    (hrel : a * γ + c * α = 2 * b * β) :
    ∃ R : ℝ → ℝ, ∀ x ∈ domain b c,
      HasDerivAt R (integrand a b c α β γ x) x := by
  have hc : c * α = 2 * b * β := by
    simpa [ha] using hrel
  have hac : α * c = 2 * b * β := by
    calc
      α * c = c * α := mul_comm _ _
      _ = 2 * b * β := hc
  refine ⟨rationalPrimitive b c α β γ, ?_⟩
  intro x hx
  exact gap4 a b c α β γ x ha hb hac hx

end

end ProofGap.Exercise1902_3
