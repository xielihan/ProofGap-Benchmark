import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2133
noncomputable section

def t (x : ℝ) := Real.sqrt (1 + x ^ 2)
def integrand (x : ℝ) := x ^ 5 / Real.sqrt (1 + x ^ 2)
def pulledBack (x : ℝ) := (t x ^ 2 - 1) ^ 2 * deriv t x
def expanded (x : ℝ) := (t x ^ 4 - 2 * t x ^ 2 + 1) * deriv t x
def primitiveT (x : ℝ) :=
  (1 / 5 : ℝ) * t x ^ 5 - (2 / 3 : ℝ) * t x ^ 3 + t x
def primitive (x : ℝ) :=
  (1 / 15 : ℝ) * (8 - 4 * x ^ 2 + 3 * x ^ 4) * Real.sqrt (1 + x ^ 2)

def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x, HasDerivAt F (f x) x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem t_hasDerivAt (x : ℝ) : HasDerivAt t (x / t x) x := by
  have hpos : 0 < 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa [pow_two, two_mul] using
      (hasDerivAt_id x).mul (hasDerivAt_id x)
  have hinner : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x :=
    hsq.const_add 1
  have htpos : 0 < t x := by
    simpa [t] using Real.sqrt_pos.2 hpos
  have hraw :
      HasDerivAt t ((1 / (2 * t x)) * (2 * x)) x := by
    simpa [t, Function.comp_def] using
      (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp x hinner
  convert hraw using 1
  field_simp [ne_of_gt htpos] <;> ring

theorem gap1 (x : ℝ) : x ^ 2 = t x ^ 2 - 1 := by
  have h : 0 ≤ 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  unfold t
  rw [Real.sq_sqrt h]
  ring
theorem gap2 (x : ℝ) : x = t x * deriv t x := by
  have htpos : 0 < t x := by
    have hpos : 0 < 1 + x ^ 2 := by
      nlinarith [sq_nonneg x]
    simpa [t] using Real.sqrt_pos.2 hpos
  rw [(t_hasDerivAt x).deriv]
  field_simp [ne_of_gt htpos]
theorem gap3 : Family integrand = Family pulledBack := by
  apply congrArg Family
  funext x
  have htpos : 0 < t x := by
    have hpos : 0 < 1 + x ^ 2 := by
      nlinarith [sq_nonneg x]
    simpa [t] using Real.sqrt_pos.2 hpos
  unfold integrand pulledBack
  rw [← gap1 x]
  change x ^ 5 / t x = (x ^ 2) ^ 2 * deriv t x
  apply (div_eq_iff (ne_of_gt htpos)).2
  calc
    x ^ 5 = x ^ 4 * x := by ring
    _ = x ^ 4 * (t x * deriv t x) := by rw [← gap2 x]
    _ = (x ^ 2) ^ 2 * deriv t x * t x := by ring
theorem gap4 : Family pulledBack = Family expanded := by
  apply congrArg Family
  funext x
  unfold pulledBack expanded
  ring
theorem gap5 : Family expanded = Translates primitiveT := by
  have hp : ∀ x, HasDerivAt primitiveT (expanded x) x := by
    intro x
    have ht : HasDerivAt t (deriv t x) x :=
      (t_hasDerivAt x).differentiableAt.hasDerivAt
    have h :=
      (((ht.pow 5).const_mul (1 / 5 : ℝ)).sub
        ((ht.pow 3).const_mul (2 / 3 : ℝ))).add ht
    convert h using 1 <;> simp [expanded] <;> ring
  ext F
  change (∀ x, HasDerivAt F (expanded x) x) ↔
    (∃ C : ℝ, ∀ x, F x = primitiveT x + C)
  constructor
  · intro hF
    have hzero (x : ℝ) :
        HasDerivAt (fun y => F y - primitiveT y) 0 x := by
      simpa using (hF x).sub (hp x)
    have hdiff : Differentiable ℝ (fun y : ℝ => F y - primitiveT y) :=
      fun x => (hzero x).differentiableAt
    have hderiv : ∀ x, deriv (fun y : ℝ => F y - primitiveT y) x = 0 :=
      fun x => (hzero x).deriv
    refine ⟨F 0 - primitiveT 0, ?_⟩
    intro x
    have hc := is_const_of_deriv_eq_zero hdiff hderiv x 0
    change F x - primitiveT x = F 0 - primitiveT 0 at hc
    linarith
  · rintro ⟨C, hC⟩
    intro x
    have hEq : F = primitiveT + fun _ => C := by
      funext y
      exact hC y
    rw [hEq]
    simpa only [add_zero] using (hp x).add (hasDerivAt_const x C)
theorem gap6 : Translates primitiveT = Translates primitive := by
  have hprim : primitiveT = primitive := by
    funext x
    have ht2 : t x ^ 2 = 1 + x ^ 2 := by
      linarith [gap1 x]
    change
      (1 / 5 : ℝ) * t x ^ 5 - (2 / 3 : ℝ) * t x ^ 3 + t x =
        (1 / 15 : ℝ) * (8 - 4 * x ^ 2 + 3 * x ^ 4) * t x
    calc
      (1 / 5 : ℝ) * t x ^ 5 - (2 / 3 : ℝ) * t x ^ 3 + t x =
          (1 / 15 : ℝ) *
            (3 * (t x ^ 2) ^ 2 - 10 * t x ^ 2 + 15) * t x := by ring
      _ = (1 / 15 : ℝ) *
            (3 * (1 + x ^ 2) ^ 2 - 10 * (1 + x ^ 2) + 15) * t x := by
              rw [ht2]
      _ = (1 / 15 : ℝ) * (8 - 4 * x ^ 2 + 3 * x ^ 4) * t x := by ring
  exact congrArg Translates hprim
theorem gap7 : Family integrand = Translates primitive := by
  calc
    Family integrand = Family pulledBack := gap3
    _ = Family expanded := gap4
    _ = Translates primitiveT := gap5
    _ = Translates primitive := gap6

end
end ProofGap.Exercise2133
