import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1176

noncomputable section

open scoped BigOperators

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def y (u : ℝ) : ℝ := u ^ 2
def idFun (u : ℝ) : ℝ := u

def leibnizSum (u : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 11,
    (Nat.choose 10 i : ℝ) *
      iterDeriv (10 - i) idFun u * iterDeriv i idFun u

def partialExpansion (u : ℝ) : ℝ :=
  u * iterDeriv 10 idFun u +
    10 * iterDeriv 9 idFun u * iterDeriv 1 idFun u +
    45 * iterDeriv 8 idFun u * iterDeriv 2 idFun u +
    120 * iterDeriv 7 idFun u * iterDeriv 3 idFun u +
    210 * iterDeriv 6 idFun u * iterDeriv 4 idFun u

def fullExpansion (u : ℝ) : ℝ :=
  partialExpansion u +
    252 * iterDeriv 5 idFun u ^ 2 +
    210 * iterDeriv 4 idFun u * iterDeriv 6 idFun u +
    120 * iterDeriv 3 idFun u * iterDeriv 7 idFun u +
    45 * iterDeriv 2 idFun u * iterDeriv 8 idFun u +
    10 * iterDeriv 1 idFun u * iterDeriv 9 idFun u +
    u * iterDeriv 10 idFun u

def combinedExpansion (u : ℝ) : ℝ :=
  2 * u * iterDeriv 10 idFun u +
    20 * iterDeriv 1 idFun u * iterDeriv 9 idFun u +
    90 * iterDeriv 2 idFun u * iterDeriv 8 idFun u +
    240 * iterDeriv 3 idFun u * iterDeriv 7 idFun u +
    420 * iterDeriv 4 idFun u * iterDeriv 6 idFun u +
    252 * iterDeriv 5 idFun u ^ 2

private lemma idFun_apply (u : ℝ) : idFun u = u := by
  rfl

private lemma deriv_const_eq (c : ℝ) :
    deriv (fun _ : ℝ => c) = fun _ : ℝ => 0 := by
  funext u
  exact (hasDerivAt_const u c).deriv

private lemma deriv_idFun_eq :
    deriv idFun = fun _ : ℝ => 1 := by
  funext u
  change deriv (fun z : ℝ => z) u = 1
  exact (hasDerivAt_id u).deriv

private lemma deriv_y_eq :
    deriv y = fun u : ℝ => 2 * u := by
  funext u
  have hy : y = fun z : ℝ => z * z := by
    funext z
    simp [y, pow_two]
  rw [hy]
  have h : HasDerivAt (fun z : ℝ => z) 1 u := hasDerivAt_id u
  convert (h.mul h).deriv using 1 <;> ring

private lemma deriv_two_mul_eq :
    deriv (fun u : ℝ => 2 * u) = fun _ : ℝ => 2 := by
  funext u
  have hc : HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 u :=
    hasDerivAt_const u 2
  have hi : HasDerivAt (fun z : ℝ => z) 1 u := hasDerivAt_id u
  convert (hc.mul hi).deriv using 1 <;> ring

private lemma iterDeriv_y_ten (u : ℝ) : iterDeriv 10 y u = 0 := by
  simp [iterDeriv, Function.iterate_succ_apply, deriv_y_eq,
    deriv_two_mul_eq, deriv_const_eq]

theorem gap1 (u : ℝ) :
    iterDeriv 10 y u = iterDeriv 10 (fun z : ℝ => z * z) u := by
  have h : y = fun z : ℝ => z * z := by
    funext z
    simp [y, pow_two]
  rw [h]

theorem gap2 (u : ℝ) :
    iterDeriv 10 (fun z : ℝ => z * z) u = leibnizSum u := by
  calc
    iterDeriv 10 (fun z : ℝ => z * z) u = iterDeriv 10 y u := (gap1 u).symm
    _ = 0 := iterDeriv_y_ten u
    _ = leibnizSum u := by
      symm
      simp [leibnizSum, Finset.sum_range_succ, iterDeriv,
        Function.iterate_succ_apply, deriv_idFun_eq, deriv_const_eq,
        idFun_apply]

theorem gap3 (u : ℝ) :
    iterDeriv 10 y u = leibnizSum u := by
  exact (gap1 u).trans (gap2 u)

theorem gap4 (u : ℝ) :
    iterDeriv 10 y u = partialExpansion u := by
  calc
    iterDeriv 10 y u = 0 := iterDeriv_y_ten u
    _ = partialExpansion u := by
      symm
      simp [partialExpansion, iterDeriv, Function.iterate_succ_apply,
        deriv_idFun_eq, deriv_const_eq, idFun_apply]

theorem gap5 (u : ℝ) :
    iterDeriv 10 y u = fullExpansion u := by
  rw [gap4]
  simp [fullExpansion, iterDeriv, Function.iterate_succ_apply,
    deriv_idFun_eq, deriv_const_eq, idFun_apply]

theorem gap6 (u : ℝ) :
    iterDeriv 10 y u = combinedExpansion u := by
  calc
    iterDeriv 10 y u = 0 := iterDeriv_y_ten u
    _ = combinedExpansion u := by
      symm
      simp [combinedExpansion, iterDeriv, Function.iterate_succ_apply,
        deriv_idFun_eq, deriv_const_eq, idFun_apply]

end

end ProofGap.Exercise1176
