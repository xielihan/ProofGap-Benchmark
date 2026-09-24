import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ProofGap.Exercise1177

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def y (u : ℝ) : ℝ := Real.exp u
def idFun (u : ℝ) : ℝ := u
def d (n : ℕ) (u : ℝ) : ℝ := iterDeriv n idFun u

private theorem basicDerivs :
    deriv y = y ∧
      deriv idFun = (fun _ : ℝ => 1) ∧
        ∀ c : ℝ, deriv (fun _ : ℝ => c) = fun _ => 0 := by
  constructor
  · funext u
    change deriv Real.exp u = Real.exp u
    exact (Real.hasDerivAt_exp u).deriv
  constructor
  · funext u
    change deriv (fun x : ℝ => x) u = 1
    exact (hasDerivAt_id u).deriv
  · intro c
    funext u
    exact (hasDerivAt_const (x := u) (c := c)).deriv

theorem gap1 (u : ℝ) :
    iterDeriv 1 y u = Real.exp u * d 1 u := by
  rcases basicDerivs with ⟨hy, hid, hconst⟩
  simp [iterDeriv, d, hy, hid, y]

theorem gap2 (u : ℝ) :
    iterDeriv 2 y u =
      Real.exp u * d 1 u ^ 2 + Real.exp u * d 2 u := by
  rcases basicDerivs with ⟨hy, hid, hconst⟩
  simp [iterDeriv, d, hy, hid, hconst, y]

theorem gap3 (u : ℝ) :
    iterDeriv 3 y u =
      Real.exp u *
        (d 1 u ^ 3 + d 1 u * d 2 u +
          deriv (fun z : ℝ => d 1 z ^ 2) u + d 3 u) := by
  rcases basicDerivs with ⟨hy, hid, hconst⟩
  simp [iterDeriv, d, hy, hid, hconst, y]

theorem gap4 (u : ℝ) :
    Real.exp u *
        (d 1 u ^ 3 + d 1 u * d 2 u +
          deriv (fun z : ℝ => d 1 z ^ 2) u + d 3 u) =
      Real.exp u * (d 1 u ^ 3 + 3 * d 1 u * d 2 u + d 3 u) := by
  rcases basicDerivs with ⟨hy, hid, hconst⟩
  simp [d, iterDeriv, hid, hconst]

theorem gap5 (u : ℝ) :
    iterDeriv 3 y u =
      Real.exp u * (d 1 u ^ 3 + 3 * d 1 u * d 2 u + d 3 u) := by
  rw [gap3 u, gap4 u]

theorem gap6 (u : ℝ) :
    iterDeriv 4 y u =
      Real.exp u *
        (d 1 u ^ 4 + 3 * d 1 u ^ 2 * d 2 u +
          d 1 u * d 3 u +
          deriv (fun z : ℝ => d 1 z ^ 3) u +
          3 * deriv (fun z : ℝ => d 1 z * d 2 z) u + d 4 u) := by
  rcases basicDerivs with ⟨hy, hid, hconst⟩
  simp [iterDeriv, d, hy, hid, hconst, y]

theorem gap7 (u : ℝ) :
    iterDeriv 4 y u =
      Real.exp u *
        (d 1 u ^ 4 + 6 * d 1 u ^ 2 * d 2 u +
          3 * d 2 u ^ 2 + 4 * d 1 u * d 3 u + d 4 u) := by
  rcases basicDerivs with ⟨hy, hid, hconst⟩
  simp [iterDeriv, d, hy, hid, hconst, y]

end

end ProofGap.Exercise1177
