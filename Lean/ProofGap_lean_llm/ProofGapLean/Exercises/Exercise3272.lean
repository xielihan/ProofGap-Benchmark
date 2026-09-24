import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3272

noncomputable section

def u (x y : ℝ) : ℝ :=
  Real.cos x * Real.cosh y

def iterDeriv (n : ℕ) (g : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) g

def partialXOrder (m : ℕ) (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  iterDeriv m (fun t => g t y) x

def partialYOrder (n : ℕ) (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  iterDeriv n (fun t => g x t) y

def mixedOrder (m n : ℕ) (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialYOrder n (fun a b => partialXOrder m g a b) x y

def sixthDirectional (x y dx dy : ℝ) : ℝ :=
  iterDeriv 6 (fun s => u (x + s * dx) (y + s * dy)) 0

def sixthOperator (x y dx dy : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 7,
    (Nat.choose 6 k : ℝ) *
      mixedOrder k (6 - k) u x y * dx ^ k * dy ^ (6 - k)

def expandedForm (x y dx dy : ℝ) : ℝ :=
  -Real.cos x * Real.cosh y * dx ^ 6 -
    6 * Real.sin x * Real.sinh y * dx ^ 5 * dy +
    15 * Real.cos x * Real.cosh y * dx ^ 4 * dy ^ 2 +
    20 * Real.sin x * Real.sinh y * dx ^ 3 * dy ^ 3 -
    15 * Real.cos x * Real.cosh y * dx ^ 2 * dy ^ 4 -
    6 * Real.sin x * Real.sinh y * dx * dy ^ 5 +
    Real.cos x * Real.cosh y * dy ^ 6

def factoredForm (x y dx dy : ℝ) : ℝ :=
  -Real.cos x * Real.cosh y *
      (dx ^ 6 - 15 * dx ^ 4 * dy ^ 2 +
        15 * dx ^ 2 * dy ^ 4 - dy ^ 6) -
    2 * Real.sin x * Real.sinh y * dx * dy *
      (3 * dx ^ 4 - 10 * dx ^ 2 * dy ^ 2 + 3 * dy ^ 4)

private abbrev PathCoeffs := ℝ × ℝ × ℝ × ℝ

private def initialCoeffs : PathCoeffs :=
  (1, 0, 0, 0)

private def advance (dx dy : ℝ) (p : PathCoeffs) : PathCoeffs :=
  (p.2.1 * dx + p.2.2.1 * dy,
    -p.1 * dx + p.2.2.2 * dy,
    p.1 * dy + p.2.2.2 * dx,
    p.2.1 * dy - p.2.2.1 * dx)

private def pathCombo (p : PathCoeffs) (x y dx dy s : ℝ) : ℝ :=
  p.1 * (Real.cos (x + s * dx) * Real.cosh (y + s * dy)) +
    p.2.1 * (Real.sin (x + s * dx) * Real.cosh (y + s * dy)) +
    p.2.2.1 * (Real.cos (x + s * dx) * Real.sinh (y + s * dy)) +
    p.2.2.2 * (Real.sin (x + s * dx) * Real.sinh (y + s * dy))

private theorem deriv_pathCombo
    (p : PathCoeffs) (x y dx dy : ℝ) :
    deriv (pathCombo p x y dx dy) =
      pathCombo (advance dx dy p) x y dx dy := by
  funext s
  have hx : HasDerivAt (fun t : ℝ => x + t * dx) dx s := by
    convert (hasDerivAt_const s x).add
      ((hasDerivAt_id s).mul_const dx) using 1 <;>
      simp only [Pi.add_apply, id_eq, zero_add, one_mul]
  have hy : HasDerivAt (fun t : ℝ => y + t * dy) dy s := by
    convert (hasDerivAt_const s y).add
      ((hasDerivAt_id s).mul_const dy) using 1 <;>
      simp only [Pi.add_apply, id_eq, zero_add, one_mul]
  have hcos := (Real.hasDerivAt_cos (x + s * dx)).comp s hx
  have hsin := (Real.hasDerivAt_sin (x + s * dx)).comp s hx
  have hcosh := (Real.hasDerivAt_cosh (y + s * dy)).comp s hy
  have hsinh := (Real.hasDerivAt_sinh (y + s * dy)).comp s hy
  have hcc := hcos.mul hcosh
  have hsc := hsin.mul hcosh
  have hcs := hcos.mul hsinh
  have hss := hsin.mul hsinh
  have htotal :=
    ((((hcc.const_mul p.1).add (hsc.const_mul p.2.1)).add
      (hcs.const_mul p.2.2.1)).add (hss.const_mul p.2.2.2))
  convert htotal.deriv using 1 <;>
    simp [pathCombo, advance] <;> ring

private theorem iterDeriv_pathCombo
    (n : ℕ) (p : PathCoeffs) (x y dx dy : ℝ) :
    iterDeriv n (pathCombo p x y dx dy) =
      pathCombo ((advance dx dy)^[n] p) x y dx dy := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
      simp only [iterDeriv, Function.iterate_succ_apply]
      rw [deriv_pathCombo]
      simpa [iterDeriv] using ih (advance dx dy p)

private theorem partialX_as_path (m : ℕ) (a b : ℝ) :
    partialXOrder m u a b =
      pathCombo ((advance 1 0)^[m] initialCoeffs) 0 b 1 0 a := by
  unfold partialXOrder
  have hfun :
      (fun t : ℝ => u t b) = pathCombo initialCoeffs 0 b 1 0 := by
    funext t
    simp [u, pathCombo, initialCoeffs]
  rw [hfun, iterDeriv_pathCombo]

private def atX (p : PathCoeffs) (x : ℝ) : PathCoeffs :=
  (p.1 * Real.cos x + p.2.1 * Real.sin x,
    0,
    p.2.2.1 * Real.cos x + p.2.2.2 * Real.sin x,
    0)

private theorem mixed_as_path (m n : ℕ) (x y : ℝ) :
    mixedOrder m n u x y =
      pathCombo
        ((advance 0 1)^[n]
          (atX ((advance 1 0)^[m] initialCoeffs) x))
        0 0 0 1 y := by
  unfold mixedOrder partialYOrder
  have hfun :
      (fun t : ℝ => partialXOrder m u x t) =
        pathCombo
          (atX ((advance 1 0)^[m] initialCoeffs) x)
          0 0 0 1 := by
    funext t
    rw [partialX_as_path]
    simp [pathCombo, atX]
    ring
  rw [hfun, iterDeriv_pathCombo]

private theorem directional_expansion (x y dx dy : ℝ) :
    sixthDirectional x y dx dy = expandedForm x y dx dy := by
  unfold sixthDirectional
  have hfun :
      (fun s : ℝ => u (x + s * dx) (y + s * dy)) =
        pathCombo initialCoeffs x y dx dy := by
    funext s
    simp [u, pathCombo, initialCoeffs]
  rw [hfun, iterDeriv_pathCombo]
  norm_num [Function.iterate_succ_apply, advance, initialCoeffs,
    pathCombo, expandedForm] <;> ring

private theorem operator_expansion (x y dx dy : ℝ) :
    sixthOperator x y dx dy = expandedForm x y dx dy := by
  norm_num [sixthOperator, mixed_as_path, Function.iterate_succ_apply,
    advance, atX, initialCoeffs, pathCombo, expandedForm,
    Finset.sum_range_succ, Nat.choose] <;> ring

theorem gap1 (x y dx dy : ℝ) :
    sixthDirectional x y dx dy = sixthOperator x y dx dy := by
  calc
    sixthDirectional x y dx dy = expandedForm x y dx dy :=
      directional_expansion x y dx dy
    _ = sixthOperator x y dx dy :=
      (operator_expansion x y dx dy).symm

theorem gap2 (x y dx dy : ℝ) :
    sixthOperator x y dx dy = expandedForm x y dx dy := by
  exact operator_expansion x y dx dy

theorem gap3 (x y dx dy : ℝ) :
    sixthDirectional x y dx dy = expandedForm x y dx dy := by
  exact directional_expansion x y dx dy

theorem gap4 (x y dx dy : ℝ) :
    sixthDirectional x y dx dy = factoredForm x y dx dy := by
  rw [directional_expansion]
  unfold expandedForm factoredForm
  ring

end

end ProofGap.Exercise3272
