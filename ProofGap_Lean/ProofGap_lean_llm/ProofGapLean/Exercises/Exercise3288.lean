import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3288

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def nthDifferential (n : ℕ) (u : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  iterDeriv n (fun s => u (x + s * dx) (y + s * dy)) 0

private theorem exercise3288_affine_deriv_scale
    (g : ℝ → ℝ) (a b c z : ℝ) :
    deriv (fun s : ℝ => g (a + s * b) * c) z =
      deriv g (a + z * b) * b * c := by
  by_cases hb : b = 0
  · subst b
    simpa using (hasDerivAt_const z (g a * c)).deriv
  · by_cases hc : c = 0
    · subst c
      simpa using (hasDerivAt_const z (0 : ℝ)).deriv
    · by_cases hg : DifferentiableAt ℝ g (a + z * b)
      · have haffine : HasDerivAt (fun s : ℝ => a + s * b) b z := by
          have hmul : HasDerivAt (fun s : ℝ => s * b) b z := by
            simpa using (hasDerivAt_id z).mul_const b
          have hadd :
              HasDerivAt
                ((fun _ : ℝ => a) + (fun s : ℝ => s * b))
                (0 + b) z :=
            (hasDerivAt_const z a).add hmul
          rw [zero_add] at hadd
          change HasDerivAt
            ((fun _ : ℝ => a) + (fun s : ℝ => s * b)) b z
          exact hadd
        have hcomp :
            HasDerivAt (fun s : ℝ => g (a + s * b))
              (deriv g (a + z * b) * b) z := by
          simpa [Function.comp_def, smul_eq_mul, mul_comm] using
            (hg.hasDerivAt.comp z haffine)
        exact (hcomp.mul_const c).deriv
      · have hnot :
            ¬ DifferentiableAt ℝ
              (fun s : ℝ => g (a + s * b) * c) z := by
          intro hh
          apply hg
          let q : ℝ → ℝ := fun r => (r - a) * b⁻¹
          have hq : DifferentiableAt ℝ q (a + z * b) := by
            simpa [q] using
              ((((hasDerivAt_id (a + z * b)).sub_const a).mul_const b⁻¹).differentiableAt)
          have hqp : q (a + z * b) = z := by
            dsimp [q]
            field_simp [hb] <;> ring
          have hhq :
              DifferentiableAt ℝ
                (fun s : ℝ => g (a + s * b) * c)
                (q (a + z * b)) := by
            rw [hqp]
            exact hh
          have hcomp :
              DifferentiableAt ℝ
                ((fun s : ℝ => g (a + s * b) * c) ∘ q)
                (a + z * b) :=
            hhq.comp (a + z * b) hq
          have hrecover :
              DifferentiableAt ℝ
                (fun r : ℝ =>
                  (((fun s : ℝ => g (a + s * b) * c) ∘ q) r) * c⁻¹)
                (a + z * b) := by
            simpa using
              (hcomp.hasDerivAt.mul_const c⁻¹).differentiableAt
          have hfun :
              (fun r : ℝ =>
                (((fun s : ℝ => g (a + s * b) * c) ∘ q) r) * c⁻¹) =
                g := by
            funext r
            have harg : a + q r * b = r := by
              dsimp [q]
              field_simp [hb] <;> ring
            simp only [Function.comp_apply]
            rw [harg]
            field_simp [hc] <;> ring
          rw [hfun] at hrecover
          exact hrecover
        rw [deriv_zero_of_not_differentiableAt hnot,
          deriv_zero_of_not_differentiableAt hg]
        simp

theorem gap1 (u t : ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y, u x y = f (t x y))
    (ht : ∀ x y, t x y = x + y)
    (hf : Differentiable ℝ f) (x y dx dy : ℝ) :
    nthDifferential 1 u x y dx dy =
      deriv f (t x y) * (dx + dy) := by
  have hpath :
      (fun s : ℝ => u (x + s * dx) (y + s * dy)) =
        (fun s : ℝ => f (t x y + s * (dx + dy))) := by
    funext s
    simp only [hu, ht]
    congr 1
    ring
  change deriv (fun s : ℝ => u (x + s * dx) (y + s * dy)) 0 =
    deriv f (t x y) * (dx + dy)
  rw [hpath]
  simpa using
    (exercise3288_affine_deriv_scale f (t x y) (dx + dy) 1 0)

theorem gap2 (u t : ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y, u x y = f (t x y))
    (ht : ∀ x y, t x y = x + y)
    (hf : ContDiff ℝ 2 f) (x y dx dy : ℝ) :
    nthDifferential 2 u x y dx dy =
      iterDeriv 2 f (t x y) * (dx + dy) ^ 2 := by
  have hpath :
      (fun s : ℝ => u (x + s * dx) (y + s * dy)) =
        (fun s : ℝ => f (t x y + s * (dx + dy))) := by
    funext s
    simp only [hu, ht]
    congr 1
    ring
  have hfirst :
      deriv (fun s : ℝ => f (t x y + s * (dx + dy))) =
        (fun s : ℝ =>
          deriv f (t x y + s * (dx + dy)) * (dx + dy)) := by
    funext s
    simpa using
      (exercise3288_affine_deriv_scale f (t x y) (dx + dy) 1 s)
  change deriv (deriv (fun s : ℝ => u (x + s * dx) (y + s * dy))) 0 =
    deriv (deriv f) (t x y) * (dx + dy) ^ 2
  rw [hpath, hfirst]
  simpa [pow_two, mul_assoc] using
    (exercise3288_affine_deriv_scale (deriv f) (t x y)
      (dx + dy) (dx + dy) 0)

end

end ProofGap.Exercise3288
