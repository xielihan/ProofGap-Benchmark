import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3233

noncomputable section

def partialX (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => f s y z) x

def partialY (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => f x s z) y

def partialZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => f x y s) z

def Differentiable3 (f : ℝ → ℝ → ℝ → ℝ) : Prop :=
  Differentiable ℝ
    (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2)

def HomogeneousOfDegree (f : ℝ → ℝ → ℝ → ℝ) (n : ℝ) : Prop :=
  ∀ x y z t : ℝ, 0 < t →
    f (t * x) (t * y) (t * z) = Real.rpow t n * f x y z

def admissible (f : ℝ → ℝ → ℝ → ℝ) (n : ℝ) : Prop :=
  Differentiable3 f ∧ HomogeneousOfDegree f n

private theorem differentiable3_along_real_curve
    {f : ℝ → ℝ → ℝ → ℝ} (hf : Differentiable3 f)
    {g : ℝ → ℝ × (ℝ × ℝ)} (hg : Differentiable ℝ g) :
    Differentiable ℝ
      (fun s => f (g s).1 (g s).2.1 (g s).2.2) := by
  intro s
  unfold Differentiable3 at hf
  simpa only [Function.comp_apply] using
    (hf (g s)).comp s (hg s)

private theorem deriv_scale_of_function_eq
    (g h : ℝ → ℝ) (c t x : ℝ)
    (hg : DifferentiableAt ℝ g (t * x))
    (hh : DifferentiableAt ℝ h x)
    (heq : ∀ s : ℝ, g (t * s) = c * h s) :
    t * deriv g (t * x) = c * deriv h x := by
  have hlinear : HasDerivAt (fun s : ℝ => t * s) t x := by
    simpa [mul_comm] using ((hasDerivAt_id x).const_mul t)
  have hmap :
      Filter.Tendsto
        (Prod.map (fun s : ℝ => t * s) (fun s : ℝ => t * s))
        (nhds x ×ˢ pure x)
        (nhds (t * x) ×ˢ pure (t * x)) := by
    exact Filter.Tendsto.prodMap hlinear.continuousAt (by simp)
  have hclm :
      (ContinuousLinearMap.toSpanSingleton ℝ (deriv g (t * x))).comp
          (ContinuousLinearMap.toSpanSingleton ℝ t) =
        ContinuousLinearMap.toSpanSingleton ℝ
          (t * deriv g (t * x)) := by
    ext u <;> simp [mul_assoc]
  have hraw := hg.hasDerivAt.comp hlinear hmap
  rw [hclm] at hraw
  have hleft :
      HasDerivAt (fun s : ℝ => g (t * s))
        (t * deriv g (t * x)) x := by
    simpa only [Function.comp_apply] using hraw
  have hright :
      HasDerivAt (fun s : ℝ => c * h s)
        (c * deriv h x) x := by
    simpa [mul_comm] using (hh.hasDerivAt.const_mul c)
  have hfun :
      (fun s : ℝ => g (t * s)) = (fun s : ℝ => c * h s) :=
    funext heq
  calc
    t * deriv g (t * x) = deriv (fun s : ℝ => g (t * s)) x :=
      hleft.deriv.symm
    _ = deriv (fun s : ℝ => c * h s) x :=
      congrArg (fun k : ℝ → ℝ => deriv k x) hfun
    _ = c * deriv h x := hright.deriv

private theorem rpow_eq_mul_rpow_sub_one (t n : ℝ) (ht : 0 < t) :
    Real.rpow t n = t * Real.rpow t (n - 1) := by
  calc
    Real.rpow t n = Real.exp (Real.log t * n) :=
      Real.rpow_def_of_pos ht n
    _ = Real.exp (Real.log t + Real.log t * (n - 1)) := by
      congr 1 <;> ring
    _ = Real.exp (Real.log t) * Real.exp (Real.log t * (n - 1)) := by
      rw [Real.exp_add]
    _ = t * Real.exp (Real.log t * (n - 1)) := by
      rw [Real.exp_log ht]
    _ = t * Real.rpow t (n - 1) :=
      congrArg (fun u : ℝ => t * u)
        (Real.rpow_def_of_pos ht (n - 1)).symm

theorem gap1 :
    ∀ (f : ℝ → ℝ → ℝ → ℝ) (n t x y z : ℝ),
      admissible f n → 0 < t →
        t * partialX f (t * x) (t * y) (t * z) =
          Real.rpow t n * partialX f x y z := by
  intro f n t x y z hf ht
  rcases hf with ⟨hdf, hhom⟩
  have hg : Differentiable ℝ (fun s : ℝ => f s (t * y) (t * z)) := by
    simpa using
      (differentiable3_along_real_curve
        (g := fun s : ℝ => (s, (t * y, t * z))) hdf
        (by fun_prop))
  have hh : Differentiable ℝ (fun s : ℝ => f s y z) := by
    simpa using
      (differentiable3_along_real_curve
        (g := fun s : ℝ => (s, (y, z))) hdf
        (by fun_prop))
  unfold partialX
  exact deriv_scale_of_function_eq
    (fun s : ℝ => f s (t * y) (t * z))
    (fun s : ℝ => f s y z) (Real.rpow t n) t x
    (hg (t * x)) (hh x) (fun s => hhom s y z t ht)

theorem gap2 :
    ∀ (f : ℝ → ℝ → ℝ → ℝ) (n t x y z : ℝ),
      admissible f n → 0 < t →
        t * partialY f (t * x) (t * y) (t * z) =
          Real.rpow t n * partialY f x y z := by
  intro f n t x y z hf ht
  rcases hf with ⟨hdf, hhom⟩
  have hg : Differentiable ℝ (fun s : ℝ => f (t * x) s (t * z)) := by
    simpa using
      (differentiable3_along_real_curve
        (g := fun s : ℝ => (t * x, (s, t * z))) hdf
        (by fun_prop))
  have hh : Differentiable ℝ (fun s : ℝ => f x s z) := by
    simpa using
      (differentiable3_along_real_curve
        (g := fun s : ℝ => (x, (s, z))) hdf
        (by fun_prop))
  unfold partialY
  exact deriv_scale_of_function_eq
    (fun s : ℝ => f (t * x) s (t * z))
    (fun s : ℝ => f x s z) (Real.rpow t n) t y
    (hg (t * y)) (hh y) (fun s => hhom x s z t ht)

theorem gap3 :
    ∀ (f : ℝ → ℝ → ℝ → ℝ) (n t x y z : ℝ),
      admissible f n → 0 < t →
        t * partialZ f (t * x) (t * y) (t * z) =
          Real.rpow t n * partialZ f x y z := by
  intro f n t x y z hf ht
  rcases hf with ⟨hdf, hhom⟩
  have hg : Differentiable ℝ (fun s : ℝ => f (t * x) (t * y) s) := by
    simpa using
      (differentiable3_along_real_curve
        (g := fun s : ℝ => (t * x, (t * y, s))) hdf
        (by fun_prop))
  have hh : Differentiable ℝ (fun s : ℝ => f x y s) := by
    simpa using
      (differentiable3_along_real_curve
        (g := fun s : ℝ => (x, (y, s))) hdf
        (by fun_prop))
  unfold partialZ
  exact deriv_scale_of_function_eq
    (fun s : ℝ => f (t * x) (t * y) s)
    (fun s : ℝ => f x y s) (Real.rpow t n) t z
    (hg (t * z)) (hh z) (fun s => hhom x y s t ht)

theorem gap4 :
    ∀ (f : ℝ → ℝ → ℝ → ℝ) (n t x y z : ℝ),
      admissible f n → 0 < t →
        partialX f (t * x) (t * y) (t * z) =
          Real.rpow t (n - 1) * partialX f x y z := by
  intro f n t x y z hf ht
  have hscaled := gap1 f n t x y z hf ht
  rw [rpow_eq_mul_rpow_sub_one t n ht] at hscaled
  have hc :
      t * partialX f (t * x) (t * y) (t * z) =
        t * (Real.rpow t (n - 1) * partialX f x y z) := by
    simpa only [mul_assoc] using hscaled
  exact mul_left_cancel₀ (ne_of_gt ht) hc

theorem gap5 :
    ∀ (f : ℝ → ℝ → ℝ → ℝ) (n t x y z : ℝ),
      admissible f n → 0 < t →
        partialY f (t * x) (t * y) (t * z) =
          Real.rpow t (n - 1) * partialY f x y z := by
  intro f n t x y z hf ht
  have hscaled := gap2 f n t x y z hf ht
  rw [rpow_eq_mul_rpow_sub_one t n ht] at hscaled
  have hc :
      t * partialY f (t * x) (t * y) (t * z) =
        t * (Real.rpow t (n - 1) * partialY f x y z) := by
    simpa only [mul_assoc] using hscaled
  exact mul_left_cancel₀ (ne_of_gt ht) hc

theorem gap6 :
    ∀ (f : ℝ → ℝ → ℝ → ℝ) (n t x y z : ℝ),
      admissible f n → 0 < t →
        partialZ f (t * x) (t * y) (t * z) =
          Real.rpow t (n - 1) * partialZ f x y z := by
  intro f n t x y z hf ht
  have hscaled := gap3 f n t x y z hf ht
  rw [rpow_eq_mul_rpow_sub_one t n ht] at hscaled
  have hc :
      t * partialZ f (t * x) (t * y) (t * z) =
        t * (Real.rpow t (n - 1) * partialZ f x y z) := by
    simpa only [mul_assoc] using hscaled
  exact mul_left_cancel₀ (ne_of_gt ht) hc

theorem gap7 :
    ∀ (f : ℝ → ℝ → ℝ → ℝ) (n x y z t : ℝ),
      admissible f n → 0 < t →
        partialX f (t * x) (t * y) (t * z) =
            Real.rpow t (n - 1) * partialX f x y z ∧
          partialY f (t * x) (t * y) (t * z) =
            Real.rpow t (n - 1) * partialY f x y z ∧
          partialZ f (t * x) (t * y) (t * z) =
            Real.rpow t (n - 1) * partialZ f x y z := by
  intro f n x y z t hf ht
  constructor
  · exact gap4 f n t x y z hf ht
  constructor
  · exact gap5 f n t x y z hf ht
  · exact gap6 f n t x y z hf ht

end

end ProofGap.Exercise3233
