import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace ProofGap.Exercise1388

noncomputable section

open Filter

def f (x : ℝ) : ℝ := Real.sqrt x
def polynomial (x : ℝ) : ℝ :=
  1 + (1 / 2 : ℝ) * (x - 1) - (1 / 8 : ℝ) * (x - 1) ^ 2
def iterDeriv (n : ℕ) (g : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) g

def AgreesToOrderAt (g p : ℝ → ℝ) (a : ℝ) (n : ℕ) : Prop :=
  Asymptotics.IsLittleO (nhds a) (fun x => g x - p x)
    (fun x => (x - a) ^ n)

theorem gap1 (x : ℝ) (hx : 0 < x) :
    iterDeriv 1 f x = 1 / (2 * Real.sqrt x) := by
  simpa [iterDeriv, f] using (Real.hasDerivAt_sqrt hx.ne').deriv

theorem gap2 (x : ℝ) (hx : 0 < x) :
    iterDeriv 2 f x = -(1 / (4 * x * Real.sqrt x)) := by
  have heq :
      deriv f =ᶠ[nhds x] fun y => 1 / (2 * Real.sqrt y) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (Real.hasDerivAt_sqrt hy.ne').deriv
  have hsqrt : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hderiv :
      HasDerivAt (fun y : ℝ => 1 / (2 * Real.sqrt y))
        (-(1 / (4 * x * Real.sqrt x))) x := by
    convert (hasDerivAt_const x (1 : ℝ)).div
      ((Real.hasDerivAt_sqrt hx.ne').const_mul 2) (by positivity) using 1 <;>
      field_simp <;> nlinarith [Real.sq_sqrt hx.le]
  rw [show iterDeriv 2 f x = deriv (deriv f) x by rfl, heq.deriv_eq]
  exact hderiv.deriv

theorem gap3 :
    f 1 = 1 := by
  simp [f]

theorem gap4 :
    iterDeriv 1 f 1 = (1 / 2 : ℝ) := by
  simpa using gap1 1 (by norm_num)

theorem gap5 :
    iterDeriv 2 f 1 = -(1 / 4 : ℝ) := by
  simpa using gap2 1 (by norm_num)

theorem gap6 :
    AgreesToOrderAt f polynomial 1 2 := by
  let q : ℝ → ℝ := fun x =>
    ((Real.sqrt x - 1) * (Real.sqrt x + 3)) /
      (8 * (Real.sqrt x + 1) ^ 2)
  have hq0 : Tendsto q (nhds 1) (nhds 0) := by
    have hc : ContinuousAt q 1 := by
      dsimp [q]
      fun_prop (disch := norm_num)
    change Tendsto q (nhds 1) (nhds (q 1)) at hc
    convert hc using 1 <;> norm_num [q]
  have hqo :
      Asymptotics.IsLittleO (nhds 1) q (fun _ : ℝ => (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).2 hq0
  have hprod :
      Asymptotics.IsLittleO (nhds 1)
        (fun x => q x * (x - 1) ^ 2) (fun x : ℝ => (x - 1) ^ 2) := by
    simpa using hqo.mul_isBigO
      (Asymptotics.isBigO_refl (fun x : ℝ => (x - 1) ^ 2) (nhds 1))
  refine hprod.congr' ?_ (Eventually.of_forall (fun x => rfl))
  filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
  dsimp [f, polynomial, q]
  have hs : Real.sqrt x + 1 ≠ 0 := by positivity
  field_simp
  nlinarith [Real.sq_sqrt hx.le]

end

end ProofGap.Exercise1388
