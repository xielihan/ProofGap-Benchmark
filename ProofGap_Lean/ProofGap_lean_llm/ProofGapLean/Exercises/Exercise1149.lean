import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1149

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def ImplicitNear (y : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ z : ℝ, |z - x| < ε →
      y z ^ 2 + 2 * Real.log (y z) = z ^ 4

private theorem implicitNear_eventually {y : ℝ → ℝ} {x : ℝ}
    (hcurve : ImplicitNear y x) :
    ∀ᶠ z in nhds x, ImplicitNear y z := by
  rcases hcurve with ⟨ε, hε, hc⟩
  have hnear : ∀ᶠ z : ℝ in nhds x, |z - x| < ε / 2 := by
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨ε / 2, by linarith, ?_⟩
    intro z hz
    simpa [Real.dist_eq] using hz
  filter_upwards [hnear] with z hz
  refine ⟨ε / 2, by linarith, ?_⟩
  intro w hw
  apply hc w
  rw [show w - x = (w - z) + (z - x) by ring]
  exact lt_of_le_of_lt (abs_add_le (w - z) (z - x)) (by linarith)

theorem gap1 (y : ℝ → ℝ) (x : ℝ) (hy : 0 < y x)
    (hsmooth : ContDiffAt ℝ 1 y x) (hcurve : ImplicitNear y x) :
    2 * y x * deriv y x + 2 * deriv y x / y x = 4 * x ^ 3 := by
  rcases hcurve with ⟨ε, hε, hcurve⟩
  have heq :
      (fun z : ℝ => y z ^ 2 + 2 * Real.log (y z)) =ᶠ[nhds x]
        (fun z : ℝ => z ^ 4) := by
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨ε, hε, ?_⟩
    intro z hz
    apply hcurve z
    simpa [Real.dist_eq] using hz
  have hd : DifferentiableAt ℝ y x :=
    hsmooth.differentiableAt (by decide)
  have hsq :
      HasDerivAt (fun z : ℝ => y z ^ 2) (2 * y x * deriv y x) x := by
    convert hd.hasDerivAt.pow 2 using 1 <;> simp <;> ring
  have hlog :
      HasDerivAt (fun z : ℝ => Real.log (y z))
        ((1 / y x) * deriv y x) x := by
    simpa only [Function.comp_def, one_div] using
      (Real.hasDerivAt_log hy.ne').comp x hd.hasDerivAt
  have hlhs :
      HasDerivAt (fun z : ℝ => y z ^ 2 + 2 * Real.log (y z))
        (2 * y x * deriv y x + 2 * deriv y x / y x) x := by
    convert hsq.add (hlog.const_mul 2) using 1 <;> ring
  have hrhs :
      HasDerivAt (fun z : ℝ => z ^ 4) (4 * x ^ 3) x := by
    convert (hasDerivAt_id x).pow 4 using 1 <;> simp <;> ring
  calc
    2 * y x * deriv y x + 2 * deriv y x / y x =
        deriv (fun z : ℝ => y z ^ 2 + 2 * Real.log (y z)) x :=
      hlhs.deriv.symm
    _ = deriv (fun z : ℝ => z ^ 4) x := heq.deriv_eq
    _ = 4 * x ^ 3 := hrhs.deriv

theorem gap2 (y : ℝ → ℝ) (x : ℝ) (hy : 0 < y x)
    (hsmooth : ContDiffAt ℝ 2 y x) (hcurve : ImplicitNear y x) :
    2 * deriv y x ^ 2 + 2 * y x * nthDeriv 2 y x +
        2 * nthDeriv 2 y x / y x -
        2 * deriv y x ^ 2 / y x ^ 2 =
      12 * x ^ 2 := by
  have hsmooth1 : ContDiffAt ℝ 1 y x :=
    hsmooth.of_le (by norm_num)
  have hypos : ∀ᶠ z in nhds x, 0 < y z :=
    hsmooth.continuousAt.eventually (Ioi_mem_nhds hy)
  have heq :
      (fun z : ℝ =>
        2 * y z * deriv y z + 2 * deriv y z / y z) =ᶠ[nhds x]
        (fun z : ℝ => 4 * z ^ 3) := by
    filter_upwards [implicitNear_eventually hcurve,
      hsmooth1.eventually (by decide), hypos] with z hcz hsz hyz
    exact gap1 y z hyz hsz hcz
  have hd : DifferentiableAt ℝ y x :=
    hsmooth.differentiableAt (by decide)
  have hdySmooth : ContDiffAt ℝ 1 (deriv y) x :=
    hsmooth.derivWithin (m := 1) (by norm_num)
  have hdy : DifferentiableAt ℝ (deriv y) x :=
    hdySmooth.differentiableAt (by decide)
  have hfirst :
      HasDerivAt (fun z : ℝ => 2 * y z * deriv y z)
        (2 * deriv y x ^ 2 + 2 * y x * nthDeriv 2 y x) x := by
    change HasDerivAt (fun z : ℝ => 2 * y z * deriv y z)
      (2 * deriv y x ^ 2 + 2 * y x * deriv (deriv y) x) x
    convert (hd.hasDerivAt.mul hdy.hasDerivAt).const_mul 2 using 1
    · funext z
      simp only [Pi.mul_apply]
      ring
    · ring
  have hsecond :
      HasDerivAt (fun z : ℝ => 2 * deriv y z / y z)
        (2 * nthDeriv 2 y x / y x -
          2 * deriv y x ^ 2 / y x ^ 2) x := by
    change HasDerivAt (fun z : ℝ => 2 * deriv y z / y z)
      (2 * deriv (deriv y) x / y x -
        2 * deriv y x ^ 2 / y x ^ 2) x
    have hquot :=
      hdy.hasDerivAt.div hd.hasDerivAt hy.ne'
    convert hquot.const_mul 2 using 1
    · funext z
      simp only [Pi.div_apply, Pi.mul_apply]
      ring
    · field_simp [hy.ne']
  have hlhs :
      HasDerivAt
        (fun z : ℝ => 2 * y z * deriv y z + 2 * deriv y z / y z)
        (2 * deriv y x ^ 2 + 2 * y x * nthDeriv 2 y x +
          2 * nthDeriv 2 y x / y x -
          2 * deriv y x ^ 2 / y x ^ 2) x := by
    convert hfirst.add hsecond using 1 <;> ring
  have hrhs :
      HasDerivAt (fun z : ℝ => 4 * z ^ 3) (12 * x ^ 2) x := by
    convert ((hasDerivAt_id x).pow 3).const_mul 4 using 1 <;>
      simp <;> ring
  calc
    2 * deriv y x ^ 2 + 2 * y x * nthDeriv 2 y x +
          2 * nthDeriv 2 y x / y x -
          2 * deriv y x ^ 2 / y x ^ 2 =
        deriv
          (fun z : ℝ =>
            2 * y z * deriv y z + 2 * deriv y z / y z) x :=
      hlhs.deriv.symm
    _ = deriv (fun z : ℝ => 4 * z ^ 3) x := heq.deriv_eq
    _ = 12 * x ^ 2 := hrhs.deriv

theorem gap3 (y : ℝ → ℝ) (x : ℝ) (hy : 0 < y x)
    (hsmooth : ContDiffAt ℝ 1 y x) (hcurve : ImplicitNear y x) :
    deriv y x = 2 * x ^ 3 * y x / (1 + y x ^ 2) := by
  have h := gap1 y x hy hsmooth hcurve
  have hden : 1 + y x ^ 2 ≠ 0 := by positivity
  apply (eq_div_iff hden).2
  field_simp [hy.ne'] at h
  nlinarith

theorem gap4 (y : ℝ → ℝ) (x : ℝ) (hy : 0 < y x)
    (hsmooth : ContDiffAt ℝ 2 y x) (hcurve : ImplicitNear y x) :
    nthDeriv 2 y x =
      2 * x ^ 2 * y x / (1 + y x ^ 2) ^ 3 *
        (3 * (1 + y x ^ 2) ^ 2 + 2 * x ^ 4 * (1 - y x ^ 2)) := by
  have hsmooth1 : ContDiffAt ℝ 1 y x :=
    hsmooth.of_le (by norm_num)
  have h1 := gap3 y x hy hsmooth1 hcurve
  have h2 := gap2 y x hy hsmooth hcurve
  have hden : 1 + y x ^ 2 ≠ 0 := by positivity
  rw [h1] at h2
  field_simp [hy.ne', hden] at h2 ⊢
  ring_nf at h2 ⊢
  nlinarith [h2]

end

end ProofGap.Exercise1149
