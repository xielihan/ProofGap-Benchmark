import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1147

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def ParabolaNear (y : ℝ → ℝ) (p x : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ z : ℝ, |z - x| < ε → y z ^ 2 = 2 * p * z

private theorem parabolaNear_eventually {y : ℝ → ℝ} {p x : ℝ}
    (hcurve : ParabolaNear y p x) :
    ∀ᶠ z in nhds x, ParabolaNear y p z := by
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

theorem gap1 (y : ℝ → ℝ) (p x : ℝ) (hy : y x ≠ 0)
    (hd : DifferentiableAt ℝ y x)
    (hcurve : ParabolaNear y p x) :
    deriv y x = p / y x := by
  rcases hcurve with ⟨ε, hε, hcurve⟩
  have heq :
      (fun z : ℝ => y z ^ 2) =ᶠ[nhds x] (fun z : ℝ => 2 * p * z) := by
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨ε, hε, ?_⟩
    intro z hz
    apply hcurve z
    simpa [Real.dist_eq] using hz
  have hlhs :
      HasDerivAt (fun z : ℝ => y z ^ 2) (2 * y x * deriv y x) x := by
    convert hd.hasDerivAt.pow 2 using 1 <;> simp <;> ring
  have hrhs :
      HasDerivAt (fun z : ℝ => 2 * p * z) (2 * p) x := by
    simpa using (hasDerivAt_id x).const_mul (2 * p)
  have hderiv : 2 * y x * deriv y x = 2 * p := by
    calc
      2 * y x * deriv y x =
          deriv (fun z : ℝ => y z ^ 2) x := hlhs.deriv.symm
      _ = deriv (fun z : ℝ => 2 * p * z) x := heq.deriv_eq
      _ = 2 * p := hrhs.deriv
  apply (eq_div_iff hy).2
  nlinarith

theorem gap2 (y : ℝ → ℝ) (p x : ℝ) (hy : y x ≠ 0)
    (hsmooth : ContDiffAt ℝ 2 y x) (hcurve : ParabolaNear y p x) :
    nthDeriv 2 y x = -(p / y x ^ 2) * deriv y x := by
  have hderiv :
      deriv y =ᶠ[nhds x] (fun z : ℝ => p / y z) := by
    filter_upwards [parabolaNear_eventually hcurve,
      hsmooth.eventually (by decide),
      hsmooth.continuousAt.eventually_ne hy] with z hcz hsz hyz
    exact gap1 y p z hyz (hsz.differentiableAt (by decide)) hcz
  have hd : DifferentiableAt ℝ y x :=
    hsmooth.differentiableAt (by decide)
  have hnum : HasDerivAt (fun _ : ℝ => p) 0 x :=
    hasDerivAt_const x p
  have hquot := hnum.div hd.hasDerivAt hy
  change deriv (deriv y) x = -(p / y x ^ 2) * deriv y x
  calc
    deriv (deriv y) x = deriv (fun z : ℝ => p / y z) x :=
      hderiv.deriv_eq
    _ = (0 * y x - p * deriv y x) / y x ^ 2 := hquot.deriv
    _ = -(p / y x ^ 2) * deriv y x := by ring

theorem gap3 (y : ℝ → ℝ) (p x : ℝ) (hy : y x ≠ 0)
    (h1 : deriv y x = p / y x) :
    -(p / y x ^ 2) * deriv y x = -(p ^ 2) / y x ^ 3 := by
  rw [h1]
  field_simp [hy]

theorem gap4 (y : ℝ → ℝ) (p x : ℝ) (hy : y x ≠ 0)
    (hsmooth : ContDiffAt ℝ 2 y x) (hcurve : ParabolaNear y p x) :
    nthDeriv 2 y x = -(p ^ 2) / y x ^ 3 := by
  have hd : DifferentiableAt ℝ y x :=
    hsmooth.differentiableAt (by decide)
  have h1 : deriv y x = p / y x :=
    gap1 y p x hy hd hcurve
  calc
    nthDeriv 2 y x = -(p / y x ^ 2) * deriv y x :=
      gap2 y p x hy hsmooth hcurve
    _ = -(p ^ 2) / y x ^ 3 := gap3 y p x hy h1

theorem gap5 (y : ℝ → ℝ) (p x : ℝ) (hy : y x ≠ 0)
    (hsmooth : ContDiffAt ℝ 3 y x) (hcurve : ParabolaNear y p x) :
    nthDeriv 3 y x = (3 * p ^ 2 / y x ^ 4) * deriv y x := by
  have hsmooth2 : ContDiffAt ℝ 2 y x :=
    hsmooth.of_le (by norm_num)
  have hsecond :
      nthDeriv 2 y =ᶠ[nhds x] (fun z : ℝ => -(p ^ 2) / y z ^ 3) := by
    filter_upwards [parabolaNear_eventually hcurve,
      hsmooth2.eventually (by decide),
      hsmooth.continuousAt.eventually_ne hy] with z hcz hsz hyz
    exact gap4 y p z hyz hsz hcz
  have hd : DifferentiableAt ℝ y x :=
    hsmooth.differentiableAt (by decide)
  have hden : HasDerivAt (fun z : ℝ => y z ^ 3)
      (3 * y x ^ 2 * deriv y x) x := by
    convert hd.hasDerivAt.pow 3 using 1 <;> simp <;> ring
  have hnum : HasDerivAt (fun _ : ℝ => -(p ^ 2)) 0 x :=
    hasDerivAt_const x (-(p ^ 2))
  have hquot := hnum.div hden (pow_ne_zero 3 hy)
  change deriv (nthDeriv 2 y) x =
    (3 * p ^ 2 / y x ^ 4) * deriv y x
  calc
    deriv (nthDeriv 2 y) x =
        deriv (fun z : ℝ => -(p ^ 2) / y z ^ 3) x :=
      hsecond.deriv_eq
    _ = (0 * y x ^ 3 - (-(p ^ 2)) *
          (3 * y x ^ 2 * deriv y x)) / (y x ^ 3) ^ 2 :=
      hquot.deriv
    _ = (3 * p ^ 2 / y x ^ 4) * deriv y x := by
      field_simp [hy]
      ring

theorem gap6 (y : ℝ → ℝ) (p x : ℝ) (hy : y x ≠ 0)
    (h1 : deriv y x = p / y x) :
    (3 * p ^ 2 / y x ^ 4) * deriv y x = 3 * p ^ 3 / y x ^ 5 := by
  rw [h1]
  field_simp [hy]

theorem gap7 (y : ℝ → ℝ) (p x : ℝ) (hy : y x ≠ 0)
    (hsmooth : ContDiffAt ℝ 3 y x) (hcurve : ParabolaNear y p x) :
    nthDeriv 3 y x = 3 * p ^ 3 / y x ^ 5 := by
  have hd : DifferentiableAt ℝ y x :=
    hsmooth.differentiableAt (by decide)
  have h1 : deriv y x = p / y x :=
    gap1 y p x hy hd hcurve
  calc
    nthDeriv 3 y x = (3 * p ^ 2 / y x ^ 4) * deriv y x :=
      gap5 y p x hy hsmooth hcurve
    _ = 3 * p ^ 3 / y x ^ 5 := gap6 y p x hy h1

end

end ProofGap.Exercise1147
