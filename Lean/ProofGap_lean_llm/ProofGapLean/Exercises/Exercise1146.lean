import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Neighborhoods
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1146

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def CircleNear (y : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ z : ℝ, |z - x| < ε → z ^ 2 + y z ^ 2 = 25

private theorem circleNear_eventually {y : ℝ → ℝ} {x : ℝ}
    (hcircle : CircleNear y x) :
    ∀ᶠ z in nhds x, CircleNear y z := by
  rcases hcircle with ⟨ε, hε, hc⟩
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

theorem gap1 (y : ℝ → ℝ) (x : ℝ) (hy : y x ≠ 0)
    (hd : DifferentiableAt ℝ y x)
    (hcircle : CircleNear y x) :
    deriv y x = -x / y x := by
  rcases hcircle with ⟨ε, hε, hcircle⟩
  have heq :
      (fun z : ℝ => z ^ 2 + y z ^ 2) =ᶠ[nhds x] (fun _ : ℝ => 25) := by
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨ε, hε, ?_⟩
    intro z hz
    apply hcircle z
    simpa [Real.dist_eq] using hz
  have hcalc : HasDerivAt (fun z : ℝ => z ^ 2 + y z ^ 2)
      (2 * x + 2 * y x * deriv y x) x := by
    have hx := (hasDerivAt_id x).pow 2
    have hy' := hd.hasDerivAt.pow 2
    convert hx.add hy' using 1 <;> simp [id] <;> ring
  have hzero : deriv (fun z : ℝ => z ^ 2 + y z ^ 2) x = 0 := by
    rw [heq.deriv_eq]
    simp
  apply (eq_div_iff hy).2
  nlinarith [hcalc.deriv, hzero]

theorem gap2 (y : ℝ → ℝ) (x : ℝ) (hy : y x ≠ 0)
    (hsmooth : ContDiffAt ℝ 2 y x) (hcircle : CircleNear y x) :
    nthDeriv 2 y x =
      -(y x - x * deriv y x) / y x ^ 2 := by
  have hderiv :
      deriv y =ᶠ[nhds x] (fun z : ℝ => -z / y z) := by
    filter_upwards [circleNear_eventually hcircle,
      hsmooth.eventually (by decide),
      hsmooth.continuousAt.eventually_ne hy] with z hcz hsz hyz
    exact gap1 y z hyz (hsz.differentiableAt (by decide)) hcz
  have hd : DifferentiableAt ℝ y x :=
    hsmooth.differentiableAt (by decide)
  have hnum : HasDerivAt (fun z : ℝ => -z) (-1) x := by
    simpa using (hasDerivAt_id x).neg
  have hquot := hnum.div hd.hasDerivAt hy
  change deriv (deriv y) x = -(y x - x * deriv y x) / y x ^ 2
  calc
    deriv (deriv y) x = deriv (fun z : ℝ => -z / y z) x := hderiv.deriv_eq
    _ = ((-1) * y x - (-x) * deriv y x) / y x ^ 2 := hquot.deriv
    _ = -(y x - x * deriv y x) / y x ^ 2 := by ring

theorem gap3 (y : ℝ → ℝ) (x : ℝ) (hy : y x ≠ 0)
    (h1 : deriv y x = -x / y x) :
    -(y x - x * deriv y x) / y x ^ 2 =
      -(y x + x ^ 2 / y x) / y x ^ 2 := by
  rw [h1]
  ring

theorem gap4 (y : ℝ → ℝ) (x : ℝ) (hy : y x ≠ 0) :
    -(y x + x ^ 2 / y x) / y x ^ 2 =
      -(x ^ 2 + y x ^ 2) / y x ^ 3 := by
  field_simp [hy]
  ring

theorem gap5 (y : ℝ → ℝ) (x : ℝ) (hy : y x ≠ 0)
    (hcircle : x ^ 2 + y x ^ 2 = 25) :
    -(x ^ 2 + y x ^ 2) / y x ^ 3 = -25 / y x ^ 3 := by
  rw [hcircle]

theorem gap6 (y : ℝ → ℝ) (x : ℝ) (hy : y x ≠ 0) :
    ContDiffAt ℝ 2 y x → CircleNear y x →
      nthDeriv 2 y x = -25 / y x ^ 3 := by
  intro hsmooth hcircle
  have hpoint : x ^ 2 + y x ^ 2 = 25 := by
    rcases hcircle with ⟨ε, hε, hc⟩
    exact hc x (by simpa using hε)
  have hd : DifferentiableAt ℝ y x :=
    hsmooth.differentiableAt (by decide)
  have h1 : deriv y x = -x / y x :=
    gap1 y x hy hd hcircle
  calc
    nthDeriv 2 y x = -(y x - x * deriv y x) / y x ^ 2 :=
      gap2 y x hy hsmooth hcircle
    _ = -(y x + x ^ 2 / y x) / y x ^ 2 := gap3 y x hy h1
    _ = -(x ^ 2 + y x ^ 2) / y x ^ 3 := gap4 y x hy
    _ = -25 / y x ^ 3 := gap5 y x hy hpoint

theorem gap7 (y : ℝ → ℝ) (x : ℝ) (hy : y x ≠ 0)
    (hsmooth : ContDiffAt ℝ 3 y x) (hcircle : CircleNear y x) :
    nthDeriv 3 y x = 75 * deriv y x / y x ^ 4 := by
  have hsmooth2 : ContDiffAt ℝ 2 y x :=
    hsmooth.of_le (by norm_num)
  have hsecond :
      nthDeriv 2 y =ᶠ[nhds x] (fun z : ℝ => -25 / y z ^ 3) := by
    filter_upwards [circleNear_eventually hcircle,
      hsmooth2.eventually (by decide),
      hsmooth.continuousAt.eventually_ne hy] with z hcz hsz hyz
    exact gap6 y z hyz hsz hcz
  have hd : DifferentiableAt ℝ y x :=
    hsmooth.differentiableAt (by decide)
  have hden : HasDerivAt (fun z : ℝ => y z ^ 3)
      (3 * y x ^ 2 * deriv y x) x := by
    convert hd.hasDerivAt.pow 3 using 1 <;> simp <;> ring
  have hnum : HasDerivAt (fun _ : ℝ => (-25 : ℝ)) 0 x :=
    hasDerivAt_const x (-25 : ℝ)
  have hquot := hnum.div hden (pow_ne_zero 3 hy)
  change deriv (nthDeriv 2 y) x = 75 * deriv y x / y x ^ 4
  calc
    deriv (nthDeriv 2 y) x = deriv (fun z : ℝ => -25 / y z ^ 3) x :=
      hsecond.deriv_eq
    _ = (0 * y x ^ 3 - (-25) * (3 * y x ^ 2 * deriv y x)) /
          (y x ^ 3) ^ 2 := hquot.deriv
    _ = 75 * deriv y x / y x ^ 4 := by
      field_simp [hy]
      ring

theorem gap8 (y : ℝ → ℝ) (x : ℝ) (hy : y x ≠ 0)
    (h1 : deriv y x = -x / y x) :
    75 * deriv y x / y x ^ 4 = -(75 * x) / y x ^ 5 := by
  rw [h1]
  field_simp [hy]

theorem gap9 (y : ℝ → ℝ) (x : ℝ) (hy : y x ≠ 0)
    (hsmooth : ContDiffAt ℝ 3 y x) (hcircle : CircleNear y x) :
    nthDeriv 3 y x = -(75 * x) / y x ^ 5 := by
  have hd : DifferentiableAt ℝ y x :=
    hsmooth.differentiableAt (by decide)
  have h1 : deriv y x = -x / y x :=
    gap1 y x hy hd hcircle
  calc
    nthDeriv 3 y x = 75 * deriv y x / y x ^ 4 :=
      gap7 y x hy hsmooth hcircle
    _ = -(75 * x) / y x ^ 5 := gap8 y x hy h1

theorem gap10 (y : ℝ → ℝ) (x : ℝ) (hx : x = 3) (hy : y x = 4)
    (hsmooth : ContDiffAt ℝ 1 y x) (hcircle : CircleNear y x) :
    deriv y x = -(3 : ℝ) / 4 := by
  have hy0 : y x ≠ 0 := by
    rw [hy]
    norm_num
  have hd : DifferentiableAt ℝ y x :=
    hsmooth.differentiableAt (by decide)
  calc
    deriv y x = -x / y x := gap1 y x hy0 hd hcircle
    _ = -(3 : ℝ) / 4 := by rw [hy, hx]

theorem gap11 (y : ℝ → ℝ) (x : ℝ) (hx : x = 3) (hy : y x = 4)
    (hsmooth : ContDiffAt ℝ 2 y x) (hcircle : CircleNear y x) :
    nthDeriv 2 y x = -(25 : ℝ) / 64 := by
  have hy0 : y x ≠ 0 := by
    rw [hy]
    norm_num
  calc
    nthDeriv 2 y x = -25 / y x ^ 3 := gap6 y x hy0 hsmooth hcircle
    _ = -(25 : ℝ) / 64 := by
      rw [hy]
      norm_num

theorem gap12 (y : ℝ → ℝ) (x : ℝ) (hx : x = 3) (hy : y x = 4)
    (hsmooth : ContDiffAt ℝ 3 y x) (hcircle : CircleNear y x) :
    nthDeriv 3 y x = -(225 : ℝ) / 1024 := by
  have hy0 : y x ≠ 0 := by
    rw [hy]
    norm_num
  calc
    nthDeriv 3 y x = -(75 * x) / y x ^ 5 :=
      gap9 y x hy0 hsmooth hcircle
    _ = -(225 : ℝ) / 1024 := by
      rw [hy, hx]
      norm_num

end

end ProofGap.Exercise1146
