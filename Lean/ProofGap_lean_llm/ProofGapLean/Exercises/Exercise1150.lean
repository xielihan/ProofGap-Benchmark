import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1150

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def SpiralNear (y : ℝ → ℝ) (a x : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ z : ℝ, |z - x| < ε →
      Real.sqrt (z ^ 2 + y z ^ 2) =
        a * Real.exp (Real.arctan (y z / z))

private theorem log_spiral_point (a z w : ℝ) (ha : 0 < a)
    (h : Real.sqrt (z ^ 2 + w ^ 2) =
      a * Real.exp (Real.arctan (w / z))) :
    (1 / 2 : ℝ) * Real.log (z ^ 2 + w ^ 2) =
      Real.log a + Real.arctan (w / z) := by
  have hnonneg : 0 ≤ z ^ 2 + w ^ 2 :=
    add_nonneg (sq_nonneg z) (sq_nonneg w)
  have hlog := congrArg Real.log h
  rw [Real.log_sqrt hnonneg,
    Real.log_mul (ne_of_gt ha) (Real.exp_ne_zero _), Real.log_exp] at hlog
  nlinarith

private theorem spiralNear_eventually (y : ℝ → ℝ) (a x : ℝ)
    (hcurve : SpiralNear y a x) :
    ∀ᶠ z in nhds x, SpiralNear y a z := by
  rcases hcurve with ⟨ε, hε, hlocal⟩
  have hhalf : 0 < ε / 2 := half_pos hε
  have hball : Metric.ball x (ε / 2) ∈ nhds x :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hhalf)
  filter_upwards [hball] with z hz
  have hzx : |z - x| < ε / 2 := by
    simpa [Real.dist_eq] using hz
  refine ⟨ε / 2, hhalf, ?_⟩
  intro w hw
  apply hlocal w
  have heq : w - x = (w - z) + (z - x) := by ring
  rw [heq]
  exact lt_of_le_of_lt (abs_add_le (w - z) (z - x)) (by linarith)

theorem gap1 (y : ℝ → ℝ) (a x : ℝ) (ha : 0 < a)
    (hr : 0 < x ^ 2 + y x ^ 2) (hcurve : SpiralNear y a x) :
    (1 / 2 : ℝ) * Real.log (x ^ 2 + y x ^ 2) =
      Real.log a + Real.arctan (y x / x) := by
  rcases hcurve with ⟨ε, hε, hlocal⟩
  have hpoint := hlocal x (by simpa using hε)
  exact log_spiral_point a x (y x) ha hpoint

theorem gap2 (y : ℝ → ℝ) (a x : ℝ) (ha : 0 < a) (hx : x ≠ 0)
    (hr : 0 < x ^ 2 + y x ^ 2)
    (hsmooth : ContDiffAt ℝ 1 y x) (hcurve : SpiralNear y a x) :
    (x + y x * deriv y x) / (x ^ 2 + y x ^ 2) =
      (x * deriv y x - y x) / (x ^ 2 + y x ^ 2) := by
  have hy : HasDerivAt y (deriv y x) x :=
    (hsmooth.differentiableAt (by norm_num)).hasDerivAt
  have hrad :
      HasDerivAt (fun z : ℝ => z ^ 2 + y z ^ 2)
        (2 * x + 2 * y x * deriv y x) x := by
    convert ((hasDerivAt_id x).pow 2).add (hy.pow 2) using 1 <;>
      norm_num <;> ring
  have hr0 : x ^ 2 + y x ^ 2 ≠ 0 := ne_of_gt hr
  have hleftRaw := (hrad.log hr0).const_mul (1 / 2 : ℝ)
  have hleft :
      HasDerivAt
        (fun z : ℝ => (1 / 2 : ℝ) * Real.log (z ^ 2 + y z ^ 2))
        ((x + y x * deriv y x) / (x ^ 2 + y x ^ 2)) x := by
    convert hleftRaw using 1 <;> field_simp [hr0] <;> ring
  have hquot :
      HasDerivAt (fun z : ℝ => y z / z)
        ((deriv y x * x - y x) / x ^ 2) x := by
    simpa using hy.div (hasDerivAt_id x) hx
  have hatanDen : 1 + (y x / x) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (y x / x)]
  have hrightRaw := (hquot.arctan).const_add (Real.log a)
  have hright :
      HasDerivAt
        (fun z : ℝ => Real.log a + Real.arctan (y z / z))
        ((x * deriv y x - y x) / (x ^ 2 + y x ^ 2)) x := by
    convert hrightRaw using 1 <;>
      field_simp [hx, hr0, hatanDen] <;> ring
  have hlogeq :
      (fun z : ℝ => (1 / 2 : ℝ) * Real.log (z ^ 2 + y z ^ 2)) =ᶠ[nhds x]
        (fun z : ℝ => Real.log a + Real.arctan (y z / z)) := by
    filter_upwards [spiralNear_eventually y a x hcurve] with z hzcurve
    rcases hzcurve with ⟨δ, hδ, hzlocal⟩
    have hzpoint := hzlocal z (by simpa using hδ)
    exact log_spiral_point a z (y z) ha hzpoint
  calc
    (x + y x * deriv y x) / (x ^ 2 + y x ^ 2) =
        deriv (fun z : ℝ => (1 / 2 : ℝ) * Real.log (z ^ 2 + y z ^ 2)) x :=
      hleft.deriv.symm
    _ = deriv (fun z : ℝ => Real.log a + Real.arctan (y z / z)) x :=
      hlogeq.deriv_eq
    _ = (x * deriv y x - y x) / (x ^ 2 + y x ^ 2) :=
      hright.deriv

theorem gap3 (y : ℝ → ℝ) (a x : ℝ) (ha : 0 < a) (hx : x ≠ 0)
    (hr : 0 < x ^ 2 + y x ^ 2) (hxy : x - y x ≠ 0)
    (hsmooth : ContDiffAt ℝ 1 y x) (hcurve : SpiralNear y a x) :
    deriv y x = (x + y x) / (x - y x) := by
  have h := gap2 y a x ha hx hr hsmooth hcurve
  have hr0 : x ^ 2 + y x ^ 2 ≠ 0 := ne_of_gt hr
  field_simp [hr0] at h
  apply (eq_div_iff hxy).2
  nlinarith [h]

theorem gap4 (y : ℝ → ℝ) (a x : ℝ) (ha : 0 < a) (hx : x ≠ 0)
    (hr : 0 < x ^ 2 + y x ^ 2) (hxy : x - y x ≠ 0)
    (hsmooth : ContDiffAt ℝ 2 y x) (hcurve : SpiralNear y a x) :
    nthDeriv 2 y x =
      ((1 + deriv y x) * (x - y x) -
        (1 - deriv y x) * (x + y x)) / (x - y x) ^ 2 := by
  have hsmooth1 : ContDiffAt ℝ 1 y x := hsmooth.of_le (by norm_num)
  have hsmoothEv : ∀ᶠ z in nhds x, ContDiffAt ℝ 1 y z :=
    hsmooth1.eventually (by norm_num)
  have hxEv : ∀ᶠ z in nhds x, z ≠ 0 := continuousAt_id.eventually_ne hx
  have hxyEv : ∀ᶠ z in nhds x, z - y z ≠ 0 :=
    (continuousAt_id.sub hsmooth.continuousAt).eventually_ne hxy
  have hfirst :
      (fun z : ℝ => deriv y z) =ᶠ[nhds x]
        (fun z : ℝ => (z + y z) / (z - y z)) := by
    filter_upwards [hsmoothEv, spiralNear_eventually y a x hcurve, hxEv, hxyEv] with
      z hsz hzcurve hz0 hzy0
    have hrz : 0 < z ^ 2 + y z ^ 2 := by positivity
    exact gap3 y a z ha hz0 hrz hzy0 hsz hzcurve
  have hy : HasDerivAt y (deriv y x) x :=
    (hsmooth1.differentiableAt (by norm_num)).hasDerivAt
  have hnum :
      HasDerivAt (fun z : ℝ => z + y z) (1 + deriv y x) x := by
    simpa using (hasDerivAt_id x).add hy
  have hden :
      HasDerivAt (fun z : ℝ => z - y z) (1 - deriv y x) x := by
    simpa using (hasDerivAt_id x).sub hy
  have hquot :
      HasDerivAt (fun z : ℝ => (z + y z) / (z - y z))
        (((1 + deriv y x) * (x - y x) -
          (x + y x) * (1 - deriv y x)) / (x - y x) ^ 2) x :=
    hnum.div hden hxy
  have hquotDeriv :
      deriv (fun z : ℝ => (z + y z) / (z - y z)) x =
        ((1 + deriv y x) * (x - y x) -
          (1 - deriv y x) * (x + y x)) / (x - y x) ^ 2 := by
    convert hquot.deriv using 1 <;> ring
  change deriv (deriv y) x = _
  calc
    deriv (deriv y) x =
        deriv (fun z : ℝ => (z + y z) / (z - y z)) x := hfirst.deriv_eq
    _ = ((1 + deriv y x) * (x - y x) -
          (1 - deriv y x) * (x + y x)) / (x - y x) ^ 2 := hquotDeriv

theorem gap5 (y : ℝ → ℝ) (a x : ℝ) (ha : 0 < a) (hx : x ≠ 0)
    (hr : 0 < x ^ 2 + y x ^ 2) (hxy : x - y x ≠ 0)
    (hsmooth : ContDiffAt ℝ 2 y x) (hcurve : SpiralNear y a x) :
    ((1 + deriv y x) * (x - y x) -
        (1 - deriv y x) * (x + y x)) / (x - y x) ^ 2 =
      (2 * x * deriv y x - 2 * y x) / (x - y x) ^ 2 := by
  ring

theorem gap6 (y : ℝ → ℝ) (a x : ℝ) (ha : 0 < a) (hx : x ≠ 0)
    (hr : 0 < x ^ 2 + y x ^ 2) (hxy : x - y x ≠ 0)
    (hsmooth : ContDiffAt ℝ 2 y x) (hcurve : SpiralNear y a x)
    (h1 : deriv y x = (x + y x) / (x - y x)) :
    (2 * x * deriv y x - 2 * y x) / (x - y x) ^ 2 =
      (2 * x * ((x + y x) / (x - y x)) - 2 * y x) /
        (x - y x) ^ 2 := by
  rw [h1]

theorem gap7 (y : ℝ → ℝ) (a x : ℝ) (ha : 0 < a) (hx : x ≠ 0)
    (hr : 0 < x ^ 2 + y x ^ 2) (hxy : x - y x ≠ 0)
    (hsmooth : ContDiffAt ℝ 2 y x) (hcurve : SpiralNear y a x) :
    (2 * x * ((x + y x) / (x - y x)) - 2 * y x) /
        (x - y x) ^ 2 =
      2 * (x ^ 2 + y x ^ 2) / (x - y x) ^ 3 := by
  field_simp [hxy] <;> ring

theorem gap8 (y : ℝ → ℝ) (a x : ℝ) (ha : 0 < a) (hx : x ≠ 0)
    (hr : 0 < x ^ 2 + y x ^ 2) (hxy : x - y x ≠ 0)
    (hsmooth : ContDiffAt ℝ 2 y x) (hcurve : SpiralNear y a x) :
    nthDeriv 2 y x =
      2 * (x ^ 2 + y x ^ 2) / (x - y x) ^ 3 := by
  have h1 := gap3 y a x ha hx hr hxy (hsmooth.of_le (by norm_num)) hcurve
  calc
    nthDeriv 2 y x =
        ((1 + deriv y x) * (x - y x) -
          (1 - deriv y x) * (x + y x)) / (x - y x) ^ 2 :=
      gap4 y a x ha hx hr hxy hsmooth hcurve
    _ = (2 * x * deriv y x - 2 * y x) / (x - y x) ^ 2 :=
      gap5 y a x ha hx hr hxy hsmooth hcurve
    _ = (2 * x * ((x + y x) / (x - y x)) - 2 * y x) /
          (x - y x) ^ 2 :=
      gap6 y a x ha hx hr hxy hsmooth hcurve h1
    _ = 2 * (x ^ 2 + y x ^ 2) / (x - y x) ^ 3 :=
      gap7 y a x ha hx hr hxy hsmooth hcurve

end

end ProofGap.Exercise1150
