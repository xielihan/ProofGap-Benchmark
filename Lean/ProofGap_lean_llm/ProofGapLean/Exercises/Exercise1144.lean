import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1144

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def X (f : ℝ → ℝ) (t : ℝ) : ℝ := deriv f t
def Y (f : ℝ → ℝ) (t : ℝ) : ℝ := t * deriv f t - f t
def d1 (f : ℝ → ℝ) (t : ℝ) : ℝ := deriv (Y f) t / deriv (X f) t
def d2 (f : ℝ → ℝ) (t : ℝ) : ℝ := deriv (d1 f) t / deriv (X f) t
def d3 (f : ℝ → ℝ) (t : ℝ) : ℝ := deriv (d2 f) t / deriv (X f) t

def TwiceDifferentiableAt (f : ℝ → ℝ) (t : ℝ) : Prop :=
  ContDiffAt ℝ 2 f t

def ThreeTimesDifferentiableAt (f : ℝ → ℝ) (t : ℝ) : Prop :=
  ContDiffAt ℝ 3 f t

theorem gap1 (f : ℝ → ℝ) (t : ℝ)
    (hsmooth : TwiceDifferentiableAt f t)
    (h2 : nthDeriv 2 f t ≠ 0) :
    d1 f t = t * nthDeriv 2 f t / nthDeriv 2 f t := by
  have hf : DifferentiableAt ℝ f t :=
    hsmooth.differentiableAt (by decide)
  have hdfSmooth : ContDiffAt ℝ 1 (deriv f) t :=
    hsmooth.derivWithin (m := 1) (by norm_num)
  have hdf : DifferentiableAt ℝ (deriv f) t :=
    hdfSmooth.differentiableAt (by decide)
  have hY : HasDerivAt (Y f) (t * nthDeriv 2 f t) t := by
    unfold Y
    convert ((hasDerivAt_id t).mul hdf.hasDerivAt).sub hf.hasDerivAt using 1 <;>
      simp only [Pi.mul_apply, id_eq, nthDeriv] <;> ring
  have hX : HasDerivAt (X f) (nthDeriv 2 f t) t := by
    unfold X
    change HasDerivAt (deriv f) (deriv (deriv f) t) t
    exact hdf.hasDerivAt
  unfold d1
  rw [hY.deriv, hX.deriv]

theorem gap2 (f : ℝ → ℝ) (t : ℝ)
    (hsmooth : TwiceDifferentiableAt f t)
    (h2 : nthDeriv 2 f t ≠ 0) :
    t * nthDeriv 2 f t / nthDeriv 2 f t = t := by
  field_simp [h2]

theorem gap3 (f : ℝ → ℝ) (t : ℝ)
    (hsmooth : TwiceDifferentiableAt f t)
    (h2 : nthDeriv 2 f t ≠ 0) :
    d1 f t = t := by
  calc
    d1 f t = t * nthDeriv 2 f t / nthDeriv 2 f t :=
      gap1 f t hsmooth h2
    _ = t := gap2 f t hsmooth h2

theorem gap4 (f : ℝ → ℝ) (t : ℝ)
    (hsmooth : TwiceDifferentiableAt f t)
    (h2 : nthDeriv 2 f t ≠ 0) :
    d2 f t = 1 / nthDeriv 2 f t := by
  have hdfSmooth : ContDiffAt ℝ 1 (deriv f) t :=
    hsmooth.derivWithin (m := 1) (by norm_num)
  have hsecondSmooth : ContDiffAt ℝ 0 (nthDeriv 2 f) t := by
    change ContDiffAt ℝ 0 (deriv (deriv f)) t
    exact hdfSmooth.derivWithin (m := 0) (by norm_num)
  have h2ev : ∀ᶠ z in nhds t, nthDeriv 2 f z ≠ 0 :=
    hsecondSmooth.continuousAt.eventually_ne h2
  have heq : d1 f =ᶠ[nhds t] (fun z : ℝ => z) := by
    filter_upwards [hsmooth.eventually (by decide), h2ev] with z hsz hz
    exact gap3 f z hsz hz
  have hd1 : deriv (d1 f) t = 1 := by
    calc
      deriv (d1 f) t = deriv (fun z : ℝ => z) t := heq.deriv_eq
      _ = 1 := (hasDerivAt_id t).deriv
  have hX : deriv (X f) t = nthDeriv 2 f t := by
    rfl
  unfold d2
  rw [hd1, hX]

theorem gap5 (f : ℝ → ℝ) (t : ℝ)
    (hsmooth : ThreeTimesDifferentiableAt f t)
    (h2 : nthDeriv 2 f t ≠ 0) :
    d3 f t =
      -((nthDeriv 3 f t / nthDeriv 2 f t ^ 2) / nthDeriv 2 f t) := by
  have hsmooth2 : TwiceDifferentiableAt f t :=
    hsmooth.of_le (by norm_num)
  have hdfSmooth : ContDiffAt ℝ 1 (deriv f) t :=
    hsmooth2.derivWithin (m := 1) (by norm_num)
  have hsecondContinuous : ContDiffAt ℝ 0 (nthDeriv 2 f) t := by
    change ContDiffAt ℝ 0 (deriv (deriv f)) t
    exact hdfSmooth.derivWithin (m := 0) (by norm_num)
  have h2ev : ∀ᶠ z in nhds t, nthDeriv 2 f z ≠ 0 :=
    hsecondContinuous.continuousAt.eventually_ne h2
  have heq :
      d2 f =ᶠ[nhds t] (fun z : ℝ => 1 / nthDeriv 2 f z) := by
    filter_upwards [hsmooth2.eventually (by decide), h2ev] with z hsz hz
    exact gap4 f z hsz hz
  have hfirstSmooth : ContDiffAt ℝ 2 (deriv f) t :=
    hsmooth.derivWithin (m := 2) (by norm_num)
  have hsecondSmooth : ContDiffAt ℝ 1 (nthDeriv 2 f) t := by
    change ContDiffAt ℝ 1 (deriv (deriv f)) t
    exact hfirstSmooth.derivWithin (m := 1) (by norm_num)
  have hsecond :
      HasDerivAt (nthDeriv 2 f) (nthDeriv 3 f t) t := by
    simpa [nthDeriv] using
      (hsecondSmooth.differentiableAt (by decide)).hasDerivAt
  have hrecip :
      HasDerivAt (fun z : ℝ => 1 / nthDeriv 2 f z)
        (-(nthDeriv 3 f t / nthDeriv 2 f t ^ 2)) t := by
    convert (hasDerivAt_const t (1 : ℝ)).div hsecond h2 using 1 <;>
      ring
  have hd2 :
      deriv (d2 f) t = -(nthDeriv 3 f t / nthDeriv 2 f t ^ 2) := by
    calc
      deriv (d2 f) t =
          deriv (fun z : ℝ => 1 / nthDeriv 2 f z) t := heq.deriv_eq
      _ = -(nthDeriv 3 f t / nthDeriv 2 f t ^ 2) := hrecip.deriv
  have hX : deriv (X f) t = nthDeriv 2 f t := by
    rfl
  unfold d3
  rw [hd2, hX]
  ring

theorem gap6 (f : ℝ → ℝ) (t : ℝ)
    (hsmooth : ThreeTimesDifferentiableAt f t)
    (h2 : nthDeriv 2 f t ≠ 0) :
    -((nthDeriv 3 f t / nthDeriv 2 f t ^ 2) / nthDeriv 2 f t) =
      -(nthDeriv 3 f t) / nthDeriv 2 f t ^ 3 := by
  field_simp [h2]

theorem gap7 (f : ℝ → ℝ) (t : ℝ)
    (hsmooth : ThreeTimesDifferentiableAt f t)
    (h2 : nthDeriv 2 f t ≠ 0) :
    d3 f t = -(nthDeriv 3 f t) / nthDeriv 2 f t ^ 3 := by
  calc
    d3 f t =
        -((nthDeriv 3 f t / nthDeriv 2 f t ^ 2) /
          nthDeriv 2 f t) := gap5 f t hsmooth h2
    _ = -(nthDeriv 3 f t) / nthDeriv 2 f t ^ 3 :=
      gap6 f t hsmooth h2

end

end ProofGap.Exercise1144
