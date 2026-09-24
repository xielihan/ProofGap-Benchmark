import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1134_2

noncomputable section

def y (u v : ℝ → ℝ) (x : ℝ) : ℝ := u x / v x
def secondDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (fun t => deriv f t) x

def TwiceDifferentiableAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ ε > 0,
    DifferentiableOn ℝ f (Set.Ioo (x - ε) (x + ε)) ∧
      DifferentiableAt ℝ (fun t => deriv f t) x

def expanded (u v : ℝ → ℝ) (x : ℝ) : ℝ :=
  (v x ^ 2 *
        (deriv v x * deriv u x + v x * secondDeriv u x -
          deriv u x * deriv v x - u x * secondDeriv v x) -
      2 * v x * deriv v x * (v x * deriv u x - u x * deriv v x)) /
    v x ^ 4

def finalForm (u v : ℝ → ℝ) (x : ℝ) : ℝ :=
  (v x * (v x * secondDeriv u x - u x * secondDeriv v x) -
      2 * deriv v x * (v x * deriv u x - u x * deriv v x)) /
    v x ^ 3

theorem gap1 (u v : ℝ → ℝ) (x : ℝ)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x)
    (hv0 : v x ≠ 0) :
    deriv (y u v) x =
      (v x * deriv u x - u x * deriv v x) / v x ^ 2 := by
  unfold y
  convert (hu.hasDerivAt.div hv.hasDerivAt hv0).deriv using 1 <;>
    ring

theorem gap2 (u v : ℝ → ℝ) (x : ℝ)
    (hu : TwiceDifferentiableAt u x) (hv : TwiceDifferentiableAt v x)
    (hv0 : v x ≠ 0) :
    secondDeriv (y u v) x = expanded u v x := by
  rcases hu with ⟨εu, hεu, huOn, hdu⟩
  rcases hv with ⟨εv, hεv, hvOn, hdv⟩
  have hxu : x ∈ Set.Ioo (x - εu) (x + εu) := by
    constructor <;> linarith
  have hxv : x ∈ Set.Ioo (x - εv) (x + εv) := by
    constructor <;> linarith
  have huAt : DifferentiableAt ℝ u x :=
    (huOn x hxu).differentiableAt (isOpen_Ioo.mem_nhds hxu)
  have hvAt : DifferentiableAt ℝ v x :=
    (hvOn x hxv).differentiableAt (isOpen_Ioo.mem_nhds hxv)
  have hvne : ∀ᶠ t in nhds x, v t ≠ 0 :=
    hvAt.continuousAt.eventually_ne hv0
  have heq :
      (fun t => deriv (y u v) t) =ᶠ[nhds x]
        (fun t =>
          (v t * deriv u t - u t * deriv v t) / v t ^ 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hxu,
      isOpen_Ioo.mem_nhds hxv, hvne] with t htu htv ht0
    exact gap1 u v t
      ((huOn t htu).differentiableAt (isOpen_Ioo.mem_nhds htu))
      ((hvOn t htv).differentiableAt (isOpen_Ioo.mem_nhds htv))
      ht0
  have huu : HasDerivAt (fun t => deriv u t) (secondDeriv u x) x := by
    simpa [secondDeriv] using hdu.hasDerivAt
  have hvv : HasDerivAt (fun t => deriv v t) (secondDeriv v x) x := by
    simpa [secondDeriv] using hdv.hasDerivAt
  have hnum :
      HasDerivAt
        (fun t => v t * deriv u t - u t * deriv v t)
        (deriv v x * deriv u x + v x * secondDeriv u x -
          (deriv u x * deriv v x + u x * secondDeriv v x)) x := by
    exact (hvAt.hasDerivAt.mul huu).sub (huAt.hasDerivAt.mul hvv)
  have hden :
      HasDerivAt (fun t => v t ^ 2) (2 * v x * deriv v x) x := by
    have hraw :
        HasDerivAt (fun t => v t ^ 2)
          (deriv v x * v x + v x * deriv v x) x := by
      simpa only [Pi.mul_apply, pow_two] using
        hvAt.hasDerivAt.mul hvAt.hasDerivAt
    convert hraw using 1 <;> ring
  have hquot :
      HasDerivAt
        (fun t =>
          (v t * deriv u t - u t * deriv v t) / v t ^ 2)
        (expanded u v x) x := by
    convert hnum.div hden (pow_ne_zero 2 hv0) using 1
    unfold expanded
    ring
  unfold secondDeriv
  calc
    deriv (fun t => deriv (y u v) t) x =
        deriv
          (fun t =>
            (v t * deriv u t - u t * deriv v t) / v t ^ 2) x :=
      heq.deriv_eq
    _ = expanded u v x := hquot.deriv

theorem gap3 (u v : ℝ → ℝ) (x : ℝ) (hv0 : v x ≠ 0) :
    expanded u v x = finalForm u v x := by
  unfold expanded finalForm
  field_simp [hv0]
  ring

theorem gap4 (u v : ℝ → ℝ) (x : ℝ)
    (hu : TwiceDifferentiableAt u x) (hv : TwiceDifferentiableAt v x)
    (hv0 : v x ≠ 0) :
    secondDeriv (y u v) x = finalForm u v x := by
  calc
    secondDeriv (y u v) x = expanded u v x := gap2 u v x hu hv hv0
    _ = finalForm u v x := gap3 u v x hv0

end

end ProofGap.Exercise1134_2
