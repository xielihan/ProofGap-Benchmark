import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise1138

noncomputable section

def y (u v : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.log (Real.sqrt (u t ^ 2 + v t ^ 2))

def secondDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (fun t => deriv f t) x

def TwiceDifferentiableAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ ε > 0,
    DifferentiableOn ℝ f (Set.Ioo (x - ε) (x + ε)) ∧
      DifferentiableAt ℝ (fun t => deriv f t) x

def expanded (u v : ℝ → ℝ) (t : ℝ) : ℝ :=
  ((u t ^ 2 + v t ^ 2) *
        (deriv u t ^ 2 + u t * secondDeriv u t +
          deriv v t ^ 2 + v t * secondDeriv v t) -
      2 * (u t * deriv u t + v t * deriv v t) ^ 2) /
    (u t ^ 2 + v t ^ 2) ^ 2

def finalForm (u v : ℝ → ℝ) (t : ℝ) : ℝ :=
  ((v t ^ 2 - u t ^ 2) * deriv u t ^ 2 -
      4 * u t * v t * deriv u t * deriv v t +
      (u t ^ 2 - v t ^ 2) * deriv v t ^ 2 +
      (u t ^ 2 + v t ^ 2) *
        (u t * secondDeriv u t + v t * secondDeriv v t)) /
    (u t ^ 2 + v t ^ 2) ^ 2

private abbrev neighborhoodFilter {α : Type*} [TopologicalSpace α] (a : α) : Filter α :=
  nhds a

local notation "𝓝" => neighborhoodFilter

theorem gap1 (u v : ℝ → ℝ) (t : ℝ)
    (hu : DifferentiableAt ℝ u t) (hv : DifferentiableAt ℝ v t)
    (hr : 0 < u t ^ 2 + v t ^ 2) :
    deriv (y u v) t =
      (u t * deriv u t + v t * deriv v t) / (u t ^ 2 + v t ^ 2) := by
  have hsum :
      HasDerivAt (fun s => u s ^ 2 + v s ^ 2)
        (2 * u t * deriv u t + 2 * v t * deriv v t) t := by
    convert (hu.hasDerivAt.pow 2).add (hv.hasDerivAt.pow 2) using 1 <;> ring
  have hsqrt :=
    (Real.hasDerivAt_sqrt (ne_of_gt hr)).comp t hsum
  have hchain :=
    (Real.hasDerivAt_log (ne_of_gt (Real.sqrt_pos.2 hr))).comp t hsqrt
  have hfinal :
      HasDerivAt (y u v)
        ((u t * deriv u t + v t * deriv v t) /
          (u t ^ 2 + v t ^ 2)) t := by
    unfold y
    convert hchain using 1
    field_simp [ne_of_gt hr, ne_of_gt (Real.sqrt_pos.2 hr)]
    rw [Real.sq_sqrt hr.le]
  exact hfinal.deriv

theorem gap2 (u v : ℝ → ℝ) (t : ℝ)
    (hu : TwiceDifferentiableAt u t) (hv : TwiceDifferentiableAt v t)
    (hr : 0 < u t ^ 2 + v t ^ 2) :
    secondDeriv (y u v) t = expanded u v t := by
  rcases hu with ⟨εu, hεu, hu_on, hdu⟩
  rcases hv with ⟨εv, hεv, hv_on, hdv⟩
  have htu : t ∈ Set.Ioo (t - εu) (t + εu) := by
    constructor <;> linarith
  have htv : t ∈ Set.Ioo (t - εv) (t + εv) := by
    constructor <;> linarith
  have hut : DifferentiableAt ℝ u t :=
    (hu_on t htu).differentiableAt (isOpen_Ioo.mem_nhds htu)
  have hvt : DifferentiableAt ℝ v t :=
    (hv_on t htv).differentiableAt (isOpen_Ioo.mem_nhds htv)
  have hu_eventually : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ u s := by
    filter_upwards [isOpen_Ioo.mem_nhds htu] with s hs
    exact (hu_on s hs).differentiableAt (isOpen_Ioo.mem_nhds hs)
  have hv_eventually : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ v s := by
    filter_upwards [isOpen_Ioo.mem_nhds htv] with s hs
    exact (hv_on s hs).differentiableAt (isOpen_Ioo.mem_nhds hs)
  have hr_eventually : ∀ᶠ s in 𝓝 t, 0 < u s ^ 2 + v s ^ 2 := by
    have hc : ContinuousAt (fun s => u s ^ 2 + v s ^ 2) t :=
      (hut.continuousAt.pow 2).add (hvt.continuousAt.pow 2)
    exact hc (Ioi_mem_nhds hr)
  have heq :
      (fun s => deriv (y u v) s) =ᶠ[𝓝 t]
        (fun s =>
          (u s * deriv u s + v s * deriv v s) /
            (u s ^ 2 + v s ^ 2)) := by
    filter_upwards [hu_eventually, hv_eventually, hr_eventually] with s hus hvs hrs
    exact gap1 u v s hus hvs hrs
  have hnum :
      HasDerivAt
        (fun s => u s * deriv u s + v s * deriv v s)
        (deriv u t ^ 2 + u t * secondDeriv u t +
          deriv v t ^ 2 + v t * secondDeriv v t) t := by
    unfold secondDeriv
    convert
      (hut.hasDerivAt.mul hdu.hasDerivAt).add
        (hvt.hasDerivAt.mul hdv.hasDerivAt) using 1 <;> ring
  have hden :
      HasDerivAt (fun s => u s ^ 2 + v s ^ 2)
        (2 * (u t * deriv u t + v t * deriv v t)) t := by
    convert (hut.hasDerivAt.pow 2).add (hvt.hasDerivAt.pow 2) using 1 <;> ring
  have hquot :
      HasDerivAt
        (fun s =>
          (u s * deriv u s + v s * deriv v s) /
            (u s ^ 2 + v s ^ 2))
        (expanded u v t) t := by
    convert hnum.div hden (ne_of_gt hr) using 1
    unfold expanded
    ring
  unfold secondDeriv
  calc
    deriv (fun s => deriv (y u v) s) t =
        deriv
          (fun s =>
            (u s * deriv u s + v s * deriv v s) /
              (u s ^ 2 + v s ^ 2)) t := heq.deriv_eq
    _ = expanded u v t := hquot.deriv

theorem gap3 (u v : ℝ → ℝ) (t : ℝ)
    (hr : 0 < u t ^ 2 + v t ^ 2) :
    expanded u v t = finalForm u v t := by
  unfold expanded finalForm
  ring

theorem gap4 (u v : ℝ → ℝ) (t : ℝ)
    (hu : TwiceDifferentiableAt u t) (hv : TwiceDifferentiableAt v t)
    (hr : 0 < u t ^ 2 + v t ^ 2) :
    secondDeriv (y u v) t = finalForm u v t := by
  calc
    secondDeriv (y u v) t = expanded u v t := gap2 u v t hu hv hr
    _ = finalForm u v t := gap3 u v t hr

end

end ProofGap.Exercise1138
