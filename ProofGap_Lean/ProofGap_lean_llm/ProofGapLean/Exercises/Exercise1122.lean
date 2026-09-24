import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1122

noncomputable section

def y (u v : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.log (u x / v x)

def secondDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (fun t => deriv f t) x

def TwiceDifferentiableAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ ε > 0,
    DifferentiableOn ℝ f (Set.Ioo (x - ε) (x + ε)) ∧
      DifferentiableAt ℝ (fun t => deriv f t) x

theorem gap1 (u v : ℝ → ℝ) (x : ℝ)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x)
    (hu0 : u x ≠ 0) (hv0 : v x ≠ 0) (hpos : 0 < u x / v x) :
    deriv (y u v) x = deriv u x / u x - deriv v x / v x := by
  change deriv (fun t => Real.log (u t / v t)) x = _
  have hq :
      HasDerivAt (fun t => u t / v t)
        ((deriv u x * v x - u x * deriv v x) / v x ^ 2) x :=
    hu.hasDerivAt.div hv.hasDerivAt hv0
  have hlog :=
    (Real.hasDerivAt_log (ne_of_gt hpos)).comp x hq
  have hlog_deriv :
      deriv (fun t => Real.log (u t / v t)) x =
        (u x / v x)⁻¹ *
          ((deriv u x * v x - u x * deriv v x) / v x ^ 2) := by
    simpa only [Function.comp_apply] using hlog.deriv
  rw [hlog_deriv]
  field_simp [hu0, hv0]

theorem gap2 (u v : ℝ → ℝ) (x : ℝ)
    (hu : TwiceDifferentiableAt u x) (hv : TwiceDifferentiableAt v x)
    (hu0 : u x ≠ 0) (hv0 : v x ≠ 0) (hpos : 0 < u x / v x) :
    secondDeriv (y u v) x =
      (u x * secondDeriv u x - deriv u x ^ 2) / u x ^ 2 -
        (v x * secondDeriv v x - deriv v x ^ 2) / v x ^ 2 := by
  rcases hu with ⟨eu, heu, hud, hudu⟩
  rcases hv with ⟨ev, hev, hvd, hvdv⟩
  have hxu : x ∈ Set.Ioo (x - eu) (x + eu) := by
    constructor <;> linarith
  have hxv : x ∈ Set.Ioo (x - ev) (x + ev) := by
    constructor <;> linarith
  have hudx : DifferentiableAt ℝ u x :=
    (hud x hxu).differentiableAt (isOpen_Ioo.mem_nhds hxu)
  have hvdx : DifferentiableAt ℝ v x :=
    (hvd x hxv).differentiableAt (isOpen_Ioo.mem_nhds hxv)
  have hu_near : ∀ᶠ z in nhds x, DifferentiableAt ℝ u z := by
    filter_upwards [show ∀ᶠ z in nhds x,
        z ∈ Set.Ioo (x - eu) (x + eu) from isOpen_Ioo.mem_nhds hxu] with z hz
    exact (hud z hz).differentiableAt (isOpen_Ioo.mem_nhds hz)
  have hv_near : ∀ᶠ z in nhds x, DifferentiableAt ℝ v z := by
    filter_upwards [show ∀ᶠ z in nhds x,
        z ∈ Set.Ioo (x - ev) (x + ev) from isOpen_Ioo.mem_nhds hxv] with z hz
    exact (hvd z hz).differentiableAt (isOpen_Ioo.mem_nhds hz)
  have hqcont : ContinuousAt (fun z => u z / v z) x :=
    hudx.continuousAt.div hvdx.continuousAt hv0
  have hpos_near : ∀ᶠ z in nhds x, 0 < u z / v z :=
    hqcont (isOpen_Ioi.mem_nhds hpos)
  have heq :
      (fun z => deriv (y u v) z) =ᶠ[nhds x]
        (fun z => deriv u z / u z - deriv v z / v z) := by
    filter_upwards [hu_near, hv_near, hpos_near] with z huz hvz hp
    have huz0 : u z ≠ 0 := by
      intro hz
      simp [hz] at hp
    have hvz0 : v z ≠ 0 := by
      intro hz
      simp [hz] at hp
    exact gap1 u v z huz hvz huz0 hvz0 hp
  have huu :
      HasDerivAt (fun z => deriv u z / u z)
        ((secondDeriv u x * u x - deriv u x * deriv u x) / u x ^ 2) x := by
    simpa [secondDeriv] using
      (hudu.hasDerivAt.div hudx.hasDerivAt hu0)
  have hvv :
      HasDerivAt (fun z => deriv v z / v z)
        ((secondDeriv v x * v x - deriv v x * deriv v x) / v x ^ 2) x := by
    simpa [secondDeriv] using
      (hvdv.hasDerivAt.div hvdx.hasDerivAt hv0)
  have hsub :
      HasDerivAt
        (fun z => deriv u z / u z - deriv v z / v z)
        (((secondDeriv u x * u x - deriv u x * deriv u x) / u x ^ 2) -
          ((secondDeriv v x * v x - deriv v x * deriv v x) / v x ^ 2)) x := by
    simpa using huu.sub hvv
  calc
    secondDeriv (y u v) x =
        deriv (fun z => deriv u z / u z - deriv v z / v z) x :=
      heq.deriv_eq
    _ = ((secondDeriv u x * u x - deriv u x * deriv u x) / u x ^ 2) -
          ((secondDeriv v x * v x - deriv v x * deriv v x) / v x ^ 2) :=
      hsub.deriv
    _ = (u x * secondDeriv u x - deriv u x ^ 2) / u x ^ 2 -
          (v x * secondDeriv v x - deriv v x ^ 2) / v x ^ 2 := by
      ring

end

end ProofGap.Exercise1122
