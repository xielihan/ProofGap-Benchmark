import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.OrderClosed

namespace ProofGap.Exercise1123

noncomputable section

def y (u v : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.sqrt (u x ^ 2 + v x ^ 2)

def secondDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (fun t => deriv f t) x

def TwiceDifferentiableAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ ε > 0,
    DifferentiableOn ℝ f (Set.Ioo (x - ε) (x + ε)) ∧
      DifferentiableAt ℝ (fun t => deriv f t) x

def expanded (u v : ℝ → ℝ) (x : ℝ) : ℝ :=
  (((u x * secondDeriv u x + deriv u x ^ 2 +
          v x * secondDeriv v x + deriv v x ^ 2) *
        Real.sqrt (u x ^ 2 + v x ^ 2) -
      (u x * deriv u x + v x * deriv v x) ^ 2 /
        Real.sqrt (u x ^ 2 + v x ^ 2)) /
    (u x ^ 2 + v x ^ 2))

def finalForm (u v : ℝ → ℝ) (x : ℝ) : ℝ :=
  ((u x ^ 2 + v x ^ 2) *
        (u x * secondDeriv u x + v x * secondDeriv v x) +
      (deriv u x * v x - deriv v x * u x) ^ 2) /
    Real.rpow (u x ^ 2 + v x ^ 2) (3 / 2 : ℝ)

theorem gap1 (u v : ℝ → ℝ) (x : ℝ)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x)
    (hr : 0 < u x ^ 2 + v x ^ 2) :
    deriv (y u v) x =
      (u x * deriv u x + v x * deriv v x) /
        Real.sqrt (u x ^ 2 + v x ^ 2) := by
  have hu' : HasDerivAt u (deriv u x) x := hu.hasDerivAt
  have hv' : HasDerivAt v (deriv v x) x := hv.hasDerivAt
  have hsum :
      HasDerivAt (fun t => u t ^ 2 + v t ^ 2)
        ((deriv u x * u x + u x * deriv u x) +
          (deriv v x * v x + v x * deriv v x)) x := by
    simpa only [Pi.add_apply, Pi.mul_apply, pow_two] using
      HasDerivAt.add (hu'.mul hu') (hv'.mul hv')
  have hsqrt :
      HasDerivAt (fun t => Real.sqrt (u t ^ 2 + v t ^ 2))
        (1 / (2 * Real.sqrt (u x ^ 2 + v x ^ 2)) *
          ((deriv u x * u x + u x * deriv u x) +
            (deriv v x * v x + v x * deriv v x))) x := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_sqrt (ne_of_gt hr)).comp x hsum
  have hs : Real.sqrt (u x ^ 2 + v x ^ 2) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hr
  unfold y
  calc
    deriv (fun t => Real.sqrt (u t ^ 2 + v t ^ 2)) x =
        1 / (2 * Real.sqrt (u x ^ 2 + v x ^ 2)) *
          ((deriv u x * u x + u x * deriv u x) +
            (deriv v x * v x + v x * deriv v x)) := hsqrt.deriv
    _ = (u x * deriv u x + v x * deriv v x) /
        Real.sqrt (u x ^ 2 + v x ^ 2) := by
      field_simp [hs] <;> ring

theorem gap2 (u v : ℝ → ℝ) (x : ℝ)
    (hu : TwiceDifferentiableAt u x) (hv : TwiceDifferentiableAt v x)
    (hr : 0 < u x ^ 2 + v x ^ 2) :
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
  have hcont : ContinuousAt (fun t => u t ^ 2 + v t ^ 2) x :=
    (huAt.continuousAt.pow 2).add (hvAt.continuousAt.pow 2)
  have hpos : ∀ᶠ t in nhds x, 0 < u t ^ 2 + v t ^ 2 :=
    hcont.eventually (Ioi_mem_nhds hr)
  have heq :
      (fun t => deriv (y u v) t) =ᶠ[nhds x]
        (fun t =>
          (u t * deriv u t + v t * deriv v t) /
            Real.sqrt (u t ^ 2 + v t ^ 2)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hxu,
      isOpen_Ioo.mem_nhds hxv, hpos] with t htu htv htpos
    have hut : DifferentiableAt ℝ u t :=
      (huOn t htu).differentiableAt (isOpen_Ioo.mem_nhds htu)
    have hvt : DifferentiableAt ℝ v t :=
      (hvOn t htv).differentiableAt (isOpen_Ioo.mem_nhds htv)
    exact gap1 u v t hut hvt htpos
  have hu' : HasDerivAt u (deriv u x) x := huAt.hasDerivAt
  have hv' : HasDerivAt v (deriv v x) x := hvAt.hasDerivAt
  have huu : HasDerivAt (fun t => deriv u t) (secondDeriv u x) x := by
    simpa [secondDeriv] using hdu.hasDerivAt
  have hvv : HasDerivAt (fun t => deriv v t) (secondDeriv v x) x := by
    simpa [secondDeriv] using hdv.hasDerivAt
  have hnum :
      HasDerivAt
        (fun t => u t * deriv u t + v t * deriv v t)
        ((deriv u x * deriv u x + u x * secondDeriv u x) +
          (deriv v x * deriv v x + v x * secondDeriv v x)) x := by
    simpa only [Pi.add_apply, Pi.mul_apply] using
      HasDerivAt.add (hu'.mul huu) (hv'.mul hvv)
  have hsum :
      HasDerivAt (fun t => u t ^ 2 + v t ^ 2)
        ((deriv u x * u x + u x * deriv u x) +
          (deriv v x * v x + v x * deriv v x)) x := by
    simpa only [Pi.add_apply, Pi.mul_apply, pow_two] using
      HasDerivAt.add (hu'.mul hu') (hv'.mul hv')
  have hsqrt :
      HasDerivAt (fun t => Real.sqrt (u t ^ 2 + v t ^ 2))
        (1 / (2 * Real.sqrt (u x ^ 2 + v x ^ 2)) *
          ((deriv u x * u x + u x * deriv u x) +
            (deriv v x * v x + v x * deriv v x))) x := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_sqrt (ne_of_gt hr)).comp x hsum
  have hs : Real.sqrt (u x ^ 2 + v x ^ 2) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hr
  let q' : ℝ :=
    ((((deriv u x * deriv u x + u x * secondDeriv u x) +
          (deriv v x * deriv v x + v x * secondDeriv v x)) *
        Real.sqrt (u x ^ 2 + v x ^ 2) -
      (u x * deriv u x + v x * deriv v x) *
        (1 / (2 * Real.sqrt (u x ^ 2 + v x ^ 2)) *
          ((deriv u x * u x + u x * deriv u x) +
            (deriv v x * v x + v x * deriv v x)))) /
      Real.sqrt (u x ^ 2 + v x ^ 2) ^ 2)
  have hquot :
      HasDerivAt
        (fun t =>
          (u t * deriv u t + v t * deriv v t) /
            Real.sqrt (u t ^ 2 + v t ^ 2)) q' x := by
    dsimp [q']
    simpa only [Pi.div_apply] using hnum.div hsqrt hs
  have hactual : HasDerivAt (fun t => deriv (y u v) t) q' x :=
    hquot.congr_of_eventuallyEq heq
  unfold secondDeriv
  rw [hactual.deriv]
  dsimp [q']
  unfold expanded
  rw [Real.sq_sqrt (le_of_lt hr)]
  field_simp [hs, ne_of_gt hr]
  ring

theorem gap3 (u v : ℝ → ℝ) (x : ℝ)
    (hr : 0 < u x ^ 2 + v x ^ 2) :
    expanded u v x = finalForm u v x := by
  let R : ℝ := u x ^ 2 + v x ^ 2
  have hR : 0 < R := by
    simpa [R] using hr
  have hhalf : Real.rpow R (1 / 2 : ℝ) = Real.sqrt R := by
    simpa using (Real.sqrt_eq_rpow R).symm
  have hOne : Real.rpow R (1 : ℝ) = R := by
    simp
  have hadd :
      Real.rpow R (1 + 1 / 2 : ℝ) =
        Real.rpow R (1 : ℝ) * Real.rpow R (1 / 2 : ℝ) := by
    exact Real.rpow_add hR 1 (1 / 2)
  have hsquare : Real.sqrt R * Real.sqrt R = R := by
    simpa [pow_two] using Real.sq_sqrt (le_of_lt hR)
  have hrpow :
      Real.rpow R (3 / 2 : ℝ) = R * Real.sqrt R := by
    calc
      Real.rpow R (3 / 2 : ℝ) =
          Real.rpow R (1 + 1 / 2 : ℝ) := by
            congr 1 <;> norm_num
      _ = Real.rpow R (1 : ℝ) * Real.rpow R (1 / 2 : ℝ) := hadd
      _ = R * Real.sqrt R := by rw [hOne, hhalf]
  have hsR : Real.sqrt R ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hR
  unfold expanded finalForm
  change
    (((u x * secondDeriv u x + deriv u x ^ 2 +
          v x * secondDeriv v x + deriv v x ^ 2) *
        Real.sqrt R -
      (u x * deriv u x + v x * deriv v x) ^ 2 /
        Real.sqrt R) / R) =
      ((R * (u x * secondDeriv u x + v x * secondDeriv v x) +
        (deriv u x * v x - deriv v x * u x) ^ 2) /
        Real.rpow R (3 / 2 : ℝ))
  rw [hrpow]
  field_simp [hsR, ne_of_gt hR]
  rw [Real.sq_sqrt (le_of_lt hR)]
  dsimp [R]
  ring

theorem gap4 (u v : ℝ → ℝ) (x : ℝ)
    (hu : TwiceDifferentiableAt u x) (hv : TwiceDifferentiableAt v x)
    (hr : 0 < u x ^ 2 + v x ^ 2) :
    secondDeriv (y u v) x = finalForm u v x := by
  calc
    secondDeriv (y u v) x = expanded u v x := gap2 u v x hu hv hr
    _ = finalForm u v x := gap3 u v x hr

end

end ProofGap.Exercise1123
