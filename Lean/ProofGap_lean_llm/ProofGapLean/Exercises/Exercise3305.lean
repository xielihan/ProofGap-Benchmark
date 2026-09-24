import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3305

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def partialX (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => u t y z) x

def partialXX (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  iterDeriv 2 (fun t => u t y z) x

def partialYY (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  iterDeriv 2 (fun t => u x t z) y

def partialZZ (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  iterDeriv 2 (fun t => u x y t) z

def laplacian (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  partialXX u x y z + partialYY u x y z + partialZZ u x y z

def radius (x y z : ℝ) : ℝ :=
  Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)

def radialProfile (f : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  iterDeriv 2 f ρ + 2 * deriv f ρ / ρ

def IsRadialWithProfile (g r : ℝ → ℝ → ℝ → ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ x y z, r x y z ≠ 0 → g x y z = F (r x y z)

private theorem radialLine_derivs (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (a x : ℝ) (ha : 0 ≤ a)
    (hr : Real.sqrt (x ^ 2 + a) ≠ 0) :
    deriv (fun t : ℝ => f (Real.sqrt (t ^ 2 + a))) x =
        deriv f (Real.sqrt (x ^ 2 + a)) *
          (x / Real.sqrt (x ^ 2 + a)) ∧
      iterDeriv 2 (fun t : ℝ => f (Real.sqrt (t ^ 2 + a))) x =
        iterDeriv 2 f (Real.sqrt (x ^ 2 + a)) *
            (x ^ 2 / Real.sqrt (x ^ 2 + a) ^ 2) +
          deriv f (Real.sqrt (x ^ 2 + a)) *
            ((Real.sqrt (x ^ 2 + a) ^ 2 - x ^ 2) /
              Real.sqrt (x ^ 2 + a) ^ 3) := by
  have hf_data :=
    (contDiff_succ_iff_fderiv (n := 1)).mp
      (show ContDiff ℝ (1 + 1) f by simpa using hf)
  have hf' : Differentiable ℝ f := hf_data.1
  have hfd_cd : ContDiff ℝ 1 (fderiv ℝ f) := hf_data.2.2
  have hfd : Differentiable ℝ (fderiv ℝ f) :=
    hfd_cd.differentiable (by decide)
  have hdf : Differentiable ℝ (deriv f) := by
    intro t
    change DifferentiableAt ℝ (fun s : ℝ => (fderiv ℝ f s) 1) t
    exact
      ((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).differentiable
        (fderiv ℝ f t)).comp t (hfd t)
  have hR_at : ∀ t : ℝ, Real.sqrt (t ^ 2 + a) ≠ 0 →
      HasDerivAt (fun s : ℝ => Real.sqrt (s ^ 2 + a))
        (t / Real.sqrt (t ^ 2 + a)) t := by
    intro t ht
    have hqne : t ^ 2 + a ≠ 0 := by
      intro hzero
      apply ht
      simp only [hzero, Real.sqrt_zero]
    have hq : HasDerivAt (fun s : ℝ => s ^ 2 + a) (2 * t) t := by
      convert ((hasDerivAt_id t).pow 2).add_const a using 1 <;>
        simp only [id_eq] <;> ring
    have hs := (Real.hasDerivAt_sqrt hqne).comp t hq
    convert hs using 1 <;> field_simp [ht] <;> ring
  have hR := hR_at x hr
  have hR2 : HasDerivAt
      (fun t : ℝ => t / Real.sqrt (t ^ 2 + a))
      ((Real.sqrt (x ^ 2 + a) ^ 2 - x ^ 2) /
        Real.sqrt (x ^ 2 + a) ^ 3) x := by
    have h := (hasDerivAt_id x).div hR hr
    convert h using 1 <;> simp only [id_eq] <;>
      field_simp [hr] <;> ring_nf
  have hcomp_at : ∀ t : ℝ, Real.sqrt (t ^ 2 + a) ≠ 0 →
      HasDerivAt (fun s : ℝ => f (Real.sqrt (s ^ 2 + a)))
        (deriv f (Real.sqrt (t ^ 2 + a)) *
          (t / Real.sqrt (t ^ 2 + a))) t := by
    intro t ht
    exact (hf' _).hasDerivAt.comp t (hR_at t ht)
  have hdfcomp : HasDerivAt
      (fun t : ℝ => deriv f (Real.sqrt (t ^ 2 + a)))
      (iterDeriv 2 f (Real.sqrt (x ^ 2 + a)) *
        (x / Real.sqrt (x ^ 2 + a))) x := by
    simpa only [iterDeriv, Function.iterate_succ_apply,
      Function.iterate_zero_apply] using
      ((hdf _).hasDerivAt.comp x hR)
  have hprod : HasDerivAt
      (fun t : ℝ => deriv f (Real.sqrt (t ^ 2 + a)) *
        (t / Real.sqrt (t ^ 2 + a)))
      (iterDeriv 2 f (Real.sqrt (x ^ 2 + a)) *
          (x ^ 2 / Real.sqrt (x ^ 2 + a) ^ 2) +
        deriv f (Real.sqrt (x ^ 2 + a)) *
          ((Real.sqrt (x ^ 2 + a) ^ 2 - x ^ 2) /
            Real.sqrt (x ^ 2 + a) ^ 3)) x := by
    have h := hdfcomp.mul hR2
    convert h using 1 <;> field_simp [hr] <;> ring_nf
  have hinner : Continuous (fun t : ℝ => t ^ 2 + a) :=
    (continuous_id.pow 2).add continuous_const
  have hroot : Continuous (fun t : ℝ => Real.sqrt (t ^ 2 + a)) :=
    Real.continuous_sqrt.comp hinner
  have hroot_ne :
      ∀ᶠ t in nhds x, Real.sqrt (t ^ 2 + a) ≠ 0 :=
    hroot.continuousAt.eventually_ne hr
  have hderiv_eq :
      (fun t : ℝ => deriv (fun s : ℝ => f (Real.sqrt (s ^ 2 + a))) t) =ᶠ[nhds x]
        (fun t : ℝ => deriv f (Real.sqrt (t ^ 2 + a)) *
          (t / Real.sqrt (t ^ 2 + a))) :=
    hroot_ne.mono (by
      intro t ht
      exact (hcomp_at t ht).deriv)
  constructor
  · exact (hcomp_at x hr).deriv
  · change deriv (deriv (fun t : ℝ => f (Real.sqrt (t ^ 2 + a)))) x = _
    exact (hprod.congr_of_eventuallyEq hderiv_eq).deriv

theorem gap1 (u r : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y z, u x y z = f (r x y z))
    (hradius : ∀ x y z, r x y z = radius x y z)
    (hf : ContDiff ℝ 2 f) (x y z : ℝ) (hr : r x y z ≠ 0) :
    partialX u x y z =
      deriv f (r x y z) * (x / r x y z) := by
  have huv : (fun t : ℝ => u t y z) =
      (fun t : ℝ => f (Real.sqrt (t ^ 2 + (y ^ 2 + z ^ 2)))) := by
    funext t
    rw [hu t y z, hradius t y z]
    simp only [radius, add_assoc]
  have hr' : Real.sqrt (x ^ 2 + (y ^ 2 + z ^ 2)) ≠ 0 := by
    simpa only [hradius x y z, radius, add_assoc] using hr
  have h := radialLine_derivs f hf (y ^ 2 + z ^ 2) x
    (by positivity) hr'
  unfold partialX
  rw [huv, hradius x y z]
  simpa only [radius, add_assoc] using h.1

theorem gap2 (u r : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y z, u x y z = f (r x y z))
    (hradius : ∀ x y z, r x y z = radius x y z)
    (hf : ContDiff ℝ 2 f) (x y z : ℝ) (hr : r x y z ≠ 0) :
    partialXX u x y z =
      iterDeriv 2 f (r x y z) * (x ^ 2 / r x y z ^ 2) +
        deriv f (r x y z) *
          ((r x y z ^ 2 - x ^ 2) / r x y z ^ 3) := by
  have huv : (fun t : ℝ => u t y z) =
      (fun t : ℝ => f (Real.sqrt (t ^ 2 + (y ^ 2 + z ^ 2)))) := by
    funext t
    rw [hu t y z, hradius t y z]
    simp only [radius, add_assoc]
  have hr' : Real.sqrt (x ^ 2 + (y ^ 2 + z ^ 2)) ≠ 0 := by
    simpa only [hradius x y z, radius, add_assoc] using hr
  have h := radialLine_derivs f hf (y ^ 2 + z ^ 2) x
    (by positivity) hr'
  unfold partialXX
  rw [huv, hradius x y z]
  simpa only [radius, add_assoc] using h.2

theorem gap3 (u r : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y z, u x y z = f (r x y z))
    (hradius : ∀ x y z, r x y z = radius x y z)
    (hf : ContDiff ℝ 2 f) (x y z : ℝ) (hr : r x y z ≠ 0) :
    partialYY u x y z =
      iterDeriv 2 f (r x y z) * (y ^ 2 / r x y z ^ 2) +
        deriv f (r x y z) *
          ((r x y z ^ 2 - y ^ 2) / r x y z ^ 3) := by
  have huv : (fun t : ℝ => u x t z) =
      (fun t : ℝ => f (Real.sqrt (t ^ 2 + (x ^ 2 + z ^ 2)))) := by
    funext t
    rw [hu x t z, hradius x t z]
    simp only [radius]
    congr 1
    ring
  have hsqrt :
      Real.sqrt (y ^ 2 + (x ^ 2 + z ^ 2)) = radius x y z := by
    simp only [radius]
    congr 1
    ring
  have hr' : Real.sqrt (y ^ 2 + (x ^ 2 + z ^ 2)) ≠ 0 := by
    rw [hsqrt]
    simpa only [hradius x y z] using hr
  have h := radialLine_derivs f hf (x ^ 2 + z ^ 2) y
    (by positivity) hr'
  unfold partialYY
  rw [huv, hradius x y z]
  rw [hsqrt] at h
  exact h.2

theorem gap4 (u r : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y z, u x y z = f (r x y z))
    (hradius : ∀ x y z, r x y z = radius x y z)
    (hf : ContDiff ℝ 2 f) (x y z : ℝ) (hr : r x y z ≠ 0) :
    partialZZ u x y z =
      iterDeriv 2 f (r x y z) * (z ^ 2 / r x y z ^ 2) +
        deriv f (r x y z) *
          ((r x y z ^ 2 - z ^ 2) / r x y z ^ 3) := by
  have huv : (fun t : ℝ => u x y t) =
      (fun t : ℝ => f (Real.sqrt (t ^ 2 + (x ^ 2 + y ^ 2)))) := by
    funext t
    rw [hu x y t, hradius x y t]
    simp only [radius]
    congr 1
    ring
  have hsqrt :
      Real.sqrt (z ^ 2 + (x ^ 2 + y ^ 2)) = radius x y z := by
    simp only [radius]
    congr 1
    ring
  have hr' : Real.sqrt (z ^ 2 + (x ^ 2 + y ^ 2)) ≠ 0 := by
    rw [hsqrt]
    simpa only [hradius x y z] using hr
  have h := radialLine_derivs f hf (x ^ 2 + y ^ 2) z
    (by positivity) hr'
  unfold partialZZ
  rw [huv, hradius x y z]
  rw [hsqrt] at h
  exact h.2

theorem gap5 (u r : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y z, u x y z = f (r x y z))
    (hradius : ∀ x y z, r x y z = radius x y z)
    (hf : ContDiff ℝ 2 f) (x y z : ℝ) (hr : r x y z ≠ 0) :
    laplacian u x y z =
      iterDeriv 2 f (r x y z) +
        2 * deriv f (r x y z) / r x y z := by
  unfold laplacian
  rw [gap2 u r f hu hradius hf x y z hr,
    gap3 u r f hu hradius hf x y z hr,
    gap4 u r f hu hradius hf x y z hr]
  have hnonneg : 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 := by positivity
  have hsq : r x y z ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := by
    rw [hradius x y z]
    exact Real.sq_sqrt hnonneg
  field_simp [hr]
  rw [hsq]
  ring

theorem gap6 (f : ℝ → ℝ) :
    ∀ ρ : ℝ, ρ ≠ 0 →
      iterDeriv 2 f ρ + 2 * deriv f ρ / ρ = radialProfile f ρ := by
  intro ρ hρ
  rfl

theorem gap7 (u r : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y z, u x y z = f (r x y z))
    (hradius : ∀ x y z, r x y z = radius x y z)
    (hf : ContDiff ℝ 2 f) :
    IsRadialWithProfile (laplacian u) r (radialProfile f) := by
  unfold IsRadialWithProfile
  intro x y z hr
  rw [gap5 u r f hu hradius hf x y z hr]
  rfl

theorem gap8 (u r : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y z, u x y z = f (r x y z))
    (hradius : ∀ x y z, r x y z = radius x y z)
    (hf : ContDiff ℝ 2 f) :
    ∀ x y z, r x y z ≠ 0 →
      laplacian u x y z = radialProfile f (r x y z) := by
  simpa only [IsRadialWithProfile] using
    (gap7 u r f hu hradius hf)

end

end ProofGap.Exercise3305
