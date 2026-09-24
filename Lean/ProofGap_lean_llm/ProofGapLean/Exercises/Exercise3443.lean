import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3443

noncomputable section

def d1 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv f t

def d2 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (deriv f) t

def d3 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (deriv (deriv f)) t

def dydx (x y : ℝ → ℝ) (t : ℝ) : ℝ :=
  d1 y t / d1 x t

def d2ydx2 (x y : ℝ → ℝ) (t : ℝ) : ℝ :=
  d1 (dydx x y) t / d1 x t

def d3ydx3 (x y : ℝ → ℝ) (t : ℝ) : ℝ :=
  d1 (d2ydx2 x y) t / d1 x t

def regular (t : ℝ) : Prop :=
  t ≠ 0

private theorem d1_reciprocal_at_regular
    (x : ℝ → ℝ)
    (hX : ∀ t, regular t → x t = 1 / t)
    {t : ℝ} (ht : regular t) :
    d1 x t = -(1 / t ^ 2) := by
  have ht0 : t ≠ 0 := ht
  have heq : x =ᶠ[nhds t] (fun s : ℝ => 1 / s) :=
    (eventually_ne_nhds ht0).mono (fun s hs => hX s hs)
  unfold d1
  calc
    deriv x t = deriv (fun s : ℝ => 1 / s) t := heq.deriv_eq
    _ = -(1 / t ^ 2) := by
      simpa [div_eq_mul_inv] using
        (((hasDerivAt_const t (1 : ℝ)).div
          (hasDerivAt_id t) ht0).deriv)

theorem gap1 (x y u : ℝ → ℝ)
    (hX : ∀ t, regular t → x t = 1 / t)
    (hY : ∀ t, regular t → y t = u t / t)
    (hu : ContDiff ℝ 1 u) :
    ∀ t, regular t →
      dydx x y t =
        ((d1 u t * t - u t) / t ^ 2) / (-(1 / t ^ 2)) := by
  intro t ht
  have ht0 : t ≠ 0 := ht
  have hyeq : y =ᶠ[nhds t] (fun s : ℝ => u s / s) :=
    (eventually_ne_nhds ht0).mono (fun s hs => hY s hs)
  have hut : DifferentiableAt ℝ u t :=
    (hu.differentiable (by norm_num)).differentiableAt
  have hquot :
      HasDerivAt (fun s : ℝ => u s / s)
        ((d1 u t * t - u t) / t ^ 2) t := by
    simpa [d1] using
      (hut.hasDerivAt.div (hasDerivAt_id t) ht0)
  have hyderiv :
      d1 y t = (d1 u t * t - u t) / t ^ 2 := by
    unfold d1
    calc
      deriv y t = deriv (fun s : ℝ => u s / s) t := hyeq.deriv_eq
      _ = (d1 u t * t - u t) / t ^ 2 := hquot.deriv
  unfold dydx
  rw [hyderiv, d1_reciprocal_at_regular x hX ht]

theorem gap2 (u : ℝ → ℝ) :
    ∀ t, regular t →
      ((d1 u t * t - u t) / t ^ 2) / (-(1 / t ^ 2)) =
        u t - t * d1 u t := by
  intro t ht
  change t ≠ 0 at ht
  field_simp [ht] <;> ring

theorem gap3 (x y u : ℝ → ℝ)
    (hExpand :
      ∀ t, regular t →
        dydx x y t =
          ((d1 u t * t - u t) / t ^ 2) / (-(1 / t ^ 2)))
    (hCancel :
      ∀ t, regular t →
        ((d1 u t * t - u t) / t ^ 2) / (-(1 / t ^ 2)) =
          u t - t * d1 u t) :
    ∀ t, regular t →
      dydx x y t = u t - t * d1 u t := by
  intro t ht
  exact (hExpand t ht).trans (hCancel t ht)

theorem gap4 (x y u : ℝ → ℝ)
    (hX : ∀ t, regular t → x t = 1 / t)
    (hFirst :
      ∀ t, regular t →
        dydx x y t = u t - t * d1 u t)
    (hu : ContDiff ℝ 2 u) :
    ∀ t, regular t →
      d2ydx2 x y t =
        (-t * d2 u t) / (-(1 / t ^ 2)) := by
  intro t ht
  have ht0 : t ≠ 0 := ht
  have hfirsteq :
      dydx x y =ᶠ[nhds t]
        (fun s : ℝ => u s - s * d1 u s) :=
    (eventually_ne_nhds ht0).mono (fun s hs => hFirst s hs)
  have hregFull :=
    (contDiff_succ_iff_fderiv (n := 1) (f := u)).mp
      (by simpa using hu)
  have hut : DifferentiableAt ℝ u t :=
    hregFull.1.differentiableAt
  have hfdu : ContDiff ℝ 1 (fderiv ℝ u) :=
    hregFull.2.2
  have hdu : ContDiff ℝ 1 (deriv u) := by
    change ContDiff ℝ 1 (fun s : ℝ => (fderiv ℝ u s) (1 : ℝ))
    simpa using
      hfdu.clm_apply
        (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ)))
  have hdut : DifferentiableAt ℝ (deriv u) t :=
    (hdu.differentiable (by norm_num)).differentiableAt
  have hmodel :
      HasDerivAt (fun s : ℝ => u s - s * d1 u s)
        (-t * d2 u t) t := by
    convert
      (hut.hasDerivAt.sub
        ((hasDerivAt_id t).mul hdut.hasDerivAt)) using 1 <;>
      simp [d1, d2] <;> ring
  have hnum : d1 (dydx x y) t = -t * d2 u t := by
    unfold d1
    calc
      deriv (dydx x y) t =
          deriv (fun s : ℝ => u s - s * d1 u s) t :=
        hfirsteq.deriv_eq
      _ = -t * d2 u t := hmodel.deriv
  unfold d2ydx2
  rw [hnum, d1_reciprocal_at_regular x hX ht]

theorem gap5 (u : ℝ → ℝ) :
    ∀ t, regular t →
      (-t * d2 u t) / (-(1 / t ^ 2)) =
        t ^ 3 * d2 u t := by
  intro t ht
  change t ≠ 0 at ht
  field_simp [ht] <;> ring

theorem gap6 (x y u : ℝ → ℝ)
    (hExpand :
      ∀ t, regular t →
        d2ydx2 x y t =
          (-t * d2 u t) / (-(1 / t ^ 2)))
    (hCancel :
      ∀ t, regular t →
        (-t * d2 u t) / (-(1 / t ^ 2)) =
          t ^ 3 * d2 u t) :
    ∀ t, regular t →
      d2ydx2 x y t = t ^ 3 * d2 u t := by
  intro t ht
  exact (hExpand t ht).trans (hCancel t ht)

theorem gap7 (x y u : ℝ → ℝ)
    (hX : ∀ t, regular t → x t = 1 / t)
    (hSecond :
      ∀ t, regular t →
        d2ydx2 x y t = t ^ 3 * d2 u t)
    (hu : ContDiff ℝ 3 u) :
    ∀ t, regular t →
      d3ydx3 x y t =
        (3 * t ^ 2 * d2 u t + t ^ 3 * d3 u t) /
          (-(1 / t ^ 2)) := by
  intro t ht
  have ht0 : t ≠ 0 := ht
  have hsecondeq :
      d2ydx2 x y =ᶠ[nhds t]
        (fun s : ℝ => s ^ 3 * d2 u s) :=
    (eventually_ne_nhds ht0).mono (fun s hs => hSecond s hs)
  have hregFull :=
    (contDiff_succ_iff_fderiv (n := 2) (f := u)).mp
      (by simpa using hu)
  have hfdu : ContDiff ℝ 2 (fderiv ℝ u) :=
    hregFull.2.2
  have hdu : ContDiff ℝ 2 (deriv u) := by
    change ContDiff ℝ 2 (fun s : ℝ => (fderiv ℝ u s) (1 : ℝ))
    simpa using
      hfdu.clm_apply
        (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => (1 : ℝ)))
  have hduRegFull :=
    (contDiff_succ_iff_fderiv (n := 1) (f := deriv u)).mp
      (by simpa using hdu)
  have hfddu : ContDiff ℝ 1 (fderiv ℝ (deriv u)) :=
    hduRegFull.2.2
  have hddu : ContDiff ℝ 1 (deriv (deriv u)) := by
    change ContDiff ℝ 1
      (fun s : ℝ => (fderiv ℝ (deriv u) s) (1 : ℝ))
    simpa using
      hfddu.clm_apply
        (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ)))
  have hddut : DifferentiableAt ℝ (deriv (deriv u)) t :=
    (hddu.differentiable (by norm_num)).differentiableAt
  have hmodel :
      HasDerivAt (fun s : ℝ => s ^ 3 * d2 u s)
        (3 * t ^ 2 * d2 u t + t ^ 3 * d3 u t) t := by
    convert
      (((hasDerivAt_id t).pow 3).mul hddut.hasDerivAt) using 1 <;>
      norm_num [d2, d3] <;> ring
  have hnum :
      d1 (d2ydx2 x y) t =
        3 * t ^ 2 * d2 u t + t ^ 3 * d3 u t := by
    unfold d1
    calc
      deriv (d2ydx2 x y) t =
          deriv (fun s : ℝ => s ^ 3 * d2 u s) t :=
        hsecondeq.deriv_eq
      _ = 3 * t ^ 2 * d2 u t + t ^ 3 * d3 u t := hmodel.deriv
  unfold d3ydx3
  rw [hnum, d1_reciprocal_at_regular x hX ht]

theorem gap8 (u : ℝ → ℝ) :
    ∀ t, regular t →
      (3 * t ^ 2 * d2 u t + t ^ 3 * d3 u t) /
          (-(1 / t ^ 2)) =
        -t ^ 4 * (3 * d2 u t + t * d3 u t) := by
  intro t ht
  change t ≠ 0 at ht
  field_simp [ht] <;> ring

theorem gap9 (x y u : ℝ → ℝ)
    (hExpand :
      ∀ t, regular t →
        d3ydx3 x y t =
          (3 * t ^ 2 * d2 u t + t ^ 3 * d3 u t) /
            (-(1 / t ^ 2)))
    (hCancel :
      ∀ t, regular t →
        (3 * t ^ 2 * d2 u t + t ^ 3 * d3 u t) /
            (-(1 / t ^ 2)) =
          -t ^ 4 * (3 * d2 u t + t * d3 u t)) :
    ∀ t, regular t →
      d3ydx3 x y t =
        -t ^ 4 * (3 * d2 u t + t * d3 u t) := by
  intro t ht
  exact (hExpand t ht).trans (hCancel t ht)

theorem gap10 (x y u : ℝ → ℝ)
    (hODE :
      ∀ t, regular t →
        d3ydx3 x y t -
            (x t) ^ 3 * d2ydx2 x y t +
            x t * dydx x y t -
            y t =
          0)
    (hX : ∀ t, regular t → x t = 1 / t)
    (hY : ∀ t, regular t → y t = u t / t)
    (hFirst :
      ∀ t, regular t →
        dydx x y t = u t - t * d1 u t)
    (hSecond :
      ∀ t, regular t →
        d2ydx2 x y t = t ^ 3 * d2 u t)
    (hThird :
      ∀ t, regular t →
        d3ydx3 x y t =
          -t ^ 4 * (3 * d2 u t + t * d3 u t)) :
    ∀ t, regular t →
      t ^ 5 * d3 u t +
          (3 * t ^ 4 + 1) * d2 u t +
          d1 u t =
        0 := by
  intro t ht
  have ht0 : t ≠ 0 := ht
  have h := hODE t ht
  rw [hX t ht, hY t ht, hFirst t ht, hSecond t ht, hThird t ht] at h
  have halg :
      -t ^ 4 * (3 * d2 u t + t * d3 u t) -
              (1 / t) ^ 3 * (t ^ 3 * d2 u t) +
            (1 / t) * (u t - t * d1 u t) -
          u t / t =
        -(t ^ 5 * d3 u t +
            (3 * t ^ 4 + 1) * d2 u t +
            d1 u t) := by
    field_simp [ht0] <;> ring
  rw [halg] at h
  exact neg_eq_zero.mp h

end

end ProofGap.Exercise3443
