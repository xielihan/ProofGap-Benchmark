import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3456

noncomputable section

def d1 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv f t

def d2 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (deriv f) t

def regular (x r : ℝ → ℝ) (t : ℝ) : Prop :=
  0 < r t ∧ x t ≠ 0

def secondExpansion (x y r φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  x t *
      (y t / r t * d2 r t -
        y t / (r t) ^ 2 * (d1 r t) ^ 2 +
        1 / r t * d1 r t * d1 y t +
        d1 x t * d1 φ t + x t * d2 φ t) -
    y t *
      (x t / r t * d2 r t -
        x t / (r t) ^ 2 * (d1 r t) ^ 2 +
        1 / r t * d1 x t * d1 r t -
        d1 y t * d1 φ t - y t * d2 φ t)

def collectedSecond (x y r φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  d1 r t / r t * (x t * d1 y t - y t * d1 x t) +
    (x t * d1 x t + y t * d1 y t) * d1 φ t +
    ((x t) ^ 2 + (y t) ^ 2) * d2 φ t

private theorem eventually_regular_of_continuous {x r : ℝ → ℝ} {t : ℝ}
    (hx : Continuous x) (hr : Continuous r) (ht : regular x r t) :
    ∀ᶠ s in nhds t, regular x r s := by
  exact (continuousAt_const.eventually_lt hr.continuousAt ht.1).and
    (hx.continuousAt.eventually_ne ht.2)

private theorem hasDerivAt_deriv_of_contDiff_two {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (t : ℝ) :
    HasDerivAt (deriv f) (deriv (deriv f) t) t := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) := by
    apply ContDiff.fderiv_right
    · simpa using hf
    · norm_num
  have hone : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ)) := contDiff_const
  have hd : ContDiff ℝ 1 (deriv f) := by
    change ContDiff ℝ 1 (fun s : ℝ => (fderiv ℝ f s) 1)
    exact hfd.clm_apply hone
  exact (hd.differentiable (by norm_num)).differentiableAt.hasDerivAt

theorem gap1 (x y r : ℝ → ℝ)
    (hRadius :
      ∀ t, r t = Real.sqrt ((x t) ^ 2 + (y t) ^ 2))
    (hx : ContDiff ℝ 1 x)
    (hy : ContDiff ℝ 1 y) :
    ∀ t, regular x r t →
      d1 r t =
        (x t * d1 x t + y t * d1 y t) /
          Real.sqrt ((x t) ^ 2 + (y t) ^ 2) := by
  intro t ht
  have hx1 : HasDerivAt x (d1 x t) t := by
    unfold d1
    exact (hx.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hy1 : HasDerivAt y (d1 y t) t := by
    unfold d1
    exact (hy.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hs0 : HasDerivAt (fun s => x s * x s + y s * y s)
      (d1 x t * x t + x t * d1 x t +
        (d1 y t * y t + y t * d1 y t)) t := by
    change HasDerivAt (x * x + y * y) _ t
    exact (hx1.mul hx1).add (hy1.mul hy1)
  have hs : HasDerivAt (fun s => (x s) ^ 2 + (y s) ^ 2)
      (d1 x t * x t + x t * d1 x t +
        (d1 y t * y t + y t * d1 y t)) t := by
    simpa only [pow_two] using hs0
  have hsqrt_ne : Real.sqrt ((x t) ^ 2 + (y t) ^ 2) ≠ 0 := by
    rw [← hRadius t]
    exact ne_of_gt ht.1
  have hsum_ne : (x t) ^ 2 + (y t) ^ 2 ≠ 0 := by
    intro h
    apply hsqrt_ne
    rw [h]
    simp
  have hd := (Real.hasDerivAt_sqrt hsum_ne).comp t hs
  have hd' : HasDerivAt (fun s => Real.sqrt ((x s) ^ 2 + (y s) ^ 2))
      (1 / (2 * Real.sqrt ((x t) ^ 2 + (y t) ^ 2)) *
        (d1 x t * x t + x t * d1 x t +
          (d1 y t * y t + y t * d1 y t))) t := by
    simpa only [Function.comp_apply] using hd
  rw [show r = fun s => Real.sqrt ((x s) ^ 2 + (y s) ^ 2) from funext hRadius]
  unfold d1
  rw [hd'.deriv]
  simp only [d1]
  field_simp [hsqrt_ne] <;> ring

theorem gap2 (x y r : ℝ → ℝ)
    (hRadius :
      ∀ t, r t = Real.sqrt ((x t) ^ 2 + (y t) ^ 2)) :
    ∀ t, regular x r t →
      (x t * d1 x t + y t * d1 y t) /
          Real.sqrt ((x t) ^ 2 + (y t) ^ 2) =
        x t / r t * d1 x t + y t / r t * d1 y t := by
  intro t ht
  rw [← hRadius t]
  field_simp [ne_of_gt ht.1]

theorem gap3 (x y r : ℝ → ℝ)
    (hDifferentiate :
      ∀ t, regular x r t →
        d1 r t =
          (x t * d1 x t + y t * d1 y t) /
            Real.sqrt ((x t) ^ 2 + (y t) ^ 2))
    (hSubstitute :
      ∀ t, regular x r t →
        (x t * d1 x t + y t * d1 y t) /
            Real.sqrt ((x t) ^ 2 + (y t) ^ 2) =
          x t / r t * d1 x t + y t / r t * d1 y t) :
    ∀ t, regular x r t →
      d1 r t =
        x t / r t * d1 x t + y t / r t * d1 y t := by
  intro t ht
  exact (hDifferentiate t ht).trans (hSubstitute t ht)

theorem gap4 (x y r : ℝ → ℝ)
    (hRadial :
      ∀ t, regular x r t →
        d1 r t =
          x t / r t * d1 x t + y t / r t * d1 y t) :
    ∀ t, regular x r t →
      r t * d1 r t = x t * d1 x t + y t * d1 y t := by
  intro t ht
  have hr0 : r t ≠ 0 := ne_of_gt ht.1
  rw [hRadial t ht]
  field_simp [hr0]

theorem gap5 (x y φ r : ℝ → ℝ)
    (hRadius :
      ∀ t, r t = Real.sqrt ((x t) ^ 2 + (y t) ^ 2))
    (hAngle :
      ∀ t, regular x r t →
        φ t = Real.arctan (y t / x t))
    (hx : ContDiff ℝ 1 x)
    (hy : ContDiff ℝ 1 y) :
    ∀ t, regular x r t →
      d1 φ t =
        (x t * d1 y t - y t * d1 x t) /
          ((x t) ^ 2 + (y t) ^ 2) := by
  intro t ht
  have hrcont : Continuous r := by
    rw [show r = fun s => Real.sqrt ((x s) ^ 2 + (y s) ^ 2) from funext hRadius]
    exact ((hx.continuous.pow 2).add (hy.continuous.pow 2)).sqrt
  have hreg := eventually_regular_of_continuous hx.continuous hrcont ht
  have heq : φ =ᶠ[nhds t] (fun s => Real.arctan (y s / x s)) :=
    hreg.mono (fun s hs => hAngle s hs)
  have hx1 : HasDerivAt x (d1 x t) t := by
    unfold d1
    exact (hx.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hy1 : HasDerivAt y (d1 y t) t := by
    unfold d1
    exact (hy.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hquot := hy1.div hx1 ht.2
  have hquot' : HasDerivAt (fun s => y s / x s)
      ((d1 y t * x t - y t * d1 x t) / x t ^ 2) t := by
    change HasDerivAt (y / x) _ t
    exact hquot
  have harctan := (Real.hasDerivAt_arctan (y t / x t)).comp t hquot'
  have harctan' : HasDerivAt (fun s => Real.arctan (y s / x s))
      (1 / (1 + (y t / x t) ^ 2) *
        ((d1 y t * x t - y t * d1 x t) / x t ^ 2)) t := by
    simpa only [Function.comp_apply] using harctan
  change deriv φ t =
    (x t * deriv y t - y t * deriv x t) / ((x t) ^ 2 + (y t) ^ 2)
  rw [heq.deriv_eq, harctan'.deriv]
  simp only [d1]
  field_simp [ht.2] <;> ring

theorem gap6 (x y r : ℝ → ℝ)
    (hRadiusSquared :
      ∀ t, regular x r t →
        (r t) ^ 2 = (x t) ^ 2 + (y t) ^ 2) :
    ∀ t, regular x r t →
      (x t * d1 y t - y t * d1 x t) /
          ((x t) ^ 2 + (y t) ^ 2) =
        x t / (r t) ^ 2 * d1 y t -
          y t / (r t) ^ 2 * d1 x t := by
  intro t ht
  rw [← hRadiusSquared t ht]
  field_simp [ne_of_gt ht.1]

theorem gap7 (x y r φ : ℝ → ℝ)
    (hDifferentiate :
      ∀ t, regular x r t →
        d1 φ t =
          (x t * d1 y t - y t * d1 x t) /
            ((x t) ^ 2 + (y t) ^ 2))
    (hSubstitute :
      ∀ t, regular x r t →
        (x t * d1 y t - y t * d1 x t) /
            ((x t) ^ 2 + (y t) ^ 2) =
          x t / (r t) ^ 2 * d1 y t -
            y t / (r t) ^ 2 * d1 x t) :
    ∀ t, regular x r t →
      d1 φ t =
        x t / (r t) ^ 2 * d1 y t -
          y t / (r t) ^ 2 * d1 x t := by
  intro t ht
  exact (hDifferentiate t ht).trans (hSubstitute t ht)

theorem gap8 (x y r φ : ℝ → ℝ)
    (hAngular :
      ∀ t, regular x r t →
        d1 φ t =
          x t / (r t) ^ 2 * d1 y t -
            y t / (r t) ^ 2 * d1 x t) :
    ∀ t, regular x r t →
      (r t) ^ 2 * d1 φ t =
        x t * d1 y t - y t * d1 x t := by
  intro t ht
  have hr0 : r t ≠ 0 := ne_of_gt ht.1
  rw [hAngular t ht]
  field_simp [hr0]

theorem gap9 (x y r φ : ℝ → ℝ)
    (hRadial :
      ∀ t, regular x r t →
        r t * d1 r t = x t * d1 x t + y t * d1 y t)
    (hAngular :
      ∀ t, regular x r t →
        (r t) ^ 2 * d1 φ t =
          x t * d1 y t - y t * d1 x t) :
    ∀ t, regular x r t →
      x t * r t * d1 r t -
          y t * (r t) ^ 2 * d1 φ t =
        (x t) ^ 2 * d1 x t + x t * y t * d1 y t -
          (x t * y t * d1 y t - (y t) ^ 2 * d1 x t) := by
  intro t ht
  calc
    x t * r t * d1 r t - y t * (r t) ^ 2 * d1 φ t =
        x t * (r t * d1 r t) - y t * ((r t) ^ 2 * d1 φ t) := by ring
    _ = x t * (x t * d1 x t + y t * d1 y t) -
        y t * (x t * d1 y t - y t * d1 x t) := by
          rw [hRadial t ht, hAngular t ht]
    _ = (x t) ^ 2 * d1 x t + x t * y t * d1 y t -
          (x t * y t * d1 y t - (y t) ^ 2 * d1 x t) := by ring

theorem gap10 (x y : ℝ → ℝ) :
    ∀ t,
      (x t) ^ 2 * d1 x t + x t * y t * d1 y t -
          (x t * y t * d1 y t - (y t) ^ 2 * d1 x t) =
        ((x t) ^ 2 + (y t) ^ 2) * d1 x t := by
  intro t
  ring

theorem gap11 (x y r : ℝ → ℝ)
    (hRadiusSquared :
      ∀ t, regular x r t →
        (r t) ^ 2 = (x t) ^ 2 + (y t) ^ 2) :
    ∀ t, regular x r t →
      ((x t) ^ 2 + (y t) ^ 2) * d1 x t =
        (r t) ^ 2 * d1 x t := by
  intro t ht
  rw [hRadiusSquared t ht]

theorem gap12 (x y r φ : ℝ → ℝ)
    (hExpand :
      ∀ t, regular x r t →
        x t * r t * d1 r t -
            y t * (r t) ^ 2 * d1 φ t =
          (x t) ^ 2 * d1 x t + x t * y t * d1 y t -
            (x t * y t * d1 y t - (y t) ^ 2 * d1 x t))
    (hCollect :
      ∀ t,
        (x t) ^ 2 * d1 x t + x t * y t * d1 y t -
            (x t * y t * d1 y t - (y t) ^ 2 * d1 x t) =
          ((x t) ^ 2 + (y t) ^ 2) * d1 x t)
    (hRadius :
      ∀ t, regular x r t →
        ((x t) ^ 2 + (y t) ^ 2) * d1 x t =
          (r t) ^ 2 * d1 x t) :
    ∀ t, regular x r t →
      x t * r t * d1 r t -
          y t * (r t) ^ 2 * d1 φ t =
        (r t) ^ 2 * d1 x t := by
  intro t ht
  exact (hExpand t ht).trans ((hCollect t).trans (hRadius t ht))

theorem gap13 (x y r φ : ℝ → ℝ)
    (hEquation :
      ∀ t, regular x r t →
        x t * r t * d1 r t -
            y t * (r t) ^ 2 * d1 φ t =
          (r t) ^ 2 * d1 x t) :
    ∀ t, regular x r t →
      d1 x t = x t / r t * d1 r t - y t * d1 φ t := by
  intro t ht
  have hr0 : r t ≠ 0 := ne_of_gt ht.1
  have hr2 : (r t) ^ 2 ≠ 0 := pow_ne_zero 2 hr0
  apply mul_left_cancel₀ hr2
  rw [← hEquation t ht]
  field_simp [hr0] <;> ring

theorem gap14 (x y r φ : ℝ → ℝ)
    (hRadial :
      ∀ t, regular x r t →
        r t * d1 r t = x t * d1 x t + y t * d1 y t)
    (hAngular :
      ∀ t, regular x r t →
        (r t) ^ 2 * d1 φ t =
          x t * d1 y t - y t * d1 x t)
    (hRadiusSquared :
      ∀ t, regular x r t →
        (r t) ^ 2 = (x t) ^ 2 + (y t) ^ 2) :
    ∀ t, regular x r t →
      d1 y t = y t / r t * d1 r t + x t * d1 φ t := by
  intro t ht
  have hr0 : r t ≠ 0 := ne_of_gt ht.1
  have hR := hRadial t ht
  have hA := hAngular t ht
  have hS := hRadiusSquared t ht
  have hpoly : (r t) ^ 2 * d1 y t =
      r t * (y t * d1 r t + r t * x t * d1 φ t) := by
    calc
      (r t) ^ 2 * d1 y t = ((x t) ^ 2 + (y t) ^ 2) * d1 y t := by rw [hS]
      _ = y t * (x t * d1 x t + y t * d1 y t) +
          x t * (x t * d1 y t - y t * d1 x t) := by ring
      _ = y t * (r t * d1 r t) + x t * ((r t) ^ 2 * d1 φ t) := by
        rw [hR, hA]
      _ = r t * (y t * d1 r t + r t * x t * d1 φ t) := by ring
  field_simp [hr0]
  nlinarith [hpoly, ht.1]

theorem gap15 (x y r φ : ℝ → ℝ)
    (hXDerivative :
      ∀ t, regular x r t →
        d1 x t = x t / r t * d1 r t - y t * d1 φ t)
    (hYDerivative :
      ∀ t, regular x r t →
        d1 y t = y t / r t * d1 r t + x t * d1 φ t)
    (hx : ContDiff ℝ 2 x)
    (hy : ContDiff ℝ 2 y)
    (hr : ContDiff ℝ 2 r)
    (hφ : ContDiff ℝ 2 φ) :
    ∀ t, regular x r t →
      x t * d2 y t - y t * d2 x t =
        secondExpansion x y r φ t := by
  intro t ht
  have hr0 : r t ≠ 0 := ne_of_gt ht.1
  have hreg := eventually_regular_of_continuous hx.continuous hr.continuous ht
  have hxeq : (fun s => d1 x s) =ᶠ[nhds t]
      (fun s => x s / r s * d1 r s - y s * d1 φ s) :=
    hreg.mono (fun s hs => hXDerivative s hs)
  have hyeq : (fun s => d1 y s) =ᶠ[nhds t]
      (fun s => y s / r s * d1 r s + x s * d1 φ s) :=
    hreg.mono (fun s hs => hYDerivative s hs)
  have hx1 : HasDerivAt x (d1 x t) t := by
    unfold d1
    exact (hx.differentiable (by decide)).differentiableAt.hasDerivAt
  have hy1 : HasDerivAt y (d1 y t) t := by
    unfold d1
    exact (hy.differentiable (by decide)).differentiableAt.hasDerivAt
  have hr1 : HasDerivAt r (d1 r t) t := by
    unfold d1
    exact (hr.differentiable (by decide)).differentiableAt.hasDerivAt
  have hr2 : HasDerivAt (d1 r) (d2 r t) t := by
    change HasDerivAt (deriv r) (deriv (deriv r) t) t
    exact hasDerivAt_deriv_of_contDiff_two hr t
  have hφ2 : HasDerivAt (d1 φ) (d2 φ t) t := by
    change HasDerivAt (deriv φ) (deriv (deriv φ) t) t
    exact hasDerivAt_deriv_of_contDiff_two hφ t
  have hxp : HasDerivAt
      (fun s => x s / r s * d1 r s - y s * d1 φ s)
      (((d1 x t * r t - x t * d1 r t) / (r t) ^ 2) * d1 r t +
        x t / r t * d2 r t -
        (d1 y t * d1 φ t + y t * d2 φ t)) t := by
    convert ((hx1.div hr1 hr0).mul hr2).sub (hy1.mul hφ2) using 1 <;> ring
  have hyp : HasDerivAt
      (fun s => y s / r s * d1 r s + x s * d1 φ s)
      (((d1 y t * r t - y t * d1 r t) / (r t) ^ 2) * d1 r t +
        y t / r t * d2 r t +
        (d1 x t * d1 φ t + x t * d2 φ t)) t := by
    convert ((hy1.div hr1 hr0).mul hr2).add (hx1.mul hφ2) using 1 <;> ring
  have hdx : d2 x t =
      ((d1 x t * r t - x t * d1 r t) / (r t) ^ 2) * d1 r t +
        x t / r t * d2 r t -
        (d1 y t * d1 φ t + y t * d2 φ t) := by
    calc
      d2 x t = deriv (fun s => x s / r s * d1 r s - y s * d1 φ s) t := by
        simpa [d1, d2] using hxeq.deriv_eq
      _ = _ := hxp.deriv
  have hdy : d2 y t =
      ((d1 y t * r t - y t * d1 r t) / (r t) ^ 2) * d1 r t +
        y t / r t * d2 r t +
        (d1 x t * d1 φ t + x t * d2 φ t) := by
    calc
      d2 y t = deriv (fun s => y s / r s * d1 r s + x s * d1 φ s) t := by
        simpa [d1, d2] using hyeq.deriv_eq
      _ = _ := hyp.deriv
  unfold secondExpansion
  rw [hdx, hdy]
  field_simp [hr0]
  ring

theorem gap16 (x y r φ : ℝ → ℝ) :
    ∀ t, regular x r t →
      secondExpansion x y r φ t =
        collectedSecond x y r φ t := by
  intro t ht
  have hr0 : r t ≠ 0 := ne_of_gt ht.1
  unfold secondExpansion collectedSecond
  field_simp [hr0]
  ring

theorem gap17 (x y r φ : ℝ → ℝ)
    (hRadial :
      ∀ t, regular x r t →
        r t * d1 r t = x t * d1 x t + y t * d1 y t)
    (hAngular :
      ∀ t, regular x r t →
        (r t) ^ 2 * d1 φ t =
          x t * d1 y t - y t * d1 x t)
    (hRadiusSquared :
      ∀ t, regular x r t →
        (r t) ^ 2 = (x t) ^ 2 + (y t) ^ 2) :
    ∀ t, regular x r t →
      collectedSecond x y r φ t =
        2 * r t * d1 r t * d1 φ t +
          (r t) ^ 2 * d2 φ t := by
  intro t ht
  have hr0 : r t ≠ 0 := ne_of_gt ht.1
  unfold collectedSecond
  rw [← hAngular t ht, ← hRadial t ht, ← hRadiusSquared t ht]
  field_simp [hr0]
  ring

theorem gap18 (x y r φ : ℝ → ℝ)
    (hExpand :
      ∀ t, regular x r t →
        x t * d2 y t - y t * d2 x t =
          secondExpansion x y r φ t)
    (hCollect :
      ∀ t, regular x r t →
        secondExpansion x y r φ t =
          collectedSecond x y r φ t)
    (hSubstitute :
      ∀ t, regular x r t →
        collectedSecond x y r φ t =
          2 * r t * d1 r t * d1 φ t +
            (r t) ^ 2 * d2 φ t) :
    ∀ t, regular x r t →
      x t * d2 y t - y t * d2 x t =
        2 * r t * d1 r t * d1 φ t +
          (r t) ^ 2 * d2 φ t := by
  intro t ht
  exact (hExpand t ht).trans ((hCollect t ht).trans (hSubstitute t ht))

theorem gap19 (W x y : ℝ → ℝ)
    (hW : ∀ t, W t = x t * d2 y t - y t * d2 x t) :
    ∀ t, W t = x t * d2 y t - y t * d2 x t := by
  exact hW

theorem gap20 (W x y r φ : ℝ → ℝ)
    (hW : ∀ t, W t = x t * d2 y t - y t * d2 x t)
    (hTransform :
      ∀ t, regular x r t →
        x t * d2 y t - y t * d2 x t =
          2 * r t * d1 r t * d1 φ t +
            (r t) ^ 2 * d2 φ t) :
    ∀ t, regular x r t →
      W t =
        2 * r t * d1 r t * d1 φ t +
          (r t) ^ 2 * d2 φ t := by
  intro t ht
  exact (hW t).trans (hTransform t ht)

theorem gap21 (r φ : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r)
    (hφ : ContDiff ℝ 2 φ) :
    ∀ t,
      2 * r t * d1 r t * d1 φ t +
          (r t) ^ 2 * d2 φ t =
        d1 (fun s => (r s) ^ 2 * d1 φ s) t := by
  intro t
  have hr1 : HasDerivAt r (d1 r t) t := by
    unfold d1
    exact (hr.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hφ2 : HasDerivAt (d1 φ) (d2 φ t) t := by
    change HasDerivAt (deriv φ) (deriv (deriv φ) t) t
    exact hasDerivAt_deriv_of_contDiff_two hφ t
  have hp : HasDerivAt (fun s => (r s) ^ 2 * d1 φ s)
      ((d1 r t * r t + r t * d1 r t) * d1 φ t +
        (r t) ^ 2 * d2 φ t) t := by
    simpa only [pow_two] using (hr1.mul hr1).mul hφ2
  calc
    2 * r t * d1 r t * d1 φ t + (r t) ^ 2 * d2 φ t =
        (d1 r t * r t + r t * d1 r t) * d1 φ t +
          (r t) ^ 2 * d2 φ t := by ring
    _ = d1 (fun s => (r s) ^ 2 * d1 φ s) t := by
      unfold d1
      exact hp.deriv.symm

theorem gap22 (W x r φ : ℝ → ℝ)
    (hW :
      ∀ t, regular x r t →
        W t =
          2 * r t * d1 r t * d1 φ t +
            (r t) ^ 2 * d2 φ t)
    (hProduct :
      ∀ t,
        2 * r t * d1 r t * d1 φ t +
            (r t) ^ 2 * d2 φ t =
          d1 (fun s => (r s) ^ 2 * d1 φ s) t) :
    ∀ t, regular x r t →
      W t = d1 (fun s => (r s) ^ 2 * d1 φ s) t := by
  intro t ht
  exact (hW t ht).trans (hProduct t)

end

end ProofGap.Exercise3456
