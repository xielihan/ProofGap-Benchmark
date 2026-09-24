import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3416

noncomputable section

open Filter

def partial1 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f t y z) x

def partial2 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f x t z) y

def partial3 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f x y t) z

def partial11 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partial1 f t y z) x

def partial12 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partial1 f x t z) y

def partial13 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partial1 f x y t) z

def partial22 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partial2 f x t z) y

def partial23 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partial2 f x y t) z

def partial33 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partial3 f x y t) z

def firstDerivative (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv f x

def secondDerivative (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv f) x

def linear3 (f : ℝ → ℝ → ℝ → ℝ)
    (x y z dx dy dz : ℝ) : ℝ :=
  partial1 f x y z * dx +
    partial2 f x y z * dy +
    partial3 f x y z * dz

def quadratic3 (f : ℝ → ℝ → ℝ → ℝ)
    (x y z dx dy dz : ℝ) : ℝ :=
  partial11 f x y z * dx ^ 2 +
    2 * partial12 f x y z * dx * dy +
    2 * partial13 f x y z * dx * dz +
    partial22 f x y z * dy ^ 2 +
    2 * partial23 f x y z * dy * dz +
    partial33 f x y z * dz ^ 2

def minor1 (g h : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  partial2 g x y z * partial3 h x y z -
    partial3 g x y z * partial2 h x y z

def minor2 (g h : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  partial3 g x y z * partial1 h x y z -
    partial1 g x y z * partial3 h x y z

def minor3 (g h : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  partial1 g x y z * partial2 h x y z -
    partial2 g x y z * partial1 h x y z

def jacobian3 (f g h : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  partial1 f x y z * minor1 g h x y z +
    partial2 f x y z * minor2 g h x y z +
    partial3 f x y z * minor3 g h x y z

def minor4 (f h : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  partial2 h x y z * partial3 f x y z -
    partial3 h x y z * partial2 f x y z

def minor5 (f g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  partial2 f x y z * partial3 g x y z -
    partial3 f x y z * partial2 g x y z

def scaledQuadratic (f : ℝ → ℝ → ℝ → ℝ)
    (x y z I1 I2 I3 : ℝ) : ℝ :=
  quadratic3 f x y z I1 I2 I3

private abbrev Vec3 := ℝ × (ℝ × ℝ)

private def uncurry3 (f : ℝ → ℝ → ℝ → ℝ) : Vec3 → ℝ :=
  fun p => f p.1 p.2.1 p.2.2

private theorem partials_eq_fderiv3_at
    (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ)
    (hf : DifferentiableAt ℝ (uncurry3 f) (x, (y, z))) :
    partial1 f x y z =
        fderiv ℝ (uncurry3 f) (x, (y, z))
          ((1, (0, 0)) : Vec3) ∧
      partial2 f x y z =
        fderiv ℝ (uncurry3 f) (x, (y, z))
          ((0, (1, 0)) : Vec3) ∧
      partial3 f x y z =
        fderiv ℝ (uncurry3 f) (x, (y, z))
          ((0, (0, 1)) : Vec3) := by
  constructor
  · have hp :=
      (hasDerivAt_id x).hasFDerivAt.prodMk
        ((hasDerivAt_const (x := x) y).hasFDerivAt.prodMk
          (hasDerivAt_const (x := x) z).hasFDerivAt)
    have h := hf.hasFDerivAt.comp x hp
    simpa [partial1, uncurry3, Function.comp_def] using h.hasDerivAt.deriv
  constructor
  · have hp :=
      (hasDerivAt_const (x := y) x).hasFDerivAt.prodMk
        ((hasDerivAt_id y).hasFDerivAt.prodMk
          (hasDerivAt_const (x := y) z).hasFDerivAt)
    have h := hf.hasFDerivAt.comp y hp
    simpa [partial2, uncurry3, Function.comp_def] using h.hasDerivAt.deriv
  · have hp :=
      (hasDerivAt_const (x := z) x).hasFDerivAt.prodMk
        ((hasDerivAt_const (x := z) y).hasFDerivAt.prodMk
          (hasDerivAt_id z).hasFDerivAt)
    have h := hf.hasFDerivAt.comp z hp
    simpa [partial3, uncurry3, Function.comp_def] using h.hasDerivAt.deriv

private theorem hasDerivAt_comp3
    (f : ℝ → ℝ → ℝ → ℝ) (A B C : ℝ → ℝ)
    {x dA dB dC : ℝ}
    (hf : DifferentiableAt ℝ (uncurry3 f) (A x, (B x, C x)))
    (hA : HasDerivAt A dA x) (hB : HasDerivAt B dB x)
    (hC : HasDerivAt C dC x) :
    HasDerivAt (fun t => f (A t) (B t) (C t))
      (partial1 f (A x) (B x) (C x) * dA +
        partial2 f (A x) (B x) (C x) * dB +
        partial3 f (A x) (B x) (C x) * dC) x := by
  let D := fderiv ℝ (uncurry3 f) (A x, (B x, C x))
  have hc := hf.hasFDerivAt.comp x
    (hA.hasFDerivAt.prodMk
      (hB.hasFDerivAt.prodMk hC.hasFDerivAt))
  have hc' :
      HasDerivAt (fun t => f (A t) (B t) (C t))
        (D (dA, (dB, dC))) x := by
    simpa [D, uncurry3, Function.comp_def] using hc.hasDerivAt
  obtain ⟨h1, h2, h3⟩ :=
    partials_eq_fderiv3_at f (A x) (B x) (C x) hf
  have hvec :
      ((dA, (dB, dC)) : Vec3) =
        dA • ((1, (0, 0)) : Vec3) +
          dB • ((0, (1, 0)) : Vec3) +
          dC • ((0, (0, 1)) : Vec3) := by
    ext <;> simp
  convert hc' using 1
  rw [hvec, map_add, map_add, map_smul, map_smul, map_smul,
    ← h1, ← h2, ← h3]
  simp [smul_eq_mul]
  ring

private theorem differentiableAt_uncurry_partials3
    (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ)
    (hf : ContDiffAt ℝ 2 (uncurry3 f) (x, (y, z))) :
    DifferentiableAt ℝ (uncurry3 (partial1 f)) (x, (y, z)) ∧
      DifferentiableAt ℝ (uncurry3 (partial2 f)) (x, (y, z)) ∧
      DifferentiableAt ℝ (uncurry3 (partial3 f)) (x, (y, z)) := by
  let F := uncurry3 f
  let e1 : Vec3 := (1, (0, 0))
  let e2 : Vec3 := (0, (1, 0))
  let e3 : Vec3 := (0, (0, 1))
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ F) (x, (y, z)) := by
    simpa [F] using hf.fderiv_right (by norm_num)
  have hnear : ∀ᶠ q : Vec3 in nhds (x, (y, z)),
      DifferentiableAt ℝ F q := by
    filter_upwards [hf.eventually (by decide)] with q hq
    exact hq.differentiableAt (by decide)
  have makeDiff (e : Vec3) :
      DifferentiableAt ℝ (fun q : Vec3 => fderiv ℝ F q e)
        (x, (y, z)) := by
    let ev : (Vec3 →L[ℝ] ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.apply ℝ ℝ e
    simpa [ev, Function.comp_def] using
      ev.differentiableAt.comp (x, (y, z))
        (hfd.differentiableAt (by decide))
  have hEq1 :
      uncurry3 (partial1 f) =ᶠ[nhds (x, (y, z))]
        fun q : Vec3 => fderiv ℝ F q e1 := by
    filter_upwards [hnear] with q hq
    simpa [F, e1, uncurry3] using
      (partials_eq_fderiv3_at f q.1 q.2.1 q.2.2 hq).1
  have hEq2 :
      uncurry3 (partial2 f) =ᶠ[nhds (x, (y, z))]
        fun q : Vec3 => fderiv ℝ F q e2 := by
    filter_upwards [hnear] with q hq
    simpa [F, e2, uncurry3] using
      (partials_eq_fderiv3_at f q.1 q.2.1 q.2.2 hq).2.1
  have hEq3 :
      uncurry3 (partial3 f) =ᶠ[nhds (x, (y, z))]
        fun q : Vec3 => fderiv ℝ F q e3 := by
    filter_upwards [hnear] with q hq
    simpa [F, e3, uncurry3] using
      (partials_eq_fderiv3_at f q.1 q.2.1 q.2.2 hq).2.2
  exact ⟨(makeDiff e1).congr_of_eventuallyEq hEq1,
    (makeDiff e2).congr_of_eventuallyEq hEq2,
    (makeDiff e3).congr_of_eventuallyEq hEq3⟩

private theorem mixed_partials3_at
    (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ)
    (hf : ContDiffAt ℝ 2 (uncurry3 f) (x, (y, z))) :
    partial1 (partial2 f) x y z = partial12 f x y z ∧
      partial1 (partial3 f) x y z = partial13 f x y z ∧
      partial2 (partial3 f) x y z = partial23 f x y z := by
  let F := uncurry3 f
  let H := fderiv ℝ (fderiv ℝ F) (x, (y, z))
  let e1 : Vec3 := (1, (0, 0))
  let e2 : Vec3 := (0, (1, 0))
  let e3 : Vec3 := (0, (0, 1))
  have hnear : ∀ᶠ q : Vec3 in nhds (x, (y, z)),
      DifferentiableAt ℝ F q := by
    filter_upwards [hf.eventually (by decide)] with q hq
    exact hq.differentiableAt (by decide)
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ F) (x, (y, z)) := by
    simpa [F] using hf.fderiv_right (by norm_num)
  have hFD : HasFDerivAt (fderiv ℝ F) H (x, (y, z)) := by
    simpa [H] using (hfd.differentiableAt (by decide)).hasFDerivAt
  have hnearX :=
    (continuousAt_id.prodMk
      (continuousAt_const.prodMk continuousAt_const)).eventually hnear
  have hnearY :=
    (continuousAt_const.prodMk
      (continuousAt_id.prodMk continuousAt_const)).eventually hnear
  have hnearZ :=
    (continuousAt_const.prodMk
      (continuousAt_const.prodMk continuousAt_id)).eventually hnear
  have hp2x :
      (fun t : ℝ => partial2 f t y z) =ᶠ[nhds x]
        fun t => fderiv ℝ F (t, (y, z)) e2 := by
    filter_upwards [hnearX] with t ht
    simpa [F, e2] using
      (partials_eq_fderiv3_at f t y z ht).2.1
  have hp1y :
      (fun t : ℝ => partial1 f x t z) =ᶠ[nhds y]
        fun t => fderiv ℝ F (x, (t, z)) e1 := by
    filter_upwards [hnearY] with t ht
    simpa [F, e1] using
      (partials_eq_fderiv3_at f x t z ht).1
  have hp3x :
      (fun t : ℝ => partial3 f t y z) =ᶠ[nhds x]
        fun t => fderiv ℝ F (t, (y, z)) e3 := by
    filter_upwards [hnearX] with t ht
    simpa [F, e3] using
      (partials_eq_fderiv3_at f t y z ht).2.2
  have hp1z :
      (fun t : ℝ => partial1 f x y t) =ᶠ[nhds z]
        fun t => fderiv ℝ F (x, (y, t)) e1 := by
    filter_upwards [hnearZ] with t ht
    simpa [F, e1] using
      (partials_eq_fderiv3_at f x y t ht).1
  have hp3y :
      (fun t : ℝ => partial3 f x t z) =ᶠ[nhds y]
        fun t => fderiv ℝ F (x, (t, z)) e3 := by
    filter_upwards [hnearY] with t ht
    simpa [F, e3] using
      (partials_eq_fderiv3_at f x t z ht).2.2
  have hp2z :
      (fun t : ℝ => partial2 f x y t) =ᶠ[nhds z]
        fun t => fderiv ℝ F (x, (y, t)) e2 := by
    filter_upwards [hnearZ] with t ht
    simpa [F, e2] using
      (partials_eq_fderiv3_at f x y t ht).2.1
  let ev1 : (Vec3 →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ e1
  let ev2 : (Vec3 →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ e2
  let ev3 : (Vec3 →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ e3
  have hout2x :
      HasDerivAt (fun t : ℝ => fderiv ℝ F (t, (y, z)) e2)
        (H e1 e2) x := by
    have hh := (ev2.hasFDerivAt.comp (x, (y, z)) hFD).comp x
      ((hasDerivAt_id x).hasFDerivAt.prodMk
        ((hasDerivAt_const x y).hasFDerivAt.prodMk
          (hasDerivAt_const x z).hasFDerivAt))
    simpa [ev2, e1, e2, Function.comp_def] using hh.hasDerivAt
  have hout1y :
      HasDerivAt (fun t : ℝ => fderiv ℝ F (x, (t, z)) e1)
        (H e2 e1) y := by
    have hh := (ev1.hasFDerivAt.comp (x, (y, z)) hFD).comp y
      ((hasDerivAt_const y x).hasFDerivAt.prodMk
        ((hasDerivAt_id y).hasFDerivAt.prodMk
          (hasDerivAt_const y z).hasFDerivAt))
    simpa [ev1, e1, e2, Function.comp_def] using hh.hasDerivAt
  have hout3x :
      HasDerivAt (fun t : ℝ => fderiv ℝ F (t, (y, z)) e3)
        (H e1 e3) x := by
    have hh := (ev3.hasFDerivAt.comp (x, (y, z)) hFD).comp x
      ((hasDerivAt_id x).hasFDerivAt.prodMk
        ((hasDerivAt_const x y).hasFDerivAt.prodMk
          (hasDerivAt_const x z).hasFDerivAt))
    simpa [ev3, e1, e3, Function.comp_def] using hh.hasDerivAt
  have hout1z :
      HasDerivAt (fun t : ℝ => fderiv ℝ F (x, (y, t)) e1)
        (H e3 e1) z := by
    have hh := (ev1.hasFDerivAt.comp (x, (y, z)) hFD).comp z
      ((hasDerivAt_const z x).hasFDerivAt.prodMk
        ((hasDerivAt_const z y).hasFDerivAt.prodMk
          (hasDerivAt_id z).hasFDerivAt))
    simpa [ev1, e1, e3, Function.comp_def] using hh.hasDerivAt
  have hout3y :
      HasDerivAt (fun t : ℝ => fderiv ℝ F (x, (t, z)) e3)
        (H e2 e3) y := by
    have hh := (ev3.hasFDerivAt.comp (x, (y, z)) hFD).comp y
      ((hasDerivAt_const y x).hasFDerivAt.prodMk
        ((hasDerivAt_id y).hasFDerivAt.prodMk
          (hasDerivAt_const y z).hasFDerivAt))
    simpa [ev3, e2, e3, Function.comp_def] using hh.hasDerivAt
  have hout2z :
      HasDerivAt (fun t : ℝ => fderiv ℝ F (x, (y, t)) e2)
        (H e3 e2) z := by
    have hh := (ev2.hasFDerivAt.comp (x, (y, z)) hFD).comp z
      ((hasDerivAt_const z x).hasFDerivAt.prodMk
        ((hasDerivAt_const z y).hasFDerivAt.prodMk
          (hasDerivAt_id z).hasFDerivAt))
    simpa [ev2, e2, e3, Function.comp_def] using hh.hasDerivAt
  have h12L : partial1 (partial2 f) x y z = H e1 e2 := by
    unfold partial1
    exact hp2x.deriv_eq.trans hout2x.deriv
  have h12R : partial12 f x y z = H e2 e1 := by
    unfold partial12
    exact hp1y.deriv_eq.trans hout1y.deriv
  have h13L : partial1 (partial3 f) x y z = H e1 e3 := by
    unfold partial1
    exact hp3x.deriv_eq.trans hout3x.deriv
  have h13R : partial13 f x y z = H e3 e1 := by
    unfold partial13
    exact hp1z.deriv_eq.trans hout1z.deriv
  have h23L : partial2 (partial3 f) x y z = H e2 e3 := by
    unfold partial2
    exact hp3y.deriv_eq.trans hout3y.deriv
  have h23R : partial23 f x y z = H e3 e2 := by
    unfold partial23
    exact hp2z.deriv_eq.trans hout2z.deriv
  have hs12 : H e1 e2 = H e2 e1 := by
    simpa [H, F, e1, e2] using
      hf.isSymmSndFDerivAt (by norm_num) e1 e2
  have hs13 : H e1 e3 = H e3 e1 := by
    simpa [H, F, e1, e3] using
      hf.isSymmSndFDerivAt (by norm_num) e1 e3
  have hs23 : H e2 e3 = H e3 e2 := by
    simpa [H, F, e2, e3] using
      hf.isSymmSndFDerivAt (by norm_num) e2 e3
  exact ⟨h12L.trans (hs12.trans h12R.symm),
    h13L.trans (hs13.trans h13R.symm),
    h23L.trans (hs23.trans h23R.symm)⟩

private theorem eventually_deriv_eq
    {a b : ℝ → ℝ} {x : ℝ} (h : a =ᶠ[nhds x] b) :
    (fun t => deriv a t) =ᶠ[nhds x] fun t => deriv b t := by
  rcases mem_nhds_iff.mp h with ⟨s, hs, hsOpen, hxs⟩
  filter_upwards [hsOpen.mem_nhds hxs] with t ht
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hsOpen.mem_nhds ht] with r hr
  exact hs hr

private theorem second_chain3_at
    (f : ℝ → ℝ → ℝ → ℝ) (y z : ℝ → ℝ) (x : ℝ)
    (hf : ContDiffAt ℝ 2 (uncurry3 f) (x, (y x, z x)))
    (hy : ContDiffAt ℝ 2 y x) (hz : ContDiffAt ℝ 2 z x) :
    secondDerivative (fun t => f t (y t) (z t)) x =
      quadratic3 f x (y x) (z x)
          1 (firstDerivative y x) (firstDerivative z x) +
        partial2 f x (y x) (z x) * secondDerivative y x +
        partial3 f x (y x) (z x) * secondDerivative z x := by
  let c : ℝ → Vec3 := fun t => (t, (y t, z t))
  have hc : ContinuousAt c x := by
    exact continuousAt_id.prodMk (hy.continuousAt.prodMk hz.continuousAt)
  have hfNear :
      ∀ᶠ t in nhds x, ContDiffAt ℝ 2 (uncurry3 f) (c t) :=
    hc.eventually (hf.eventually (by decide))
  have hyNear : ∀ᶠ t in nhds x, ContDiffAt ℝ 2 y t :=
    hy.eventually (by decide)
  have hzNear : ∀ᶠ t in nhds x, ContDiffAt ℝ 2 z t :=
    hz.eventually (by decide)
  have hfirst :
      (fun t => deriv (fun r => f r (y r) (z r)) t) =ᶠ[nhds x]
        fun t =>
          partial1 f t (y t) (z t) +
            partial2 f t (y t) (z t) * deriv y t +
            partial3 f t (y t) (z t) * deriv z t := by
    filter_upwards [hfNear, hyNear, hzNear] with t hft hyt hzt
    simpa only [mul_one] using
      (hasDerivAt_comp3 f (fun r : ℝ => r) y z
      (hft.differentiableAt (by decide)) (hasDerivAt_id t)
      (hyt.differentiableAt (by decide)).hasDerivAt
      (hzt.differentiableAt (by decide)).hasDerivAt).deriv
  obtain ⟨h1d, h2d, h3d⟩ :=
    differentiableAt_uncurry_partials3 f x (y x) (z x) hf
  obtain ⟨hm12, hm13, hm23⟩ :=
    mixed_partials3_at f x (y x) (z x) hf
  have hyAt := (hy.differentiableAt (by decide)).hasDerivAt
  have hzAt := (hz.differentiableAt (by decide)).hasDerivAt
  have h1raw := hasDerivAt_comp3 (partial1 f) (fun t : ℝ => t) y z
    h1d (hasDerivAt_id x) hyAt hzAt
  have h1 :
      HasDerivAt (fun t => partial1 f t (y t) (z t))
        (partial11 f x (y x) (z x) +
          partial12 f x (y x) (z x) * deriv y x +
          partial13 f x (y x) (z x) * deriv z x) x := by
    simpa [partial11, partial12, partial13] using h1raw
  have h2raw := hasDerivAt_comp3 (partial2 f) (fun t : ℝ => t) y z
    h2d (hasDerivAt_id x) hyAt hzAt
  have h2 :
      HasDerivAt (fun t => partial2 f t (y t) (z t))
        (partial12 f x (y x) (z x) +
          partial22 f x (y x) (z x) * deriv y x +
          partial23 f x (y x) (z x) * deriv z x) x := by
    convert h2raw using 1
    rw [hm12]
    change
      partial12 f x (y x) (z x) +
          partial22 f x (y x) (z x) * deriv y x +
          partial23 f x (y x) (z x) * deriv z x =
        partial12 f x (y x) (z x) * 1 +
          partial22 f x (y x) (z x) * deriv y x +
          partial23 f x (y x) (z x) * deriv z x
    ring
  have h3raw := hasDerivAt_comp3 (partial3 f) (fun t : ℝ => t) y z
    h3d (hasDerivAt_id x) hyAt hzAt
  have h3 :
      HasDerivAt (fun t => partial3 f t (y t) (z t))
        (partial13 f x (y x) (z x) +
          partial23 f x (y x) (z x) * deriv y x +
          partial33 f x (y x) (z x) * deriv z x) x := by
    convert h3raw using 1
    rw [hm13, hm23]
    change
      partial13 f x (y x) (z x) +
          partial23 f x (y x) (z x) * deriv y x +
          partial33 f x (y x) (z x) * deriv z x =
        partial13 f x (y x) (z x) * 1 +
          partial23 f x (y x) (z x) * deriv y x +
          partial33 f x (y x) (z x) * deriv z x
    ring
  have hy1 :
      HasDerivAt (deriv y) (deriv (deriv y) x) x := by
    simpa using
      (hy.derivWithin (m := 1) (by norm_num)).differentiableAt
        (by decide) |>.hasDerivAt
  have hz1 :
      HasDerivAt (deriv z) (deriv (deriv z) x) x := by
    simpa using
      (hz.derivWithin (m := 1) (by norm_num)).differentiableAt
        (by decide) |>.hasDerivAt
  have hsum := h1.add ((h2.mul hy1).add (h3.mul hz1))
  have hsumFunction :
      (fun t =>
          partial1 f t (y t) (z t) +
            partial2 f t (y t) (z t) * deriv y t +
            partial3 f t (y t) (z t) * deriv z t) =
        (fun t => partial1 f t (y t) (z t)) +
          ((fun t => partial2 f t (y t) (z t)) * deriv y +
            (fun t => partial3 f t (y t) (z t)) * deriv z) := by
    funext t
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  change
    deriv (deriv (fun t => f t (y t) (z t))) x =
      quadratic3 f x (y x) (z x) 1 (deriv y x) (deriv z x) +
        partial2 f x (y x) (z x) * deriv (deriv y) x +
        partial3 f x (y x) (z x) * deriv (deriv z) x
  rw [hfirst.deriv_eq, hsumFunction, hsum.deriv]
  unfold quadratic3
  ring

theorem gap1 (f : ℝ → ℝ → ℝ → ℝ) (u y z : ℝ → ℝ) (x dx : ℝ)
    (hfDiff : DifferentiableAt ℝ
      (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) (x, y x, z x))
    (huDiff : DifferentiableAt ℝ u x)
    (hyDiff : DifferentiableAt ℝ y x)
    (hzDiff : DifferentiableAt ℝ z x)
    (hU : ∀ᶠ t in nhds x, u t = f t (y t) (z t)) :
    firstDerivative u x * dx =
      partial1 f x (y x) (z x) * dx +
        partial2 f x (y x) (z x) * (firstDerivative y x * dx) +
        partial3 f x (y x) (z x) * (firstDerivative z x * dx) := by
  have hchain := hasDerivAt_comp3 f (fun t : ℝ => t) y z
    hfDiff (hasDerivAt_id x) hyDiff.hasDerivAt hzDiff.hasDerivAt
  unfold firstDerivative
  rw [Filter.EventuallyEq.deriv_eq hU, hchain.deriv]
  ring

theorem gap2 (f : ℝ → ℝ → ℝ → ℝ) (x y z dx dy dz : ℝ) :
    partial1 f x y z * dx + partial2 f x y z * dy +
        partial3 f x y z * dz =
      dx * partial1 f x y z + dy * partial2 f x y z +
        dz * partial3 f x y z := by
  ring

theorem gap3 (f : ℝ → ℝ → ℝ → ℝ) (u y z : ℝ → ℝ) (x dx : ℝ)
    (h1 : firstDerivative u x * dx =
      partial1 f x (y x) (z x) * dx +
        partial2 f x (y x) (z x) * (firstDerivative y x * dx) +
        partial3 f x (y x) (z x) * (firstDerivative z x * dx))
    (h2 : partial1 f x (y x) (z x) * dx +
        partial2 f x (y x) (z x) * (firstDerivative y x * dx) +
        partial3 f x (y x) (z x) * (firstDerivative z x * dx) =
      dx * partial1 f x (y x) (z x) +
        (firstDerivative y x * dx) * partial2 f x (y x) (z x) +
        (firstDerivative z x * dx) * partial3 f x (y x) (z x)) :
    firstDerivative u x * dx =
      dx * partial1 f x (y x) (z x) +
        (firstDerivative y x * dx) * partial2 f x (y x) (z x) +
        (firstDerivative z x * dx) * partial3 f x (y x) (z x) := by
  exact h1.trans h2

theorem gap4 (g : ℝ → ℝ → ℝ → ℝ) (y z : ℝ → ℝ) (x dx : ℝ)
    (hgDiff : DifferentiableAt ℝ
      (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) (x, y x, z x))
    (hyDiff : DifferentiableAt ℝ y x)
    (hzDiff : DifferentiableAt ℝ z x)
    (hG : ∀ᶠ t in nhds x, g t (y t) (z t) = 0) :
    0 = partial1 g x (y x) (z x) * dx +
      partial2 g x (y x) (z x) * (firstDerivative y x * dx) +
      partial3 g x (y x) (z x) * (firstDerivative z x * dx) := by
  have hchain := hasDerivAt_comp3 g (fun t : ℝ => t) y z
    hgDiff (hasDerivAt_id x) hyDiff.hasDerivAt hzDiff.hasDerivAt
  have hz0 : deriv (fun t => g t (y t) (z t)) x = 0 := by
    rw [Filter.EventuallyEq.deriv_eq hG]
    simp
  rw [hchain.deriv] at hz0
  have hz0' :
      partial1 g x (y x) (z x) +
          partial2 g x (y x) (z x) * deriv y x +
          partial3 g x (y x) (z x) * deriv z x = 0 := by
    simpa only [id_eq, mul_one] using hz0
  unfold firstDerivative
  calc
    0 = (partial1 g x (y x) (z x) +
        partial2 g x (y x) (z x) * deriv y x +
        partial3 g x (y x) (z x) * deriv z x) * dx := by
      rw [hz0']
      ring
    _ = _ := by ring

theorem gap5 (g : ℝ → ℝ → ℝ → ℝ) (x y z dx dy dz : ℝ) :
    partial1 g x y z * dx + partial2 g x y z * dy +
        partial3 g x y z * dz =
      dx * partial1 g x y z + dy * partial2 g x y z +
        dz * partial3 g x y z := by
  ring

theorem gap6 (g : ℝ → ℝ → ℝ → ℝ) (x y z dx dy dz : ℝ)
    (h1 : 0 = partial1 g x y z * dx + partial2 g x y z * dy +
      partial3 g x y z * dz)
    (h2 : partial1 g x y z * dx + partial2 g x y z * dy +
        partial3 g x y z * dz =
      dx * partial1 g x y z + dy * partial2 g x y z +
        dz * partial3 g x y z) :
    0 = dx * partial1 g x y z + dy * partial2 g x y z +
      dz * partial3 g x y z := by
  exact h1.trans h2

theorem gap7 (h : ℝ → ℝ → ℝ → ℝ) (y z : ℝ → ℝ) (x dx : ℝ)
    (hhDiff : DifferentiableAt ℝ
      (fun p : ℝ × ℝ × ℝ => h p.1 p.2.1 p.2.2) (x, y x, z x))
    (hyDiff : DifferentiableAt ℝ y x)
    (hzDiff : DifferentiableAt ℝ z x)
    (hH : ∀ᶠ t in nhds x, h t (y t) (z t) = 0) :
    0 = partial1 h x (y x) (z x) * dx +
      partial2 h x (y x) (z x) * (firstDerivative y x * dx) +
      partial3 h x (y x) (z x) * (firstDerivative z x * dx) := by
  exact gap4 h y z x dx hhDiff hyDiff hzDiff hH

theorem gap8 (h : ℝ → ℝ → ℝ → ℝ) (x y z dx dy dz : ℝ) :
    partial1 h x y z * dx + partial2 h x y z * dy +
        partial3 h x y z * dz =
      dx * partial1 h x y z + dy * partial2 h x y z +
        dz * partial3 h x y z := by
  ring

theorem gap9 (h : ℝ → ℝ → ℝ → ℝ) (x y z dx dy dz : ℝ)
    (h1 : 0 = partial1 h x y z * dx + partial2 h x y z * dy +
      partial3 h x y z * dz)
    (h2 : partial1 h x y z * dx + partial2 h x y z * dy +
        partial3 h x y z * dz =
      dx * partial1 h x y z + dy * partial2 h x y z +
        dz * partial3 h x y z) :
    0 = dx * partial1 h x y z + dy * partial2 h x y z +
      dz * partial3 h x y z := by
  exact h1.trans h2

theorem gap10 (g h : ℝ → ℝ → ℝ → ℝ) (y z : ℝ → ℝ) (x : ℝ)
    (hI : minor1 g h x (y x) (z x) ≠ 0)
    (hG : 0 = partial1 g x (y x) (z x) +
      partial2 g x (y x) (z x) * firstDerivative y x +
      partial3 g x (y x) (z x) * firstDerivative z x)
    (hH : 0 = partial1 h x (y x) (z x) +
      partial2 h x (y x) (z x) * firstDerivative y x +
      partial3 h x (y x) (z x) * firstDerivative z x) :
    firstDerivative y x =
      minor2 g h x (y x) (z x) / minor1 g h x (y x) (z x) := by
  apply (eq_div_iff hI).2
  unfold minor1 minor2
  linear_combination
    -(partial3 h x (y x) (z x)) * hG +
      (partial3 g x (y x) (z x)) * hH

theorem gap11 (g h : ℝ → ℝ → ℝ → ℝ) (y z : ℝ → ℝ) (x : ℝ)
    (hI : minor1 g h x (y x) (z x) ≠ 0)
    (hG : 0 = partial1 g x (y x) (z x) +
      partial2 g x (y x) (z x) * firstDerivative y x +
      partial3 g x (y x) (z x) * firstDerivative z x)
    (hH : 0 = partial1 h x (y x) (z x) +
      partial2 h x (y x) (z x) * firstDerivative y x +
      partial3 h x (y x) (z x) * firstDerivative z x) :
    firstDerivative z x =
      minor3 g h x (y x) (z x) / minor1 g h x (y x) (z x) := by
  apply (eq_div_iff hI).2
  unfold minor1 minor3
  linear_combination
    -(partial2 g x (y x) (z x)) * hH +
      (partial2 h x (y x) (z x)) * hG

theorem gap12 (f g h : ℝ → ℝ → ℝ → ℝ) (u y z : ℝ → ℝ) (x : ℝ)
    (hI : minor1 g h x (y x) (z x) ≠ 0)
    (hU : firstDerivative u x =
      partial1 f x (y x) (z x) +
        partial2 f x (y x) (z x) * firstDerivative y x +
        partial3 f x (y x) (z x) * firstDerivative z x)
    (hY : firstDerivative y x =
      minor2 g h x (y x) (z x) / minor1 g h x (y x) (z x))
    (hZ : firstDerivative z x =
      minor3 g h x (y x) (z x) / minor1 g h x (y x) (z x)) :
    firstDerivative u x =
      partial1 f x (y x) (z x) +
        partial2 f x (y x) (z x) *
          (minor2 g h x (y x) (z x) / minor1 g h x (y x) (z x)) +
        partial3 f x (y x) (z x) *
          (minor3 g h x (y x) (z x) / minor1 g h x (y x) (z x)) := by
  rw [hU, hY, hZ]

theorem gap13 (f g h : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ)
    (hI : minor1 g h x y z ≠ 0) :
    partial1 f x y z +
        partial2 f x y z * (minor2 g h x y z / minor1 g h x y z) +
        partial3 f x y z * (minor3 g h x y z / minor1 g h x y z) =
      (minor1 g h x y z * partial1 f x y z +
        minor2 g h x y z * partial2 f x y z +
        minor3 g h x y z * partial3 f x y z) /
        minor1 g h x y z := by
  field_simp [hI]

theorem gap14 (f g h : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ)
    (hI : minor1 g h x y z ≠ 0) :
    (minor1 g h x y z * partial1 f x y z +
        minor2 g h x y z * partial2 f x y z +
        minor3 g h x y z * partial3 f x y z) /
        minor1 g h x y z =
      jacobian3 f g h x y z / minor1 g h x y z := by
  unfold jacobian3
  ring

theorem gap15 (f g h : ℝ → ℝ → ℝ → ℝ) (u y z : ℝ → ℝ) (x : ℝ)
    (hI : minor1 g h x (y x) (z x) ≠ 0)
    (h1 : firstDerivative u x =
      partial1 f x (y x) (z x) +
        partial2 f x (y x) (z x) *
          (minor2 g h x (y x) (z x) / minor1 g h x (y x) (z x)) +
        partial3 f x (y x) (z x) *
          (minor3 g h x (y x) (z x) / minor1 g h x (y x) (z x)))
    (h2 : partial1 f x (y x) (z x) +
        partial2 f x (y x) (z x) *
          (minor2 g h x (y x) (z x) / minor1 g h x (y x) (z x)) +
        partial3 f x (y x) (z x) *
          (minor3 g h x (y x) (z x) / minor1 g h x (y x) (z x)) =
      jacobian3 f g h x (y x) (z x) / minor1 g h x (y x) (z x)) :
    firstDerivative u x =
      jacobian3 f g h x (y x) (z x) / minor1 g h x (y x) (z x) := by
  exact h1.trans h2

theorem gap16 (f g h : ℝ → ℝ → ℝ → ℝ) (u y z : ℝ → ℝ) (x : ℝ)
    (hI : minor1 g h x (y x) (z x) ≠ 0)
    (hFormula : firstDerivative u x =
      jacobian3 f g h x (y x) (z x) / minor1 g h x (y x) (z x)) :
    firstDerivative u x =
      jacobian3 f g h x (y x) (z x) / minor1 g h x (y x) (z x) := by
  exact hFormula

theorem gap17 (f : ℝ → ℝ → ℝ → ℝ) (u y z : ℝ → ℝ) (x : ℝ)
    (hfC2 : ContDiffAt ℝ 2
      (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) (x, y x, z x))
    (huC2 : ContDiffAt ℝ 2 u x)
    (hyC2 : ContDiffAt ℝ 2 y x)
    (hzC2 : ContDiffAt ℝ 2 z x)
    (hU : ∀ᶠ t in nhds x, u t = f t (y t) (z t)) :
    secondDerivative u x =
      quadratic3 f x (y x) (z x) 1 (firstDerivative y x) (firstDerivative z x) +
        partial2 f x (y x) (z x) * secondDerivative y x +
        partial3 f x (y x) (z x) * secondDerivative z x := by
  have hcomp := second_chain3_at f y z x hfC2 hyC2 hzC2
  have hderivs := eventually_deriv_eq hU
  unfold secondDerivative
  rw [hderivs.deriv_eq]
  exact hcomp

theorem gap18 (g : ℝ → ℝ → ℝ → ℝ) (y z : ℝ → ℝ) (x : ℝ)
    (hgC2 : ContDiffAt ℝ 2
      (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) (x, y x, z x))
    (hyC2 : ContDiffAt ℝ 2 y x)
    (hzC2 : ContDiffAt ℝ 2 z x)
    (hG : ∀ᶠ t in nhds x, g t (y t) (z t) = 0) :
    0 =
      quadratic3 g x (y x) (z x) 1 (firstDerivative y x) (firstDerivative z x) +
        partial2 g x (y x) (z x) * secondDerivative y x +
        partial3 g x (y x) (z x) * secondDerivative z x := by
  have hcomp := second_chain3_at g y z x hgC2 hyC2 hzC2
  have hderivs := eventually_deriv_eq hG
  calc
    0 = secondDerivative (fun t => g t (y t) (z t)) x := by
      unfold secondDerivative
      rw [hderivs.deriv_eq]
      simp
    _ = _ := hcomp

theorem gap19 (h : ℝ → ℝ → ℝ → ℝ) (y z : ℝ → ℝ) (x : ℝ)
    (hhC2 : ContDiffAt ℝ 2
      (fun p : ℝ × ℝ × ℝ => h p.1 p.2.1 p.2.2) (x, y x, z x))
    (hyC2 : ContDiffAt ℝ 2 y x)
    (hzC2 : ContDiffAt ℝ 2 z x)
    (hH : ∀ᶠ t in nhds x, h t (y t) (z t) = 0) :
    0 =
      quadratic3 h x (y x) (z x) 1 (firstDerivative y x) (firstDerivative z x) +
        partial2 h x (y x) (z x) * secondDerivative y x +
        partial3 h x (y x) (z x) * secondDerivative z x := by
  exact gap18 h y z x hhC2 hyC2 hzC2 hH

theorem gap20 (g h : ℝ → ℝ → ℝ → ℝ) (y z : ℝ → ℝ) (x : ℝ)
    (hI : minor1 g h x (y x) (z x) ≠ 0)
    (hG : 0 =
      quadratic3 g x (y x) (z x) 1 (firstDerivative y x) (firstDerivative z x) +
        partial2 g x (y x) (z x) * secondDerivative y x +
        partial3 g x (y x) (z x) * secondDerivative z x)
    (hH : 0 =
      quadratic3 h x (y x) (z x) 1 (firstDerivative y x) (firstDerivative z x) +
        partial2 h x (y x) (z x) * secondDerivative y x +
        partial3 h x (y x) (z x) * secondDerivative z x) :
    secondDerivative y x =
      (partial3 g x (y x) (z x) *
          quadratic3 h x (y x) (z x) 1 (firstDerivative y x) (firstDerivative z x) -
        partial3 h x (y x) (z x) *
          quadratic3 g x (y x) (z x) 1 (firstDerivative y x) (firstDerivative z x)) /
        minor1 g h x (y x) (z x) := by
  apply (eq_div_iff hI).2
  unfold minor1
  linear_combination
    -(partial3 h x (y x) (z x)) * hG +
      (partial3 g x (y x) (z x)) * hH

theorem gap21 (g h : ℝ → ℝ → ℝ → ℝ) (y z : ℝ → ℝ) (x : ℝ)
    (hI : minor1 g h x (y x) (z x) ≠ 0)
    (hG : 0 =
      quadratic3 g x (y x) (z x) 1 (firstDerivative y x) (firstDerivative z x) +
        partial2 g x (y x) (z x) * secondDerivative y x +
        partial3 g x (y x) (z x) * secondDerivative z x)
    (hH : 0 =
      quadratic3 h x (y x) (z x) 1 (firstDerivative y x) (firstDerivative z x) +
        partial2 h x (y x) (z x) * secondDerivative y x +
        partial3 h x (y x) (z x) * secondDerivative z x) :
    secondDerivative z x =
      (partial2 h x (y x) (z x) *
          quadratic3 g x (y x) (z x) 1 (firstDerivative y x) (firstDerivative z x) -
        partial2 g x (y x) (z x) *
          quadratic3 h x (y x) (z x) 1 (firstDerivative y x) (firstDerivative z x)) /
        minor1 g h x (y x) (z x) := by
  apply (eq_div_iff hI).2
  unfold minor1
  linear_combination
    -(partial2 g x (y x) (z x)) * hH +
      (partial2 h x (y x) (z x)) * hG

theorem gap22 (f g h : ℝ → ℝ → ℝ → ℝ) (u y z : ℝ → ℝ) (x : ℝ)
    (hI : minor1 g h x (y x) (z x) ≠ 0)
    (hU : secondDerivative u x =
      quadratic3 f x (y x) (z x) 1 (firstDerivative y x) (firstDerivative z x) +
        partial2 f x (y x) (z x) * secondDerivative y x +
        partial3 f x (y x) (z x) * secondDerivative z x)
    (hY : secondDerivative y x =
      (partial3 g x (y x) (z x) *
          quadratic3 h x (y x) (z x) 1 (firstDerivative y x) (firstDerivative z x) -
        partial3 h x (y x) (z x) *
          quadratic3 g x (y x) (z x) 1 (firstDerivative y x) (firstDerivative z x)) /
        minor1 g h x (y x) (z x))
    (hZ : secondDerivative z x =
      (partial2 h x (y x) (z x) *
          quadratic3 g x (y x) (z x) 1 (firstDerivative y x) (firstDerivative z x) -
        partial2 g x (y x) (z x) *
          quadratic3 h x (y x) (z x) 1 (firstDerivative y x) (firstDerivative z x)) /
        minor1 g h x (y x) (z x)) :
    secondDerivative u x =
      (minor1 g h x (y x) (z x) *
          quadratic3 f x (y x) (z x) 1 (firstDerivative y x) (firstDerivative z x) +
        minor4 f h x (y x) (z x) *
          quadratic3 g x (y x) (z x) 1 (firstDerivative y x) (firstDerivative z x) +
        minor5 f g x (y x) (z x) *
          quadratic3 h x (y x) (z x) 1 (firstDerivative y x) (firstDerivative z x)) /
        minor1 g h x (y x) (z x) := by
  rw [hU, hY, hZ]
  field_simp [hI]
  unfold minor1 minor4 minor5
  ring

theorem gap23 (f g h : ℝ → ℝ → ℝ → ℝ) (u y z : ℝ → ℝ) (x : ℝ)
    (hI : minor1 g h x (y x) (z x) ≠ 0)
    (hY : firstDerivative y x =
      minor2 g h x (y x) (z x) / minor1 g h x (y x) (z x))
    (hZ : firstDerivative z x =
      minor3 g h x (y x) (z x) / minor1 g h x (y x) (z x))
    (hSecond : secondDerivative u x =
      (minor1 g h x (y x) (z x) *
          quadratic3 f x (y x) (z x) 1 (firstDerivative y x) (firstDerivative z x) +
        minor4 f h x (y x) (z x) *
          quadratic3 g x (y x) (z x) 1 (firstDerivative y x) (firstDerivative z x) +
        minor5 f g x (y x) (z x) *
          quadratic3 h x (y x) (z x) 1 (firstDerivative y x) (firstDerivative z x)) /
        minor1 g h x (y x) (z x)) :
    secondDerivative u x =
      (minor1 g h x (y x) (z x) *
          scaledQuadratic f x (y x) (z x)
            (minor1 g h x (y x) (z x))
            (minor2 g h x (y x) (z x))
            (minor3 g h x (y x) (z x)) +
        minor4 f h x (y x) (z x) *
          scaledQuadratic g x (y x) (z x)
            (minor1 g h x (y x) (z x))
            (minor2 g h x (y x) (z x))
            (minor3 g h x (y x) (z x)) +
        minor5 f g x (y x) (z x) *
          scaledQuadratic h x (y x) (z x)
            (minor1 g h x (y x) (z x))
            (minor2 g h x (y x) (z x))
            (minor3 g h x (y x) (z x))) /
        (minor1 g h x (y x) (z x)) ^ 3 := by
  rw [hY, hZ] at hSecond
  rw [hSecond]
  unfold scaledQuadratic quadratic3
  field_simp [hI]

end

end ProofGap.Exercise3416
