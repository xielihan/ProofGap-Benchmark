import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3313

noncomputable section

def radius (x y z : ℝ) : ℝ :=
  Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)

def profile (k s : ℝ) : ℝ :=
  Real.exp (-k * s) / s

def kernel (k x y z : ℝ) : ℝ :=
  profile k (radius x y z)

def v (a : ℝ) : ℝ → ℝ → ℝ → ℝ :=
  kernel a

def w (a : ℝ) : ℝ → ℝ → ℝ → ℝ :=
  kernel (-a)

def u (C₁ C₂ a x y z : ℝ) : ℝ :=
  C₁ * v a x y z + C₂ * w a x y z

def partialX (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => f s y z) x

def partialY (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => f x s z) y

def partialZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => f x y s) z

def partialXX (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => partialX f s y z) x

def partialYY (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => partialY f x s z) y

def partialZZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => partialZ f x y s) z

def laplacian (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  partialXX f x y z + partialYY f x y z + partialZZ f x y z

private theorem hasDerivAt_radius_first (x y z : ℝ)
    (hr : radius x y z ≠ 0) :
    HasDerivAt (fun t => radius t y z) (x / radius x y z) x := by
  have hq : x ^ 2 + y ^ 2 + z ^ 2 ≠ 0 := by
    intro h
    apply hr
    simp [radius, h]
  have hpoly :
      HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2 + z ^ 2) (2 * x) x := by
    convert (((hasDerivAt_id x).pow 2).add_const (y ^ 2)).add_const (z ^ 2) using 1 <;>
      simp [Function.id_def] <;> ring
  have h := (Real.hasDerivAt_sqrt hq).comp x hpoly
  convert h using 1 <;> simp only [radius] <;> field_simp [hr] <;> ring

private theorem hasDerivAt_profile (a s : ℝ) (hs : s ≠ 0) :
    HasDerivAt (profile a)
      (Real.exp (-a * s) * (-1 / s ^ 2 - a / s)) s := by
  have hlin : HasDerivAt (fun t : ℝ => -a * t) (-a) s := by
    convert (hasDerivAt_const s (-a)).mul (hasDerivAt_id s) using 1 <;> ring
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-a * t))
      (Real.exp (-a * s) * (-a)) s := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (-a * s)).comp s hlin
  have hquot := hexp.div (hasDerivAt_id s) hs
  convert hquot using 1 <;> simp [profile, Function.comp_def] <;>
    field_simp [hs] <;> ring

private theorem hasDerivAt_v_first (a x y z : ℝ)
    (hr : radius x y z ≠ 0) :
    HasDerivAt (fun t => v a t y z)
      (-x * v a x y z *
        (1 / radius x y z ^ 2 + a / radius x y z)) x := by
  have hp := hasDerivAt_profile a (radius x y z) hr
  have hx := hasDerivAt_radius_first x y z hr
  have h := hp.comp x hx
  convert h using 1 <;> simp only [v, kernel, profile] <;>
    field_simp [hr] <;> ring

private theorem hasDerivAt_radial_factor (a x y z : ℝ)
    (hr : radius x y z ≠ 0) :
    HasDerivAt
      (fun t => 1 / radius t y z ^ 2 + a / radius t y z)
      ((-2 / radius x y z ^ 3 - a / radius x y z ^ 2) *
        (x / radius x y z)) x := by
  have hx := hasDerivAt_radius_first x y z hr
  have hs : radius x y z ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hfirst :=
    (hasDerivAt_const x (1 : ℝ)).div (hx.pow 2) hs
  have hsecond :=
    (hasDerivAt_const x a).div hx hr
  have h := hfirst.add hsecond
  convert h using 1 <;> simp <;> field_simp [hr] <;> ring

private theorem eventually_radius_ne_zero (x y z : ℝ)
    (hr : radius x y z ≠ 0) :
    ∀ᶠ t in nhds x, radius t y z ≠ 0 := by
  exact (hasDerivAt_radius_first x y z hr).continuousAt.eventually_ne hr

private theorem hasDerivAt_partialX_v (a x y z : ℝ)
    (hr : radius x y z ≠ 0) :
    HasDerivAt (fun t => partialX (v a) t y z)
      (-partialX (v a) x y z *
          (1 / radius x y z ^ 2 + a / radius x y z) * x -
        v a x y z *
          (-2 / radius x y z ^ 3 - a / radius x y z ^ 2) *
          (x / radius x y z) * x -
        v a x y z *
          (1 / radius x y z ^ 2 + a / radius x y z)) x := by
  let B : ℝ → ℝ := fun t =>
    1 / radius t y z ^ 2 + a / radius t y z
  let g : ℝ → ℝ := fun t => -t * v a t y z * B t
  have hv := hasDerivAt_v_first a x y z hr
  have hB := hasDerivAt_radial_factor a x y z hr
  have hg : HasDerivAt g
      (((-1) * v a x y z + (-x) *
          (-x * v a x y z *
            (1 / radius x y z ^ 2 + a / radius x y z))) *
          (1 / radius x y z ^ 2 + a / radius x y z) +
        (-x * v a x y z) *
          ((-2 / radius x y z ^ 3 - a / radius x y z ^ 2) *
            (x / radius x y z))) x := by
    simpa [g, B] using (((hasDerivAt_id x).neg.mul hv).mul hB)
  have heq : (fun t => partialX (v a) t y z) =ᶠ[nhds x] g := by
    filter_upwards [eventually_radius_ne_zero x y z hr] with t ht
    simpa [g, B, partialX] using (hasDerivAt_v_first a t y z ht).deriv
  have hout := hg.congr_of_eventuallyEq heq
  have hx : partialX (v a) x y z =
      -x * v a x y z *
        (1 / radius x y z ^ 2 + a / radius x y z) := by
    simpa [partialX] using hv.deriv
  convert hout using 1
  rw [hx]
  ring

private theorem partialXX_linear (C₁ C₂ k l x y z : ℝ)
    (hr : radius x y z ≠ 0) :
    partialXX
        (fun p q r => C₁ * v k p q r + C₂ * v l p q r) x y z =
      C₁ * partialXX (v k) x y z +
        C₂ * partialXX (v l) x y z := by
  have heq :
      (fun t => partialX
        (fun p q r => C₁ * v k p q r + C₂ * v l p q r) t y z) =ᶠ[nhds x]
      (fun t => C₁ * partialX (v k) t y z +
        C₂ * partialX (v l) t y z) := by
    filter_upwards [eventually_radius_ne_zero x y z hr] with t ht
    have hk := hasDerivAt_v_first k t y z ht
    have hl := hasDerivAt_v_first l t y z ht
    have hsum := (hk.const_mul C₁).add (hl.const_mul C₂)
    change deriv (fun s => C₁ * v k s y z + C₂ * v l s y z) t =
      C₁ * deriv (fun s => v k s y z) t +
        C₂ * deriv (fun s => v l s y z) t
    rw [hk.deriv, hl.deriv]
    simpa only [Pi.add_apply] using hsum.deriv
  have hk2 := hasDerivAt_partialX_v k x y z hr
  have hl2 := hasDerivAt_partialX_v l x y z hr
  have hsum := (hk2.const_mul C₁).add (hl2.const_mul C₂)
  unfold partialXX
  rw [heq.deriv_eq, hk2.deriv, hl2.deriv]
  simpa only [Pi.add_apply] using hsum.deriv

theorem gap1 (C₁ C₂ a x y z : ℝ) (hr : radius x y z ≠ 0) :
    u C₁ C₂ a x y z = C₁ * v a x y z + C₂ * w a x y z := by
  rfl

theorem gap2 (a x y z : ℝ) (hr : radius x y z ≠ 0) :
    partialX (v a) x y z =
      deriv (profile a) (radius x y z) * partialX radius x y z := by
  have hp := hasDerivAt_profile a (radius x y z) hr
  have hx := hasDerivAt_radius_first x y z hr
  rw [show deriv (profile a) (radius x y z) =
      Real.exp (-a * radius x y z) *
        (-1 / radius x y z ^ 2 - a / radius x y z) by
    exact hp.deriv]
  rw [show partialX radius x y z = x / radius x y z by
    simpa [partialX] using hx.deriv]
  simpa [partialX, v, kernel, Function.comp_def] using (hp.comp x hx).deriv

theorem gap3 (a x y z : ℝ) (hr : radius x y z ≠ 0) :
    deriv (profile a) (radius x y z) * partialX radius x y z =
      Real.exp (-a * radius x y z) *
        (-1 / radius x y z ^ 2 - a / radius x y z) *
        (x / radius x y z) := by
  rw [(hasDerivAt_profile a (radius x y z) hr).deriv]
  rw [show partialX radius x y z = x / radius x y z by
    simpa [partialX] using (hasDerivAt_radius_first x y z hr).deriv]

theorem gap4 (a x y z : ℝ) (hr : radius x y z ≠ 0) :
    Real.exp (-a * radius x y z) *
        (-1 / radius x y z ^ 2 - a / radius x y z) *
        (x / radius x y z) =
      -x * v a x y z *
        (1 / radius x y z ^ 2 + a / radius x y z) := by
  simp only [v, kernel, profile]
  field_simp [hr]
  ring

theorem gap5 (a x y z : ℝ) (hr : radius x y z ≠ 0) :
    partialX (v a) x y z =
      -x * v a x y z *
        (1 / radius x y z ^ 2 + a / radius x y z) := by
  rw [gap2 a x y z hr, gap3 a x y z hr, gap4 a x y z hr]

theorem gap6 (a x y z : ℝ) (hr : radius x y z ≠ 0) :
    partialXX (v a) x y z =
      -partialX (v a) x y z *
          (1 / radius x y z ^ 2 + a / radius x y z) * x -
        v a x y z *
          (-2 / radius x y z ^ 3 - a / radius x y z ^ 2) *
          (x / radius x y z) * x -
        v a x y z *
          (1 / radius x y z ^ 2 + a / radius x y z) := by
  simpa [partialXX] using (hasDerivAt_partialX_v a x y z hr).deriv

theorem gap7 (a x y z : ℝ) (hr : radius x y z ≠ 0) :
    partialXX (v a) x y z =
      x ^ 2 * v a x y z *
          (1 / radius x y z ^ 2 + a / radius x y z) ^ 2 +
        x ^ 2 * v a x y z * (1 / radius x y z) *
          (2 / radius x y z ^ 3 + a / radius x y z ^ 2) -
        v a x y z *
          (1 / radius x y z ^ 2 + a / radius x y z) := by
  rw [gap6 a x y z hr, gap5 a x y z hr]
  ring

theorem gap8 (a x y z : ℝ) (hr : radius x y z ≠ 0) :
    partialXX (v a) x y z =
      v a x y z *
        ((3 / radius x y z ^ 4 + 3 * a / radius x y z ^ 3 +
            a ^ 2 / radius x y z ^ 2) * x ^ 2 -
          1 / radius x y z ^ 2 - a / radius x y z) := by
  rw [gap7 a x y z hr]
  field_simp [hr]
  ring

theorem gap9 (a x y z : ℝ) (hr : radius x y z ≠ 0) :
    laplacian (v a) x y z =
      v a x y z *
        ((3 / radius x y z ^ 4 + 3 * a / radius x y z ^ 3 +
            a ^ 2 / radius x y z ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2) -
          3 / radius x y z ^ 2 - 3 * a / radius x y z) := by
  have hx := gap8 a x y z hr
  have hry : radius y x z ≠ 0 := by
    simpa [radius, add_comm, add_left_comm, add_assoc] using hr
  have hy0 := gap8 a y x z hry
  have hy : partialYY (v a) x y z =
      v a x y z *
        ((3 / radius x y z ^ 4 + 3 * a / radius x y z ^ 3 +
            a ^ 2 / radius x y z ^ 2) * y ^ 2 -
          1 / radius x y z ^ 2 - a / radius x y z) := by
    simpa [partialXX, partialYY, partialX, partialY, v, kernel, radius,
      add_comm, add_left_comm, add_assoc] using hy0
  have hrz : radius z y x ≠ 0 := by
    simpa [radius, add_comm, add_left_comm, add_assoc] using hr
  have hz0 := gap8 a z y x hrz
  have hz : partialZZ (v a) x y z =
      v a x y z *
        ((3 / radius x y z ^ 4 + 3 * a / radius x y z ^ 3 +
            a ^ 2 / radius x y z ^ 2) * z ^ 2 -
          1 / radius x y z ^ 2 - a / radius x y z) := by
    simpa [partialXX, partialZZ, partialX, partialZ, v, kernel, radius,
      add_comm, add_left_comm, add_assoc] using hz0
  rw [laplacian, hx, hy, hz]
  ring

theorem gap10 (a x y z : ℝ) (hr : radius x y z ≠ 0) :
    v a x y z *
        ((3 / radius x y z ^ 4 + 3 * a / radius x y z ^ 3 +
            a ^ 2 / radius x y z ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2) -
          3 / radius x y z ^ 2 - 3 * a / radius x y z) =
      a ^ 2 * v a x y z := by
  have hs : radius x y z ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := by
    unfold radius
    exact Real.sq_sqrt (by positivity)
  have hfactor :
      (3 / radius x y z ^ 4 + 3 * a / radius x y z ^ 3 +
            a ^ 2 / radius x y z ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2) -
          3 / radius x y z ^ 2 - 3 * a / radius x y z = a ^ 2 := by
    rw [← hs]
    field_simp [hr]
    ring
  rw [hfactor]
  ring

theorem gap11 (a x y z : ℝ) (hr : radius x y z ≠ 0) :
    laplacian (v a) x y z = a ^ 2 * v a x y z := by
  rw [gap9 a x y z hr, gap10 a x y z hr]

theorem gap12 (a b x y z : ℝ) (hb : b = -a)
    (hr : radius x y z ≠ 0) :
    w a x y z = kernel b x y z := by
  subst b
  rfl

theorem gap13 (b x y z : ℝ) (hr : radius x y z ≠ 0) :
    laplacian (kernel b) x y z = b ^ 2 * kernel b x y z := by
  simpa [v] using gap11 b x y z hr

theorem gap14 (a b x y z : ℝ) (hb : b = -a)
    (hr : radius x y z ≠ 0) :
    b ^ 2 * w a x y z = a ^ 2 * w a x y z := by
  subst b
  ring

theorem gap15 (a x y z : ℝ) (hr : radius x y z ≠ 0) :
    laplacian (w a) x y z = a ^ 2 * w a x y z := by
  have h := gap13 (-a) x y z hr
  simpa [w] using h

theorem gap16 (C₁ C₂ a x y z : ℝ) (hr : radius x y z ≠ 0) :
    laplacian (u C₁ C₂ a) x y z =
      C₁ * laplacian (v a) x y z +
        C₂ * laplacian (w a) x y z := by
  have hxx := partialXX_linear C₁ C₂ a (-a) x y z hr
  have hxx' : partialXX (u C₁ C₂ a) x y z =
      C₁ * partialXX (v a) x y z + C₂ * partialXX (w a) x y z := by
    simpa [u, w] using hxx
  have hry : radius y x z ≠ 0 := by
    simpa [radius, add_comm, add_left_comm, add_assoc] using hr
  have hyy0 := partialXX_linear C₁ C₂ a (-a) y x z hry
  have hyy : partialYY (u C₁ C₂ a) x y z =
      C₁ * partialYY (v a) x y z + C₂ * partialYY (w a) x y z := by
    simpa [u, w, partialXX, partialYY, partialX, partialY, v, kernel, radius,
      add_comm, add_left_comm, add_assoc] using hyy0
  have hrz : radius z y x ≠ 0 := by
    simpa [radius, add_comm, add_left_comm, add_assoc] using hr
  have hzz0 := partialXX_linear C₁ C₂ a (-a) z y x hrz
  have hzz : partialZZ (u C₁ C₂ a) x y z =
      C₁ * partialZZ (v a) x y z + C₂ * partialZZ (w a) x y z := by
    simpa [u, w, partialXX, partialZZ, partialX, partialZ, v, kernel, radius,
      add_comm, add_left_comm, add_assoc] using hzz0
  rw [laplacian, hxx', hyy, hzz]
  simp only [laplacian]
  ring

theorem gap17 (C₁ C₂ a x y z : ℝ) (hr : radius x y z ≠ 0) :
    C₁ * laplacian (v a) x y z +
        C₂ * laplacian (w a) x y z =
      C₁ * a ^ 2 * v a x y z + C₂ * a ^ 2 * w a x y z := by
  rw [gap11 a x y z hr, gap15 a x y z hr]
  ring

theorem gap18 (C₁ C₂ a x y z : ℝ) (hr : radius x y z ≠ 0) :
    C₁ * a ^ 2 * v a x y z + C₂ * a ^ 2 * w a x y z =
      a ^ 2 * u C₁ C₂ a x y z := by
  unfold u
  ring

theorem gap19 (C₁ C₂ a x y z : ℝ) (hr : radius x y z ≠ 0) :
    laplacian (u C₁ C₂ a) x y z =
      a ^ 2 * u C₁ C₂ a x y z := by
  rw [gap16 C₁ C₂ a x y z hr, gap17 C₁ C₂ a x y z hr,
    gap18 C₁ C₂ a x y z hr]

theorem gap20 (C₁ C₂ a : ℝ) :
    ∀ x y z, radius x y z ≠ 0 →
      laplacian (u C₁ C₂ a) x y z =
        a ^ 2 * u C₁ C₂ a x y z := by
  intro x y z hr
  exact gap19 C₁ C₂ a x y z hr

end

end ProofGap.Exercise3313
