import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace ProofGap.Exercise3310

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  deriv (fun s => f s t) x

def partialXX (f : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  deriv (fun s => partialX f s t) x

def partialT (f : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  deriv (fun s => f x s) t

def w (a x t : ℝ) : ℝ :=
  1 / (a * Real.sqrt t) * Real.exp (-(x ^ 2) / (4 * a ^ 2 * t))

def xi (a x t : ℝ) : ℝ :=
  x / (a ^ 2 * t)

def eta (a _x t : ℝ) : ℝ :=
  -1 / (a ^ 4 * t)

def v (a : ℝ) (u : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  w a x t * u (xi a x t) (eta a x t)

private theorem w_partialX (a x t : ℝ) (ha : a ≠ 0) (ht : 0 < t) :
    partialX (w a) x t = -(x * w a x t) / (2 * a ^ 2 * t) := by
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hsqrt : Real.sqrt t ≠ 0 := Real.sqrt_ne_zero'.mpr ht
  have hinner : HasDerivAt (fun s : ℝ => -(s ^ 2) / (4 * a ^ 2 * t))
      (-(2 * x) / (4 * a ^ 2 * t)) x := by
    convert ((hasDerivAt_id x).pow 2).neg.div_const (4 * a ^ 2 * t)
      using 1 <;> simp [id] <;> field_simp [ha2, ht0] <;> ring
  have he := (Real.hasDerivAt_exp _).comp x hinner
  have hw : HasDerivAt (fun s =>
      1 / (a * Real.sqrt t) *
        Real.exp (-(s ^ 2) / (4 * a ^ 2 * t)))
      (1 / (a * Real.sqrt t) *
        (Real.exp (-(x ^ 2) / (4 * a ^ 2 * t)) *
          (-(2 * x) / (4 * a ^ 2 * t)))) x := by
    convert he.const_mul (1 / (a * Real.sqrt t)) using 1 <;> ring
  unfold partialX w
  rw [hw.deriv]
  field_simp [ha, ha2, ht0, hsqrt]
  ring

private theorem partialX_eq_fderiv (f : ℝ → ℝ → ℝ) (x t : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, t)) :
    partialX f x t =
      fderiv ℝ (Function.uncurry f) (x, t) (1, 0) := by
  unfold partialX
  have hp : HasDerivAt (fun s : ℝ => (s, t)) (1, 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x t)
  have h := (hf.hasFDerivAt.comp x hp.hasFDerivAt).hasDerivAt.deriv
  simpa [Function.uncurry] using h

private theorem partialT_eq_fderiv (f : ℝ → ℝ → ℝ) (x t : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, t)) :
    partialT f x t =
      fderiv ℝ (Function.uncurry f) (x, t) (0, 1) := by
  unfold partialT
  have hp : HasDerivAt (fun s : ℝ => (x, s)) (0, 1) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  have h := (hf.hasFDerivAt.comp t hp.hasFDerivAt).hasDerivAt.deriv
  simpa [Function.uncurry] using h

private theorem hasDerivAt_outer_pair
    (f : ℝ → ℝ → ℝ) (p q : ℝ → ℝ) (s p' q' : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (p s, q s))
    (hp : HasDerivAt p p' s) (hq : HasDerivAt q q' s) :
    HasDerivAt (fun r => f (p r) (q r))
      (partialX f (p s) (q s) * p' + partialT f (p s) (q s) * q') s := by
  have hpair : HasDerivAt (fun r => (p r, q r)) (p', q') s := by
    convert (hp.hasFDerivAt.prodMk hq.hasFDerivAt).hasDerivAt using 1 <;>
      simp
  have hc := hf.hasFDerivAt.comp s hpair.hasFDerivAt
  have hraw : HasDerivAt (fun r => f (p r) (q r))
      (fderiv ℝ (Function.uncurry f) (p s, q s) (p', q')) s := by
    convert hc.hasDerivAt using 1 <;> simp [Function.uncurry]
  convert hraw using 1
  rw [partialX_eq_fderiv f _ _ hf, partialT_eq_fderiv f _ _ hf]
  let L := fderiv ℝ (Function.uncurry f) (p s, q s)
  change L (1, 0) * p' + L (0, 1) * q' = L (p', q')
  rw [show (p', q') = p' • (1, 0) + q' • (0, 1) by ext <;> simp]
  simp only [map_add, map_smul]
  simp [smul_eq_mul]
  ring

theorem gap1 (a x t : ℝ) (ha : a ≠ 0) (ht : 0 < t) :
    partialT (w a) x t = a ^ 2 * partialXX (w a) x t := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have hsqrt : Real.sqrt t ≠ 0 := Real.sqrt_ne_zero'.mpr ht
  have hsqrtT := Real.hasDerivAt_sqrt ht0
  have hden : HasDerivAt (fun s => a * Real.sqrt s)
      (a * (1 / (2 * Real.sqrt t))) t :=
    hsqrtT.const_mul a
  have hA : HasDerivAt (fun s => 1 / (a * Real.sqrt s))
      ((0 * (a * Real.sqrt t) -
        1 * (a * (1 / (2 * Real.sqrt t)))) /
        (a * Real.sqrt t) ^ 2) t :=
    (hasDerivAt_const t 1).div hden (mul_ne_zero ha hsqrt)
  have hinner : HasDerivAt
      (fun s : ℝ => -(x ^ 2) / (4 * a ^ 2 * s))
      ((x ^ 2) / (4 * a ^ 2 * t ^ 2)) t := by
    have hq := (hasDerivAt_const t (-(x ^ 2))).div
      ((hasDerivAt_const t (4 * a ^ 2)).mul (hasDerivAt_id t))
      (mul_ne_zero (mul_ne_zero (by norm_num) ha2) ht0)
    convert hq using 1 <;>
      simp [id] <;> field_simp [ha2, ht0] <;> ring
  have hB := (Real.hasDerivAt_exp _).comp t hinner
  have hwT : HasDerivAt (fun s =>
      1 / (a * Real.sqrt s) *
        Real.exp (-(x ^ 2) / (4 * a ^ 2 * s)))
      (((0 * (a * Real.sqrt t) -
          1 * (a * (1 / (2 * Real.sqrt t)))) /
          (a * Real.sqrt t) ^ 2) *
          Real.exp (-(x ^ 2) / (4 * a ^ 2 * t)) +
        1 / (a * Real.sqrt t) *
          (Real.exp (-(x ^ 2) / (4 * a ^ 2 * t)) *
            ((x ^ 2) / (4 * a ^ 2 * t ^ 2)))) t :=
    hA.mul hB
  have hwxDiff : DifferentiableAt ℝ (fun s => w a s t) x := by
    unfold w
    fun_prop
  have hwx : HasDerivAt (fun s => w a s t)
      (partialX (w a) x t) x := by
    simpa [partialX] using hwxDiff.hasDerivAt
  have hsecond : partialXX (w a) x t =
      -((w a x t + x * partialX (w a) x t) /
        (2 * a ^ 2 * t)) := by
    unfold partialXX
    have heq : (fun s => partialX (w a) s t) =
        fun s => -(s * w a s t) / (2 * a ^ 2 * t) := by
      funext s
      exact w_partialX a s t ha ht
    rw [heq]
    have hp := (hasDerivAt_id x).mul hwx
    have hn := hp.neg.div_const (2 * a ^ 2 * t)
    convert hn.deriv using 1 <;>
      simp [id] <;> ring
  rw [hsecond, w_partialX a x t ha ht]
  unfold partialT w
  rw [hwT.deriv]
  field_simp [ha, ha2, ht0, hsqrt]
  rw [Real.sq_sqrt ht.le]
  ring

theorem gap2 (a x t : ℝ) (ha : a ≠ 0) (ht : 0 < t) :
    partialX (w a) x t = -(x * w a x t) / (2 * a ^ 2 * t) :=
  w_partialX a x t ha ht

theorem gap3 (a x t : ℝ) (ha : a ≠ 0) (ht : 0 < t) :
    partialX (xi a) x t = 1 / (a ^ 2 * t) := by
  unfold partialX xi
  have hden : a ^ 2 * t ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 ha) (ne_of_gt ht)
  have h : HasDerivAt (fun s => s / (a ^ 2 * t))
      (1 / (a ^ 2 * t)) x := by
    convert (hasDerivAt_id x).mul_const (1 / (a ^ 2 * t)) using 1
    · ext r
      simp [id]
      ring
    · simp
  exact h.deriv

theorem gap4 (a x t : ℝ) (ha : a ≠ 0) (ht : 0 < t) :
    partialXX (xi a) x t = 0 := by
  unfold partialXX partialX xi
  have hden : a ^ 2 * t ≠ 0 := mul_ne_zero (pow_ne_zero 2 ha) (ne_of_gt ht)
  have heq : (fun s => deriv (fun r => r / (a ^ 2 * t)) s) =
      fun _ => 1 / (a ^ 2 * t) := by
    funext s
    have h : HasDerivAt (fun r => r / (a ^ 2 * t))
        (1 / (a ^ 2 * t)) s := by
      convert (hasDerivAt_id s).mul_const (1 / (a ^ 2 * t)) using 1
      · ext r
        simp [id]
        ring
      · simp
    exact h.deriv
  rw [heq]
  exact (hasDerivAt_const x (1 / (a ^ 2 * t))).deriv

theorem gap5 (a x t : ℝ) (ha : a ≠ 0) (ht : 0 < t) :
    partialT (xi a) x t = -x / (a ^ 2 * t ^ 2) := by
  unfold partialT xi
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have ht0 : t ≠ 0 := ne_of_gt ht
  have h := (hasDerivAt_const t x).div
    ((hasDerivAt_const t (a ^ 2)).mul (hasDerivAt_id t))
    (mul_ne_zero ha2 ht0)
  convert h.deriv using 1 <;>
      simp [id] <;> field_simp [ha2, ht0] <;> ring

theorem gap6 (a x t : ℝ) (ha : a ≠ 0) (ht : 0 < t) :
    partialT (eta a) x t = 1 / (a ^ 4 * t ^ 2) := by
  unfold partialT eta
  have ha4 : a ^ 4 ≠ 0 := pow_ne_zero 4 ha
  have ht0 : t ≠ 0 := ne_of_gt ht
  have h := (hasDerivAt_const t (-1)).div
    ((hasDerivAt_const t (a ^ 4)).mul (hasDerivAt_id t))
    (mul_ne_zero ha4 ht0)
  convert h.deriv using 1 <;>
      simp [id] <;> field_simp [ha4, ht0] <;> ring

theorem gap7 (a : ℝ) (u : ℝ → ℝ → ℝ) (x t : ℝ)
    (ha : a ≠ 0) (ht : 0 < t) :
    v a u x t = w a x t * u (xi a x t) (eta a x t) := by rfl

theorem gap8 (a : ℝ) (u : ℝ → ℝ → ℝ)
    (huHeat : ∀ p q, partialT u p q = a ^ 2 * partialXX u p q)
    (x t : ℝ) (ha : a ≠ 0) (ht : 0 < t) :
    partialT u (xi a x t) (eta a x t) =
      a ^ 2 * partialXX u (xi a x t) (eta a x t) := by
  exact huHeat _ _

theorem gap9 (a : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiff ℝ 2 (Function.uncurry u))
    (x t : ℝ) (ha : a ≠ 0) (ht : 0 < t) :
    partialT (v a u) x t =
      partialT (w a) x t * u (xi a x t) (eta a x t) +
      w a x t *
        (partialX u (xi a x t) (eta a x t) * partialT (xi a) x t +
          partialT u (xi a x t) (eta a x t) * partialT (eta a) x t) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hwDiff : DifferentiableAt ℝ (fun s => w a x s) t := by
    unfold w
    fun_prop (disch := positivity)
  have hw : HasDerivAt (fun s => w a x s) (partialT (w a) x t) t := by
    simpa [partialT] using hwDiff.hasDerivAt
  have hxiDiff : DifferentiableAt ℝ (fun s => xi a x s) t := by
    unfold xi
    fun_prop (disch := positivity)
  have hxi : HasDerivAt (fun s => xi a x s) (partialT (xi a) x t) t := by
    simpa [partialT] using hxiDiff.hasDerivAt
  have hetaDiff : DifferentiableAt ℝ (fun s => eta a x s) t := by
    unfold eta
    fun_prop (disch := positivity)
  have heta : HasDerivAt (fun s => eta a x s) (partialT (eta a) x t) t := by
    simpa [partialT] using hetaDiff.hasDerivAt
  have huAt : DifferentiableAt ℝ (Function.uncurry u)
      (xi a x t, eta a x t) := (hu.differentiable (by decide)) _
  have hcomp := hasDerivAt_outer_pair u
    (fun s => xi a x s) (fun s => eta a x s) t
    (partialT (xi a) x t) (partialT (eta a) x t)
    huAt hxi heta
  have hv := hw.mul hcomp
  unfold partialT v
  convert hv.deriv using 1 <;> ring

theorem gap10 (a : ℝ) (u : ℝ → ℝ → ℝ)
    (huHeat : ∀ p q, partialT u p q = a ^ 2 * partialXX u p q)
    (x t : ℝ) (ha : a ≠ 0) (ht : 0 < t) :
    partialT (w a) x t * u (xi a x t) (eta a x t) +
        w a x t *
          (partialX u (xi a x t) (eta a x t) * partialT (xi a) x t +
            partialT u (xi a x t) (eta a x t) * partialT (eta a) x t) =
      a ^ 2 * partialXX (w a) x t * u (xi a x t) (eta a x t) +
        w a x t *
          (partialX u (xi a x t) (eta a x t) *
              (-x / (a ^ 2 * t ^ 2)) +
            a ^ 2 * partialXX u (xi a x t) (eta a x t) *
              (1 / (a ^ 4 * t ^ 2))) := by
  rw [gap1 a x t ha ht, gap5 a x t ha ht, gap6 a x t ha ht,
    huHeat (xi a x t) (eta a x t)]

theorem gap11 (a : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiff ℝ 2 (Function.uncurry u))
    (huHeat : ∀ p q, partialT u p q = a ^ 2 * partialXX u p q)
    (x t : ℝ) (ha : a ≠ 0) (ht : 0 < t) :
    partialT (v a u) x t =
      a ^ 2 * partialXX (w a) x t * u (xi a x t) (eta a x t) +
        w a x t *
          (partialX u (xi a x t) (eta a x t) *
              (-x / (a ^ 2 * t ^ 2)) +
            a ^ 2 * partialXX u (xi a x t) (eta a x t) *
              (1 / (a ^ 4 * t ^ 2))) := by
  rw [gap9 a u hu x t ha ht]
  exact gap10 a u huHeat x t ha ht

theorem gap12 (a : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiff ℝ 2 (Function.uncurry u))
    (x t : ℝ) (ha : a ≠ 0) (ht : 0 < t) :
    partialX (v a u) x t =
      partialX (w a) x t * u (xi a x t) (eta a x t) +
        w a x t * partialX u (xi a x t) (eta a x t) *
          partialX (xi a) x t := by
  have hwDiff : DifferentiableAt ℝ (fun s => w a s t) x := by
    unfold w
    fun_prop
  have hw : HasDerivAt (fun s => w a s t) (partialX (w a) x t) x := by
    simpa [partialX] using hwDiff.hasDerivAt
  have hxiDiff : DifferentiableAt ℝ (fun s => xi a s t) x := by
    unfold xi
    fun_prop
  have hxi : HasDerivAt (fun s => xi a s t) (partialX (xi a) x t) x := by
    simpa [partialX] using hxiDiff.hasDerivAt
  have heta : HasDerivAt (fun _ : ℝ => eta a x t) 0 x :=
    hasDerivAt_const x (eta a x t)
  have huAt : DifferentiableAt ℝ (Function.uncurry u)
      (xi a x t, eta a x t) := (hu.differentiable (by decide)) _
  have hcomp := hasDerivAt_outer_pair u
    (fun s => xi a s t) (fun _ => eta a x t) x
    (partialX (xi a) x t) 0 huAt hxi heta
  have hv := hw.mul hcomp
  have hv' : HasDerivAt
      (fun s => w a s t * u (xi a s t) (eta a x t))
      (partialX (w a) x t * u (xi a x t) (eta a x t) +
        w a x t *
          (partialX u (xi a x t) (eta a x t) * partialX (xi a) x t +
            partialT u (xi a x t) (eta a x t) * 0)) x := by
    convert hv using 1 <;> simp [eta]
  unfold partialX v
  convert hv'.deriv using 1 <;> simp [partialX, partialT, eta] <;> ring

theorem gap13 (a : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiff ℝ 2 (Function.uncurry u))
    (x t : ℝ) (ha : a ≠ 0) (ht : 0 < t) :
    partialXX (v a u) x t =
      partialXX (w a) x t * u (xi a x t) (eta a x t) +
        2 * partialX (w a) x t * partialX u (xi a x t) (eta a x t) *
          partialX (xi a) x t +
        w a x t * partialXX u (xi a x t) (eta a x t) *
          partialX (xi a) x t ^ 2 +
        w a x t * partialX u (xi a x t) (eta a x t) *
          partialXX (xi a) x t := by
  have hwC2 : ContDiff ℝ 2 (fun s => w a s t) := by
    unfold w
    fun_prop (disch := positivity)
  have hxiC2 : ContDiff ℝ 2 (fun s => xi a s t) := by
    unfold xi
    fun_prop (disch := positivity)
  have huSlice : ContDiff ℝ 2
      (fun r => u r (eta a x t)) := by
    have hp : ContDiff ℝ 2 (fun r : ℝ => (r, eta a x t)) :=
      contDiff_id.prodMk contDiff_const
    simpa [Function.uncurry] using hu.comp hp
  have hw : HasDerivAt (fun s => w a s t)
      (partialX (w a) x t) x := by
    simpa [partialX] using
      (hwC2.differentiable (by decide) x).hasDerivAt
  have hxi : HasDerivAt (fun s => xi a s t)
      (partialX (xi a) x t) x := by
    simpa [partialX] using
      (hxiC2.differentiable (by decide) x).hasDerivAt
  have hwD : HasDerivAt (fun s => partialX (w a) s t)
      (partialXX (w a) x t) x := by
    have hd : DifferentiableAt ℝ (deriv (fun s => w a s t)) x :=
      hwC2.differentiable_deriv_two x
    simpa [partialX, partialXX] using hd.hasDerivAt
  have hxiD : HasDerivAt (fun s => partialX (xi a) s t)
      (partialXX (xi a) x t) x := by
    have hd : DifferentiableAt ℝ (deriv (fun s => xi a s t)) x :=
      hxiC2.differentiable_deriv_two x
    simpa [partialX, partialXX] using hd.hasDerivAt
  have hu0 : HasDerivAt (fun r => u r (eta a x t))
      (partialX u (xi a x t) (eta a x t)) (xi a x t) := by
    simpa [partialX] using
      (huSlice.differentiable (by decide) (xi a x t)).hasDerivAt
  have hu0D : HasDerivAt
      (fun r => partialX u r (eta a x t))
      (partialXX u (xi a x t) (eta a x t)) (xi a x t) := by
    have hd : DifferentiableAt ℝ
        (deriv (fun r => u r (eta a x t))) (xi a x t) :=
      huSlice.differentiable_deriv_two (xi a x t)
    simpa [partialX, partialXX] using hd.hasDerivAt
  have huComp := hu0.comp x hxi
  have huDComp := hu0D.comp x hxi
  have htotal :=
    (hwD.mul huComp).add ((hw.mul huDComp).mul hxiD)
  have htotal' : HasDerivAt
      (fun s =>
        partialX (w a) s t * u (xi a s t) (eta a s t) +
          w a s t * partialX u (xi a s t) (eta a s t) *
            partialX (xi a) s t)
      (partialXX (w a) x t * u (xi a x t) (eta a x t) +
        2 * partialX (w a) x t *
          partialX u (xi a x t) (eta a x t) *
          partialX (xi a) x t +
        w a x t * partialXX u (xi a x t) (eta a x t) *
          partialX (xi a) x t ^ 2 +
        w a x t * partialX u (xi a x t) (eta a x t) *
          partialXX (xi a) x t) x := by
    convert htotal using 1 <;>
      simp [Function.comp_def, eta] <;> ring
  unfold partialXX
  have heq :
      (fun s => partialX (v a u) s t) =
        (fun s =>
          partialX (w a) s t * u (xi a s t) (eta a s t) +
            w a s t * partialX u (xi a s t) (eta a s t) *
              partialX (xi a) s t) := by
    funext s
    exact gap12 a u hu s t ha ht
  rw [heq]
  exact htotal'.deriv

theorem gap14 (a : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiff ℝ 2 (Function.uncurry u))
    (x t : ℝ) (ha : a ≠ 0) (ht : 0 < t) :
    partialXX (v a u) x t =
      partialXX (w a) x t * u (xi a x t) (eta a x t) -
        (x * w a x t) / (a ^ 4 * t ^ 2) *
          partialX u (xi a x t) (eta a x t) +
        w a x t / (a ^ 4 * t ^ 2) *
          partialXX u (xi a x t) (eta a x t) := by
  rw [gap13 a u hu x t ha ht, gap2 a x t ha ht,
    gap3 a x t ha ht, gap4 a x t ha ht]
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have ht0 : t ≠ 0 := ne_of_gt ht
  field_simp [ha2, ht0]
  ring

theorem gap15 (a : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiff ℝ 2 (Function.uncurry u))
    (huHeat : ∀ p q, partialT u p q = a ^ 2 * partialXX u p q)
    (x t : ℝ) (ha : a ≠ 0) (ht : 0 < t) :
    partialT (v a u) x t = a ^ 2 * partialXX (v a u) x t := by
  rw [gap11 a u hu huHeat x t ha ht, gap14 a u hu x t ha ht]
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have ht0 : t ≠ 0 := ne_of_gt ht
  field_simp [ha2, ht0]
  ring

theorem gap16 (a : ℝ) (u : ℝ → ℝ → ℝ)
    (ha : a ≠ 0)
    (hu : ContDiff ℝ 2 (Function.uncurry u))
    (huHeat : ∀ p q, partialT u p q = a ^ 2 * partialXX u p q) :
    ∀ x t, 0 < t →
      partialT (v a u) x t = a ^ 2 * partialXX (v a u) x t := by
  intro x t ht
  exact gap15 a u hu huHeat x t ha ht

end

end ProofGap.Exercise3310
