import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace ProofGap.Exercise3320

noncomputable section

def uncurry3 (g : ℝ → ℝ → ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  g p.1 p.2.1 p.2.2

def IsC1 (g : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 (uncurry3 g)

def partialU (g : ℝ → ℝ → ℝ → ℝ) (u v w : ℝ) : ℝ :=
  deriv (fun s => g s v w) u

def partialV (g : ℝ → ℝ → ℝ → ℝ) (u v w : ℝ) : ℝ :=
  deriv (fun s => g u s w) v

def partialW (g : ℝ → ℝ → ℝ → ℝ) (u v w : ℝ) : ℝ :=
  deriv (fun s => g u v s) w

def xCoord (_u v w : ℝ) : ℝ :=
  Real.sqrt (v * w)

def yCoord (u _v w : ℝ) : ℝ :=
  Real.sqrt (u * w)

def zCoord (u v _w : ℝ) : ℝ :=
  Real.sqrt (u * v)

def PositiveDomain (u v w : ℝ) : Prop :=
  0 < u ∧ 0 < v ∧ 0 < w

def F (f : ℝ → ℝ → ℝ → ℝ) (u v w : ℝ) : ℝ :=
  f (xCoord u v w) (yCoord u v w) (zCoord u v w)

def weightedDerivative (g : ℝ → ℝ → ℝ → ℝ) (u v w : ℝ) : ℝ :=
  u * partialU g u v w + v * partialV g u v w + w * partialW g u v w

def coordinateWeighted (f : ℝ → ℝ → ℝ → ℝ) (u v w : ℝ) : ℝ :=
  weightedDerivative xCoord u v w *
      partialU f (xCoord u v w) (yCoord u v w) (zCoord u v w) +
    weightedDerivative yCoord u v w *
      partialV f (xCoord u v w) (yCoord u v w) (zCoord u v w) +
    weightedDerivative zCoord u v w *
      partialW f (xCoord u v w) (yCoord u v w) (zCoord u v w)

def dividedForm (f : ℝ → ℝ → ℝ → ℝ) (u v w : ℝ) : ℝ :=
  (v * w / (2 * xCoord u v w) + w * v / (2 * xCoord u v w)) *
      partialU f (xCoord u v w) (yCoord u v w) (zCoord u v w) +
    (u * w / (2 * yCoord u v w) + w * u / (2 * yCoord u v w)) *
      partialV f (xCoord u v w) (yCoord u v w) (zCoord u v w) +
    (u * v / (2 * zCoord u v w) + v * u / (2 * zCoord u v w)) *
      partialW f (xCoord u v w) (yCoord u v w) (zCoord u v w)

def radialForm (f : ℝ → ℝ → ℝ → ℝ) (u v w : ℝ) : ℝ :=
  xCoord u v w *
      partialU f (xCoord u v w) (yCoord u v w) (zCoord u v w) +
    yCoord u v w *
      partialV f (xCoord u v w) (yCoord u v w) (zCoord u v w) +
    zCoord u v w *
      partialW f (xCoord u v w) (yCoord u v w) (zCoord u v w)

private theorem deriv_uncurry3_comp
    (f : ℝ → ℝ → ℝ → ℝ) (hf : IsC1 f)
    (a b c : ℝ → ℝ) (t : ℝ)
    (ha : DifferentiableAt ℝ a t)
    (hb : DifferentiableAt ℝ b t)
    (hc : DifferentiableAt ℝ c t) :
    deriv (fun s => f (a s) (b s) (c s)) t =
      deriv a t * partialU f (a t) (b t) (c t) +
        deriv b t * partialV f (a t) (b t) (c t) +
        deriv c t * partialW f (a t) (b t) (c t) := by
  have hcont : ContDiff ℝ 1 (uncurry3 f) := hf
  have hf' : DifferentiableAt ℝ (uncurry3 f) (a t, b t, c t) :=
    (hcont.differentiable (by norm_num)).differentiableAt
  let L : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
    fderiv ℝ (uncurry3 f) (a t, b t, c t)
  have hmain :
      HasDerivAt (fun s => f (a s) (b s) (c s))
        (L (deriv a t, deriv b t, deriv c t)) t := by
    have hp :=
      ha.hasDerivAt.hasFDerivAt.prodMk
        (hb.hasDerivAt.hasFDerivAt.prodMk hc.hasDerivAt.hasFDerivAt)
    have hcomp := hf'.hasFDerivAt.comp t hp
    simpa [L, uncurry3] using hcomp.hasDerivAt
  have hU :
      partialU f (a t) (b t) (c t) =
        L ((1 : ℝ), (0 : ℝ), (0 : ℝ)) := by
    have hp :=
      (hasDerivAt_id (a t)).hasFDerivAt.prodMk
        ((hasDerivAt_const (x := a t) (b t)).hasFDerivAt.prodMk
          (hasDerivAt_const (x := a t) (c t)).hasFDerivAt)
    have hcomp := hf'.hasFDerivAt.comp (a t) hp
    have hd := hcomp.hasDerivAt.deriv
    simpa [partialU, L, uncurry3] using hd
  have hV :
      partialV f (a t) (b t) (c t) =
        L ((0 : ℝ), (1 : ℝ), (0 : ℝ)) := by
    have hp :=
      (hasDerivAt_const (x := b t) (a t)).hasFDerivAt.prodMk
        ((hasDerivAt_id (b t)).hasFDerivAt.prodMk
          (hasDerivAt_const (x := b t) (c t)).hasFDerivAt)
    have hcomp := hf'.hasFDerivAt.comp (b t) hp
    have hd := hcomp.hasDerivAt.deriv
    simpa [partialV, L, uncurry3] using hd
  have hW :
      partialW f (a t) (b t) (c t) =
        L ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
    have hp :=
      (hasDerivAt_const (x := c t) (a t)).hasFDerivAt.prodMk
        ((hasDerivAt_const (x := c t) (b t)).hasFDerivAt.prodMk
          (hasDerivAt_id (c t)).hasFDerivAt)
    have hcomp := hf'.hasFDerivAt.comp (c t) hp
    have hd := hcomp.hasDerivAt.deriv
    simpa [partialW, L, uncurry3] using hd
  have hvec :
      (deriv a t, deriv b t, deriv c t) =
        deriv a t • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) +
          deriv b t • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) +
          deriv c t • ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  calc
    deriv (fun s => f (a s) (b s) (c s)) t =
        L (deriv a t, deriv b t, deriv c t) := hmain.deriv
    _ = deriv a t * partialU f (a t) (b t) (c t) +
          deriv b t * partialV f (a t) (b t) (c t) +
          deriv c t * partialW f (a t) (b t) (c t) := by
      rw [hvec]
      simp only [map_add, map_smul, smul_eq_mul]
      rw [← hU, ← hV, ← hW]

private theorem sqrt_mul_deriv_right (a b : ℝ) (hab : 0 < a * b) :
    2 * Real.sqrt (a * b) * deriv (fun s : ℝ => Real.sqrt (a * s)) b = a := by
  have hd :
      HasDerivAt (fun s : ℝ => Real.sqrt (a * s))
        (1 / (2 * Real.sqrt (a * b)) * (a * 1)) b := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_sqrt (ne_of_gt hab)).comp b
        ((hasDerivAt_id b).const_mul a)
  rw [hd.deriv]
  field_simp [ne_of_gt (Real.sqrt_pos.2 hab)] <;> ring

private theorem sqrt_mul_deriv_left (a b : ℝ) (hab : 0 < a * b) :
    2 * Real.sqrt (a * b) * deriv (fun s : ℝ => Real.sqrt (s * b)) a = b := by
  have hd :
      HasDerivAt (fun s : ℝ => Real.sqrt (s * b))
        (1 / (2 * Real.sqrt (a * b)) * (1 * b)) a := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_sqrt (ne_of_gt hab)).comp a
        ((hasDerivAt_id a).mul_const b)
  rw [hd.deriv]
  field_simp [ne_of_gt (Real.sqrt_pos.2 hab)] <;> ring

theorem gap1 (f : ℝ → ℝ → ℝ → ℝ) (hf : IsC1 f) :
    ∀ u v w, PositiveDomain u v w →
      u * partialU (F f) u v w =
        u * partialU f (xCoord u v w) (yCoord u v w) (zCoord u v w) *
            partialU xCoord u v w +
          u * partialV f (xCoord u v w) (yCoord u v w) (zCoord u v w) *
            partialU yCoord u v w +
          u * partialW f (xCoord u v w) (yCoord u v w) (zCoord u v w) *
            partialU zCoord u v w := by
  intro u v w h
  have hx : DifferentiableAt ℝ (fun s : ℝ => xCoord s v w) u := by
    simp [xCoord]
  have hy : DifferentiableAt ℝ (fun s : ℝ => yCoord s v w) u := by
    simpa [yCoord] using
      ((Real.hasDerivAt_sqrt
          (ne_of_gt (mul_pos h.1 h.2.2))).comp u
        ((hasDerivAt_id u).mul_const w)).differentiableAt
  have hz : DifferentiableAt ℝ (fun s : ℝ => zCoord s v w) u := by
    simpa [zCoord] using
      ((Real.hasDerivAt_sqrt
          (ne_of_gt (mul_pos h.1 h.2.1))).comp u
        ((hasDerivAt_id u).mul_const v)).differentiableAt
  have hchain :=
    deriv_uncurry3_comp f hf
      (fun s : ℝ => xCoord s v w)
      (fun s : ℝ => yCoord s v w)
      (fun s : ℝ => zCoord s v w) u hx hy hz
  have hchain' :
      partialU (F f) u v w =
        partialU xCoord u v w *
            partialU f (xCoord u v w) (yCoord u v w) (zCoord u v w) +
          partialU yCoord u v w *
            partialV f (xCoord u v w) (yCoord u v w) (zCoord u v w) +
          partialU zCoord u v w *
            partialW f (xCoord u v w) (yCoord u v w) (zCoord u v w) := by
    simpa [partialU, F] using hchain
  rw [hchain']
  ring

theorem gap2 (f : ℝ → ℝ → ℝ → ℝ) (hf : IsC1 f) :
    ∀ v u w, PositiveDomain u v w →
      v * partialV (F f) u v w =
        v * partialU f (xCoord u v w) (yCoord u v w) (zCoord u v w) *
            partialV xCoord u v w +
          v * partialV f (xCoord u v w) (yCoord u v w) (zCoord u v w) *
            partialV yCoord u v w +
          v * partialW f (xCoord u v w) (yCoord u v w) (zCoord u v w) *
            partialV zCoord u v w := by
  intro v u w h
  have hx : DifferentiableAt ℝ (fun s : ℝ => xCoord u s w) v := by
    simpa [xCoord] using
      ((Real.hasDerivAt_sqrt
          (ne_of_gt (mul_pos h.2.1 h.2.2))).comp v
        ((hasDerivAt_id v).mul_const w)).differentiableAt
  have hy : DifferentiableAt ℝ (fun s : ℝ => yCoord u s w) v := by
    simp [yCoord]
  have hz : DifferentiableAt ℝ (fun s : ℝ => zCoord u s w) v := by
    simpa [zCoord] using
      ((Real.hasDerivAt_sqrt
          (ne_of_gt (mul_pos h.1 h.2.1))).comp v
        ((hasDerivAt_id v).const_mul u)).differentiableAt
  have hchain :=
    deriv_uncurry3_comp f hf
      (fun s : ℝ => xCoord u s w)
      (fun s : ℝ => yCoord u s w)
      (fun s : ℝ => zCoord u s w) v hx hy hz
  have hchain' :
      partialV (F f) u v w =
        partialV xCoord u v w *
            partialU f (xCoord u v w) (yCoord u v w) (zCoord u v w) +
          partialV yCoord u v w *
            partialV f (xCoord u v w) (yCoord u v w) (zCoord u v w) +
          partialV zCoord u v w *
            partialW f (xCoord u v w) (yCoord u v w) (zCoord u v w) := by
    simpa [partialV, F] using hchain
  rw [hchain']
  ring

theorem gap3 (f : ℝ → ℝ → ℝ → ℝ) (hf : IsC1 f) :
    ∀ w u v, PositiveDomain u v w →
      w * partialW (F f) u v w =
        w * partialU f (xCoord u v w) (yCoord u v w) (zCoord u v w) *
            partialW xCoord u v w +
          w * partialV f (xCoord u v w) (yCoord u v w) (zCoord u v w) *
            partialW yCoord u v w +
          w * partialW f (xCoord u v w) (yCoord u v w) (zCoord u v w) *
            partialW zCoord u v w := by
  intro w u v h
  have hx : DifferentiableAt ℝ (fun s : ℝ => xCoord u v s) w := by
    simpa [xCoord] using
      ((Real.hasDerivAt_sqrt
          (ne_of_gt (mul_pos h.2.1 h.2.2))).comp w
        ((hasDerivAt_id w).const_mul v)).differentiableAt
  have hy : DifferentiableAt ℝ (fun s : ℝ => yCoord u v s) w := by
    simpa [yCoord] using
      ((Real.hasDerivAt_sqrt
          (ne_of_gt (mul_pos h.1 h.2.2))).comp w
        ((hasDerivAt_id w).const_mul u)).differentiableAt
  have hz : DifferentiableAt ℝ (fun s : ℝ => zCoord u v s) w := by
    simp [zCoord]
  have hchain :=
    deriv_uncurry3_comp f hf
      (fun s : ℝ => xCoord u v s)
      (fun s : ℝ => yCoord u v s)
      (fun s : ℝ => zCoord u v s) w hx hy hz
  have hchain' :
      partialW (F f) u v w =
        partialW xCoord u v w *
            partialU f (xCoord u v w) (yCoord u v w) (zCoord u v w) +
          partialW yCoord u v w *
            partialV f (xCoord u v w) (yCoord u v w) (zCoord u v w) +
          partialW zCoord u v w *
            partialW f (xCoord u v w) (yCoord u v w) (zCoord u v w) := by
    simpa [partialW, F] using hchain
  rw [hchain']
  ring

theorem gap4 (f : ℝ → ℝ → ℝ → ℝ) (hf : IsC1 f) :
    ∀ u v w, PositiveDomain u v w →
      weightedDerivative (F f) u v w = coordinateWeighted f u v w := by
  intro u v w h
  unfold coordinateWeighted weightedDerivative
  rw [gap1 f hf u v w h, gap2 f hf v u w h, gap3 f hf w u v h]
  ring

theorem gap5 :
    ∀ u v w, PositiveDomain u v w →
      2 * xCoord u v w * partialU xCoord u v w = 0 := by
  intro u v w _
  simp [xCoord, partialU]

theorem gap6 :
    ∀ u v w, PositiveDomain u v w → partialU xCoord u v w = 0 := by
  intro u v w _
  simp [xCoord, partialU]

theorem gap7 :
    ∀ u v w, PositiveDomain u v w → partialV yCoord u v w = 0 := by
  intro u v w _
  simp [yCoord, partialV]

theorem gap8 :
    ∀ u v w, PositiveDomain u v w → partialW zCoord u v w = 0 := by
  intro u v w _
  simp [zCoord, partialW]

theorem gap9 :
    ∀ u v w, PositiveDomain u v w →
      2 * xCoord u v w * partialW xCoord u v w = v := by
  intro u v w h
  simpa [xCoord, partialW] using
    sqrt_mul_deriv_right v w (mul_pos h.2.1 h.2.2)

theorem gap10 :
    ∀ u v w, PositiveDomain u v w →
      2 * xCoord u v w * partialV xCoord u v w = w := by
  intro u v w h
  simpa [xCoord, partialV] using
    sqrt_mul_deriv_left v w (mul_pos h.2.1 h.2.2)

theorem gap11 :
    ∀ u v w, PositiveDomain u v w →
      2 * yCoord u v w * partialU yCoord u v w = w := by
  intro u v w h
  simpa [yCoord, partialU] using
    sqrt_mul_deriv_left u w (mul_pos h.1 h.2.2)

theorem gap12 :
    ∀ u v w, PositiveDomain u v w →
      2 * yCoord u v w * partialW yCoord u v w = u := by
  intro u v w h
  simpa [yCoord, partialW] using
    sqrt_mul_deriv_right u w (mul_pos h.1 h.2.2)

theorem gap13 :
    ∀ u v w, PositiveDomain u v w →
      2 * zCoord u v w * partialU zCoord u v w = v := by
  intro u v w h
  simpa [zCoord, partialU] using
    sqrt_mul_deriv_left u v (mul_pos h.1 h.2.1)

theorem gap14 :
    ∀ u v w, PositiveDomain u v w →
      2 * zCoord u v w * partialV zCoord u v w = u := by
  intro u v w h
  simpa [zCoord, partialV] using
    sqrt_mul_deriv_right u v (mul_pos h.1 h.2.1)

theorem gap15 (f : ℝ → ℝ → ℝ → ℝ) (hf : IsC1 f) :
    ∀ u v w, PositiveDomain u v w →
      weightedDerivative (F f) u v w = dividedForm f u v w := by
  intro u v w h
  have hxne : xCoord u v w ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (mul_pos h.2.1 h.2.2))
  have hyne : yCoord u v w ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (mul_pos h.1 h.2.2))
  have hzne : zCoord u v w ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (mul_pos h.1 h.2.1))
  have hxden : 2 * xCoord u v w ≠ 0 := mul_ne_zero (by norm_num) hxne
  have hyden : 2 * yCoord u v w ≠ 0 := mul_ne_zero (by norm_num) hyne
  have hzden : 2 * zCoord u v w ≠ 0 := mul_ne_zero (by norm_num) hzne
  have hxu : partialU xCoord u v w = 0 := gap6 u v w h
  have hxv : partialV xCoord u v w = w / (2 * xCoord u v w) := by
    apply (eq_div_iff hxden).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using gap10 u v w h
  have hxw : partialW xCoord u v w = v / (2 * xCoord u v w) := by
    apply (eq_div_iff hxden).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using gap9 u v w h
  have hyu : partialU yCoord u v w = w / (2 * yCoord u v w) := by
    apply (eq_div_iff hyden).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using gap11 u v w h
  have hyv : partialV yCoord u v w = 0 := gap7 u v w h
  have hyw : partialW yCoord u v w = u / (2 * yCoord u v w) := by
    apply (eq_div_iff hyden).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using gap12 u v w h
  have hzu : partialU zCoord u v w = v / (2 * zCoord u v w) := by
    apply (eq_div_iff hzden).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using gap13 u v w h
  have hzv : partialV zCoord u v w = u / (2 * zCoord u v w) := by
    apply (eq_div_iff hzden).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using gap14 u v w h
  have hzw : partialW zCoord u v w = 0 := gap8 u v w h
  rw [gap4 f hf u v w h]
  unfold coordinateWeighted dividedForm weightedDerivative
  rw [hxu, hxv, hxw, hyu, hyv, hyw, hzu, hzv, hzw]
  ring

theorem gap16 (f : ℝ → ℝ → ℝ → ℝ) :
    ∀ v w u, PositiveDomain u v w →
      dividedForm f u v w = radialForm f u v w := by
  intro v w u h
  have hxpos : 0 < xCoord u v w := by
    exact Real.sqrt_pos.2 (mul_pos h.2.1 h.2.2)
  have hypos : 0 < yCoord u v w := by
    exact Real.sqrt_pos.2 (mul_pos h.1 h.2.2)
  have hzpos : 0 < zCoord u v w := by
    exact Real.sqrt_pos.2 (mul_pos h.1 h.2.1)
  have hxsq : (xCoord u v w) ^ 2 = v * w := by
    exact Real.sq_sqrt (le_of_lt (mul_pos h.2.1 h.2.2))
  have hysq : (yCoord u v w) ^ 2 = u * w := by
    exact Real.sq_sqrt (le_of_lt (mul_pos h.1 h.2.2))
  have hzsq : (zCoord u v w) ^ 2 = u * v := by
    exact Real.sq_sqrt (le_of_lt (mul_pos h.1 h.2.1))
  have hxc :
      v * w / (2 * xCoord u v w) + w * v / (2 * xCoord u v w) =
        xCoord u v w := by
    field_simp [ne_of_gt hxpos] <;> nlinarith [hxsq]
  have hyc :
      u * w / (2 * yCoord u v w) + w * u / (2 * yCoord u v w) =
        yCoord u v w := by
    field_simp [ne_of_gt hypos] <;> nlinarith [hysq]
  have hzc :
      u * v / (2 * zCoord u v w) + v * u / (2 * zCoord u v w) =
        zCoord u v w := by
    field_simp [ne_of_gt hzpos] <;> nlinarith [hzsq]
  unfold dividedForm radialForm
  rw [hxc, hyc, hzc]

theorem gap17 (f : ℝ → ℝ → ℝ → ℝ) (hf : IsC1 f) :
    ∀ u v w, PositiveDomain u v w →
      weightedDerivative (F f) u v w = radialForm f u v w := by
  intro u v w h
  calc
    weightedDerivative (F f) u v w = dividedForm f u v w :=
      gap15 f hf u v w h
    _ = radialForm f u v w := gap16 f v w u h

theorem gap18 (f : ℝ → ℝ → ℝ → ℝ) (hf : IsC1 f) :
    ∀ u v w, PositiveDomain u v w →
      radialForm f u v w = weightedDerivative (F f) u v w := by
  intro u v w h
  exact (gap17 f hf u v w h).symm

end

end ProofGap.Exercise3320
