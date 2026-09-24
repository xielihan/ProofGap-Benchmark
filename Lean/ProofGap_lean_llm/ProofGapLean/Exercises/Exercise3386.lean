import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3386

noncomputable section

def r (x y : ℝ) : ℝ :=
  Real.sqrt (x ^ 2 - y ^ 2)

def partialX (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => z t y) x

def partialY (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => z x t) y

def partialXX (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX z t y) x

def partialXY (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX z x t) y

def partialYY (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY z x t) y

def firstDifferential (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  partialX z x y * dx + partialY z x y * dy

def secondDifferential (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  partialXX z x y * dx ^ 2 +
    2 * partialXY z x y * dx * dy +
      partialYY z x y * dy ^ 2

def quotientField (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  z x y / r x y

def IsC2Surface (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ) : Prop :=
  IsOpen D ∧ ContDiffOn ℝ 2 (Function.uncurry z) D ∧
    ∀ p ∈ D,
      0 < p.1 ^ 2 - p.2 ^ 2 ∧ z p.1 p.2 ≠ 0 ∧
        z p.1 p.2 =
          r p.1 p.2 * Real.tan (quotientField z p.1 p.2)

theorem gap1 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D,
      quotientField z p.1 p.2 =
        Real.tan (quotientField z p.1 p.2) := by
  intro p hp
  have hs := h.2.2 p hp
  have hr : r p.1 p.2 ≠ 0 :=
    (Real.sqrt_pos.2 hs.1).ne'
  apply (div_eq_iff hr).2
  simpa [quotientField, mul_comm] using hs.2.2

theorem gap2 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D, ∀ dx dy,
      firstDifferential (quotientField z) p.1 p.2 dx dy =
        (1 + quotientField z p.1 p.2 ^ 2) *
          firstDifferential (quotientField z) p.1 p.2 dx dy := by
  intro p hp dx dy
  have hs := h.2.2 p hp
  have hA : 0 < p.1 ^ 2 - p.2 ^ 2 := hs.1
  have hr : r p.1 p.2 ≠ 0 := (Real.sqrt_pos.2 hA).ne'
  have hzpair : DifferentiableAt ℝ (Function.uncurry z) p :=
    (h.2.1.contDiffAt (h.1.mem_nhds hp)).differentiableAt
      (by intro he; cases he)
  have hzx : DifferentiableAt ℝ (fun t : ℝ => z t p.2) p.1 := by
    simpa [Function.uncurry] using
      hzpair.comp p.1
        (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => (t, p.2)) p.1)
  have hzy : DifferentiableAt ℝ (fun t : ℝ => z p.1 t) p.2 := by
    simpa [Function.uncurry] using
      hzpair.comp p.2
        (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => (p.1, t)) p.2)
  have hrx : DifferentiableAt ℝ (fun t : ℝ => r t p.2) p.1 := by
    unfold r
    exact (Real.hasDerivAt_sqrt hA.ne').differentiableAt.comp p.1 (by fun_prop)
  have hry : DifferentiableAt ℝ (fun t : ℝ => r p.1 t) p.2 := by
    unfold r
    exact (Real.hasDerivAt_sqrt hA.ne').differentiableAt.comp p.2 (by fun_prop)
  have hqx : DifferentiableAt ℝ
      (fun t : ℝ => quotientField z t p.2) p.1 := by
    exact hzx.div hrx hr
  have hqy : DifferentiableAt ℝ
      (fun t : ℝ => quotientField z p.1 t) p.2 := by
    exact hzy.div hry hr
  let q := quotientField z p.1 p.2
  have hqeq : q = Real.tan q := gap1 D z h p hp
  have hqne : q ≠ 0 := by
    exact div_ne_zero hs.2.1 hr
  have hcos : Real.cos q ≠ 0 := by
    intro hc
    have ht0 : Real.tan q = 0 := by
      simp [Real.tan_eq_sin_div_cos, hc]
    exact hqne (hqeq.trans ht0)
  have hqsin : q * Real.cos q = Real.sin q := by
    have ht : q = Real.sin q / Real.cos q := by
      simpa [Real.tan_eq_sin_div_cos] using hqeq
    field_simp [hcos] at ht
    exact ht
  have hqsin2 : (q * Real.cos q) ^ 2 = Real.sin q ^ 2 :=
    congrArg (fun u : ℝ => u ^ 2) hqsin
  have hsec : 1 / Real.cos q ^ 2 = 1 + q ^ 2 := by
    field_simp [hcos]
    nlinarith [Real.sin_sq_add_cos_sq q, hqsin2]
  have hcurveX : ContinuousAt (fun t : ℝ => (t, p.2)) p.1 := by fun_prop
  have heventX :
      (fun t : ℝ => quotientField z t p.2) =ᶠ[nhds p.1]
        (fun t : ℝ => Real.tan (quotientField z t p.2)) := by
    filter_upwards [hcurveX.tendsto.eventually (h.1.mem_nhds hp)] with t ht
    exact gap1 D z h (t, p.2) ht
  have hchainX :=
    (Real.hasDerivAt_tan hcos).comp p.1 hqx.hasDerivAt
  have hsameX := hchainX.congr_of_eventuallyEq (by
    simpa [Function.comp_def] using heventX)
  have hdx :
      partialX (quotientField z) p.1 p.2 =
        (1 + q ^ 2) * partialX (quotientField z) p.1 p.2 := by
    have hd := hsameX.deriv
    simpa [partialX, q, hsec] using hd
  have hcurveY : ContinuousAt (fun t : ℝ => (p.1, t)) p.2 := by fun_prop
  have heventY :
      (fun t : ℝ => quotientField z p.1 t) =ᶠ[nhds p.2]
        (fun t : ℝ => Real.tan (quotientField z p.1 t)) := by
    filter_upwards [hcurveY.tendsto.eventually (h.1.mem_nhds hp)] with t ht
    exact gap1 D z h (p.1, t) ht
  have hchainY :=
    (Real.hasDerivAt_tan hcos).comp p.2 hqy.hasDerivAt
  have hsameY := hchainY.congr_of_eventuallyEq (by
    simpa [Function.comp_def] using heventY)
  have hdy :
      partialY (quotientField z) p.1 p.2 =
        (1 + q ^ 2) * partialY (quotientField z) p.1 p.2 := by
    have hd := hsameY.deriv
    simpa [partialY, q, hsec] using hd
  unfold firstDifferential
  calc
    partialX (quotientField z) p.1 p.2 * dx +
        partialY (quotientField z) p.1 p.2 * dy =
      ((1 + q ^ 2) * partialX (quotientField z) p.1 p.2) * dx +
        ((1 + q ^ 2) * partialY (quotientField z) p.1 p.2) * dy := by
          rw [← hdx, ← hdy]
    _ = (1 + quotientField z p.1 p.2 ^ 2) *
        (partialX (quotientField z) p.1 p.2 * dx +
          partialY (quotientField z) p.1 p.2 * dy) := by
      dsimp [q]
      ring

theorem gap3 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D, ∀ dx dy,
      firstDifferential (quotientField z) p.1 p.2 dx dy = 0 := by
  intro p hp dx dy
  have hs := h.2.2 p hp
  have hr : r p.1 p.2 ≠ 0 := (Real.sqrt_pos.2 hs.1).ne'
  have hqne : quotientField z p.1 p.2 ≠ 0 :=
    div_ne_zero hs.2.1 hr
  have hd := gap2 D z h p hp dx dy
  have hz : quotientField z p.1 p.2 ^ 2 *
      firstDifferential (quotientField z) p.1 p.2 dx dy = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hz with hq | hd0
  · exact (pow_ne_zero 2 hqne hq).elim
  · exact hd0

theorem gap4 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D, ∀ dx dy,
      r p.1 p.2 * firstDifferential z p.1 p.2 dx dy -
        z p.1 p.2 *
          ((p.1 * dx - p.2 * dy) / r p.1 p.2) = 0 := by
  intro p hp dx dy
  have hs := h.2.2 p hp
  have hA : 0 < p.1 ^ 2 - p.2 ^ 2 := hs.1
  have hr : r p.1 p.2 ≠ 0 := (Real.sqrt_pos.2 hA).ne'
  have hzpair : DifferentiableAt ℝ (Function.uncurry z) p :=
    (h.2.1.contDiffAt (h.1.mem_nhds hp)).differentiableAt
      (by intro he; cases he)
  have hzx : DifferentiableAt ℝ (fun t : ℝ => z t p.2) p.1 := by
    simpa [Function.uncurry] using
      hzpair.comp p.1
        (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => (t, p.2)) p.1)
  have hzy : DifferentiableAt ℝ (fun t : ℝ => z p.1 t) p.2 := by
    simpa [Function.uncurry] using
      hzpair.comp p.2
        (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => (p.1, t)) p.2)
  have hiX : HasDerivAt (fun t : ℝ => t ^ 2 - p.2 ^ 2) (2 * p.1) p.1 := by
    convert (((hasDerivAt_id p.1).pow 2).sub_const (p.2 ^ 2)) using 1 <;>
      simp [id] <;> ring
  have hiY : HasDerivAt (fun t : ℝ => p.1 ^ 2 - t ^ 2) (-2 * p.2) p.2 := by
    convert ((hasDerivAt_const (x := p.2) (c := p.1 ^ 2)).sub
      ((hasDerivAt_id p.2).pow 2)) using 1 <;> simp [id] <;> ring
  have hrX : HasDerivAt (fun t : ℝ => r t p.2)
      (p.1 / r p.1 p.2) p.1 := by
    have ht := (Real.hasDerivAt_sqrt hA.ne').comp p.1 hiX
    have hcoef :
        1 / (2 * Real.sqrt (p.1 ^ 2 - p.2 ^ 2)) * (2 * p.1) =
          p.1 / Real.sqrt (p.1 ^ 2 - p.2 ^ 2) := by
      field_simp [(Real.sqrt_pos.2 hA).ne']
    simpa only [Function.comp_apply, r, hcoef] using ht
  have hrY : HasDerivAt (fun t : ℝ => r p.1 t)
      (-p.2 / r p.1 p.2) p.2 := by
    have ht := (Real.hasDerivAt_sqrt hA.ne').comp p.2 hiY
    have hcoef :
        1 / (2 * Real.sqrt (p.1 ^ 2 - p.2 ^ 2)) * (-2 * p.2) =
          -p.2 / Real.sqrt (p.1 ^ 2 - p.2 ^ 2) := by
      field_simp [(Real.sqrt_pos.2 hA).ne']
    simpa only [Function.comp_apply, r, hcoef] using ht
  have hqx0 : partialX (quotientField z) p.1 p.2 = 0 := by
    simpa [firstDifferential] using gap3 D z h p hp 1 0
  have hqy0 : partialY (quotientField z) p.1 p.2 = 0 := by
    simpa [firstDifferential] using gap3 D z h p hp 0 1
  have hquotX := hzx.hasDerivAt.div hrX hr
  have hquotY := hzy.hasDerivAt.div hrY hr
  have heqX :
      0 = (partialX z p.1 p.2 * r p.1 p.2 -
        z p.1 p.2 * (p.1 / r p.1 p.2)) / r p.1 p.2 ^ 2 := by
    calc
      0 = partialX (quotientField z) p.1 p.2 := hqx0.symm
      _ = (partialX z p.1 p.2 * r p.1 p.2 -
          z p.1 p.2 * (p.1 / r p.1 p.2)) / r p.1 p.2 ^ 2 := by
        simpa [partialX, quotientField] using hquotX.deriv
  have heqY :
      0 = (partialY z p.1 p.2 * r p.1 p.2 -
        z p.1 p.2 * (-p.2 / r p.1 p.2)) / r p.1 p.2 ^ 2 := by
    calc
      0 = partialY (quotientField z) p.1 p.2 := hqy0.symm
      _ = (partialY z p.1 p.2 * r p.1 p.2 -
          z p.1 p.2 * (-p.2 / r p.1 p.2)) / r p.1 p.2 ^ 2 := by
        simpa [partialY, quotientField] using hquotY.deriv
  have hxrel :
      r p.1 p.2 * partialX z p.1 p.2 -
        z p.1 p.2 * (p.1 / r p.1 p.2) = 0 := by
    field_simp [hr] at heqX ⊢
    ring_nf at heqX ⊢
    linarith
  have hyrel :
      r p.1 p.2 * partialY z p.1 p.2 -
        z p.1 p.2 * (-p.2 / r p.1 p.2) = 0 := by
    field_simp [hr] at heqY ⊢
    ring_nf at heqY ⊢
    linarith
  unfold firstDifferential
  calc
    r p.1 p.2 *
          (partialX z p.1 p.2 * dx + partialY z p.1 p.2 * dy) -
        z p.1 p.2 * ((p.1 * dx - p.2 * dy) / r p.1 p.2) =
      (r p.1 p.2 * partialX z p.1 p.2 -
          z p.1 p.2 * (p.1 / r p.1 p.2)) * dx +
        (r p.1 p.2 * partialY z p.1 p.2 -
          z p.1 p.2 * (-p.2 / r p.1 p.2)) * dy := by
            field_simp [hr]
            ring
    _ = 0 := by rw [hxrel, hyrel]; ring

theorem gap5 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D, ∀ dx dy,
      firstDifferential z p.1 p.2 dx dy =
        z p.1 p.2 / r p.1 p.2 ^ 2 *
          (p.1 * dx - p.2 * dy) := by
  intro p hp dx dy
  have hA := (h.2.2 p hp).1
  have hr : r p.1 p.2 ≠ 0 := (Real.sqrt_pos.2 hA).ne'
  have heq := gap4 D z h p hp dx dy
  field_simp [hr] at heq ⊢
  nlinarith

theorem gap6 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D,
      partialX z p.1 p.2 =
        z p.1 p.2 * p.1 / r p.1 p.2 ^ 2 := by
  intro p hp
  have heq := gap5 D z h p hp 1 0
  simp only [firstDifferential, mul_one, mul_zero, add_zero, sub_zero] at heq
  calc
    partialX z p.1 p.2 = z p.1 p.2 / r p.1 p.2 ^ 2 * p.1 := heq
    _ = z p.1 p.2 * p.1 / r p.1 p.2 ^ 2 := by ring

theorem gap7 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D,
      z p.1 p.2 * p.1 / r p.1 p.2 ^ 2 =
        p.1 * z p.1 p.2 / (p.1 ^ 2 - p.2 ^ 2) := by
  intro p hp
  have hA := (h.2.2 p hp).1
  have hrsq : r p.1 p.2 ^ 2 = p.1 ^ 2 - p.2 ^ 2 := by
    exact Real.sq_sqrt hA.le
  rw [hrsq]
  ring

theorem gap8 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D,
      partialX z p.1 p.2 =
        p.1 * z p.1 p.2 / (p.1 ^ 2 - p.2 ^ 2) := by
  intro p hp
  calc
    partialX z p.1 p.2 =
        z p.1 p.2 * p.1 / r p.1 p.2 ^ 2 := gap6 D z h p hp
    _ = p.1 * z p.1 p.2 / (p.1 ^ 2 - p.2 ^ 2) := gap7 D z h p hp

theorem gap9 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D,
      partialY z p.1 p.2 =
        -(p.2 * z p.1 p.2 / r p.1 p.2 ^ 2) := by
  intro p hp
  have heq := gap5 D z h p hp 0 1
  simp only [firstDifferential, mul_zero, zero_add, zero_sub, mul_one] at heq
  calc
    partialY z p.1 p.2 = -(z p.1 p.2 / r p.1 p.2 ^ 2 * p.2) := by
      simpa only [mul_neg] using heq
    _ = -(p.2 * z p.1 p.2 / r p.1 p.2 ^ 2) := by ring

theorem gap10 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D,
      -(p.2 * z p.1 p.2 / r p.1 p.2 ^ 2) =
        -(p.2 * z p.1 p.2 / (p.1 ^ 2 - p.2 ^ 2)) := by
  intro p hp
  have hA := (h.2.2 p hp).1
  have hrsq : r p.1 p.2 ^ 2 = p.1 ^ 2 - p.2 ^ 2 := by
    exact Real.sq_sqrt hA.le
  rw [hrsq]

theorem gap11 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D,
      partialY z p.1 p.2 =
        -(p.2 * z p.1 p.2 / (p.1 ^ 2 - p.2 ^ 2)) := by
  intro p hp
  calc
    partialY z p.1 p.2 =
        -(p.2 * z p.1 p.2 / r p.1 p.2 ^ 2) := gap9 D z h p hp
    _ = -(p.2 * z p.1 p.2 / (p.1 ^ 2 - p.2 ^ 2)) := gap10 D z h p hp

theorem gap12 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D, ∀ dx dy,
      (p.1 ^ 2 - p.2 ^ 2) *
          firstDifferential z p.1 p.2 dx dy =
        p.1 * z p.1 p.2 * dx - p.2 * z p.1 p.2 * dy := by
  intro p hp dx dy
  have hA := (h.2.2 p hp).1
  have hx := gap8 D z h p hp
  have hy := gap11 D z h p hp
  unfold firstDifferential
  rw [hx, hy]
  field_simp [hA.ne']
  ring

theorem gap13 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D, ∀ dx dy,
      (p.1 ^ 2 - p.2 ^ 2) *
          secondDifferential z p.1 p.2 dx dy =
        -(p.1 * dx - p.2 * dy) *
            (z p.1 p.2 * (p.1 * dx - p.2 * dy) /
              (p.1 ^ 2 - p.2 ^ 2)) +
          z p.1 p.2 * dx ^ 2 - z p.1 p.2 * dy ^ 2 := by
  intro p hp dx dy
  have hA : 0 < p.1 ^ 2 - p.2 ^ 2 := (h.2.2 p hp).1
  have hA0 : p.1 ^ 2 - p.2 ^ 2 ≠ 0 := hA.ne'
  have hzpair : DifferentiableAt ℝ (Function.uncurry z) p :=
    (h.2.1.contDiffAt (h.1.mem_nhds hp)).differentiableAt
      (by intro he; cases he)
  have hzx : DifferentiableAt ℝ (fun t : ℝ => z t p.2) p.1 := by
    simpa [Function.uncurry] using
      hzpair.comp p.1
        (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => (t, p.2)) p.1)
  have hzy : DifferentiableAt ℝ (fun t : ℝ => z p.1 t) p.2 := by
    simpa [Function.uncurry] using
      hzpair.comp p.2
        (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => (p.1, t)) p.2)
  have hzx' : HasDerivAt (fun t : ℝ => z t p.2)
      (partialX z p.1 p.2) p.1 := by
    simpa [partialX] using hzx.hasDerivAt
  have hzy' : HasDerivAt (fun t : ℝ => z p.1 t)
      (partialY z p.1 p.2) p.2 := by
    simpa [partialY] using hzy.hasDerivAt
  have hdenX : HasDerivAt (fun t : ℝ => t ^ 2 - p.2 ^ 2)
      (2 * p.1) p.1 := by
    convert (((hasDerivAt_id p.1).pow 2).sub_const (p.2 ^ 2)) using 1 <;>
      simp [id] <;> ring
  have hdenY : HasDerivAt (fun t : ℝ => p.1 ^ 2 - t ^ 2)
      (-2 * p.2) p.2 := by
    convert ((hasDerivAt_const (x := p.2) (c := p.1 ^ 2)).sub
      ((hasDerivAt_id p.2).pow 2)) using 1 <;> simp [id] <;> ring
  have hnumX : HasDerivAt (fun t : ℝ => t * z t p.2)
      (z p.1 p.2 + p.1 * partialX z p.1 p.2) p.1 := by
    convert (hasDerivAt_id p.1).mul hzx' using 1 <;> simp [id] <;> ring
  have hnumXY : HasDerivAt (fun t : ℝ => p.1 * z p.1 t)
      (p.1 * partialY z p.1 p.2) p.2 := by
    convert (hasDerivAt_const (x := p.2) (c := p.1)).mul hzy' using 1 <;>
      simp <;> ring
  have hnumY : HasDerivAt (fun t : ℝ => t * z p.1 t)
      (z p.1 p.2 + p.2 * partialY z p.1 p.2) p.2 := by
    convert (hasDerivAt_id p.2).mul hzy' using 1 <;> simp [id] <;> ring
  have hcurveX : ContinuousAt (fun t : ℝ => (t, p.2)) p.1 := by fun_prop
  have hcurveY : ContinuousAt (fun t : ℝ => (p.1, t)) p.2 := by fun_prop
  have heventXX :
      (fun t : ℝ => partialX z t p.2) =ᶠ[nhds p.1]
        (fun t : ℝ => t * z t p.2 / (t ^ 2 - p.2 ^ 2)) := by
    filter_upwards [hcurveX.tendsto.eventually (h.1.mem_nhds hp)] with t ht
    exact gap8 D z h (t, p.2) ht
  have heventXY :
      (fun t : ℝ => partialX z p.1 t) =ᶠ[nhds p.2]
        (fun t : ℝ => p.1 * z p.1 t / (p.1 ^ 2 - t ^ 2)) := by
    filter_upwards [hcurveY.tendsto.eventually (h.1.mem_nhds hp)] with t ht
    exact gap8 D z h (p.1, t) ht
  have heventYY :
      (fun t : ℝ => partialY z p.1 t) =ᶠ[nhds p.2]
        (fun t : ℝ => -(t * z p.1 t / (p.1 ^ 2 - t ^ 2))) := by
    filter_upwards [hcurveY.tendsto.eventually (h.1.mem_nhds hp)] with t ht
    exact gap11 D z h (p.1, t) ht
  have hderivXX :=
    (hnumX.div hdenX hA0).congr_of_eventuallyEq (by
      simpa only [Pi.div_apply] using heventXX)
  have hderivXY :=
    (hnumXY.div hdenY hA0).congr_of_eventuallyEq (by
      simpa only [Pi.div_apply] using heventXY)
  have hderivYY :=
    ((hnumY.div hdenY hA0).neg).congr_of_eventuallyEq (by
      simpa only [Pi.div_apply, Pi.neg_apply] using heventYY)
  have hpx := gap8 D z h p hp
  have hpy := gap11 D z h p hp
  have hxx : partialXX z p.1 p.2 =
      -(p.2 ^ 2 * z p.1 p.2) / (p.1 ^ 2 - p.2 ^ 2) ^ 2 := by
    unfold partialXX
    rw [hderivXX.deriv, hpx]
    field_simp [hA0]
    ring
  have hxy : partialXY z p.1 p.2 =
      p.1 * p.2 * z p.1 p.2 / (p.1 ^ 2 - p.2 ^ 2) ^ 2 := by
    unfold partialXY
    rw [hderivXY.deriv, hpy]
    field_simp [hA0]
    ring
  have hyy : partialYY z p.1 p.2 =
      -(p.1 ^ 2 * z p.1 p.2) / (p.1 ^ 2 - p.2 ^ 2) ^ 2 := by
    unfold partialYY
    rw [hderivYY.deriv, hpy]
    field_simp [hA0]
    ring
  unfold secondDifferential
  rw [hxx, hxy, hyy]
  field_simp [hA0]
  ring

theorem gap14 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D, ∀ dx dy,
      (p.1 ^ 2 - p.2 ^ 2) *
          secondDifferential z p.1 p.2 dx dy =
        z p.1 p.2 *
          (-(p.2 ^ 2) * dx ^ 2 +
            2 * p.1 * p.2 * dx * dy -
            p.1 ^ 2 * dy ^ 2) /
          (p.1 ^ 2 - p.2 ^ 2) := by
  intro p hp dx dy
  have hA := (h.2.2 p hp).1
  calc
    (p.1 ^ 2 - p.2 ^ 2) *
          secondDifferential z p.1 p.2 dx dy =
      -(p.1 * dx - p.2 * dy) *
            (z p.1 p.2 * (p.1 * dx - p.2 * dy) /
              (p.1 ^ 2 - p.2 ^ 2)) +
          z p.1 p.2 * dx ^ 2 - z p.1 p.2 * dy ^ 2 :=
      gap13 D z h p hp dx dy
    _ = z p.1 p.2 *
          (-(p.2 ^ 2) * dx ^ 2 +
            2 * p.1 * p.2 * dx * dy -
            p.1 ^ 2 * dy ^ 2) /
          (p.1 ^ 2 - p.2 ^ 2) := by
      field_simp [hA.ne']
      ring

theorem gap15 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D,
      partialXX z p.1 p.2 =
        -(p.2 ^ 2 * z p.1 p.2) /
          (p.1 ^ 2 - p.2 ^ 2) ^ 2 := by
  intro p hp
  have hA := (h.2.2 p hp).1
  have hh := gap14 D z h p hp 1 0
  simp [secondDifferential] at hh
  field_simp [hA.ne'] at hh ⊢
  nlinarith

theorem gap16 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D,
      partialXY z p.1 p.2 =
        p.1 * p.2 * z p.1 p.2 /
          (p.1 ^ 2 - p.2 ^ 2) ^ 2 := by
  intro p hp
  have hA := (h.2.2 p hp).1
  have hplus := gap14 D z h p hp 1 1
  have hminus := gap14 D z h p hp 1 (-1)
  simp [secondDifferential] at hplus hminus
  field_simp [hA.ne'] at hplus hminus ⊢
  ring_nf at hplus hminus ⊢
  linarith

theorem gap17 (D : Set (ℝ × ℝ)) (z : ℝ → ℝ → ℝ)
    (h : IsC2Surface D z) :
    ∀ p ∈ D,
      partialYY z p.1 p.2 =
        -(p.1 ^ 2 * z p.1 p.2) /
          (p.1 ^ 2 - p.2 ^ 2) ^ 2 := by
  intro p hp
  have hA := (h.2.2 p hp).1
  have hh := gap14 D z h p hp 0 1
  simp [secondDifferential] at hh
  field_simp [hA.ne'] at hh ⊢
  nlinarith

end

end ProofGap.Exercise3386
