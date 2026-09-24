import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise949

noncomputable section

def root (x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2)

def y (x : ℝ) : ℝ :=
  root x * Real.log (Real.sqrt ((1 - x) / (1 + x))) +
    (1 / 2 : ℝ) * Real.log ((1 - root x) / (1 + root x)) +
    root x + Real.arcsin x

def expandedDerivative (x : ℝ) : ℝ :=
  -(x / root x) * Real.log (Real.sqrt ((1 - x) / (1 + x))) +
    (1 / 2 : ℝ) * root x * (-(1 / (1 - x)) - 1 / (1 + x)) +
    (1 / 2 : ℝ) *
      (x / ((1 - root x) * root x) +
        x / ((1 + root x) * root x)) -
    x / root x + 1 / root x

def finalDerivative (x : ℝ) : ℝ :=
  root x / x -
    x / root x * Real.log (Real.sqrt ((1 - x) / (1 + x)))

private theorem sqrtCompHasDerivAt {f : ℝ → ℝ} {f' x : ℝ}
    (hx : 0 < f x) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t => Real.sqrt (f t))
      (f' / (2 * Real.sqrt (f x))) x := by
  have hsqrt_exp : ∀ z : ℝ, 0 < z →
      Real.sqrt z = Real.exp ((1 / 2 : ℝ) * Real.log z) := by
    intro z hz
    have he_sq :
        Real.exp ((1 / 2 : ℝ) * Real.log z) ^ 2 = z := by
      calc
        Real.exp ((1 / 2 : ℝ) * Real.log z) ^ 2 =
            Real.exp ((1 / 2 : ℝ) * Real.log z) *
              Real.exp ((1 / 2 : ℝ) * Real.log z) := by ring
        _ = Real.exp
              ((1 / 2 : ℝ) * Real.log z +
                (1 / 2 : ℝ) * Real.log z) := by
              rw [Real.exp_add]
        _ = Real.exp (Real.log z) := by congr 1 <;> ring
        _ = z := Real.exp_log hz
    nlinarith [Real.sq_sqrt (le_of_lt hz), Real.sqrt_nonneg z,
      Real.exp_pos ((1 / 2 : ℝ) * Real.log z)]
  have hev : ∀ᶠ t in nhds x, 0 < f t :=
    hf.continuousAt.eventually (isOpen_Ioi.mem_nhds hx)
  have hlog :
      HasDerivAt (fun t => Real.log (f t)) (f' / f x) x :=
    hf.log (ne_of_gt hx)
  have hscale :
      HasDerivAt (fun t => (1 / 2 : ℝ) * Real.log (f t))
        ((1 / 2 : ℝ) * (f' / f x)) x := by
    convert (hasDerivAt_const x (1 / 2 : ℝ)).mul hlog using 1 <;>
      simp <;> ring
  have hexp :
      HasDerivAt
        (fun t => Real.exp ((1 / 2 : ℝ) * Real.log (f t)))
        (Real.exp ((1 / 2 : ℝ) * Real.log (f x)) *
          ((1 / 2 : ℝ) * (f' / f x))) x := by
    simpa using hscale.exp
  have heq :
      (fun t => Real.exp ((1 / 2 : ℝ) * Real.log (f t))) =ᶠ[nhds x]
        (fun t => Real.sqrt (f t)) := by
    filter_upwards [hev] with t ht
    exact (hsqrt_exp (f t) ht).symm
  have htrans := hexp.congr_of_eventuallyEq heq.symm
  have hcoef :
      Real.exp ((1 / 2 : ℝ) * Real.log (f x)) *
          ((1 / 2 : ℝ) * (f' / f x)) =
        f' / (2 * Real.sqrt (f x)) := by
    rw [← hsqrt_exp (f x) hx]
    have hrpos : 0 < Real.sqrt (f x) := Real.sqrt_pos.2 hx
    have hrecip : Real.sqrt (f x) / f x = 1 / Real.sqrt (f x) := by
      field_simp [ne_of_gt hx, ne_of_gt hrpos]
      nlinarith [Real.sq_sqrt (le_of_lt hx)]
    calc
      Real.sqrt (f x) * ((1 / 2 : ℝ) * (f' / f x)) =
          (f' / 2) * (Real.sqrt (f x) / f x) := by ring
      _ = (f' / 2) * (1 / Real.sqrt (f x)) := by rw [hrecip]
      _ = f' / (2 * Real.sqrt (f x)) := by
        field_simp [ne_of_gt hrpos]
  rw [← hcoef]
  exact htrans

theorem gap1 (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt y (expandedDerivative x) x := by
  have hsq : 0 < 1 - x ^ 2 := by
    nlinarith [mul_pos hx0 (sub_pos.mpr hx1)]
  have hrpos : 0 < root x := by
    rw [root]
    exact Real.sqrt_pos.2 hsq
  have hrne : root x ≠ 0 := ne_of_gt hrpos
  have hr_sq : root x ^ 2 = 1 - x ^ 2 := by
    unfold root
    exact Real.sq_sqrt (le_of_lt hsq)
  have hx_sq_pos : 0 < x ^ 2 := pow_pos hx0 2
  have hrlt : root x < 1 := by
    nlinarith [hr_sq]
  have hxp : 1 + x ≠ 0 := by linarith
  have hxm : 1 - x ≠ 0 := by linarith
  have hrp : 1 + root x ≠ 0 := by linarith
  have hrm : 1 - root x ≠ 0 := by linarith
  have hinner :
      HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-2 * x) x := by
    convert
      (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)
      using 1 <;> simp [id_eq] <;> ring
  have hroot : HasDerivAt root (-x / root x) x := by
    have hraw := sqrtCompHasDerivAt
      (f := fun t : ℝ => 1 - t ^ 2) (f' := -2 * x) (x := x)
      hsq hinner
    convert hraw using 1 <;>
      simp [root] <;>
      field_simp [ne_of_gt (Real.sqrt_pos.2 hsq)] <;> ring
  have hqpos : 0 < (1 - x) / (1 + x) :=
    div_pos (sub_pos.mpr hx1) (by linarith)
  have hsqrtqpos : 0 < Real.sqrt ((1 - x) / (1 + x)) :=
    Real.sqrt_pos.2 hqpos
  have hsqrtq_sq :
      Real.sqrt ((1 - x) / (1 + x)) ^ 2 = (1 - x) / (1 + x) :=
    Real.sq_sqrt (le_of_lt hqpos)
  have hq :
      HasDerivAt (fun t : ℝ => (1 - t) / (1 + t))
        (-2 / (1 + x) ^ 2) x := by
    convert
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).div
        ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)) hxp
      using 1 <;> simp [id_eq] <;> field_simp [hxp] <;> ring_nf
  have hlog1 :
      HasDerivAt
        (fun t : ℝ => Real.log (Real.sqrt ((1 - t) / (1 + t))))
        ((1 / 2 : ℝ) * (-(1 / (1 - x)) - 1 / (1 + x))) x := by
    have hsqrtq := sqrtCompHasDerivAt
      (f := fun t : ℝ => (1 - t) / (1 + t))
      (f' := -2 / (1 + x) ^ 2) (x := x) hqpos hq
    have hdenq :
        (1 + x) ^ 2 * Real.sqrt ((1 - x) / (1 + x)) ^ 2 =
          (1 - x) * (1 + x) := by
      rw [hsqrtq_sq]
      field_simp [hxp] <;> ring
    have hcoef1 :
        (-2 / (1 + x) ^ 2 /
            (2 * Real.sqrt ((1 - x) / (1 + x)))) /
            Real.sqrt ((1 - x) / (1 + x)) =
          (1 / 2 : ℝ) * (-(1 / (1 - x)) - 1 / (1 + x)) := by
      calc
        (-2 / (1 + x) ^ 2 /
              (2 * Real.sqrt ((1 - x) / (1 + x)))) /
              Real.sqrt ((1 - x) / (1 + x)) =
            -(1 / ((1 + x) ^ 2 *
              Real.sqrt ((1 - x) / (1 + x)) ^ 2)) := by
                field_simp [hxp, ne_of_gt hsqrtqpos] <;> ring
        _ = -(1 / ((1 - x) * (1 + x))) := by rw [hdenq]
        _ = (1 / 2 : ℝ) * (-(1 / (1 - x)) - 1 / (1 + x)) := by
              field_simp [hxm, hxp] <;> ring
    simpa only [hcoef1] using hsqrtq.log (ne_of_gt hsqrtqpos)
  have hratio_pos : 0 < (1 - root x) / (1 + root x) :=
    div_pos (sub_pos.mpr hrlt) (by linarith)
  have hnum2 :
      HasDerivAt (fun t : ℝ => 1 - root t) (x / root x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub hroot using 1 <;> ring
  have hden2 :
      HasDerivAt (fun t : ℝ => 1 + root t) (-x / root x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add hroot using 1 <;> ring
  have hlog2 :
      HasDerivAt
        (fun t : ℝ => Real.log ((1 - root t) / (1 + root t)))
        (x / ((1 - root x) * root x) +
          x / ((1 + root x) * root x)) x := by
    have hratio := hnum2.div hden2 hrp
    convert (hratio.log (ne_of_gt hratio_pos)) using 1 <;>
      simp <;>
      field_simp [hrne, hrm, hrp] <;> ring
  have hxmone : x ≠ -1 := by linarith
  have hxone : x ≠ 1 := by linarith
  have harcsin : HasDerivAt Real.arcsin (1 / root x) x := by
    simpa [root] using Real.hasDerivAt_arcsin hxmone hxone
  have htotal :=
    (((hroot.mul hlog1).add
      ((hasDerivAt_const x (1 / 2 : ℝ)).mul hlog2)).add hroot).add harcsin
  convert htotal using 1 <;>
    simp only [expandedDerivative] <;> ring

theorem gap2 (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    expandedDerivative x = finalDerivative x := by
  have hsq : 0 < 1 - x ^ 2 := by
    nlinarith [mul_pos hx0 (sub_pos.mpr hx1)]
  have hrpos : 0 < root x := by
    rw [root]
    exact Real.sqrt_pos.2 hsq
  have hrne : root x ≠ 0 := ne_of_gt hrpos
  have hr_sq : root x ^ 2 = 1 - x ^ 2 := by
    unfold root
    exact Real.sq_sqrt (le_of_lt hsq)
  have hx_sq_pos : 0 < x ^ 2 := pow_pos hx0 2
  have hrlt : root x < 1 := by
    nlinarith [hr_sq]
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hxp : 1 + x ≠ 0 := by linarith
  have hxm : 1 - x ≠ 0 := by linarith
  have hrp : 1 + root x ≠ 0 := by linarith
  have hrm : 1 - root x ≠ 0 := by linarith
  have hA :
      (1 / 2 : ℝ) * root x *
          (-(1 / (1 - x)) - 1 / (1 + x)) =
        -(1 / root x) := by
    field_simp [hxm, hxp, hrne]
    nlinarith [hr_sq]
  have hB :
      (1 / 2 : ℝ) *
          (x / ((1 - root x) * root x) +
            x / ((1 + root x) * root x)) =
        1 / (root x * x) := by
    field_simp [hxne, hrne, hrm, hrp]
    nlinarith [hr_sq]
  have hC :
      1 / (root x * x) - x / root x = root x / x := by
    field_simp [hxne, hrne]
    nlinarith [hr_sq]
  unfold expandedDerivative finalDerivative
  rw [hA, hB]
  calc
    -(x / root x) * Real.log (Real.sqrt ((1 - x) / (1 + x))) +
          -(1 / root x) + 1 / (root x * x) - x / root x +
        1 / root x =
        -(x / root x) * Real.log (Real.sqrt ((1 - x) / (1 + x))) +
          (1 / (root x * x) - x / root x) := by ring
    _ = -(x / root x) * Real.log (Real.sqrt ((1 - x) / (1 + x))) +
          root x / x := by rw [hC]
    _ = root x / x -
          x / root x * Real.log (Real.sqrt ((1 - x) / (1 + x))) := by ring

theorem gap3 (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x hx0 hx1]
  exact gap1 x hx0 hx1

end

end ProofGap.Exercise949
