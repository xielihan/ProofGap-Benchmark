import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1142

noncomputable section

def x (a t : ℝ) : ℝ := a * (t - Real.sin t)
def y (a t : ℝ) : ℝ := a * (1 - Real.cos t)
def cot (t : ℝ) : ℝ := Real.cos t / Real.sin t
def d1 (a t : ℝ) : ℝ := deriv (y a) t / deriv (x a) t
def d2 (a t : ℝ) : ℝ := deriv (d1 a) t / deriv (x a) t
def d3 (a t : ℝ) : ℝ := deriv (d2 a) t / deriv (x a) t

private theorem one_sub_cos_eq_two_sin_sq (t : ℝ) :
    1 - Real.cos t = 2 * Real.sin (t / 2) ^ 2 := by
  have ht : t / 2 + t / 2 = t := by ring
  calc
    1 - Real.cos t = 1 - Real.cos (t / 2 + t / 2) := by rw [ht]
    _ = 2 * Real.sin (t / 2) ^ 2 := by
      rw [Real.cos_add]
      nlinarith [Real.sin_sq_add_cos_sq (t / 2)]

theorem gap1 (a t : ℝ) (ha : a ≠ 0) (hh : 1 - Real.cos t ≠ 0) :
    d1 a t = a * Real.sin t / (a * (1 - Real.cos t)) := by
  have hy : HasDerivAt (y a) (a * Real.sin t) t := by
    simpa [y] using
      (((hasDerivAt_const t (1 : ℝ)).sub (Real.hasDerivAt_cos t)).const_mul a)
  have hx : HasDerivAt (x a) (a * (1 - Real.cos t)) t := by
    simpa [x] using
      (((hasDerivAt_id t).sub (Real.hasDerivAt_sin t)).const_mul a)
  unfold d1
  rw [hy.deriv, hx.deriv]

theorem gap2 (a t : ℝ) (ha : a ≠ 0)
    (hh : Real.sin (t / 2) ≠ 0) :
    a * Real.sin t / (a * (1 - Real.cos t)) = cot (t / 2) := by
  have ht : t / 2 + t / 2 = t := by ring
  have hs :
      Real.sin t = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
    calc
      Real.sin t = Real.sin (t / 2 + t / 2) := by rw [ht]
      _ = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
        rw [Real.sin_add]
        ring
  rw [hs, one_sub_cos_eq_two_sin_sq]
  unfold cot
  field_simp [ha, hh] <;> ring

theorem gap3 (a t : ℝ) (ha : a ≠ 0)
    (hh : Real.sin (t / 2) ≠ 0) :
    d1 a t = cot (t / 2) := by
  have hden : 1 - Real.cos t ≠ 0 := by
    rw [one_sub_cos_eq_two_sin_sq]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hh)
  calc
    d1 a t = a * Real.sin t / (a * (1 - Real.cos t)) := gap1 a t ha hden
    _ = cot (t / 2) := gap2 a t ha hh

theorem gap4 (a t : ℝ) (ha : a ≠ 0)
    (hh : Real.sin (t / 2) ≠ 0) :
    d2 a t =
      (-1 / (2 * Real.sin (t / 2) ^ 2)) / (a * (1 - Real.cos t)) := by
  have hsder :
      HasDerivAt (fun u : ℝ => Real.sin (u / 2))
        (Real.cos (t / 2) / 2) t := by
    convert
      (Real.hasDerivAt_sin (t / 2)).comp t
        ((hasDerivAt_id t).div_const 2) using 1 <;> ring
  have hcder :
      HasDerivAt (fun u : ℝ => Real.cos (u / 2))
        (-Real.sin (t / 2) / 2) t := by
    convert
      (Real.hasDerivAt_cos (t / 2)).comp t
        ((hasDerivAt_id t).div_const 2) using 1 <;> ring
  have hcot :
      HasDerivAt (fun u : ℝ => cot (u / 2))
        (-1 / (2 * Real.sin (t / 2) ^ 2)) t := by
    unfold cot
    convert hcder.div hsder hh using 1 <;>
      field_simp [hh] <;>
      nlinarith [Real.sin_sq_add_cos_sq (t / 2)]
  have hne : ∀ᶠ u in nhds t, Real.sin (u / 2) ≠ 0 :=
    hsder.continuousAt.eventually_ne hh
  have heq :
      d1 a =ᶠ[nhds t] (fun u : ℝ => cot (u / 2)) :=
    hne.mono (fun u hu => gap3 a u ha hu)
  have hd1 :
      deriv (d1 a) t = -1 / (2 * Real.sin (t / 2) ^ 2) := by
    calc
      deriv (d1 a) t = deriv (fun u : ℝ => cot (u / 2)) t := heq.deriv_eq
      _ = -1 / (2 * Real.sin (t / 2) ^ 2) := hcot.deriv
  have hx : HasDerivAt (x a) (a * (1 - Real.cos t)) t := by
    simpa [x] using
      (((hasDerivAt_id t).sub (Real.hasDerivAt_sin t)).const_mul a)
  unfold d2
  rw [hd1, hx.deriv]

theorem gap5 (a t : ℝ) (ha : a ≠ 0)
    (hh : Real.sin (t / 2) ≠ 0) :
    (-1 / (2 * Real.sin (t / 2) ^ 2)) / (a * (1 - Real.cos t)) =
      -1 / (4 * a * Real.sin (t / 2) ^ 4) := by
  rw [one_sub_cos_eq_two_sin_sq]
  field_simp [ha, hh] <;> ring

theorem gap6 (a t : ℝ) (ha : a ≠ 0)
    (hh : Real.sin (t / 2) ≠ 0) :
    d2 a t = -1 / (4 * a * Real.sin (t / 2) ^ 4) := by
  calc
    d2 a t =
        (-1 / (2 * Real.sin (t / 2) ^ 2)) /
          (a * (1 - Real.cos t)) := gap4 a t ha hh
    _ = -1 / (4 * a * Real.sin (t / 2) ^ 4) := gap5 a t ha hh

theorem gap7 (a t : ℝ) (ha : a ≠ 0)
    (hh : Real.sin (t / 2) ≠ 0) :
    d3 a t =
      (Real.cos (t / 2) / (2 * a * Real.sin (t / 2) ^ 5)) /
        (a * (1 - Real.cos t)) := by
  have hsder :
      HasDerivAt (fun u : ℝ => Real.sin (u / 2))
        (Real.cos (t / 2) / 2) t := by
    convert
      (Real.hasDerivAt_sin (t / 2)).comp t
        ((hasDerivAt_id t).div_const 2) using 1 <;> ring
  have hdenne :
      4 * a * Real.sin (t / 2) ^ 4 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) ha) (pow_ne_zero 4 hh)
  have hformula :
      HasDerivAt
        (fun u : ℝ => -1 / (4 * a * Real.sin (u / 2) ^ 4))
        (Real.cos (t / 2) / (2 * a * Real.sin (t / 2) ^ 5)) t := by
    convert
      (hasDerivAt_const t (-1 : ℝ)).div
        ((hsder.pow 4).const_mul (4 * a)) hdenne using 1 <;>
      simp only [Pi.pow_apply] <;>
      field_simp [ha, hh] <;> ring
  have hne : ∀ᶠ u in nhds t, Real.sin (u / 2) ≠ 0 :=
    hsder.continuousAt.eventually_ne hh
  have heq :
      d2 a =ᶠ[nhds t]
        (fun u : ℝ => -1 / (4 * a * Real.sin (u / 2) ^ 4)) :=
    hne.mono (fun u hu => gap6 a u ha hu)
  have hd2 :
      deriv (d2 a) t =
        Real.cos (t / 2) / (2 * a * Real.sin (t / 2) ^ 5) := by
    calc
      deriv (d2 a) t =
          deriv (fun u : ℝ => -1 / (4 * a * Real.sin (u / 2) ^ 4)) t :=
        heq.deriv_eq
      _ = Real.cos (t / 2) / (2 * a * Real.sin (t / 2) ^ 5) :=
        hformula.deriv
  have hx : HasDerivAt (x a) (a * (1 - Real.cos t)) t := by
    simpa [x] using
      (((hasDerivAt_id t).sub (Real.hasDerivAt_sin t)).const_mul a)
  unfold d3
  rw [hd2, hx.deriv]

theorem gap8 (a t : ℝ) (ha : a ≠ 0)
    (hh : Real.sin (t / 2) ≠ 0) :
    (Real.cos (t / 2) / (2 * a * Real.sin (t / 2) ^ 5)) /
        (a * (1 - Real.cos t)) =
      Real.cos (t / 2) / (4 * a ^ 2 * Real.sin (t / 2) ^ 7) := by
  rw [one_sub_cos_eq_two_sin_sq]
  field_simp [ha, hh] <;> ring

theorem gap9 (a t : ℝ) (ha : a ≠ 0)
    (hh : Real.sin (t / 2) ≠ 0) :
    d3 a t =
      Real.cos (t / 2) / (4 * a ^ 2 * Real.sin (t / 2) ^ 7) := by
  calc
    d3 a t =
        (Real.cos (t / 2) / (2 * a * Real.sin (t / 2) ^ 5)) /
          (a * (1 - Real.cos t)) := gap7 a t ha hh
    _ = Real.cos (t / 2) /
          (4 * a ^ 2 * Real.sin (t / 2) ^ 7) := gap8 a t ha hh

end

end ProofGap.Exercise1142
