import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise944

noncomputable section

def y (x : ℝ) : ℝ :=
  Real.arctan (x / (1 + Real.sqrt (1 - x ^ 2)))

def expandedDerivative (x : ℝ) : ℝ :=
  1 / (1 + (x / (1 + Real.sqrt (1 - x ^ 2))) ^ 2) *
    ((1 + Real.sqrt (1 - x ^ 2) +
        x ^ 2 / Real.sqrt (1 - x ^ 2)) /
      (1 + Real.sqrt (1 - x ^ 2)) ^ 2)

def finalDerivative (x : ℝ) : ℝ :=
  1 / (2 * Real.sqrt (1 - x ^ 2))

private lemma unit_radicand_pos {x : ℝ} (hx : |x| < 1) :
    0 < 1 - x ^ 2 := by
  rcases abs_lt.mp hx with ⟨hxl, hxu⟩
  have h1 : 0 < 1 - x := sub_pos.mpr hxu
  have h2 : 0 < 1 + x := by
    linarith
  nlinarith [mul_pos h1 h2]

theorem gap1 (x : ℝ) (hx : |x| < 1) :
    HasDerivAt y (expandedDerivative x) x := by
  have hrad : 0 < 1 - x ^ 2 := unit_radicand_pos hx
  have hs : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 hrad
  have hrad_deriv :
      HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-2 * x) x := by
    convert
      (HasDerivAt.sub (hasDerivAt_const x (1 : ℝ))
        ((hasDerivAt_id x).pow 2)) using 1 <;>
      simp only [id_eq] <;>
      ring_nf
  have hpow :
      HasDerivAt (fun t : ℝ => t ^ (1 / 2 : ℝ))
        ((1 / 2 : ℝ) * (1 - x ^ 2) ^ ((1 / 2 : ℝ) - 1))
        (1 - x ^ 2) := by
    exact Real.hasDerivAt_rpow_const (Or.inl hrad.ne')
  have hsqrt_raw :
      HasDerivAt (fun z : ℝ => Real.sqrt (1 - z ^ 2))
        (((1 / 2 : ℝ) * (1 - x ^ 2) ^ ((1 / 2 : ℝ) - 1)) *
          (-2 * x)) x := by
    simpa [Function.comp_def, Real.sqrt_eq_rpow] using
      (hpow.comp x hrad_deriv)
  have hsqrt_deriv :
      HasDerivAt (fun z : ℝ => Real.sqrt (1 - z ^ 2))
        (-x / Real.sqrt (1 - x ^ 2)) x := by
    convert hsqrt_raw using 1
    rw [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by ring]
    rw [Real.rpow_neg (le_of_lt hrad)]
    rw [← Real.sqrt_eq_rpow]
    field_simp [hs.ne']
  have hden : 1 + Real.sqrt (1 - x ^ 2) ≠ 0 := by
    nlinarith
  have hden_deriv :
      HasDerivAt (fun z : ℝ => 1 + Real.sqrt (1 - z ^ 2))
        (-x / Real.sqrt (1 - x ^ 2)) x := by
    convert
      (HasDerivAt.add (hasDerivAt_const x (1 : ℝ)) hsqrt_deriv) using 1 <;>
      ring_nf
  have hinner :
      HasDerivAt
        (fun z : ℝ => z / (1 + Real.sqrt (1 - z ^ 2)))
        ((1 + Real.sqrt (1 - x ^ 2) +
            x ^ 2 / Real.sqrt (1 - x ^ 2)) /
          (1 + Real.sqrt (1 - x ^ 2)) ^ 2) x := by
    convert
      (HasDerivAt.div (hasDerivAt_id x) hden_deriv hden) using 1 <;>
      simp only [id_eq] <;>
      ring_nf
  simpa [y, expandedDerivative, div_eq_mul_inv, mul_comm] using
    (HasDerivAt.arctan hinner)

theorem gap2 (x : ℝ) (hx : |x| < 1) :
    expandedDerivative x = finalDerivative x := by
  have hrad : 0 < 1 - x ^ 2 := unit_radicand_pos hx
  let s : ℝ := Real.sqrt (1 - x ^ 2)
  have hs : 0 < s := by
    simpa [s] using Real.sqrt_pos.2 hrad
  have hs_sq : s ^ 2 = 1 - x ^ 2 := by
    simpa [s] using Real.sq_sqrt (le_of_lt hrad)
  have hx_sq : x ^ 2 = 1 - s ^ 2 := by
    nlinarith [hs_sq]
  have hden : 1 + s ≠ 0 := by
    nlinarith
  unfold expandedDerivative finalDerivative
  change
    1 / (1 + (x / (1 + s)) ^ 2) *
        ((1 + s + x ^ 2 / s) / (1 + s) ^ 2) =
      1 / (2 * s)
  rw [div_pow, hx_sq]
  have hnum : 0 ≤ 1 - s ^ 2 := by
    rw [← hx_sq]
    exact sq_nonneg x
  have hbase : 0 < 1 + s := by
    linarith
  have hden_sq : 0 < (1 + s) ^ 2 := by
    simpa [pow_two] using mul_pos hbase hbase
  have houter : 1 + (1 - s ^ 2) / (1 + s) ^ 2 ≠ 0 := by
    apply ne_of_gt
    have hquot : 0 ≤ (1 - s ^ 2) / (1 + s) ^ 2 :=
      div_nonneg hnum (le_of_lt hden_sq)
    linarith
  field_simp [hs.ne', hden, houter] <;> ring

theorem gap3 (x : ℝ) (hx : |x| < 1) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x hx]
  exact gap1 x hx

end

end ProofGap.Exercise944
