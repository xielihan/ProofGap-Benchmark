import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise1055_2

noncomputable section

def cbrt (x : ℝ) : ℝ := Real.sign x * Real.rpow |x| (1 / 3 : ℝ)
def y (x : ℝ) : ℝ := (x + 1) * cbrt (3 - x)
def horizontalLine (c : ℝ) : Set (ℝ × ℝ) := {p | p.2 = c}
def verticalLine (c : ℝ) : Set (ℝ × ℝ) := {p | p.1 = c}

private theorem hasDerivAt_cbrt {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt cbrt (1 / (3 * cbrt (t ^ 2))) t := by
  have value_of_pos : ∀ {u : ℝ}, 0 < u →
      (1 / 3 : ℝ) * Real.rpow u ((1 / 3 : ℝ) - 1) =
        1 / (3 * cbrt (u ^ 2)) := by
    intro u hu
    let A : ℝ := Real.rpow u (1 / 3 : ℝ)
    have hApos : 0 < A := Real.rpow_pos_of_pos hu _
    have hB : cbrt (u ^ 2) = A * A := by
      rw [cbrt, Real.sign_of_pos (sq_pos_of_pos hu),
        abs_of_pos (sq_pos_of_pos hu)]
      simp only [one_mul, pow_two]
      change Real.rpow (u * u) (1 / 3 : ℝ) =
        Real.rpow u (1 / 3 : ℝ) * Real.rpow u (1 / 3 : ℝ)
      exact Real.mul_rpow (le_of_lt hu) (le_of_lt hu)
    have hcube : A * A * A = u := by
      dsimp [A]
      rw [← Real.rpow_add hu, ← Real.rpow_add hu]
      norm_num
    have hsub : Real.rpow u ((1 / 3 : ℝ) - 1) = A / u := by
      dsimp [A]
      rw [Real.rpow_sub hu]
      simp
    rw [hsub, hB, ← hcube]
    field_simp [ne_of_gt hApos]
    <;> ring
  rcases lt_or_gt_of_ne ht with htneg | htpos
  · have hu : 0 < -t := neg_pos.mpr htneg
    have hp : HasDerivAt (fun z : ℝ => Real.rpow z (1 / 3 : ℝ))
        ((1 / 3 : ℝ) * Real.rpow (-t) ((1 / 3 : ℝ) - 1)) (-t) :=
      Real.hasDerivAt_rpow_const (p := (1 / 3 : ℝ))
        (Or.inl (ne_of_gt hu))
    have hc := hp.comp t (hasDerivAt_id t).neg
    have hn := hc.neg
    have hv := value_of_pos hu
    have hsquare : (-t) ^ 2 = t ^ 2 := by ring
    rw [hsquare] at hv
    rw [hv] at hn
    simp only [mul_neg, neg_neg] at hn
    have heq : cbrt =ᶠ[nhds t]
        ((-(fun z : ℝ => Real.rpow z (1 / 3 : ℝ))) ∘ Neg.neg) := by
      filter_upwards [Iio_mem_nhds htneg] with z hz
      have hz' : z < 0 := hz
      change cbrt z = -Real.rpow (-z) (1 / 3 : ℝ)
      simp [cbrt, Real.sign_of_neg hz', abs_of_neg hz']
    simpa [Function.comp_def] using hn.congr_of_eventuallyEq heq
  · have hp : HasDerivAt (fun z : ℝ => Real.rpow z (1 / 3 : ℝ))
        ((1 / 3 : ℝ) * Real.rpow t ((1 / 3 : ℝ) - 1)) t :=
      Real.hasDerivAt_rpow_const (p := (1 / 3 : ℝ))
        (Or.inl (ne_of_gt htpos))
    rw [value_of_pos htpos] at hp
    have heq : cbrt =ᶠ[nhds t]
        (fun z : ℝ => Real.rpow z (1 / 3 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds htpos] with z hz
      have hz' : 0 < z := hz
      change cbrt z = Real.rpow z (1 / 3 : ℝ)
      simp [cbrt, Real.sign_of_pos hz', abs_of_pos hz']
    exact hp.congr_of_eventuallyEq heq

theorem gap1 (x : ℝ) (hx : x ≠ 3) :
    deriv y x =
      cbrt (3 - x) - (x + 1) / (3 * cbrt ((3 - x) ^ 2)) := by
  have hsub : 3 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hc := (hasDerivAt_cbrt hsub).comp x
    ((hasDerivAt_const x 3).sub (hasDerivAt_id x))
  have hy : HasDerivAt y
      (1 * cbrt (3 - x) +
        (x + 1) * (1 / (3 * cbrt ((3 - x) ^ 2)) * (0 - 1))) x := by
    simpa [y, Function.comp_def] using
      ((hasDerivAt_id x).add_const 1).mul hc
  calc
    deriv y x =
        1 * cbrt (3 - x) +
          (x + 1) * (1 / (3 * cbrt ((3 - x) ^ 2)) * (0 - 1)) := hy.deriv
    _ = cbrt (3 - x) - (x + 1) / (3 * cbrt ((3 - x) ^ 2)) := by ring

theorem gap2 : deriv y 2 = 0 := by
  rw [gap1 2 (by norm_num)]
  norm_num [cbrt]

theorem gap3 (X Y : ℝ) :
    Y - 3 = 0 * (X - 2) ↔ Y = 3 := by
  simp [sub_eq_zero]

theorem gap4 :
    horizontalLine 3 = {p : ℝ × ℝ | p.2 = 3} := by
  rfl

theorem gap5 :
    verticalLine 2 = {p : ℝ × ℝ | p.1 = 2} := by
  rfl

end

end ProofGap.Exercise1055_2
