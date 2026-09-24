import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1107

noncomputable section

def volume (R : ℝ) : ℝ := (4 / 3 : ℝ) * Real.pi * R ^ 3

def differential (f : ℝ → ℝ) (x dx : ℝ) : ℝ :=
  deriv f x * dx

def relativeError (value change : ℝ) : ℝ := |change / value|

theorem gap1 (R dR : ℝ) :
    differential volume R dR =
      ((4 / 3 : ℝ) * Real.pi * 3 * R ^ 2) * dR := by
  have hid : HasDerivAt (fun x : ℝ => x) 1 R := hasDerivAt_id R
  have hcube : HasDerivAt (fun x : ℝ => x ^ 3) (3 * R ^ 2) R := by
    convert ((hid.mul hid).mul hid) using 1
    · funext x
      simp only [Pi.mul_apply, Pi.pow_apply]
      ring
    · simp only [Pi.mul_apply]
      ring
  have hvolume :
      HasDerivAt volume
        (((4 / 3 : ℝ) * Real.pi) * (3 * R ^ 2)) R := by
    simpa [volume] using
      hcube.const_mul ((4 / 3 : ℝ) * Real.pi)
  unfold differential
  rw [hvolume.deriv]
  ring

theorem gap2 (R dR : ℝ) (hR : R ≠ 0) :
    ((4 / 3 : ℝ) * Real.pi * 3 * R ^ 2) * dR =
      (volume R * (3 / R)) * dR := by
  unfold volume
  field_simp [hR] <;> ring

theorem gap3 (R dR : ℝ) (hR : R ≠ 0) :
    differential volume R dR = (volume R * (3 / R)) * dR := by
  rw [gap1 R dR, gap2 R dR hR]

theorem gap4 (R dR : ℝ) (hR : R ≠ 0) :
    relativeError (volume R) (differential volume R dR) =
      3 * relativeError R dR := by
  have hvol : volume R ≠ 0 := by
    unfold volume
    exact
      mul_ne_zero
        (mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos))
        (pow_ne_zero 3 hR)
  rw [gap3 R dR hR]
  unfold relativeError
  have hquot :
      ((volume R * (3 / R)) * dR) / volume R =
        3 * (dR / R) := by
    field_simp [hvol, hR] <;> ring
  rw [hquot, abs_mul]
  norm_num

theorem gap5 (R dR : ℝ) (hR : R ≠ 0) :
    relativeError R dR =
      (1 / 3 : ℝ) *
        relativeError (volume R) (differential volume R dR) := by
  rw [gap4 R dR hR]
  ring

theorem gap6 (δV : ℝ) (hδV : δV ≤ 0.01) :
    (1 / 3 : ℝ) * δV ≤ (1 / 3 : ℝ) * 0.01 := by
  linarith

theorem gap7 : (1 / 3 : ℝ) * 0.01 = 1 / 300 := by
  norm_num

theorem gap8 (δR δV : ℝ) (hδR : δR = (1 / 3 : ℝ) * δV)
    (hδV : δV ≤ 0.01) :
    δR ≤ 1 / 300 := by
  calc
    δR = (1 / 3 : ℝ) * δV := hδR
    _ ≤ (1 / 3 : ℝ) * 0.01 := gap6 δV hδV
    _ = 1 / 300 := gap7

theorem gap9 (R dR : ℝ) (hR : R ≠ 0)
    (hδV :
      relativeError (volume R) (differential volume R dR) ≤ 0.01) :
    relativeError R dR ∈ {δ : ℝ | δ ≤ 1 / 300} := by
  change relativeError R dR ≤ 1 / 300
  exact
    gap8
      (relativeError R dR)
      (relativeError (volume R) (differential volume R dR))
      (gap5 R dR hR)
      hδV

end

end ProofGap.Exercise1107
