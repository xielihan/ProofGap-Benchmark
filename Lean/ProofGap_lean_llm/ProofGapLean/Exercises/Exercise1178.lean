import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1178

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def y (u : ℝ) : ℝ := Real.log u
def idFun (u : ℝ) : ℝ := u
def d (n : ℕ) (u : ℝ) : ℝ := iterDeriv n idFun u

private theorem deriv_idFun_eq :
    deriv idFun = fun _ : ℝ => 1 := by
  funext u
  exact (hasDerivAt_id u).deriv

private theorem deriv_const_eq (c : ℝ) :
    deriv (fun _ : ℝ => c) = fun _ : ℝ => 0 := by
  funext u
  exact (hasDerivAt_const u c).deriv

private theorem hasDerivAt_one_div (u : ℝ) (hu : u ≠ 0) :
    HasDerivAt (fun z : ℝ => 1 / z) (-1 / u ^ 2) u := by
  have hfun : (fun z : ℝ => 1 / z) = id⁻¹ := by
    funext z
    simp [one_div]
  rw [hfun]
  exact (hasDerivAt_id u).inv hu

private theorem hasDerivAt_neg_one_div_sq (u : ℝ) (hu : u ≠ 0) :
    HasDerivAt (fun z : ℝ => -(1 / z ^ 2)) (2 / u ^ 3) u := by
  have hfun : (fun z : ℝ => -(1 / z ^ 2)) =
      (fun z : ℝ => -((1 / z) * (1 / z))) := by
    funext z
    simp [one_div, pow_two]
  rw [hfun]
  convert ((hasDerivAt_one_div u hu).mul
    (hasDerivAt_one_div u hu)).neg using 1 <;>
    field_simp [hu] <;> ring

private theorem iterDeriv_one_log (u : ℝ) (hu : 0 < u) :
    iterDeriv 1 y u = 1 / u := by
  change deriv Real.log u = 1 / u
  simpa [one_div] using (Real.hasDerivAt_log hu.ne').deriv

private theorem iterDeriv_two_log (u : ℝ) (hu : 0 < u) :
    iterDeriv 2 y u = -(1 / u ^ 2) := by
  have heq :
      deriv Real.log =ᶠ[nhds u] (fun z : ℝ => 1 / z) := by
    filter_upwards [eventually_ne_nhds hu.ne'] with z hz
    simpa [one_div] using (Real.hasDerivAt_log hz).deriv
  change deriv (deriv Real.log) u = -(1 / u ^ 2)
  calc
    deriv (deriv Real.log) u = deriv (fun z : ℝ => 1 / z) u :=
      heq.deriv_eq
    _ = -(1 / u ^ 2) := by
      rw [(hasDerivAt_one_div u hu.ne').deriv]
      ring

private theorem iterDeriv_three_log (u : ℝ) (hu : 0 < u) :
    iterDeriv 3 y u = 2 / u ^ 3 := by
  have heq :
      deriv (deriv Real.log) =ᶠ[nhds u]
        (fun z : ℝ => -(1 / z ^ 2)) := by
    filter_upwards [eventually_gt_nhds hu] with z hz
    exact iterDeriv_two_log z hz
  change deriv (deriv (deriv Real.log)) u = 2 / u ^ 3
  calc
    deriv (deriv (deriv Real.log)) u =
        deriv (fun z : ℝ => -(1 / z ^ 2)) u := heq.deriv_eq
    _ = 2 / u ^ 3 := (hasDerivAt_neg_one_div_sq u hu.ne').deriv

theorem gap1 (u : ℝ) (hu : 0 < u) :
    iterDeriv 1 y u = (1 / u) * d 1 u := by
  rw [iterDeriv_one_log u hu]
  simp [d, iterDeriv, Function.iterate_succ_apply, deriv_idFun_eq]

theorem gap2 (u : ℝ) (hu : 0 < u) :
    iterDeriv 2 y u =
      -(1 / u ^ 2) * d 1 u ^ 2 + (1 / u) * d 2 u := by
  rw [iterDeriv_two_log u hu]
  simp [d, iterDeriv, Function.iterate_succ_apply, deriv_idFun_eq,
    deriv_const_eq]

theorem gap3 (u : ℝ) (hu : 0 < u) :
    iterDeriv 3 y u =
      (2 / u ^ 3) * d 1 u ^ 3 -
        (2 / u ^ 2) * d 1 u * d 2 u -
        (1 / u ^ 2) * d 2 u * d 1 u +
        (1 / u) * d 3 u := by
  rw [iterDeriv_three_log u hu]
  simp [d, iterDeriv, Function.iterate_succ_apply, deriv_idFun_eq,
    deriv_const_eq]

theorem gap4 (u : ℝ) (hu : 0 < u) :
    (2 / u ^ 3) * d 1 u ^ 3 -
        (2 / u ^ 2) * d 1 u * d 2 u -
        (1 / u ^ 2) * d 2 u * d 1 u +
        (1 / u) * d 3 u =
      (2 / u ^ 3) * d 1 u ^ 3 -
        (3 / u ^ 2) * d 1 u * d 2 u +
        (1 / u) * d 3 u := by
  ring

theorem gap5 (u : ℝ) (hu : 0 < u) :
    iterDeriv 3 y u =
      (2 / u ^ 3) * d 1 u ^ 3 -
        (3 / u ^ 2) * d 1 u * d 2 u +
        (1 / u) * d 3 u := by
  calc
    iterDeriv 3 y u =
        (2 / u ^ 3) * d 1 u ^ 3 -
          (2 / u ^ 2) * d 1 u * d 2 u -
          (1 / u ^ 2) * d 2 u * d 1 u +
          (1 / u) * d 3 u := gap3 u hu
    _ = (2 / u ^ 3) * d 1 u ^ 3 -
          (3 / u ^ 2) * d 1 u * d 2 u +
          (1 / u) * d 3 u := gap4 u hu

end

end ProofGap.Exercise1178
