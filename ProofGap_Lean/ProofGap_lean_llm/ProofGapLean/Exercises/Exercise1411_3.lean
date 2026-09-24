import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1411_3

noncomputable section
open Filter
open scoped Topology

def punctured := nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ
def target (A n x : ℝ) :=
  (A / x) * (1 - Real.rpow (1 + x / 100) (-n))
def constantModel (A n : ℝ) (_x : ℝ) := n * A / 100

theorem gap1 (A n : ℝ) :
    Asymptotics.IsEquivalent punctured (target A n) (constantModel A n) := by
  by_cases hA : A = 0
  · subst A
    have ht0 : target 0 n = (fun _ : ℝ => 0) := by
      funext x
      simp [target]
    have hc0 : constantModel 0 n = (fun _ : ℝ => 0) := by
      funext x
      simp [constantModel]
    rw [ht0, hc0]
  by_cases hn : n = 0
  · subst n
    have ht0 : target A 0 = (fun _ : ℝ => 0) := by
      funext x
      simp [target]
    have hc0 : constantModel A 0 = (fun _ : ℝ => 0) := by
      funext x
      simp [constantModel]
    rw [ht0, hc0]
  have hinner :
      HasDerivAt (fun x : ℝ => 1 + x / 100) (1 / 100) 0 := by
    simpa only [zero_div, add_zero] using
      (((hasDerivAt_id (0 : ℝ)).div_const (100 : ℝ)).const_add (1 : ℝ))
  have hlog :
      HasDerivAt (fun x : ℝ => Real.log (1 + x / 100)) (1 / 100) 0 := by
    have hout : HasDerivAt Real.log 1 (1 + (0 : ℝ) / 100) := by
      convert Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0) using 1 <;>
        norm_num
    simpa only [one_mul] using hout.comp 0 hinner
  have hmul :
      HasDerivAt (fun x : ℝ => Real.log (1 + x / 100) * (-n))
        (-n / 100) 0 := by
    convert hlog.mul_const (-n) using 1 <;> ring
  have hderiv :
      HasDerivAt
        (fun x : ℝ => Real.exp (Real.log (1 + x / 100) * (-n)))
        (-n / 100) 0 := by
    have hout :
        HasDerivAt Real.exp 1
          (Real.log (1 + (0 : ℝ) / 100) * (-n)) := by
      convert Real.hasDerivAt_exp 0 using 1 <;>
        simp only [zero_div, add_zero, Real.log_one, zero_mul, Real.exp_zero]
    simpa only [one_mul] using hout.comp 0 hmul
  have hslope0 := hasDerivAt_iff_tendsto_slope.mp hderiv
  have hneg :
      Tendsto
        (fun x : ℝ =>
          -((x - 0)⁻¹ *
            (Real.exp (Real.log (1 + x / 100) * (-n)) -
              Real.exp (Real.log (1 + 0 / 100) * (-n)))))
        punctured (𝓝 (n / 100)) := by
    convert hslope0.neg using 1 <;>
      simp only [zero_div, add_zero, Real.log_one, zero_mul,
        Real.exp_zero, neg_div] <;>
      ring_nf
  have hslope :
      Tendsto
        (fun x : ℝ =>
          (1 - Real.exp (Real.log (1 + x / 100) * (-n))) / x)
        punctured (𝓝 (n / 100)) := by
    refine (tendsto_congr' ?_).2 hneg
    filter_upwards with x
    simp only [sub_zero, div_eq_mul_inv, zero_div, add_zero, Real.log_one,
      zero_mul, mul_zero, Real.exp_zero, mul_one]
    ring
  have hpos_nhds :
      ∀ᶠ x : ℝ in 𝓝 0, 0 < 1 + x / 100 := by
    apply hinner.continuousAt
    exact isOpen_Ioi.mem_nhds (by norm_num)
  have hpos : ∀ᶠ x : ℝ in punctured, 0 < 1 + x / 100 := by
    exact hpos_nhds.filter_mono (by
      unfold punctured
      exact inf_le_left)
  have heq :
      target A n =ᶠ[punctured]
        (fun x : ℝ =>
          (A / x) *
            (1 - Real.exp (Real.log (1 + x / 100) * (-n)))) := by
    filter_upwards [hpos] with x hx
    have hrpow :
        Real.rpow (1 + x / 100) (-n) =
          Real.exp (Real.log (1 + x / 100) * (-n)) := by
      exact Real.rpow_def_of_pos hx (-n)
    simp only [target]
    rw [hrpow]
  have hscaled :
      Tendsto
        (fun x : ℝ =>
          (A / x) *
            (1 - Real.exp (Real.log (1 + x / 100) * (-n))))
        punctured (𝓝 (n * A / 100)) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      ((tendsto_const_nhds :
          Tendsto (fun _ : ℝ => A) punctured (𝓝 A)).mul hslope)
  have ht :
      Tendsto (target A n) punctured (𝓝 (n * A / 100)) := by
    exact (tendsto_congr' heq).2 hscaled
  have hc : n * A / 100 ≠ 0 :=
    div_ne_zero (mul_ne_zero hn hA) (by norm_num)
  have hcm :
      ∀ᶠ x in punctured, constantModel A n x ≠ 0 := by
    simp [constantModel, hc]
  apply (Asymptotics.isEquivalent_iff_tendsto_one hcm).2
  simpa [constantModel, hc] using ht.div_const (n * A / 100)
theorem gap2 (A n x : ℝ) (hx : x ≠ 0) :
    (A / x) * (1 - (1 - n * x / 100)) = n * A / 100 := by
  field_simp [hx] <;> ring
theorem gap3 (A n : ℝ) :
    Asymptotics.IsEquivalent punctured (target A n) (constantModel A n) := by
  exact gap1 A n

end
end ProofGap.Exercise1411_3
