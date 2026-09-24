import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1019_1

noncomputable section

open scoped Topology

def f (x : ℝ) : ℝ := 1 / x + Real.cos (1 / x)
def xseq (k : ℕ) : ℝ := 1 / (2 * (k : ℝ) * Real.pi + Real.pi / 2)
def rightZero : Filter ℝ := 𝓝[Set.Ioi 0] 0

private theorem hasDerivAt_f (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt f
      (-(1 / x ^ 2) + 1 / x ^ 2 * Real.sin (1 / x)) x := by
  have hrecip :
      HasDerivAt (fun y : ℝ => 1 / y) (-(1 / x ^ 2)) x := by
    convert
      (hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx using 1 <;>
      simp [id] <;> ring
  have hcos :
      HasDerivAt (fun y : ℝ => Real.cos (1 / y))
        ((-Real.sin (1 / x)) * (-(1 / x ^ 2))) x :=
    (Real.hasDerivAt_cos (1 / x)).comp x hrecip
  unfold f
  convert hrecip.add hcos using 1 <;> ring

private theorem tendsto_xseq_rightZero :
    Tendsto xseq atTop rightZero := by
  unfold rightZero
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hcast :
        Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hden :
        Tendsto
          (fun k : ℕ => 2 * (k : ℝ) * Real.pi + Real.pi / 2)
          atTop atTop := by
      refine Filter.tendsto_atTop.2 ?_
      intro b
      have hb : ∀ᶠ k : ℕ in atTop, max b 0 ≤ (k : ℝ) :=
        Filter.tendsto_atTop.1 hcast (max b 0)
      exact hb.mono (fun k hk => by
        have hbk : b ≤ (k : ℝ) := le_trans (le_max_left b 0) hk
        have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
        have hcoeff : 1 ≤ 2 * Real.pi := by
          linarith [Real.pi_gt_three]
        calc
          b ≤ (k : ℝ) := hbk
          _ ≤ (k : ℝ) * (2 * Real.pi) := by
            simpa using mul_le_mul_of_nonneg_left hcoeff hk0
          _ = 2 * (k : ℝ) * Real.pi := by ring
          _ ≤ 2 * (k : ℝ) * Real.pi + Real.pi / 2 :=
            le_add_of_nonneg_right (by positivity))
    have hcomp :
        Tendsto
          ((fun x : ℝ => x⁻¹) ∘
            (fun k : ℕ => 2 * (k : ℝ) * Real.pi + Real.pi / 2))
          atTop (𝓝 0) :=
      (tendsto_inv_atTop_zero :
        Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp hden
    exact hcomp.congr' (Filter.Eventually.of_forall (fun k => by
      simp [xseq, Function.comp_apply, one_div]))
  · exact Filter.Eventually.of_forall (fun k => by
      change 0 < xseq k
      unfold xseq
      positivity)

theorem gap1 : DifferentiableOn ℝ f (Set.Ioo 0 (Real.pi / 2)) := by
  intro x hx
  exact
    (hasDerivAt_f x (ne_of_gt hx.1)).differentiableAt.differentiableWithinAt

theorem gap2 : Tendsto f rightZero atTop := by
  have hinv : Tendsto (fun x : ℝ => 1 / x) rightZero atTop := by
    simpa only [rightZero, one_div] using
      (tendsto_inv_nhdsGT_zero :
        Tendsto (fun x : ℝ => x⁻¹) (𝓝[Set.Ioi 0] 0) atTop)
  refine Filter.tendsto_atTop.2 ?_
  intro b
  have hb : ∀ᶠ x : ℝ in rightZero, b + 1 ≤ 1 / x :=
    Filter.tendsto_atTop.1 hinv (b + 1)
  exact hb.mono (fun x hx => by
    dsimp [f]
    linarith [Real.neg_one_le_cos (1 / x)])

theorem gap3 (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt f
      (-(1 / x ^ 2) + 1 / x ^ 2 * Real.sin (1 / x)) x := by
  exact hasDerivAt_f x hx

theorem gap4 (k : ℕ) : deriv f (xseq k) = 0 := by
  have hdpos :
      0 < 2 * (k : ℝ) * Real.pi + Real.pi / 2 := by
    positivity
  have hx : xseq k ≠ 0 := by
    have : 0 < xseq k := by
      unfold xseq
      positivity
    exact ne_of_gt this
  have hinv :
      1 / xseq k = 2 * (k : ℝ) * Real.pi + Real.pi / 2 := by
    simp [xseq, one_div]
  have hang :
      2 * (k : ℝ) * Real.pi + Real.pi / 2 =
        (k : ℝ) * (2 * Real.pi) + Real.pi / 2 := by
    ring
  have hsin : Real.sin (1 / xseq k) = 1 := by
    rw [hinv, hang, Real.sin_add]
    simp
  calc
    deriv f (xseq k) =
        -(1 / (xseq k) ^ 2) +
          1 / (xseq k) ^ 2 * Real.sin (1 / xseq k) :=
      (hasDerivAt_f (xseq k) hx).deriv
    _ = 0 := by rw [hsin]; ring

theorem gap5 : Tendsto (fun k : ℕ => deriv f (xseq k)) atTop (𝓝 0) := by
  simpa only [gap4] using
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem gap6 : ¬ Tendsto (deriv f) rightZero atTop := by
  intro h
  have hcomp :
      Tendsto (fun k : ℕ => deriv f (xseq k)) atTop atTop := by
    simpa only [Function.comp_apply] using h.comp tendsto_xseq_rightZero
  have hlarge :
      ∀ᶠ k : ℕ in atTop, 1 ≤ deriv f (xseq k) :=
    Filter.tendsto_atTop.1 hcomp 1
  have hzero :
      ∀ᶠ k : ℕ in atTop, deriv f (xseq k) = 0 :=
    Filter.Eventually.of_forall gap4
  obtain ⟨k, hk, hk0⟩ := Filter.Eventually.exists (hlarge.and hzero)
  rw [hk0] at hk
  norm_num at hk

end

end ProofGap.Exercise1019_1
