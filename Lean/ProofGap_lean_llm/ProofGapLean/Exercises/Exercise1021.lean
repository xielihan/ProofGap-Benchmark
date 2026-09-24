import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1021

noncomputable section

open scoped Topology

def f (x : ℝ) : ℝ := Real.sin (x ^ 2) / x

theorem gap1 :
    DifferentiableOn ℝ f (Set.Ioi 0) := by
  intro x hx
  have hnum : DifferentiableAt ℝ (fun y : ℝ => Real.sin (y ^ 2)) x :=
    Real.differentiableAt_sin.comp x (differentiableAt_pow 2)
  simpa only [f] using
    (hnum.div (hasDerivAt_id x).differentiableAt (ne_of_gt hx)).differentiableWithinAt

theorem gap2 (x : ℝ) (hx : 0 < x) :
    HasDerivAt f
      (2 * Real.cos (x ^ 2) - Real.sin (x ^ 2) / x ^ 2) x := by
  have hsquare : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;> norm_num
  have hsin :
      HasDerivAt (fun y : ℝ => Real.sin (y ^ 2))
        (Real.cos (x ^ 2) * (2 * x)) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sin (x ^ 2)).comp x hsquare
  have hquot :
      HasDerivAt (fun y : ℝ => Real.sin (y ^ 2) / y)
        ((Real.cos (x ^ 2) * (2 * x) * x - Real.sin (x ^ 2) * 1) / x ^ 2) x := by
    simpa only [Function.comp_apply, id_eq] using
      hsin.div (hasDerivAt_id x) (ne_of_gt hx)
  have heq :
      (Real.cos (x ^ 2) * (2 * x) * x - Real.sin (x ^ 2) * 1) / x ^ 2 =
        2 * Real.cos (x ^ 2) - Real.sin (x ^ 2) / x ^ 2 := by
    field_simp [ne_of_gt hx]
  rw [← heq]
  simpa only [f] using hquot

theorem gap3 : Tendsto f atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  refine ⟨2 / ε, ?_⟩
  intro x hx
  have hthreshold : ε * (2 / ε) = 2 := by
    field_simp [ne_of_gt hε]
  have hxpos : 0 < x := by
    have hpos : 0 < 2 / ε := div_pos (by norm_num) hε
    exact lt_of_lt_of_le hpos hx
  have hmul := mul_le_mul_of_nonneg_left hx (le_of_lt hε)
  have hone : 1 / x ≤ ε / 2 := by
    apply (div_le_iff₀ hxpos).2
    nlinarith [hmul, hthreshold]
  simp only [Real.dist_eq, f, sub_zero, abs_div, abs_of_pos hxpos]
  calc
    |Real.sin (x ^ 2)| / x ≤ 1 / x :=
      (div_le_div_iff_of_pos_right hxpos).2 (Real.abs_sin_le_one (x ^ 2))
    _ ≤ ε / 2 := hone
    _ < ε := by linarith

theorem gap4 : ¬ ∃ L : ℝ, Tendsto (deriv f) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hposEventually : ∀ᶠ x : ℝ in atTop, 0 < x := by
    refine Filter.eventually_atTop.2 ⟨1, ?_⟩
    intro x hx
    linarith
  have hinv : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
    refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    refine ⟨2 / ε, ?_⟩
    intro x hx
    have hthreshold : ε * (2 / ε) = 2 := by
      field_simp [ne_of_gt hε]
    have hxpos : 0 < x := by
      have hpos : 0 < 2 / ε := div_pos (by norm_num) hε
      exact lt_of_lt_of_le hpos hx
    have hmul := mul_le_mul_of_nonneg_left hx (le_of_lt hε)
    have hone : 1 / x ≤ ε / 2 := by
      apply (div_le_iff₀ hxpos).2
      nlinarith [hmul, hthreshold]
    simp only [Real.dist_eq, sub_zero, abs_div, abs_one, abs_of_pos hxpos]
    exact lt_of_le_of_lt hone (by linarith)
  have hcorr :
      Tendsto (fun x : ℝ => Real.sin (x ^ 2) / x ^ 2) atTop (𝓝 0) := by
    have hp :
        Tendsto (fun x : ℝ => f x * (1 / x)) atTop (𝓝 (0 * 0)) :=
      gap3.mul hinv
    have hp0 : Tendsto (fun x : ℝ => f x * (1 / x)) atTop (𝓝 0) := by
      simpa using hp
    refine hp0.congr' ?_
    filter_upwards [hposEventually] with x hx
    simp only [f]
    field_simp [ne_of_gt hx] <;> ring
  have htwo :
      Tendsto (fun x : ℝ => 2 * Real.cos (x ^ 2)) atTop (𝓝 L) := by
    have hadd :
        Tendsto
          (fun x : ℝ => deriv f x + Real.sin (x ^ 2) / x ^ 2)
          atTop (𝓝 (L + 0)) :=
      hL.add hcorr
    have hadd0 :
        Tendsto
          (fun x : ℝ => deriv f x + Real.sin (x ^ 2) / x ^ 2)
          atTop (𝓝 L) := by
      simpa using hadd
    refine hadd0.congr' ?_
    filter_upwards [hposEventually] with x hx
    rw [(gap2 x hx).deriv]
    ring
  let C : ℝ := (1 / 2 : ℝ) * L
  have hcosSq :
      Tendsto (fun x : ℝ => Real.cos (x ^ 2)) atTop (𝓝 C) := by
    have hm :
        Tendsto
          (fun x : ℝ => (1 / 2 : ℝ) * (2 * Real.cos (x ^ 2)))
          atTop (𝓝 ((1 / 2 : ℝ) * L)) :=
      tendsto_const_nhds.mul htwo
    dsimp [C]
    refine hm.congr' (Filter.Eventually.of_forall ?_)
    intro x
    ring
  have hroot :
      Tendsto (fun x : ℝ => Real.cos ((Real.sqrt x) ^ 2)) atTop (𝓝 C) :=
    hcosSq.comp Real.tendsto_sqrt_atTop
  have hcos : Tendsto Real.cos atTop (𝓝 C) := by
    refine hroot.congr' ?_
    filter_upwards [hposEventually] with x hx
    rw [Real.sq_sqrt (le_of_lt hx)]
  have hshift (a : ℝ) :
      Tendsto (fun x : ℝ => x + a) atTop atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    refine Filter.eventually_atTop.2 ⟨b - a, ?_⟩
    intro x hx
    linarith
  have hcosPi :
      Tendsto (fun x : ℝ => Real.cos (x + Real.pi)) atTop (𝓝 C) :=
    hcos.comp (hshift Real.pi)
  have hnegCosAtC :
      Tendsto (fun x : ℝ => -Real.cos x) atTop (𝓝 C) := by
    simpa only [Real.cos_add_pi] using hcosPi
  have hCneg : C = -C :=
    tendsto_nhds_unique hnegCosAtC hcos.neg
  have hC : C = 0 := by
    linarith
  have hcosHalf :
      Tendsto (fun x : ℝ => Real.cos (x + Real.pi / 2)) atTop (𝓝 C) :=
    hcos.comp (hshift (Real.pi / 2))
  have hnegSinAtC :
      Tendsto (fun x : ℝ => -Real.sin x) atTop (𝓝 C) := by
    simpa only [Real.cos_add_pi_div_two] using hcosHalf
  have hsin0 : Tendsto Real.sin atTop (𝓝 0) := by
    have hn := hnegSinAtC.neg
    simpa [hC] using hn
  have hcos0 : Tendsto Real.cos atTop (𝓝 0) := by
    simpa [hC] using hcos
  have hsumsq :
      Tendsto
        (fun x : ℝ => Real.sin x * Real.sin x + Real.cos x * Real.cos x)
        atTop (𝓝 0) := by
    simpa using (hsin0.mul hsin0).add (hcos0.mul hcos0)
  have hone0 :
      Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 0) := by
    refine hsumsq.congr' (Filter.Eventually.of_forall ?_)
    intro x
    simpa [pow_two] using Real.sin_sq_add_cos_sq x
  have hzero_one : (0 : ℝ) = 1 :=
    tendsto_nhds_unique hone0 tendsto_const_nhds
  exact zero_ne_one hzero_one

end

end ProofGap.Exercise1021
