import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Positivity
import Mathlib.Tactic

namespace ProofGap.Exercise2911

noncomputable section

open Filter
open scoped BigOperators Interval Topology

def seriesTerm (x : ℝ) (n : ℕ) : ℝ :=
  (n + 1 : ℝ) * x ^ (n + 1)

def integralSeriesTerm (x : ℝ) (n : ℕ) : ℝ :=
  ((n + 1 : ℝ) / (n + 2 : ℝ)) * x ^ (n + 2)

def powerTailTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (n + 2)

def fractionalTailTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (n + 2) / (n + 2 : ℝ)

def logarithmTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (n + 1) / (n + 1 : ℝ)

def F (x : ℝ) : ℝ :=
  ∑' n, seriesTerm x n

def antiderivative (x : ℝ) : ℝ :=
  x / (1 - x) + Real.log (1 - x)

private theorem hasSumTailOne {f : ℕ → ℝ} {a : ℝ} (h : HasSum f a) :
    HasSum (fun n => f (n + 1)) (a - f 0) := by
  simpa using ((hasSum_nat_add_iff' 1).2 h)

private theorem absLtOneOfMemUIcc {x t : ℝ} (hx : |x| < 1)
    (ht : t ∈ Set.uIcc (0 : ℝ) x) : |t| < 1 := by
  rcases Set.mem_uIcc.mp ht with h | h
  · rw [abs_of_nonneg h.1]
    exact lt_of_le_of_lt (h.2.trans (le_abs_self x)) hx
  · have hx0 : x ≤ 0 := h.1.trans h.2
    rw [abs_of_nonpos h.2, abs_of_nonpos hx0] at *
    linarith

private theorem antiderivativeHasDerivAt (x : ℝ) (hx : |x| < 1) :
    HasDerivAt antiderivative (x / (1 - x) ^ 2) x := by
  have hpos : 0 < 1 - x := by
    have := (abs_lt.mp hx).2
    linarith
  have hne : 1 - x ≠ 0 := ne_of_gt hpos
  have hlin : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa [id_eq] using
      (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
  have hquot : HasDerivAt (fun y : ℝ => y / (1 - y))
      ((1 * (1 - x) - x * (-1)) / (1 - x) ^ 2) x := by
    simpa [id_eq] using (hasDerivAt_id x).div hlin hne
  have hlog : HasDerivAt (fun y : ℝ => Real.log (1 - y))
      ((1 - x)⁻¹ * (-1)) x := by
    simpa [Function.comp_apply] using (Real.hasDerivAt_log hne).comp x hlin
  have hcalc :
      (1 * (1 - x) - x * (-1)) / (1 - x) ^ 2 +
          (1 - x)⁻¹ * (-1) =
        x / (1 - x) ^ 2 := by
    field_simp [hne]
    ring
  rw [← hcalc]
  simpa only [antiderivative] using hquot.add hlog

private theorem seriesHasSum (x : ℝ) (hx : |x| < 1) :
    HasSum (fun n => seriesTerm x n) (x / (1 - x) ^ 2) := by
  have hnorm : ‖x‖ < 1 := by
    simpa [Real.norm_eq_abs] using hx
  have hne : 1 - x ≠ 0 := by
    have := (abs_lt.mp hx).2
    linarith
  have hw : HasSum (fun n : ℕ => (n : ℝ) * x ^ n)
      (x / (1 - x) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one hnorm
  have hg : HasSum (fun n : ℕ => x ^ n) (1 - x)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hnorm
  have hs := (hw.add hg).mul_left x
  convert hs using 1
  · funext n
    simp [seriesTerm, pow_succ]
    ring
  · field_simp [hne]
    ring

private theorem seriesClosed (x : ℝ) (hx : |x| < 1) :
    F x = x / (1 - x) ^ 2 := by
  exact (seriesHasSum x hx).tsum_eq

private theorem logarithmHasSum (x : ℝ) (hx : |x| < 1) :
    HasSum (fun n => logarithmTerm x n) (-Real.log (1 - x)) := by
  have hxIoo : x ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp hx
  have hxIco : x ∈ Set.Ico (-1 : ℝ) 1 :=
    ⟨le_of_lt hxIoo.1, hxIoo.2⟩
  have hxIoc : x ∈ Set.Ioc (-1 : ℝ) 1 :=
    ⟨hxIoo.1, le_of_lt hxIoo.2⟩
  have hxIcc : x ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨le_of_lt hxIoo.1, le_of_lt hxIoo.2⟩
  have hx1 : x ≠ 1 := ne_of_lt hxIoo.2
  have hxm1 : x ≠ -1 := ne_of_gt hxIoo.1
  have hxabsle : |x| ≤ 1 := le_of_lt hx
  have hxnorm : ‖x‖ < 1 := by
    simpa [Real.norm_eq_abs] using hx
  have hxnormle : ‖x‖ ≤ 1 := le_of_lt hxnorm
  unfold logarithmTerm
  exact?

private theorem powerTailHasSum (x : ℝ) (hx : |x| < 1) :
    HasSum (fun n => powerTailTerm x n) (x ^ 2 / (1 - x)) := by
  have hnorm : ‖x‖ < 1 := by
    simpa [Real.norm_eq_abs] using hx
  simpa [powerTailTerm, pow_add, mul_comm, div_eq_mul_inv] using
    (hasSum_geometric_of_norm_lt_one hnorm).mul_left (x ^ 2)

private theorem fractionalTailHasSum (x : ℝ) (hx : |x| < 1) :
    HasSum (fun n => fractionalTailTerm x n)
      (-Real.log (1 - x) - x) := by
  have h := hasSumTailOne (logarithmHasSum x hx)
  have hfun : (fun n => fractionalTailTerm x n) =
      (fun n => logarithmTerm x (n + 1)) := by
    funext n
    unfold fractionalTailTerm logarithmTerm
    have hden : (n + 2 : ℝ) = (((n + 1 : ℕ) : ℝ) + 1) := by
      norm_num [Nat.cast_add] <;> ring
    rw [hden]
  rw [hfun]
  simpa [logarithmTerm] using h

private theorem integralTermsHasSum (x : ℝ) (hx : |x| < 1) :
    HasSum (fun n => integralSeriesTerm x n) (antiderivative x) := by
  have hp := powerTailHasSum x hx
  have hf := fractionalTailHasSum x hx
  have hfun : (fun n => integralSeriesTerm x n) =
      (fun n => powerTailTerm x n - fractionalTailTerm x n) := by
    funext n
    unfold integralSeriesTerm powerTailTerm fractionalTailTerm
    have hn : (n + 2 : ℝ) ≠ 0 := by positivity
    field_simp [hn]
    ring
  rw [hfun]
  convert hp.sub hf using 1
  have hne : 1 - x ≠ 0 := by
    have := (abs_lt.mp hx).2
    linarith
  unfold antiderivative
  field_simp [hne]
  ring

private theorem integralClosed (x : ℝ) (hx : |x| < 1) :
    (∫ t in (0 : ℝ)..x, F t) = antiderivative x := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) x,
      HasDerivAt antiderivative (F t) t := by
    intro t ht
    have htlt := absLtOneOfMemUIcc hx ht
    rw [seriesClosed t htlt]
    exact antiderivativeHasDerivAt t htlt
  have hdiff : ∀ t ∈ Set.uIcc (0 : ℝ) x,
      DifferentiableAt ℝ antiderivative t := by
    intro t ht
    exact (hderiv t ht).differentiableAt
  have hg : ContinuousOn (fun t : ℝ => t / (1 - t) ^ 2)
      (Set.uIcc (0 : ℝ) x) := by
    apply ContinuousOn.div continuousOn_id
      ((continuousOn_const.sub continuousOn_id).pow 2)
    intro t ht
    apply pow_ne_zero
    have htlt := absLtOneOfMemUIcc hx ht
    simpa only [id_eq] using
      (ne_of_gt (sub_pos.mpr (abs_lt.mp htlt).2))
  have hFcont : ContinuousOn F (Set.uIcc (0 : ℝ) x) :=
    hg.congr (fun t ht => seriesClosed t (absLtOneOfMemUIcc hx ht))
  have hDcont : ContinuousOn (deriv antiderivative)
      (Set.uIcc (0 : ℝ) x) :=
    hFcont.congr (fun t ht => (hderiv t ht).deriv)
  have hDint : IntervalIntegrable (deriv antiderivative)
      MeasureTheory.volume (0 : ℝ) x :=
    hDcont.intervalIntegrable
  have hFTC :
      (∫ t in (0 : ℝ)..x, deriv antiderivative t) =
        antiderivative x - antiderivative 0 :=
    intervalIntegral.integral_deriv_eq_sub hdiff hDint
  calc
    (∫ t in (0 : ℝ)..x, F t) =
        ∫ t in (0 : ℝ)..x, deriv antiderivative t := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact (hderiv t ht).deriv.symm
    _ = antiderivative x := by
      simpa [antiderivative] using hFTC

private theorem notTendstoNatMulPow (x : ℝ) (hx : |x| = 1) :
    ¬Tendsto (fun n : ℕ => (n : ℝ) * x ^ n) atTop (𝓝 0) := by
  intro h
  have hmem : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  have hev : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * x ^ n ∈ Set.Ioo (-1 : ℝ) 1 := h.eventually hmem
  rcases eventually_atTop.1 hev with ⟨N, hN⟩
  let m := max N 1
  have hm := hN m (le_max_left N 1)
  have hsmall : |(m : ℝ) * x ^ m| < 1 := abs_lt.mpr hm
  have habs : |(m : ℝ) * x ^ m| = (m : ℝ) := by
    rw [abs_mul, abs_pow, hx]
    simp
  rw [habs] at hsmall
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (le_max_right N 1)
  linarith

private theorem notTendstoSeriesTerm (x : ℝ) (hx : |x| = 1) :
    ¬Tendsto (fun n : ℕ => seriesTerm x n) atTop (𝓝 0) := by
  intro h
  have hmem : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  have hev : ∀ᶠ n : ℕ in atTop,
      seriesTerm x n ∈ Set.Ioo (-1 : ℝ) 1 := h.eventually hmem
  rcases eventually_atTop.1 hev with ⟨N, hN⟩
  have hm := hN N (le_refl N)
  have hsmall : |seriesTerm x N| < 1 := abs_lt.mpr hm
  have habs : |seriesTerm x N| = (N : ℝ) + 1 := by
    unfold seriesTerm
    have hcoef : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
    rw [abs_mul, abs_pow, hx, abs_of_nonneg hcoef]
    simp
  rw [habs] at hsmall
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  linarith

theorem gap1 :
    ∀ x : ℝ, |x| < 1 →
      (∫ t in (0 : ℝ)..x, F t) =
        ∑' n, integralSeriesTerm x n := by
  intro x hx
  calc
    (∫ t in (0 : ℝ)..x, F t) = antiderivative x := integralClosed x hx
    _ = ∑' n, integralSeriesTerm x n :=
      (integralTermsHasSum x hx).tsum_eq.symm

theorem gap2 :
    ∀ x : ℝ, |x| < 1 →
      (∫ t in (0 : ℝ)..x, F t) =
        (∑' n, powerTailTerm x n) -
          ∑' n, fractionalTailTerm x n := by
  intro x hx
  have hne : 1 - x ≠ 0 := by
    have := (abs_lt.mp hx).2
    linarith
  calc
    (∫ t in (0 : ℝ)..x, F t) = antiderivative x := integralClosed x hx
    _ = (∑' n, powerTailTerm x n) - ∑' n, fractionalTailTerm x n := by
      rw [(powerTailHasSum x hx).tsum_eq,
        (fractionalTailHasSum x hx).tsum_eq]
      unfold antiderivative
      field_simp [hne]
      ring

theorem gap3 :
    ∀ x : ℝ, |x| < 1 →
      (∫ t in (0 : ℝ)..x, F t) =
        x * (∑' n : ℕ, x ^ n) - ∑' n, logarithmTerm x n := by
  intro x hx
  have hnorm : ‖x‖ < 1 := by
    simpa [Real.norm_eq_abs] using hx
  have hne : 1 - x ≠ 0 := by
    have := (abs_lt.mp hx).2
    linarith
  calc
    (∫ t in (0 : ℝ)..x, F t) = antiderivative x := integralClosed x hx
    _ = x * (∑' n : ℕ, x ^ n) - ∑' n, logarithmTerm x n := by
      rw [(hasSum_geometric_of_norm_lt_one hnorm).tsum_eq,
        (logarithmHasSum x hx).tsum_eq]
      unfold antiderivative
      field_simp [hne]
      ring

theorem gap4 :
    ∀ x : ℝ, |x| < 1 →
      (∫ t in (0 : ℝ)..x, F t) = antiderivative x := by
  intro x hx
  exact integralClosed x hx

theorem gap5 :
    ∀ x : ℝ, |x| < 1 →
      F x = deriv antiderivative x := by
  intro x hx
  calc
    F x = x / (1 - x) ^ 2 := seriesClosed x hx
    _ = deriv antiderivative x :=
      (antiderivativeHasDerivAt x hx).deriv.symm

theorem gap6 :
    ∀ x : ℝ, |x| < 1 →
      deriv antiderivative x = x / (1 - x) ^ 2 := by
  intro x hx
  exact (antiderivativeHasDerivAt x hx).deriv

theorem gap7 :
    ∀ x : ℝ, |x| < 1 →
      F x = x / (1 - x) ^ 2 := by
  intro x hx
  exact seriesClosed x hx

theorem gap8 :
    ∀ x : ℝ, |x| = 1 →
      ¬Tendsto (fun n : ℕ => (n : ℝ) * x ^ n) atTop (𝓝 0) := by
  intro x hx
  exact notTendstoNatMulPow x hx

theorem gap9 :
    ∀ x : ℝ, |x| = 1 →
      ¬Summable (fun n : ℕ => seriesTerm x n) := by
  intro x hx hsum
  exact notTendstoSeriesTerm x hx hsum.tendsto_atTop_zero

theorem gap10 :
    ∀ x : ℝ, |x| < 1 →
      (∑' n, seriesTerm x n) = x / (1 - x) ^ 2 := by
  intro x hx
  exact seriesClosed x hx

end

end ProofGap.Exercise2911
