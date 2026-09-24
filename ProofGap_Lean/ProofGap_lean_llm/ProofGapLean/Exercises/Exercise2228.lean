import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open Filter Topology
open scoped Interval

namespace ProofGap.Exercise2228

noncomputable section

def alpha (n : ℕ) : ℝ :=
  Real.sin (Real.pi / n) / (Real.pi / n) - 1

def reciprocalSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n,
    1 / (2 + Real.cos ((k : ℝ) * Real.pi / n))

def originalSeq (n : ℕ) : ℝ :=
  Real.sin (Real.pi / n) * reciprocalSum n

def transformedSeq (n : ℕ) : ℝ :=
  (1 + alpha n) * (Real.pi / n) * reciprocalSum n

def scaledRiemannSum (n : ℕ) : ℝ :=
  (Real.pi / n) * reciprocalSum n

def primitive (x : ℝ) : ℝ :=
  if x = 1 then
    Real.pi / Real.sqrt 3
  else
    (2 / Real.sqrt 3) *
      Real.arctan (Real.tan (Real.pi * x / 2) / Real.sqrt 3)

private def cosineAntiderivative (x : ℝ) : ℝ :=
  (1 / Real.sqrt 3) *
    Real.arccos ((1 + 2 * Real.cos (Real.pi * x)) /
      (2 + Real.cos (Real.pi * x)))

private theorem cosineAntiderivative_continuous :
    Continuous cosineAntiderivative := by
  apply continuous_const.mul
  apply Real.continuous_arccos.comp
  apply Continuous.div
  · exact continuous_const.add
      (continuous_const.mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
  · exact continuous_const.add
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  · intro x
    have hc := Real.neg_one_le_cos (Real.pi * x)
    linarith

private theorem cosineAntiderivative_deriv
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt cosineAntiderivative
      (Real.pi / (2 + Real.cos (Real.pi * x))) x := by
  let t : ℝ := Real.pi * x
  let c : ℝ := Real.cos t
  let s : ℝ := Real.sin t
  let d : ℝ := 2 + c
  let z : ℝ := (1 + 2 * c) / d
  have ht0 : 0 < t := by
    dsimp [t]
    exact mul_pos Real.pi_pos hx.1
  have htpi : t < Real.pi := by
    dsimp [t]
    have hp : 0 < Real.pi * (1 - x) :=
      mul_pos Real.pi_pos (sub_pos.mpr hx.2)
    nlinarith
  have hspos : 0 < s := by
    dsimp [s]
    exact Real.sin_pos_of_pos_of_lt_pi ht0 htpi
  have htrig : s ^ 2 + c ^ 2 = 1 := by
    simpa [s, c] using Real.sin_sq_add_cos_sq t
  have hcSq : c ^ 2 < 1 := by
    nlinarith [mul_pos hspos hspos]
  have hcLower : -1 < c := by
    nlinarith [sq_nonneg (c + 1)]
  have hcUpper : c < 1 := by
    nlinarith [sq_nonneg (c - 1)]
  have hdpos : 0 < d := by
    dsimp [d]
    linarith
  have hd0 : d ≠ 0 := ne_of_gt hdpos
  have hzmem : z ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · apply (lt_div_iff₀ hdpos).2
      dsimp [z, d]
      linarith
    · apply (div_lt_iff₀ hdpos).2
      dsimp [z, d]
      linarith
  have hrad : 0 ≤ 1 - z ^ 2 := by
    rw [show 1 - z ^ 2 = (1 - z) * (1 + z) by ring]
    exact mul_nonneg (le_of_lt (sub_pos.mpr hzmem.2))
      (le_of_lt (by linarith [hzmem.1] : 0 < 1 + z))
  have hident : 1 - z ^ 2 = 3 * s ^ 2 / d ^ 2 := by
    calc
      1 - z ^ 2 = (d ^ 2 - (1 + 2 * c) ^ 2) / d ^ 2 := by
        dsimp [z]
        field_simp [hd0]
      _ = 3 * s ^ 2 / d ^ 2 := by
        congr 1
        dsimp [d]
        nlinarith [htrig]
  have hsqrt3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt3sq : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  have hsqrt : Real.sqrt (1 - z ^ 2) = Real.sqrt 3 * s / d := by
    have hl := Real.sq_sqrt hrad
    have hrnonneg : 0 ≤ Real.sqrt 3 * s / d := by
      exact div_nonneg (mul_nonneg (le_of_lt hsqrt3) (le_of_lt hspos))
        (le_of_lt hdpos)
    have hr : (Real.sqrt 3 * s / d) ^ 2 = 1 - z ^ 2 := by
      rw [hident]
      field_simp [hd0]
      nlinarith [hsqrt3sq]
    nlinarith [Real.sqrt_nonneg (1 - z ^ 2)]
  have hlin : HasDerivAt (fun y : ℝ => Real.pi * y) Real.pi x := by
    convert (hasDerivAt_const x Real.pi).mul (hasDerivAt_id x) using 1 <;> ring
  have hcder : HasDerivAt (fun y : ℝ => Real.cos (Real.pi * y))
      (-Real.pi * s) x := by
    convert (Real.hasDerivAt_cos (Real.pi * x)).comp x hlin using 1 <;>
      simp [s, t, mul_comm]
  have hnum := (hasDerivAt_const x (1 : ℝ)).add (hcder.const_mul 2)
  have hden := (hasDerivAt_const x (2 : ℝ)).add hcder
  have hdenx : 2 + Real.cos (Real.pi * x) ≠ 0 := by
    simpa [d, c, t] using hd0
  have hzder : HasDerivAt
      (fun y : ℝ => (1 + 2 * Real.cos (Real.pi * y)) /
        (2 + Real.cos (Real.pi * y)))
      (-3 * Real.pi * s / d ^ 2) x := by
    convert hnum.div hden hdenx using 1
    dsimp [d, c, s, t]
    field_simp [hdenx]
    ring
  have harc :=
    (Real.hasDerivAt_arccos (ne_of_gt hzmem.1) (ne_of_lt hzmem.2)).comp x hzder
  have hall := harc.const_mul (1 / Real.sqrt 3)
  convert hall using 1
  change Real.pi / d =
    1 / Real.sqrt 3 *
      (-(1 / Real.sqrt (1 - z ^ 2)) * (-3 * Real.pi * s / d ^ 2))
  rw [hsqrt]
  field_simp [ne_of_gt hsqrt3, hd0, ne_of_gt hspos] <;>
    nlinarith [hsqrt3sq]

private theorem cosine_integral_value :
    Real.pi * (∫ x in (0 : ℝ)..1,
      1 / (2 + Real.cos (Real.pi * x))) =
      Real.pi / Real.sqrt 3 := by
  have hden : ∀ x : ℝ, 2 + Real.cos (Real.pi * x) ≠ 0 := by
    intro x
    have hc := Real.neg_one_le_cos (Real.pi * x)
    linarith
  have hcos : Continuous (fun x : ℝ => Real.cos (Real.pi * x)) := by
    exact Real.continuous_cos.comp
      (continuous_const.mul continuous_id)
  have hintCont : Continuous
      (fun x : ℝ => Real.pi / (2 + Real.cos (Real.pi * x))) := by
    exact continuous_const.div (continuous_const.add hcos) hden
  have hFTC :
      (∫ x in (0 : ℝ)..1, Real.pi / (2 + Real.cos (Real.pi * x))) =
        cosineAntiderivative 1 - cosineAntiderivative 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right
    · exact cosineAntiderivative_continuous.continuousOn
    · intro x hx
      exact (cosineAntiderivative_deriv (by simpa using hx)).hasDerivWithinAt
    · exact hintCont.continuousOn.intervalIntegrable
  calc
    Real.pi * (∫ x in (0 : ℝ)..1,
        1 / (2 + Real.cos (Real.pi * x))) =
        ∫ x in (0 : ℝ)..1,
          Real.pi / (2 + Real.cos (Real.pi * x)) := by
            rw [← intervalIntegral.integral_const_mul]
            congr 1
            funext x
            ring
    _ = cosineAntiderivative 1 - cosineAntiderivative 0 := hFTC
    _ = Real.pi / Real.sqrt 3 := by
      norm_num [cosineAntiderivative, Real.pi_ne_zero, div_eq_mul_inv,
        mul_comm]

private theorem tendsto_rightEndpoint_sum_of_monotone
    (f : ℝ → ℝ) (hf : Continuous f)
    (hmono : MonotoneOn f (Set.Icc (0 : ℝ) 1)) :
    Tendsto
      (fun n : ℕ =>
        (1 / (n : ℝ)) *
          (∑ k ∈ Finset.Icc 1 n, f ((k : ℝ) / (n : ℝ))))
      atTop (nhds (∫ x in (0 : ℝ)..1, f x)) := by
  let I : ℝ := ∫ x in (0 : ℝ)..1, f x
  have hbnds : ∀ n : ℕ, 0 < n →
      I ≤ (1 / (n : ℝ)) *
          (∑ k ∈ Finset.Icc 1 n, f ((k : ℝ) / (n : ℝ))) ∧
      (1 / (n : ℝ)) *
          (∑ k ∈ Finset.Icc 1 n, f ((k : ℝ) / (n : ℝ))) ≤
        I + (1 / (n : ℝ)) * (f 1 - f 0) := by
    intro n hn
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    let u : ℕ → ℝ := fun k => f ((k : ℝ) / (n : ℝ))
    have hpartition :
        (∑ k ∈ Finset.range n,
          (∫ x in (k : ℝ) / (n : ℝ)..
            ((k + 1 : ℕ) : ℝ) / (n : ℝ), f x)) = I := by
      have hpartial (m : ℕ) :
          (∑ k ∈ Finset.range m,
            (∫ x in (k : ℝ) / (n : ℝ)..
              ((k + 1 : ℕ) : ℝ) / (n : ℝ), f x)) =
            ∫ x in (0 : ℝ)..(m : ℝ) / (n : ℝ), f x := by
        induction m with
        | zero => simp
        | succ m ih =>
          rw [Finset.sum_range_succ, ih]
          simpa [Nat.succ_eq_add_one] using
            (intervalIntegral.integral_add_adjacent_intervals
              (hf.continuousOn.intervalIntegrable)
              (hf.continuousOn.intervalIntegrable))
      simpa [I, hn0] using hpartial n
    have hcell (k : ℕ) (hk : k ∈ Finset.range n) :
        (1 / (n : ℝ)) * u k ≤
            (∫ x in (k : ℝ) / (n : ℝ)..
              ((k + 1 : ℕ) : ℝ) / (n : ℝ), f x) ∧
          (∫ x in (k : ℝ) / (n : ℝ)..
              ((k + 1 : ℕ) : ℝ) / (n : ℝ), f x) ≤
            (1 / (n : ℝ)) * u (k + 1) := by
      have hklt : k < n := Finset.mem_range.mp hk
      have hksucc : k + 1 ≤ n := by omega
      have hab : (k : ℝ) / (n : ℝ) ≤
          ((k + 1 : ℕ) : ℝ) / (n : ℝ) := by
        exact div_le_div_of_nonneg_right
          (Nat.cast_le.mpr (Nat.le_succ k)) hnR.le
      have ha0 : 0 ≤ (k : ℝ) / (n : ℝ) :=
        div_nonneg (Nat.cast_nonneg k) hnR.le
      have hnumle : ((k + 1 : ℕ) : ℝ) ≤ (n : ℝ) :=
        Nat.cast_le.mpr hksucc
      have hb1 : ((k + 1 : ℕ) : ℝ) / (n : ℝ) ≤ 1 := by
        exact (div_le_iff₀ hnR).2 (by simpa using hnumle)
      have haMem : (k : ℝ) / (n : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨ha0, le_trans hab hb1⟩
      have hbMem : ((k + 1 : ℕ) : ℝ) / (n : ℝ) ∈
          Set.Icc (0 : ℝ) 1 :=
        ⟨le_trans ha0 hab, hb1⟩
      have hwidth :
          ((k + 1 : ℕ) : ℝ) / (n : ℝ) -
              (k : ℝ) / (n : ℝ) = 1 / (n : ℝ) := by
        rw [Nat.cast_add, Nat.cast_one]
        ring
      have hlow :
          (∫ x in (k : ℝ) / (n : ℝ)..
              ((k + 1 : ℕ) : ℝ) / (n : ℝ),
              f ((k : ℝ) / (n : ℝ))) ≤
            ∫ x in (k : ℝ) / (n : ℝ)..
              ((k + 1 : ℕ) : ℝ) / (n : ℝ), f x := by
        apply intervalIntegral.integral_mono_on hab
        · exact continuous_const.continuousOn.intervalIntegrable
        · exact hf.continuousOn.intervalIntegrable
        · intro x hx
          have hxMem : x ∈ Set.Icc (0 : ℝ) 1 :=
            ⟨le_trans ha0 hx.1, le_trans hx.2 hb1⟩
          exact hmono haMem hxMem hx.1
      have hupp :
          (∫ x in (k : ℝ) / (n : ℝ)..
              ((k + 1 : ℕ) : ℝ) / (n : ℝ), f x) ≤
            ∫ x in (k : ℝ) / (n : ℝ)..
              ((k + 1 : ℕ) : ℝ) / (n : ℝ),
              f (((k + 1 : ℕ) : ℝ) / (n : ℝ)) := by
        apply intervalIntegral.integral_mono_on hab
        · exact hf.continuousOn.intervalIntegrable
        · exact continuous_const.continuousOn.intervalIntegrable
        · intro x hx
          have hxMem : x ∈ Set.Icc (0 : ℝ) 1 :=
            ⟨le_trans ha0 hx.1, le_trans hx.2 hb1⟩
          exact hmono hxMem hbMem hx.2
      constructor
      · calc
          (1 / (n : ℝ)) * u k =
              ∫ x in (k : ℝ) / (n : ℝ)..
                ((k + 1 : ℕ) : ℝ) / (n : ℝ),
                f ((k : ℝ) / (n : ℝ)) := by
                  simp [u]
                  left
                  field_simp [hn0] <;> ring
          _ ≤ ∫ x in (k : ℝ) / (n : ℝ)..
                ((k + 1 : ℕ) : ℝ) / (n : ℝ), f x := hlow
      · calc
          (∫ x in (k : ℝ) / (n : ℝ)..
              ((k + 1 : ℕ) : ℝ) / (n : ℝ), f x) ≤
              ∫ x in (k : ℝ) / (n : ℝ)..
                ((k + 1 : ℕ) : ℝ) / (n : ℝ),
                f (((k + 1 : ℕ) : ℝ) / (n : ℝ)) := hupp
          _ = (1 / (n : ℝ)) * u (k + 1) := by
                simp [u]
                left
                field_simp [hn0] <;> ring
    have hsumLower :
        (∑ k ∈ Finset.range n, (1 / (n : ℝ)) * u k) ≤ I := by
      calc
        (∑ k ∈ Finset.range n, (1 / (n : ℝ)) * u k) ≤
            ∑ k ∈ Finset.range n,
              (∫ x in (k : ℝ) / (n : ℝ)..
                ((k + 1 : ℕ) : ℝ) / (n : ℝ), f x) := by
                  exact Finset.sum_le_sum
                    (fun k hk => (hcell k hk).1)
        _ = I := hpartition
    have hsumUpper :
        I ≤ ∑ k ∈ Finset.range n,
          (1 / (n : ℝ)) * u (k + 1) := by
      calc
        I = ∑ k ∈ Finset.range n,
            (∫ x in (k : ℝ) / (n : ℝ)..
              ((k + 1 : ℕ) : ℝ) / (n : ℝ), f x) := hpartition.symm
        _ ≤ ∑ k ∈ Finset.range n,
            (1 / (n : ℝ)) * u (k + 1) := by
              exact Finset.sum_le_sum
                (fun k hk => (hcell k hk).2)
    have htelAux (m : ℕ) :
        (∑ k ∈ Finset.range m, u (k + 1)) -
            (∑ k ∈ Finset.range m, u k) = u m - u 0 := by
      induction m with
      | zero => simp
      | succ m ih =>
          simp only [Finset.sum_range_succ]
          linarith
    have htel :
        (∑ k ∈ Finset.range n, (1 / (n : ℝ)) * u (k + 1)) -
            (∑ k ∈ Finset.range n, (1 / (n : ℝ)) * u k) =
          (1 / (n : ℝ)) * (f 1 - f 0) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_sub, htelAux n]
      simp [u, hn0]
    have hindex :
        (Finset.range n).image (fun k : ℕ => k + 1) =
          Finset.Icc 1 n := by
      ext j
      simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
      constructor
      · rintro ⟨k, hk, rfl⟩
        constructor <;> omega
      · rintro ⟨hj1, hjn⟩
        refine ⟨j - 1, ?_, ?_⟩ <;> omega
    have hshift :
        (∑ k ∈ Finset.range n, u (k + 1)) =
          ∑ k ∈ Finset.Icc 1 n, u k := by
      rw [← hindex]
      symm
      apply Finset.sum_image
      intro a ha b hb hab
      simpa using hab
    have hactual :
        (1 / (n : ℝ)) *
            (∑ k ∈ Finset.Icc 1 n, f ((k : ℝ) / (n : ℝ))) =
          ∑ k ∈ Finset.range n,
            (1 / (n : ℝ)) * u (k + 1) := by
      change (1 / (n : ℝ)) * (∑ k ∈ Finset.Icc 1 n, u k) =
        ∑ k ∈ Finset.range n, (1 / (n : ℝ)) * u (k + 1)
      rw [← hshift, Finset.mul_sum]
    constructor
    · rw [hactual]
      exact hsumUpper
    · rw [hactual]
      linarith [hsumLower, htel]
  have hInv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0))
  have hErr : Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) * (f 1 - f 0))
      atTop (nhds 0) := by
    simpa using
      hInv.mul
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => f 1 - f 0) atTop (nhds (f 1 - f 0)))
  have hUpper : Tendsto
      (fun n : ℕ => I + (1 / (n : ℝ)) * (f 1 - f 0))
      atTop (nhds I) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => I) atTop (nhds I)).add hErr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => I) atTop (nhds I))
    hUpper ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (hbnds n hn).1
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (hbnds n hn).2

theorem gap1 (n : ℕ) :
    Real.sin (Real.pi / n) =
      (Real.pi / n) * (1 + alpha n) := by
  let q : ℝ := Real.pi / (n : ℝ)
  change Real.sin q = q * (1 + (Real.sin q / q - 1))
  by_cases hq : q = 0
  · simp [hq]
  · field_simp [hq] <;> ring

theorem gap2 :
    Tendsto alpha atTop (𝓝 0) := by
  have hx : Tendsto (fun n : ℕ => Real.pi / (n : ℝ)) atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => Real.pi / (n : ℝ)) atTop (nhds 0))
  have hs : Tendsto (fun n : ℕ => Real.sinc (Real.pi / (n : ℝ))) atTop (nhds 1) := by
    simpa using Real.continuous_sinc.continuousAt.tendsto.comp hx
  have hz : Tendsto (fun n : ℕ => Real.sinc (Real.pi / (n : ℝ)) - 1) atTop (nhds 0) := by
    simpa using hs.sub_const (1 : ℝ)
  apply hz.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hq : Real.pi / (n : ℝ) ≠ 0 := div_ne_zero Real.pi_ne_zero hn0
  simp [alpha, Real.sinc, hq]

theorem gap3 :
    ∀ L : ℝ, Tendsto originalSeq atTop (𝓝 L) ↔
      Tendsto transformedSeq atTop (𝓝 L) := by
  intro L
  have hseq : originalSeq = transformedSeq := by
    funext n
    simp only [originalSeq, transformedSeq]
    rw [gap1]
    ring
  rw [hseq]

theorem gap4 :
    ∀ L : ℝ, Tendsto scaledRiemannSum atTop (𝓝 L) →
      Tendsto transformedSeq atTop (𝓝 L) := by
  intro L hL
  have ha : Tendsto (fun n : ℕ => 1 + alpha n) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add gap2
  have hp : Tendsto
      (fun n : ℕ => (1 + alpha n) * scaledRiemannSum n)
      atTop (nhds L) := by
    simpa using ha.mul hL
  have heq : transformedSeq =
      (fun n : ℕ => (1 + alpha n) * scaledRiemannSum n) := by
    funext n
    simp [transformedSeq, scaledRiemannSum, mul_assoc]
  rw [heq]
  exact hp

theorem gap5 :
    ∀ L : ℝ, Tendsto scaledRiemannSum atTop (𝓝 L) →
      Tendsto originalSeq atTop (𝓝 L) := by
  intro L hL
  apply (gap3 L).2
  exact gap4 L hL

theorem gap6 :
    Tendsto originalSeq atTop
      (𝓝 (Real.pi *
        ∫ x in (0 : ℝ)..1, 1 / (2 + Real.cos (Real.pi * x)))) := by
  apply gap5
  let f : ℝ → ℝ := fun x => 1 / (2 + Real.cos (Real.pi * x))
  have hden : ∀ x : ℝ, 2 + Real.cos (Real.pi * x) ≠ 0 := by
    intro x
    have hc := Real.neg_one_le_cos (Real.pi * x)
    linarith
  have hcos : Continuous (fun x : ℝ => Real.cos (Real.pi * x)) := by
    exact Real.continuous_cos.comp
      (continuous_const.mul continuous_id)
  have hf : Continuous f := by
    exact continuous_const.div (continuous_const.add hcos) hden
  have hmono : MonotoneOn f (Set.Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    rcases hxy.eq_or_lt with hEq | hLt
    · subst y
      exact le_rfl
    · have hpx : Real.pi * x ∈ Set.Icc (0 : ℝ) Real.pi := by
        constructor
        · exact mul_nonneg (le_of_lt Real.pi_pos) hx.1
        · simpa using
            mul_le_mul_of_nonneg_left hx.2 (le_of_lt Real.pi_pos)
      have hpy : Real.pi * y ∈ Set.Icc (0 : ℝ) Real.pi := by
        constructor
        · exact mul_nonneg (le_of_lt Real.pi_pos) hy.1
        · simpa using
            mul_le_mul_of_nonneg_left hy.2 (le_of_lt Real.pi_pos)
      have hc : Real.cos (Real.pi * y) < Real.cos (Real.pi * x) :=
        Real.strictAntiOn_cos hpx hpy
          (mul_lt_mul_of_pos_left hLt Real.pi_pos)
      have hdx : 0 < 2 + Real.cos (Real.pi * x) := by
        have hxcos := Real.neg_one_le_cos (Real.pi * x)
        linarith
      have hdy : 0 < 2 + Real.cos (Real.pi * y) := by
        have hycos := Real.neg_one_le_cos (Real.pi * y)
        linarith
      dsimp [f]
      exact (div_le_div_iff₀ hdx hdy).2 (by linarith)
  have hR := tendsto_rightEndpoint_sum_of_monotone f hf hmono
  have hsum : ∀ n : ℕ, reciprocalSum n =
      ∑ k ∈ Finset.Icc 1 n, f ((k : ℝ) / (n : ℝ)) := by
    intro n
    simp only [reciprocalSum]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [f]
    apply congrArg (fun u : ℝ => 1 / (2 + Real.cos u))
    ring
  have hscaled : scaledRiemannSum =
      (fun n : ℕ => Real.pi *
        ((1 / (n : ℝ)) *
          ∑ k ∈ Finset.Icc 1 n, f ((k : ℝ) / (n : ℝ)))) := by
    funext n
    change (Real.pi / (n : ℝ)) * reciprocalSum n = _
    rw [hsum n]
    ring
  have hmul : Tendsto
      (fun n : ℕ => Real.pi *
        ((1 / (n : ℝ)) *
          ∑ k ∈ Finset.Icc 1 n, f ((k : ℝ) / (n : ℝ))))
      atTop (nhds (Real.pi * ∫ x in (0 : ℝ)..1, f x)) := by
    simpa using tendsto_const_nhds.mul hR
  rw [hscaled]
  simpa [f] using hmul

theorem gap7 :
    Real.pi * (∫ x in (0 : ℝ)..1, 1 / (2 + Real.cos (Real.pi * x))) =
      primitive 1 - primitive 0 := by
  simpa [primitive, div_eq_mul_inv, mul_comm] using cosine_integral_value

theorem gap8 :
    primitive 1 - primitive 0 = Real.pi / Real.sqrt 3 := by
  norm_num [primitive, Real.pi_ne_zero]

theorem gap9 :
    Tendsto originalSeq atTop (𝓝 (Real.pi / Real.sqrt 3)) := by
  simpa only [gap7, gap8] using gap6

end

end ProofGap.Exercise2228
