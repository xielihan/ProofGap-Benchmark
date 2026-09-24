import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2912

noncomputable section

open scoped BigOperators Interval

def seriesTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (n + 1 : ℝ) ^ 2 * x ^ (n + 1)

def integralSeriesTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (n + 1 : ℝ) ^ 2 /
    (n + 2 : ℝ) * x ^ (n + 2)

def logarithmTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ (n + 1) / (n + 1 : ℝ)

def alternatingGeometricTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ (n + 1)

def alternatingDerivativeTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (n + 1 : ℝ) * x ^ n

def F (x : ℝ) : ℝ :=
  ∑' n, seriesTerm x n

def G (x : ℝ) : ℝ :=
  ∑' n, alternatingGeometricTerm x n

def antiderivative (x : ℝ) : ℝ :=
  x - Real.log (1 + x) - x ^ 3 / (1 + x) ^ 2

private theorem hasSum_logarithmTerm {x : ℝ} (hx : |x| < 1) :
    HasSum (logarithmTerm x) (Real.log (1 + x)) := by
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one
    (x := -x) (by simpa only [abs_neg] using hx)).mul_left (-1)
  convert h using 1
  · ext n
    simp only [logarithmTerm]
    rw [neg_pow, pow_succ]
    ring
  · simp only [sub_neg_eq_add]
    ring

private theorem hasSum_alternatingGeometricTerm {x : ℝ} (hx : |x| < 1) :
    HasSum (alternatingGeometricTerm x) (x / (1 + x)) := by
  have h := (hasSum_geometric_of_abs_lt_one
    (r := -x) (by simpa only [abs_neg] using hx)).mul_left x
  convert h using 1
  · ext n
    simp only [alternatingGeometricTerm]
    rw [neg_pow, pow_succ]
    ring
  · field_simp
    ring

private theorem hasSum_alternatingDerivativeTerm {x : ℝ} (hx : |x| < 1) :
    HasSum (alternatingDerivativeTerm x) (1 / (1 + x) ^ 2) := by
  have h := hasSum_choose_mul_geometric_of_norm_lt_one
    (𝕜 := ℝ) 1 (r := -x) (by simpa [Real.norm_eq_abs] using hx)
  convert h using 1
  · ext n
    simp only [alternatingDerivativeTerm, Nat.choose_one_right]
    rw [neg_pow]
    push_cast
    ring
  · ring_nf

private theorem hasSum_seriesTerm {x : ℝ} (hx : |x| < 1) :
    HasSum (seriesTerm x) (x * (1 - x) / (1 + x) ^ 3) := by
  have h2 := (hasSum_choose_mul_geometric_of_norm_lt_one
    (𝕜 := ℝ) 2 (r := -x) (by simpa [Real.norm_eq_abs] using hx)).mul_left 2
  have h1 := hasSum_choose_mul_geometric_of_norm_lt_one
    (𝕜 := ℝ) 1 (r := -x) (by simpa [Real.norm_eq_abs] using hx)
  have h := (h2.sub h1).mul_left x
  convert h using 1
  · ext n
    simp only [seriesTerm, Nat.choose_one_right]
    have hcNat : 2 * (n + 2).choose 2 = (n + 2) * (n + 1) := by
      calc
        2 * (n + 2).choose 2 = Nat.factorial 2 * (n + 2).choose 2 := by norm_num
        _ = (n + 2).descFactorial 2 :=
          (Nat.descFactorial_eq_factorial_mul_choose _ _).symm
        _ = (n + 2) * (n + 1) := by simp [Nat.descFactorial, Nat.mul_comm]
    have hc : (2 : ℝ) * ((n + 2).choose 2 : ℕ) =
        (n + 2 : ℕ) * (n + 1 : ℕ) := by
      exact_mod_cast hcNat
    have hcoeff : (n + 1 : ℝ) ^ 2 =
        2 * ((n + 2).choose 2 : ℕ) - (n + 1 : ℕ) := by
      rw [hc]
      push_cast
      ring
    rw [hcoeff, neg_pow, pow_succ]
    push_cast
    ring
  · simp only [sub_neg_eq_add, Nat.reduceAdd]
    have hne : 1 + x ≠ 0 := by
      rw [abs_lt] at hx
      linarith
    field_simp [hne]
    ring

private theorem hasDerivAt_antiderivative {x : ℝ} (hx : |x| < 1) :
    HasDerivAt antiderivative (x * (1 - x) / (1 + x) ^ 3) x := by
  have hne : 1 + x ≠ 0 := by
    rw [abs_lt] at hx
    linarith
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hadd : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    convert (hasDerivAt_const x (1 : ℝ)).add hid using 1 <;> simp
  have hlog : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 + x)⁻¹ x :=
    by simpa only [Function.comp_apply, mul_one] using
      (Real.hasDerivAt_log hne).comp x hadd
  have hquot := (hid.pow 3).div (hadd.pow 2) (pow_ne_zero 2 hne)
  have h := (hid.sub hlog).sub hquot
  convert h using 1
  simp only [Pi.pow_apply, Pi.div_apply, Pi.sub_apply]
  norm_num
  field_simp [hne]
  ring

private theorem abs_lt_one_of_mem_uIcc_zero {x t : ℝ} (hx : |x| < 1)
    (ht : t ∈ Set.uIcc 0 x) : |t| < 1 := by
  rw [abs_lt] at hx ⊢
  rcases ht with ⟨htl, htr⟩
  constructor
  · exact lt_of_lt_of_le (lt_min (by norm_num) hx.1) htl
  · exact lt_of_le_of_lt htr (max_lt (by norm_num) hx.2)

private theorem integral_F_eq_antiderivative {x : ℝ} (hx : |x| < 1) :
    (∫ t in (0 : ℝ)..x, F t) = antiderivative x := by
  have hpoint : ∀ t ∈ Set.uIcc (0 : ℝ) x,
      F t = t * (1 - t) / (1 + t) ^ 3 := by
    intro t ht
    exact (hasSum_seriesTerm (abs_lt_one_of_mem_uIcc_zero hx ht)).tsum_eq
  have hclosed : ContinuousOn (fun t : ℝ => t * (1 - t) / (1 + t) ^ 3)
      (Set.uIcc (0 : ℝ) x) := by
    apply ContinuousOn.div
    · exact continuousOn_id.mul (continuousOn_const.sub continuousOn_id)
    · exact (continuousOn_const.add continuousOn_id).pow 3
    · intro t ht
      apply pow_ne_zero
      have ht' := abs_lt_one_of_mem_uIcc_zero hx ht
      rw [abs_lt] at ht'
      linarith
  have hcont : ContinuousOn F (Set.uIcc (0 : ℝ) x) := by
    exact hclosed.congr (fun t ht => hpoint t ht)
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) x,
      HasDerivAt antiderivative (F t) t := by
    intro t ht
    rw [hpoint t ht]
    exact hasDerivAt_antiderivative (abs_lt_one_of_mem_uIcc_zero hx ht)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp [antiderivative]

private theorem hasSum_integralSeriesTerm {x : ℝ} (hx : |x| < 1) :
    HasSum (integralSeriesTerm x) (antiderivative x) := by
  have hlinear := hasSum_coe_mul_geometric_of_norm_lt_one
    (𝕜 := ℝ) (r := -x) (by simpa [Real.norm_eq_abs] using hx)
  have hmain := hlinear.mul_left (x ^ 2)
  have htail : HasSum (fun n => logarithmTerm x (n + 1))
      (Real.log (1 + x) - x) := by
    have h := (hasSum_nat_add_iff' 1).mpr (hasSum_logarithmTerm hx)
    convert h using 1 <;> simp [logarithmTerm]
  have hrem := htail.mul_left (-1)
  have h := hmain.add hrem
  convert h using 1
  · ext n
    simp only [integralSeriesTerm, logarithmTerm]
    rw [neg_pow]
    push_cast
    have hden : (n + 2 : ℝ) ≠ 0 := by positivity
    field_simp [hden]
    ring
  · simp only [antiderivative, sub_neg_eq_add]
    ring

private theorem hasDerivAt_ratio {x : ℝ} (hne : 1 + x ≠ 0) :
    HasDerivAt (fun u : ℝ => u / (1 + u)) (1 / (1 + x) ^ 2) x := by
  have hid : HasDerivAt (fun u : ℝ => u) 1 x := hasDerivAt_id x
  have hadd : HasDerivAt (fun u : ℝ => 1 + u) 1 x := by
    convert (hasDerivAt_const x (1 : ℝ)).add hid using 1 <;> simp
  convert hid.div hadd hne using 1
  field_simp [hne]
  ring

private theorem deriv_G_eq {x : ℝ} (hx : |x| < 1) :
    deriv G x = 1 / (1 + x) ^ 2 := by
  have hopen : IsOpen {u : ℝ | |u| < 1} :=
    isOpen_lt continuous_abs continuous_const
  have heq : G =ᶠ[nhds x] (fun u : ℝ => u / (1 + u)) := by
    filter_upwards [hopen.mem_nhds hx] with u hu
    exact (hasSum_alternatingGeometricTerm hu).tsum_eq
  rw [heq.deriv_eq]
  have hne : 1 + x ≠ 0 := by
    rw [abs_lt] at hx
    linarith
  exact (hasDerivAt_ratio hne).deriv

private theorem not_summable_seriesTerm_of_abs_eq_one {x : ℝ} (hx : |x| = 1) :
    ¬Summable (fun n : ℕ => seriesTerm x n) := by
  intro hs
  have hnorm : Tendsto (fun n => ‖seriesTerm x n‖) atTop (nhds 0) :=
    tendsto_norm_zero.comp hs.tendsto_atTop_zero
  have hev : ∀ᶠ n in atTop, ‖seriesTerm x n‖ < 1 :=
    (tendsto_order.1 hnorm).2 1 (by norm_num)
  rw [Filter.eventually_atTop] at hev
  rcases hev with ⟨n, hn⟩
  have hn' := hn n le_rfl
  have heq : ‖seriesTerm x n‖ = (n + 1 : ℝ) ^ 2 := by
    simp [seriesTerm, Real.norm_eq_abs, abs_pow, hx]
  rw [heq] at hn'
  have hn0 : (0 : ℝ) ≤ n := by positivity
  nlinarith

theorem gap1 :
    ∀ x : ℝ, |x| < 1 →
      (∫ t in (0 : ℝ)..x, F t) =
        ∑' n, integralSeriesTerm x n := by
  intro x hx
  rw [integral_F_eq_antiderivative hx]
  exact (hasSum_integralSeriesTerm hx).tsum_eq.symm

theorem gap2 :
    ∀ x : ℝ, |x| < 1 →
      (∫ t in (0 : ℝ)..x, F t) =
        x - (∑' n, logarithmTerm x n) -
          x ^ 3 * ∑' n, alternatingDerivativeTerm x n := by
  intro x hx
  rw [integral_F_eq_antiderivative hx,
    (hasSum_logarithmTerm hx).tsum_eq,
    (hasSum_alternatingDerivativeTerm hx).tsum_eq]
  simp only [antiderivative]
  ring

theorem gap3 :
    ∀ x : ℝ, |x| < 1 →
      (∫ t in (0 : ℝ)..x, F t) =
        x - Real.log (1 + x) - x ^ 3 * deriv G x := by
  intro x hx
  rw [integral_F_eq_antiderivative hx, deriv_G_eq hx]
  simp only [antiderivative]
  ring

theorem gap4 :
    ∀ x : ℝ, |x| < 1 →
      (∫ t in (0 : ℝ)..x, F t) =
        x - Real.log (1 + x) -
          x ^ 3 * deriv (fun u : ℝ => u / (1 + u)) x := by
  intro x hx
  have hne : 1 + x ≠ 0 := by
    rw [abs_lt] at hx
    linarith
  rw [integral_F_eq_antiderivative hx, (hasDerivAt_ratio hne).deriv]
  simp only [antiderivative]
  ring

theorem gap5 :
    ∀ x : ℝ, |x| < 1 →
      (∫ t in (0 : ℝ)..x, F t) = antiderivative x := by
  intro x hx
  exact integral_F_eq_antiderivative hx

theorem gap6 :
    ∀ x : ℝ, |x| < 1 →
      F x = deriv antiderivative x := by
  intro x hx
  rw [F, (hasSum_seriesTerm hx).tsum_eq,
    (hasDerivAt_antiderivative hx).deriv]

theorem gap7 :
    ∀ x : ℝ, |x| < 1 →
      deriv antiderivative x = x * (1 - x) / (1 + x) ^ 3 := by
  intro x hx
  exact (hasDerivAt_antiderivative hx).deriv

theorem gap8 :
    ∀ x : ℝ, |x| < 1 →
      F x = x * (1 - x) / (1 + x) ^ 3 := by
  intro x hx
  exact (hasSum_seriesTerm hx).tsum_eq

theorem gap9 :
    ∀ x : ℝ, |x| = 1 →
      ¬Summable (fun n : ℕ => seriesTerm x n) := by
  intro x hx
  exact not_summable_seriesTerm_of_abs_eq_one hx

theorem gap10 :
    ∀ x : ℝ, |x| < 1 →
      (∑' n, seriesTerm x n) =
        x * (1 - x) / (1 + x) ^ 3 := by
  intro x hx
  exact (hasSum_seriesTerm hx).tsum_eq

end

end ProofGap.Exercise2912
