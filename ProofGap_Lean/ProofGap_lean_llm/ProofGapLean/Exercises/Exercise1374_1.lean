import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1374_1

noncomputable section

open Filter

def puncturedZero : Filter ℝ := nhdsWithin 0 ({0} : Set ℝ)ᶜ

def numerator (x : ℝ) : ℝ := x ^ 2 * Real.sin (1 / x)
def denominator (x : ℝ) : ℝ := Real.sin x
def derivativeRatio (x : ℝ) : ℝ :=
  (2 * x * Real.sin (1 / x) - Real.cos (1 / x)) / Real.cos x
def normalizedProduct (x : ℝ) : ℝ :=
  (x / Real.sin x) * (x * Real.sin (1 / x))

private theorem tendsto_recip_affine_nat (c d : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => 1 / (c * (n : ℝ) + d)) atTop (nhds 0) := by
  have hden :
      Tendsto (fun n : ℕ => c * (n : ℝ) + d) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt ((b - d) / c)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hstep : (b - d) / c < (n : ℝ) := lt_of_lt_of_le hN hcast
    have hcancel : c * ((b - d) / c) = b - d := by
      field_simp [ne_of_gt hc]
    nlinarith
  simpa [one_div] using (tendsto_inv_atTop_zero.comp hden)

private def evenPoint (n : ℕ) : ℝ :=
  1 / (2 * Real.pi * (n : ℝ) + 2 * Real.pi)

private def oddPoint (n : ℕ) : ℝ :=
  1 / (2 * Real.pi * (n : ℝ) + Real.pi)

private theorem evenPoint_tendsto_zero :
    Tendsto evenPoint atTop (nhds 0) := by
  change Tendsto
    (fun n : ℕ => 1 / (2 * Real.pi * (n : ℝ) + 2 * Real.pi))
    atTop (nhds 0)
  exact tendsto_recip_affine_nat
    (2 * Real.pi) (2 * Real.pi) (by positivity)

private theorem oddPoint_tendsto_zero :
    Tendsto oddPoint atTop (nhds 0) := by
  change Tendsto
    (fun n : ℕ => 1 / (2 * Real.pi * (n : ℝ) + Real.pi))
    atTop (nhds 0)
  exact tendsto_recip_affine_nat
    (2 * Real.pi) Real.pi (by positivity)

private theorem evenPoint_ne_zero (n : ℕ) : evenPoint n ≠ 0 := by
  unfold evenPoint
  positivity

private theorem oddPoint_ne_zero (n : ℕ) : oddPoint n ≠ 0 := by
  unfold oddPoint
  positivity

private theorem tendsto_punctured_of_ne
    {f : ℕ → ℝ} (h0 : Tendsto f atTop (nhds 0))
    (hne : ∀ n, f n ≠ 0) : Tendsto f atTop puncturedZero := by
  unfold puncturedZero
  refine tendsto_nhdsWithin_iff.2 ⟨h0, ?_⟩
  exact Filter.Eventually.of_forall fun n => by simpa using hne n

private theorem evenPoint_tendsto_punctured :
    Tendsto evenPoint atTop puncturedZero :=
  tendsto_punctured_of_ne evenPoint_tendsto_zero evenPoint_ne_zero

private theorem oddPoint_tendsto_punctured :
    Tendsto oddPoint atTop puncturedZero :=
  tendsto_punctured_of_ne oddPoint_tendsto_zero oddPoint_ne_zero

private theorem trig_two_pi_nat (n : ℕ) :
    Real.sin (2 * Real.pi * (n : ℝ)) = 0 ∧
      Real.cos (2 * Real.pi * (n : ℝ)) = 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have harg :
          2 * Real.pi * (Nat.succ n : ℝ) =
            2 * Real.pi * (n : ℝ) + 2 * Real.pi := by
        rw [Nat.cast_succ]
        ring
      constructor
      · rw [harg, Real.sin_add, ih.1, ih.2,
            Real.sin_two_pi, Real.cos_two_pi]
        norm_num
      · rw [harg, Real.cos_add, ih.1, ih.2,
            Real.sin_two_pi, Real.cos_two_pi]
        norm_num

private theorem trig_even_phase (n : ℕ) :
    Real.sin (2 * Real.pi * (n : ℝ) + 2 * Real.pi) = 0 ∧
      Real.cos (2 * Real.pi * (n : ℝ) + 2 * Real.pi) = 1 := by
  have h := trig_two_pi_nat n
  constructor
  · rw [Real.sin_add, h.1, h.2, Real.sin_two_pi, Real.cos_two_pi]
    norm_num
  · rw [Real.cos_add, h.1, h.2, Real.sin_two_pi, Real.cos_two_pi]
    norm_num

private theorem trig_odd_phase (n : ℕ) :
    Real.sin (2 * Real.pi * (n : ℝ) + Real.pi) = 0 ∧
      Real.cos (2 * Real.pi * (n : ℝ) + Real.pi) = -1 := by
  have h := trig_two_pi_nat n
  constructor
  · rw [Real.sin_add, h.1, h.2, Real.sin_pi, Real.cos_pi]
    norm_num
  · rw [Real.cos_add, h.1, h.2, Real.sin_pi, Real.cos_pi]
    norm_num

private theorem derivativeRatio_evenPoint (n : ℕ) :
    derivativeRatio (evenPoint n) =
      (-1 : ℝ) / Real.cos (evenPoint n) := by
  have hden :
      2 * Real.pi * (n : ℝ) + 2 * Real.pi ≠ 0 := by positivity
  have hrecip :
      1 / (1 / (2 * Real.pi * (n : ℝ) + 2 * Real.pi)) =
        2 * Real.pi * (n : ℝ) + 2 * Real.pi := by
    field_simp [hden]
  unfold derivativeRatio evenPoint
  rw [hrecip, (trig_even_phase n).1, (trig_even_phase n).2]
  ring

private theorem derivativeRatio_oddPoint (n : ℕ) :
    derivativeRatio (oddPoint n) =
      (1 : ℝ) / Real.cos (oddPoint n) := by
  have hden :
      2 * Real.pi * (n : ℝ) + Real.pi ≠ 0 := by positivity
  have hrecip :
      1 / (1 / (2 * Real.pi * (n : ℝ) + Real.pi)) =
        2 * Real.pi * (n : ℝ) + Real.pi := by
    field_simp [hden]
  unfold derivativeRatio oddPoint
  rw [hrecip, (trig_odd_phase n).1, (trig_odd_phase n).2]
  ring

theorem gap1 (x : ℝ) (hx : x ≠ 0) (hcos : Real.cos x ≠ 0) :
    deriv numerator x / deriv denominator x = derivativeRatio x := by
  have hrecip :
      HasDerivAt (fun y : ℝ => 1 / y) (-1 / x ^ 2) x := by
    simpa [one_div, pow_two] using (hasDerivAt_id x).inv hx
  have hsin :
      HasDerivAt (fun y : ℝ => Real.sin (1 / y))
        (Real.cos (1 / x) * (-1 / x ^ 2)) x :=
    (Real.hasDerivAt_sin (1 / x)).comp x hrecip
  have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;> simp <;> ring
  have hnum :
      HasDerivAt numerator
        (2 * x * Real.sin (1 / x) - Real.cos (1 / x)) x := by
    unfold numerator
    convert hpow.mul hsin using 1 <;>
      simp <;> field_simp [hx] <;> ring
  have hden : deriv denominator x = Real.cos x := by
    unfold denominator
    exact (Real.hasDerivAt_sin x).deriv
  unfold derivativeRatio
  rw [hnum.deriv, hden]

theorem gap2 :
    ¬ ∃ L : ℝ, Tendsto derivativeRatio puncturedZero (nhds L) := by
  rintro ⟨L, hL⟩
  have hLeven :
      Tendsto (fun n : ℕ => derivativeRatio (evenPoint n)) atTop (nhds L) :=
    hL.comp evenPoint_tendsto_punctured
  have hLodd :
      Tendsto (fun n : ℕ => derivativeRatio (oddPoint n)) atTop (nhds L) :=
    hL.comp oddPoint_tendsto_punctured
  have hcosEven :
      Tendsto (fun n : ℕ => Real.cos (evenPoint n)) atTop (nhds 1) := by
    have hcos0 :
        Tendsto Real.cos (nhds 0) (nhds (Real.cos 0)) :=
      Real.continuous_cos.continuousAt
    simpa using hcos0.comp evenPoint_tendsto_zero
  have hcosOdd :
      Tendsto (fun n : ℕ => Real.cos (oddPoint n)) atTop (nhds 1) := by
    have hcos0 :
        Tendsto Real.cos (nhds 0) (nhds (Real.cos 0)) :=
      Real.continuous_cos.continuousAt
    simpa using hcos0.comp oddPoint_tendsto_zero
  have hEvenQuot :
      Tendsto (fun n : ℕ => (-1 : ℝ) / Real.cos (evenPoint n))
        atTop (nhds (-1)) := by
    have hconst :
        Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (nhds (-1)) :=
      tendsto_const_nhds
    have hinv := hcosEven.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa [div_eq_mul_inv] using hconst.mul hinv
  have hOddQuot :
      Tendsto (fun n : ℕ => (1 : ℝ) / Real.cos (oddPoint n))
        atTop (nhds 1) := by
    have hconst :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hinv := hcosOdd.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa [div_eq_mul_inv] using hconst.mul hinv
  have hEven :
      Tendsto (fun n : ℕ => derivativeRatio (evenPoint n))
        atTop (nhds (-1)) := by
    apply hEvenQuot.congr'
    exact Filter.Eventually.of_forall fun n =>
      (derivativeRatio_evenPoint n).symm
  have hOdd :
      Tendsto (fun n : ℕ => derivativeRatio (oddPoint n))
        atTop (nhds 1) := by
    apply hOddQuot.congr'
    exact Filter.Eventually.of_forall fun n =>
      (derivativeRatio_oddPoint n).symm
  have hm : L = -1 := tendsto_nhds_unique hLeven hEven
  have hp : L = 1 := tendsto_nhds_unique hLodd hOdd
  linarith

theorem gap3 (x : ℝ) :
    numerator x / denominator x = normalizedProduct x := by
  unfold numerator denominator normalizedProduct
  ring

theorem gap4 :
    Tendsto (fun x : ℝ => x / Real.sin x) puncturedZero (nhds 1) := by
  have hle : puncturedZero ≤ nhds 0 := by
    unfold puncturedZero nhdsWithin
    exact inf_le_left
  have hfullValue :
      Tendsto Real.sinc (nhds 0) (nhds (Real.sinc 0)) :=
    Real.continuous_sinc.continuousAt
  have hsinc0 : Real.sinc 0 = 1 := by
    simp [Real.sinc]
  rw [hsinc0] at hfullValue
  have hsinc : Tendsto Real.sinc puncturedZero (nhds 1) :=
    hfullValue.mono_left hle
  have hinv :
      Tendsto (fun x : ℝ => (Real.sinc x)⁻¹) puncturedZero (nhds 1) := by
    simpa using hsinc.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hmem :
      ∀ᶠ x : ℝ in puncturedZero, x ∈ ({0} : Set ℝ)ᶜ := by
    unfold puncturedZero
    exact self_mem_nhdsWithin
  apply hinv.congr'
  filter_upwards [hmem] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  simp [Real.sinc, hx0]

theorem gap5 :
    Tendsto (fun x : ℝ => x * Real.sin (1 / x)) puncturedZero (nhds 0) := by
  have hle : puncturedZero ≤ nhds 0 := by
    unfold puncturedZero nhdsWithin
    exact inf_le_left
  have hidFull :
      Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0) := tendsto_id
  have hid :
      Tendsto (fun x : ℝ => x) puncturedZero (nhds 0) :=
    hidFull.mono_left hle
  have habs :
      Tendsto (fun x : ℝ => |x|) puncturedZero (nhds 0) := by
    simpa using hid.abs
  have hneg :
      Tendsto (fun x : ℝ => -|x|) puncturedZero (nhds 0) := by
    simpa using habs.neg
  have hbound : ∀ x : ℝ, |x * Real.sin (1 / x)| ≤ |x| := by
    intro x
    calc
      |x * Real.sin (1 / x)| = |x| * |Real.sin (1 / x)| := abs_mul _ _
      _ ≤ |x| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (1 / x)) (abs_nonneg x)
      _ = |x| := mul_one _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg habs ?_ ?_
  · exact Filter.Eventually.of_forall fun x => (abs_le.mp (hbound x)).1
  · exact Filter.Eventually.of_forall fun x => (abs_le.mp (hbound x)).2

theorem gap6 :
    Tendsto (fun x : ℝ => numerator x / denominator x)
      puncturedZero (nhds 0) := by
  have hprodRaw :
      Tendsto
        (fun x : ℝ => (x / Real.sin x) * (x * Real.sin (1 / x)))
        puncturedZero (nhds (1 * 0)) :=
    gap4.mul gap5
  have hprod :
      Tendsto
        (fun x : ℝ => (x / Real.sin x) * (x * Real.sin (1 / x)))
        puncturedZero (nhds 0) := by
    simpa only [one_mul] using hprodRaw
  apply hprod.congr'
  exact Filter.Eventually.of_forall fun x => by
    simpa [normalizedProduct] using (gap3 x).symm

end

end ProofGap.Exercise1374_1
