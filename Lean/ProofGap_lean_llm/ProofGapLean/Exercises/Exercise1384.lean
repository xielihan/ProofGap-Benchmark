import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace ProofGap.Exercise1384

noncomputable section

open Filter

def f (x : ℝ) : ℝ := Real.log (Real.cos x)

def sinePowerSeries (x : ℝ) : ℝ :=
  -(1 / 2 : ℝ) *
    (Real.sin x ^ 2 + Real.sin x ^ 4 / 2 + Real.sin x ^ 6 / 3)

def sineTaylor (x : ℝ) : ℝ :=
  x - x ^ 3 / (Nat.factorial 3 : ℝ) +
    x ^ 5 / (Nat.factorial 5 : ℝ)

def substitutedSeries (x : ℝ) : ℝ :=
  -(1 / 2 : ℝ) *
    (sineTaylor x ^ 2 + sineTaylor x ^ 4 / 2 + sineTaylor x ^ 6 / 3)

def finalPolynomial (x : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * x ^ 2 - x ^ 4 / 12 - x ^ 6 / 45

def AgreesToOrderAt (g p : ℝ → ℝ) (a : ℝ) (n : ℕ) : Prop :=
  Asymptotics.IsLittleO (nhds a) (fun x => g x - p x)
    (fun x => (x - a) ^ n)

private theorem log_identity (x : ℝ)
    (hx : x ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2)) :
    Real.log (Real.cos x) =
      (1 / 2 : ℝ) * Real.log (1 - Real.sin x ^ 2) := by
  have hc : 0 < Real.cos x := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [hx.1, hx.2]
  calc
    Real.log (Real.cos x) =
        (1 / 2 : ℝ) * (2 * Real.log (Real.cos x)) := by ring
    _ = (1 / 2 : ℝ) * Real.log (Real.cos x ^ 2) := by
      rw [Real.log_pow]
      norm_num
    _ = (1 / 2 : ℝ) * Real.log (1 - Real.sin x ^ 2) := by
      rw [Real.cos_sq']

private theorem log_remainder_bigO :
    (fun u : ℝ => Real.log (1 - u) + u + u ^ 2 / 2 + u ^ 3 / 3)
      =O[nhds 0] (fun u : ℝ => u ^ 4) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨2, ?_⟩
  have he : ∀ᶠ u : ℝ in nhds 0, |u| < 1 / 2 := by
    simpa only [Real.norm_eq_abs] using
      (Metric.eventually_nhds_iff_ball.2
        ⟨(1 / 2 : ℝ), by norm_num, fun y hy => by
          simpa [Real.dist_eq] using hy⟩)
  filter_upwards [he] with u hu
  have hu1 : |u| < 1 := lt_trans hu (by norm_num)
  have hb := Real.abs_log_sub_add_sum_range_le hu1 3
  norm_num [Finset.sum_range_succ] at hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hden : 1 / 2 < 1 - |u| := by linarith
  calc
    |Real.log (1 - u) + u + u ^ 2 / 2 + u ^ 3 / 3| =
        |u + u ^ 2 / 2 + u ^ 3 / 3 + Real.log (1 - u)| := by
      congr 1
      ring
    _ ≤ |u| ^ 4 / (1 - |u|) := hb
    _ ≤ 2 * |u ^ 4| := by
      rw [abs_pow]
      have hn : 0 ≤ |u| ^ 4 := pow_nonneg (abs_nonneg u) 4
      apply (div_le_iff₀ (by linarith : 0 < 1 - |u|)).2
      nlinarith

private theorem gap2_helper :
    AgreesToOrderAt
      (fun x : ℝ => (1 / 2 : ℝ) * Real.log (1 - Real.sin x ^ 2))
      sinePowerSeries 0 6 := by
  have hu : Tendsto (fun x : ℝ => Real.sin x ^ 2)
      (nhds 0) (nhds 0) := by
    convert Real.continuous_sin.continuousAt.tendsto.pow 2 using 1 <;>
      norm_num
  have hc := log_remainder_bigO.comp_tendsto hu
  have hsinO := Real.isEquivalent_sin.isBigO
  have hsin8O := hsinO.pow 8
  have hsin8O' :
      ((fun u : ℝ => u ^ 4) ∘ fun x : ℝ => Real.sin x ^ 2)
        =O[nhds 0] (fun x : ℝ => x ^ 8) := by
    convert hsin8O using 1 <;> funext x <;>
      simp [Function.comp_def] <;> ring
  have h8little :
      (fun x : ℝ => x ^ 8) =o[nhds 0] (fun x : ℝ => x ^ 6) :=
    Asymptotics.isLittleO_pow_pow (by norm_num)
  have hrem :
      (fun x : ℝ =>
        Real.log (1 - Real.sin x ^ 2) + Real.sin x ^ 2 +
          (Real.sin x ^ 2) ^ 2 / 2 + (Real.sin x ^ 2) ^ 3 / 3)
        =o[nhds 0] (fun x : ℝ => x ^ 6) := by
    have hO8 := hc.trans hsin8O'
    have ht := hO8.trans_isLittleO h8little
    simpa [Function.comp_def] using ht
  unfold AgreesToOrderAt
  simp only [sub_zero]
  have hh := hrem.const_mul_left (1 / 2 : ℝ)
  refine hh.congr' (Eventually.of_forall ?_)
    (Eventually.of_forall (fun x => by simp))
  intro x
  unfold sinePowerSeries
  ring

private theorem sine_taylor_remainder :
    (fun x : ℝ => Real.sin x - sineTaylor x)
      =o[nhds 0] (fun x : ℝ => x ^ 6) := by
  have h := taylor_isLittleO_univ
    (x₀ := 0) (n := 6) Real.contDiff_sin
  convert h using 1
  · funext x
    unfold sineTaylor
    simp [taylorWithinEval, taylorWithin, taylorCoeffWithin]
    norm_num [Finset.sum_range_succ, Real.iteratedDeriv_even_sin,
      Real.iteratedDeriv_odd_sin]
    ring
  · funext x
    ring

private theorem sine_substitution_remainder :
    AgreesToOrderAt sinePowerSeries substitutedSeries 0 6 := by
  let q : ℝ → ℝ := fun x =>
    (Real.sin x + sineTaylor x) +
      (Real.sin x + sineTaylor x) *
        (Real.sin x ^ 2 + sineTaylor x ^ 2) / 2 +
      (Real.sin x + sineTaylor x) *
        (Real.sin x ^ 4 + Real.sin x ^ 2 * sineTaylor x ^ 2 +
          sineTaylor x ^ 4) / 3
  have hq : Tendsto q (nhds 0) (nhds 0) := by
    have hc : ContinuousAt q 0 := by
      dsimp [q, sineTaylor]
      fun_prop
    convert hc.tendsto using 1 <;> norm_num [q, sineTaylor]
  have hp := sine_taylor_remainder.mul_isBigO (hq.isBigO_one ℝ)
  have hh := hp.const_mul_left (-1 / 2 : ℝ)
  unfold AgreesToOrderAt
  simp only [sub_zero]
  refine hh.congr' (Eventually.of_forall ?_)
    (Eventually.of_forall (fun x => by simp))
  intro x
  unfold sinePowerSeries substitutedSeries
  dsimp [q]
  ring

private def polynomialRemainderFactor (x : ℝ) : ℝ :=
  17 / 144 - 5963 / 86400 * x ^ 2 + 5543 / 259200 * x ^ 4 -
    563 / 129600 * x ^ 6 + 4873 / 7776000 * x ^ 8 -
    18613 / 279936000 * x ^ 10 + 39191 / 7464960000 * x ^ 12 -
    229 / 746496000 * x ^ 14 + 29 / 2239488000 * x ^ 16 -
    7 / 18662400000 * x ^ 18 + 1 / 149299200000 * x ^ 20 -
    1 / 17915904000000 * x ^ 22

private theorem substituted_final_remainder :
    AgreesToOrderAt substitutedSeries finalPolynomial 0 6 := by
  have hq : Tendsto polynomialRemainderFactor
      (nhds 0) (nhds (17 / 144 : ℝ)) := by
    have hc : ContinuousAt polynomialRemainderFactor 0 := by
      unfold polynomialRemainderFactor
      fun_prop
    convert hc.tendsto using 1 <;>
      norm_num [polynomialRemainderFactor]
  have hO := (Asymptotics.isBigO_refl
    (fun x : ℝ => x ^ 8) (nhds 0)).mul (hq.isBigO_one ℝ)
  have hO' :
      (fun x : ℝ => x ^ 8 * polynomialRemainderFactor x)
        =O[nhds 0] (fun x : ℝ => x ^ 8) := by
    simpa using hO
  have h8 :
      (fun x : ℝ => x ^ 8 * polynomialRemainderFactor x)
        =o[nhds 0] (fun x : ℝ => x ^ 6) :=
    hO'.trans_isLittleO
      (Asymptotics.isLittleO_pow_pow (by norm_num : 6 < 8))
  unfold AgreesToOrderAt
  simp only [sub_zero]
  refine h8.congr' (Eventually.of_forall ?_)
    (Eventually.of_forall (fun x => rfl))
  intro x
  unfold substitutedSeries finalPolynomial sineTaylor
    polynomialRemainderFactor
  norm_num
  ring

private theorem gap3_helper :
    AgreesToOrderAt f sinePowerSeries 0 6 := by
  have h := gap2_helper
  unfold AgreesToOrderAt at h ⊢
  have hevent : ∀ᶠ x : ℝ in nhds 0,
      x ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2) := by
    exact isOpen_Ioo.mem_nhds
      (by constructor <;> nlinarith [Real.pi_pos])
  refine h.congr' ?_ (Eventually.of_forall (fun x => rfl))
  filter_upwards [hevent] with x hx
  change (1 / 2 : ℝ) * Real.log (1 - Real.sin x ^ 2) -
      sinePowerSeries x = f x - sinePowerSeries x
  rw [f, log_identity x hx]

private theorem gap4_helper :
    AgreesToOrderAt f substitutedSeries 0 6 := by
  have h1 := gap3_helper
  have h2 := sine_substitution_remainder
  unfold AgreesToOrderAt at h1 h2 ⊢
  have hs := h1.add h2
  refine hs.congr' (Eventually.of_forall (fun x => by ring))
    (Eventually.of_forall (fun x => rfl))

private theorem gap5_helper :
    AgreesToOrderAt f finalPolynomial 0 6 := by
  have h1 := gap4_helper
  have h2 := substituted_final_remainder
  unfold AgreesToOrderAt at h1 h2 ⊢
  have hs := h1.add h2
  refine hs.congr' (Eventually.of_forall (fun x => by ring))
    (Eventually.of_forall (fun x => rfl))

private theorem sinc_limit :
    Tendsto (fun x : ℝ => Real.sin x / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  let L : Filter ℝ := nhdsWithin 0 ({0} : Set ℝ)ᶜ
  have he :
      (fun x : ℝ => Real.sin x - x) =o[L] (fun x : ℝ => x) := by
    exact Real.isEquivalent_sin.isLittleO.mono nhdsWithin_le_nhds
  have hd := he.tendsto_div_nhds_zero
  have hs : Tendsto
      (fun x : ℝ => (Real.sin x - x) / x + 1) L (nhds 1) := by
    convert hd.add_const 1 using 1 <;> norm_num
  refine hs.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  field_simp [hx0]
  ring

theorem gap1 (x : ℝ)
    (hx : x ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2)) :
    Real.log (Real.cos x) =
      (1 / 2 : ℝ) * Real.log (1 - Real.sin x ^ 2) := by
  exact log_identity x hx

theorem gap2 :
    AgreesToOrderAt
      (fun x : ℝ => (1 / 2 : ℝ) * Real.log (1 - Real.sin x ^ 2))
      sinePowerSeries 0 6 := by
  exact gap2_helper

theorem gap3 :
    AgreesToOrderAt f sinePowerSeries 0 6 := by
  exact gap3_helper

theorem gap4 :
    AgreesToOrderAt f substitutedSeries 0 6 := by
  exact gap4_helper

theorem gap5 :
    AgreesToOrderAt f finalPolynomial 0 6 := by
  exact gap5_helper

theorem gap6 :
    Tendsto (fun x : ℝ => Real.sin x / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  exact sinc_limit

end

end ProofGap.Exercise1384
