import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise1385

noncomputable section

open Filter

def f (x : ℝ) : ℝ := Real.sin (Real.sin x)

def outerSeries (x : ℝ) : ℝ :=
  Real.sin x - Real.sin x ^ 3 / (Nat.factorial 3 : ℝ)

def substitutedSeries (x : ℝ) : ℝ :=
  let s := x - x ^ 3 / (Nat.factorial 3 : ℝ)
  s - s ^ 3 / (Nat.factorial 3 : ℝ)

def finalPolynomial (x : ℝ) : ℝ := x - (1 / 3 : ℝ) * x ^ 3

def AgreesToOrderAt (g p : ℝ → ℝ) (a : ℝ) (n : ℕ) : Prop :=
  Asymptotics.IsLittleO (nhds a) (fun x => g x - p x)
    (fun x => (x - a) ^ n)

private theorem sine_cubic_remainder :
    (fun x : ℝ => Real.sin x - (x - x ^ 3 / 6))
      =o[nhds 0] (fun x : ℝ => x ^ 4) := by
  have h := taylor_isLittleO_univ
    (x₀ := 0) (n := 4) Real.contDiff_sin
  convert h using 1
  · funext x
    simp [taylorWithinEval, taylorWithin, taylorCoeffWithin]
    norm_num [Finset.sum_range_succ, Real.iteratedDeriv_even_sin,
      Real.iteratedDeriv_odd_sin]
    ring
  · funext x
    ring

private theorem gap1_helper :
    AgreesToOrderAt f outerSeries 0 4 := by
  have hs : Tendsto Real.sin (nhds 0) (nhds 0) := by
    convert Real.continuous_sin.continuousAt.tendsto using 1 <;> norm_num
  have hc := sine_cubic_remainder.comp_tendsto hs
  have hsin4O := Real.isEquivalent_sin.isBigO.pow 4
  have ht := hc.trans_isBigO hsin4O
  unfold AgreesToOrderAt
  simp only [sub_zero]
  refine ht.congr' (Eventually.of_forall ?_)
    (Eventually.of_forall ?_)
  · intro x
    unfold f outerSeries
    simp [Function.comp_def]
    norm_num
  · intro x
    simp [Function.comp_def, id_eq]

private theorem gap2_helper :
    AgreesToOrderAt outerSeries substitutedSeries 0 4 := by
  let s : ℝ → ℝ := fun x => x - x ^ 3 / 6
  let q : ℝ → ℝ := fun x =>
    1 - (Real.sin x ^ 2 + Real.sin x * s x + s x ^ 2) / 6
  have hq : Tendsto q (nhds 0) (nhds 1) := by
    have hc : ContinuousAt q 0 := by
      dsimp [q, s]
      fun_prop
    convert hc.tendsto using 1 <;> norm_num [q, s]
  have hp := sine_cubic_remainder.mul_isBigO (hq.isBigO_one ℝ)
  unfold AgreesToOrderAt
  simp only [sub_zero]
  refine hp.congr' (Eventually.of_forall ?_)
    (Eventually.of_forall (fun x => by simp))
  intro x
  unfold outerSeries substitutedSeries
  dsimp [s, q]
  norm_num
  ring

private theorem gap3_helper :
    AgreesToOrderAt f substitutedSeries 0 4 := by
  have h1 := gap1_helper
  have h2 := gap2_helper
  unfold AgreesToOrderAt at h1 h2 ⊢
  have hs := h1.add h2
  refine hs.congr' (Eventually.of_forall (fun x => by ring))
    (Eventually.of_forall (fun x => rfl))

private def polynomialFactor (x : ℝ) : ℝ :=
  1 / 12 - 1 / 72 * x ^ 2 + 1 / 1296 * x ^ 4

private theorem substituted_final :
    AgreesToOrderAt substitutedSeries finalPolynomial 0 3 := by
  have hq : Tendsto polynomialFactor
      (nhds 0) (nhds (1 / 12 : ℝ)) := by
    have hc : ContinuousAt polynomialFactor 0 := by
      unfold polynomialFactor
      fun_prop
    convert hc.tendsto using 1 <;> norm_num [polynomialFactor]
  have hO := (Asymptotics.isBigO_refl
    (fun x : ℝ => x ^ 5) (nhds 0)).mul (hq.isBigO_one ℝ)
  have hO' :
      (fun x : ℝ => x ^ 5 * polynomialFactor x)
        =O[nhds 0] (fun x : ℝ => x ^ 5) := by
    simpa using hO
  have h3 := hO'.trans_isLittleO
    (Asymptotics.isLittleO_pow_pow (by norm_num : 3 < 5))
  unfold AgreesToOrderAt
  simp only [sub_zero]
  refine h3.congr' (Eventually.of_forall ?_)
    (Eventually.of_forall (fun x => rfl))
  intro x
  unfold substitutedSeries finalPolynomial polynomialFactor
  norm_num
  ring

private theorem gap4_helper :
    AgreesToOrderAt f finalPolynomial 0 3 := by
  have h1 := gap3_helper
  unfold AgreesToOrderAt at h1 ⊢
  simp only [sub_zero] at h1 ⊢
  have h13 := h1.trans
    (Asymptotics.isLittleO_pow_pow (by norm_num : 3 < 4))
  have h2 := substituted_final
  unfold AgreesToOrderAt at h2
  simp only [sub_zero] at h2
  have hs := h13.add h2
  refine hs.congr' (Eventually.of_forall (fun x => by ring))
    (Eventually.of_forall (fun x => rfl))

theorem gap1 :
    AgreesToOrderAt f outerSeries 0 4 := by
  exact gap1_helper

theorem gap2 :
    AgreesToOrderAt outerSeries substitutedSeries 0 4 := by
  exact gap2_helper

theorem gap3 :
    AgreesToOrderAt f substitutedSeries 0 4 := by
  exact gap3_helper

theorem gap4 :
    AgreesToOrderAt f finalPolynomial 0 3 := by
  exact gap4_helper

end

end ProofGap.Exercise1385
