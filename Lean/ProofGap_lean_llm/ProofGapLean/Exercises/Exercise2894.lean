import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2894

noncomputable section

open scoped BigOperators

def sec (x : ℝ) : ℝ :=
  1 / Real.cos x

def E (n : ℕ) : ℝ :=
  iteratedDeriv (2 * n) sec 0

def secantTerm (x : ℝ) (n : ℕ) : ℝ :=
  E n * x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)

def cosineTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)

def A (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (-1 : ℝ) ^ k * E (n - k) /
      ((Nat.factorial (2 * k) : ℝ) *
        (Nat.factorial (2 * (n - k)) : ℝ))

def convolutionTerm (x : ℝ) (n : ℕ) : ℝ :=
  A n * x ^ (2 * n)

private def secComplex (z : ℂ) : ℂ := (Complex.cos z)⁻¹

private def secReal (x : ℝ) : ℝ := (secComplex x).re

private theorem secReal_eq_sec (x : ℝ) : secReal x = sec x := by
  rw [secReal, secComplex, sec]
  rw [one_div]
  rw [← Complex.ofReal_cos x, ← Complex.ofReal_inv]
  exact Complex.ofReal_re _

private theorem complex_cos_ne_zero_of_norm_lt_pi_div_two
    {z : ℂ} (hz : ‖z‖ < Real.pi / 2) :
    Complex.cos z ≠ 0 := by
  intro hzero
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hzero
  have hk0 : (2 * k + 1 : ℤ) ≠ 0 := by omega
  have hkabs : (1 : ℝ) ≤ |((2 * k + 1 : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hk0
  have hcast :
      (2 * (k : ℂ) + 1) = ((2 * k + 1 : ℤ) : ℂ) := by
    push_cast
    ring
  have hnorm :
      ‖((2 * k + 1 : ℤ) : ℂ) * (Real.pi : ℂ) / 2‖ =
        |((2 * k + 1 : ℤ) : ℝ)| * (Real.pi / 2) := by
    calc
      ‖((2 * k + 1 : ℤ) : ℂ) * (Real.pi : ℂ) / 2‖ =
          ‖((2 * k + 1 : ℤ) : ℂ)‖ * ‖(Real.pi : ℂ)‖ /
            ‖(2 : ℂ)‖ := by rw [norm_div, norm_mul]
      _ = |((2 * k + 1 : ℤ) : ℝ)| * (Real.pi / 2) := by
        rw [Complex.norm_intCast]
        simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        ring
  rw [hk, hcast, hnorm] at hz
  nlinarith [Real.pi_pos]

set_option backward.isDefEq.respectTransparency false in
private theorem secReal_hasSum_taylor
    (x : ℝ) (hx : |x| < Real.pi / 2) :
    HasSum
      (fun n : ℕ =>
        iteratedDeriv n secReal 0 / (Nat.factorial n : ℝ) * x ^ n)
      (secReal x) := by
  obtain ⟨r, hxr, hrpi⟩ := exists_between hx
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg _) hxr
  let R : NNReal := ⟨r, hr0.le⟩
  have hsubset : Metric.closedBall (0 : ℂ) R ⊆
      Metric.ball (0 : ℂ) (Real.pi / 2) := by
    intro z hz
    have hzr : ‖z‖ ≤ r := by
      simpa [R, dist_eq_norm] using hz
    have : ‖z‖ < Real.pi / 2 := lt_of_le_of_lt hzr hrpi
    simpa [dist_eq_norm] using this
  have hGdiff : DifferentiableOn ℂ secComplex
      (Metric.closedBall (0 : ℂ) R) := by
    intro z hz
    have hzpi : ‖z‖ < Real.pi / 2 := by
      have := hsubset hz
      simpa [dist_eq_norm] using this
    simpa [secComplex] using
      ((Complex.differentiable_cos z).inv
        (complex_cos_ne_zero_of_norm_lt_pi_div_two hzpi)).differentiableWithinAt
  have hR0 : (0 : NNReal) < R := hr0
  have hG := hGdiff.hasFPowerSeriesOnBall hR0
  have hGreal := hG.restrictScalars (𝕜 := ℝ)
  have hpre := hGreal.compContinuousLinearMap
    (u := Complex.ofRealCLM) (x := (0 : ℝ))
  have hraw := Complex.reCLM.comp_hasFPowerSeriesOnBall hpre
  let q : FormalMultilinearSeries ℝ ℝ ℝ :=
    Complex.reCLM.compFormalMultilinearSeries
      ((FormalMultilinearSeries.restrictScalars ℝ
        (cauchyPowerSeries secComplex 0 R)).compContinuousLinearMap
          Complex.ofRealCLM)
  have hq : HasFPowerSeriesOnBall secReal q 0 R := by
    have hc := hraw.congr (g := secReal) ?_
    · simpa [q, Complex.ofRealCLM_enorm] using hc
    · intro y hy
      rfl
  have hy : x ∈ Metric.eball (0 : ℝ) R := by
    rw [Metric.eball_coe]
    simpa [R, Real.norm_eq_abs] using hxr
  have hs := hq.hasSum hy
  have hterm : ∀ n : ℕ,
      (q n) (fun _ => x) =
        iteratedDeriv n secReal 0 / (Nat.factorial n : ℝ) * x ^ n := by
    intro n
    have hfact := hq.factorial_smul (1 : ℝ) n
    simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, nsmul_eq_mul, one_pow, one_mul] at hfact
    have hcoeff :
        q.coeff n = iteratedDeriv n secReal 0 /
          (Nat.factorial n : ℝ) := by
      apply (eq_div_iff (by positivity : (Nat.factorial n : ℝ) ≠ 0)).2
      rw [mul_comm]
      simpa [← iteratedDeriv_eq_iteratedFDeriv] using hfact
    simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, hcoeff]
    ring
  simpa using hs.congr_fun (fun n => (hterm n).symm)

private theorem sec_even : Function.Even sec := by
  intro x
  simp [sec]

private theorem iteratedDeriv_odd_sec_zero (n : ℕ) :
    iteratedDeriv (2 * n + 1) sec 0 = 0 := by
  have hfun : (fun x : ℝ => sec (-x)) = sec := funext sec_even
  have h := iteratedDeriv_comp_neg (2 * n + 1) sec (0 : ℝ)
  rw [hfun] at h
  have hsign : (-1 : ℝ) ^ (2 * n + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [hsign] at h
  have h' :
      iteratedDeriv (2 * n + 1) sec 0 =
        -iteratedDeriv (2 * n + 1) sec 0 := by
    simpa only [neg_zero, neg_smul, one_smul] using h
  linarith

private theorem secant_hasSum (x : ℝ) (hx : |x| < Real.pi / 2) :
    HasSum (secantTerm x) (sec x) := by
  have hfull := secReal_hasSum_taylor x hx
  have hfun : secReal = sec := funext secReal_eq_sec
  rw [hfun] at hfull
  let t : ℕ → ℝ := fun n =>
    iteratedDeriv n sec 0 / (Nat.factorial n : ℝ) * x ^ n
  have heven : Summable (fun n => t (2 * n)) :=
    hfull.summable.comp_injective (fun _ _ h => by omega)
  have hodd : HasSum (fun n => t (2 * n + 1)) 0 := by
    apply (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0).congr_fun
    intro n
    simp [t, iteratedDeriv_odd_sec_zero]
  have hrecombined :=
    heven.hasSum.even_add_odd hodd
  have hvalue : (∑' n, t (2 * n)) = sec x := by
    exact (hfull.unique (by simpa [t] using hrecombined)).symm
  rw [← hvalue]
  apply heven.hasSum.congr_fun
  intro n
  simp only [t, secantTerm, E]
  ring

private theorem cosine_hasSum (x : ℝ) :
    HasSum (cosineTerm x) (Real.cos x) := by
  simpa [cosineTerm] using Real.hasSum_cos x

private theorem local_gap1 :
    ∀ x : ℝ, |x| < Real.pi / 2 →
      1 = Real.cos x * (∑' s, secantTerm x s) := by
  intro x hx
  rw [(secant_hasSum x hx).tsum_eq, sec]
  have hcos : Real.cos x ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo (abs_lt.mp hx)).ne'
  field_simp

private theorem local_gap2 :
    ∀ x : ℝ, |x| < Real.pi / 2 →
      1 = (∑' k, cosineTerm x k) * (∑' s, secantTerm x s) := by
  intro x hx
  rw [(cosine_hasSum x).tsum_eq]
  exact local_gap1 x hx

private theorem convolution_inner_eq (x : ℝ) (n : ℕ) :
    (∑ kl ∈ Finset.antidiagonal n,
      cosineTerm x kl.1 * secantTerm x kl.2) =
        convolutionTerm x n := by
  calc
    (∑ kl ∈ Finset.antidiagonal n,
        cosineTerm x kl.1 * secantTerm x kl.2) =
        ∑ k ∈ Finset.range (n + 1),
          cosineTerm x k * secantTerm x (n - k) := by
      symm
      refine Finset.sum_bij (fun k _ => (k, n - k)) ?_ ?_ ?_ ?_
      · intro k hk
        simp only [Finset.mem_antidiagonal]
        have hkn := Finset.mem_range.mp hk
        omega
      · intro k₁ hk₁ k₂ hk₂ heq
        exact congrArg Prod.fst heq
      · intro kl hkl
        have hsum := Finset.mem_antidiagonal.mp hkl
        refine ⟨kl.1, ?_, ?_⟩
        · apply Finset.mem_range.mpr
          omega
        · apply Prod.ext
          · rfl
          · dsimp
            omega
      · intro k hk
        rfl
    _ = convolutionTerm x n := by
      rw [convolutionTerm, A, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := by
        exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [cosineTerm, secantTerm]
      have hpow : x ^ (2 * k) * x ^ (2 * (n - k)) = x ^ (2 * n) := by
        rw [← pow_add]
        congr 1
        omega
      calc
        (-1 : ℝ) ^ k * x ^ (2 * k) /
              (Nat.factorial (2 * k) : ℝ) *
            (E (n - k) * x ^ (2 * (n - k)) /
              (Nat.factorial (2 * (n - k)) : ℝ)) =
            ((-1 : ℝ) ^ k * E (n - k) /
              ((Nat.factorial (2 * k) : ℝ) *
                (Nat.factorial (2 * (n - k)) : ℝ))) *
              (x ^ (2 * k) * x ^ (2 * (n - k))) := by ring
        _ = ((-1 : ℝ) ^ k * E (n - k) /
              ((Nat.factorial (2 * k) : ℝ) *
                (Nat.factorial (2 * (n - k)) : ℝ))) *
              x ^ (2 * n) := by rw [hpow]

private theorem local_gap3 :
    ∀ x : ℝ, |x| < Real.pi / 2 →
      1 = ∑' n, convolutionTerm x n := by
  intro x hx
  calc
    1 = (∑' k, cosineTerm x k) * (∑' s, secantTerm x s) :=
      local_gap2 x hx
    _ = ∑' n : ℕ,
        ∑ kl ∈ Finset.antidiagonal n,
          cosineTerm x kl.1 * secantTerm x kl.2 := by
      exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
        (cosine_hasSum x).summable.norm (secant_hasSum x hx).summable.norm
    _ = ∑' n, convolutionTerm x n := by
      apply tsum_congr
      exact convolution_inner_eq x

private theorem local_gap4 :
    ∀ x : ℝ, |x| < Real.pi / 2 →
      (∑' n, convolutionTerm x n) =
        ∑' n, A n * x ^ (2 * n) := by
  intro x hx
  apply tsum_congr
  intro n
  rfl

private theorem local_gap5 :
    ∀ x : ℝ, |x| < Real.pi / 2 →
      1 = ∑' n, A n * x ^ (2 * n) := by
  intro x hx
  rw [← local_gap4 x hx]
  exact local_gap3 x hx

private theorem sum_range_even_of_odd_zero
    (f : ℕ → ℝ) (hodd : ∀ k, f (2 * k + 1) = 0) :
    ∀ n : ℕ,
      (∑ i ∈ Finset.range (2 * n + 1), f i) =
        ∑ k ∈ Finset.range (n + 1), f (2 * k) := by
  intro n
  induction n with
  | zero =>
      norm_num [Finset.sum_range_succ]
  | succ n ih =>
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega]
      rw [hodd n, add_zero, ih, Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      simp only [Nat.mul_comm]
      rw [Finset.sum_range_succ]

private theorem sec_contDiffAt (m : ℕ) :
    ContDiffAt ℝ m sec 0 := by
  have h : AnalyticAt ℝ sec 0 := by
    rw [show sec = Real.cos⁻¹ by
      funext x
      simp [sec, one_div]]
    exact Real.analyticAt_cos.inv (by norm_num : Real.cos 0 ≠ 0)
  exact h.contDiffAt

private theorem product_iteratedDeriv_sum_zero (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range (2 * n + 1),
      Nat.choose (2 * n) i *
        iteratedDeriv i Real.cos 0 *
        iteratedDeriv (2 * n - i) sec 0) = 0 := by
  have hmul :=
    iteratedDeriv_fun_mul
      (n := 2 * n) (x := (0 : ℝ))
      Real.contDiff_cos.contDiffAt (sec_contDiffAt (2 * n))
  have heq :
      (fun y : ℝ => Real.cos y * sec y) =ᶠ[nhds 0]
        (fun _ : ℝ => 1) := by
    have hne : ∀ᶠ y in nhds (0 : ℝ), Real.cos y ≠ 0 :=
      Real.continuous_cos.continuousAt.eventually_ne (by norm_num)
    filter_upwards [hne] with y hy
    simp [sec, hy]
  have hderiv :
      iteratedDeriv (2 * n) (fun y : ℝ => Real.cos y * sec y) 0 = 0 := by
    rw [heq.iteratedDeriv_eq (2 * n)]
    rw [iteratedDeriv_const, if_neg (by omega)]
  rw [hmul] at hderiv
  exact hderiv

private theorem A_eq_zero_of_pos (n : ℕ) (hn : 0 < n) :
    A n = 0 := by
  let f : ℕ → ℝ := fun i =>
    Nat.choose (2 * n) i *
      iteratedDeriv i Real.cos 0 *
      iteratedDeriv (2 * n - i) sec 0
  have hfull : (∑ i ∈ Finset.range (2 * n + 1), f i) = 0 := by
    exact product_iteratedDeriv_sum_zero n hn
  have hodd : ∀ k : ℕ, f (2 * k + 1) = 0 := by
    intro k
    have hc :
        iteratedDeriv (2 * k + 1) Real.cos 0 = 0 := by
      rw [congrFun (Real.iteratedDeriv_odd_cos k) 0]
      simp
    simp [f, hc]
  rw [sum_range_even_of_odd_zero f hodd n] at hfull
  have hscaled :
      (Nat.factorial (2 * n) : ℝ) * A n =
        ∑ k ∈ Finset.range (n + 1), f (2 * k) := by
    rw [A, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n :=
      Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hle : 2 * k ≤ 2 * n := by omega
    have hsub : 2 * n - 2 * k = 2 * (n - k) := by omega
    have hchoose :
        (Nat.choose (2 * n) (2 * k) : ℝ) *
            (Nat.factorial (2 * k) : ℝ) *
            (Nat.factorial (2 * (n - k)) : ℝ) =
          (Nat.factorial (2 * n) : ℝ) := by
      rw [← hsub]
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hle
    have hc :
        iteratedDeriv (2 * k) Real.cos 0 = (-1 : ℝ) ^ k := by
      rw [congrFun (Real.iteratedDeriv_even_cos k) 0]
      simp
    simp only [f]
    rw [hc, hsub]
    change
      (Nat.factorial (2 * n) : ℝ) *
          ((-1 : ℝ) ^ k * E (n - k) /
            ((Nat.factorial (2 * k) : ℝ) *
              (Nat.factorial (2 * (n - k)) : ℝ))) =
        (Nat.choose (2 * n) (2 * k) : ℝ) *
          (-1 : ℝ) ^ k * E (n - k)
    rw [← hchoose]
    field_simp
  rw [← hscaled] at hfull
  have hfac : (Nat.factorial (2 * n) : ℝ) ≠ 0 := by positivity
  exact (mul_eq_zero.mp hfull).resolve_left hfac

private theorem E_one_sub_E_zero : E 1 - E 0 = 0 := by
  have h := A_eq_zero_of_pos 1 (by omega)
  norm_num [A, Finset.sum_range_succ] at h ⊢
  linarith

theorem gap1 :
    ∀ x : ℝ, |x| < Real.pi / 2 →
      1 = Real.cos x * (∑' s, secantTerm x s) := by
  exact local_gap1

theorem gap2 :
    ∀ x : ℝ, |x| < Real.pi / 2 →
      1 = (∑' k, cosineTerm x k) * (∑' s, secantTerm x s) := by
  exact local_gap2

theorem gap3 :
    ∀ x : ℝ, |x| < Real.pi / 2 →
      1 = ∑' n, convolutionTerm x n := by
  exact local_gap3

theorem gap4 :
    ∀ x : ℝ, |x| < Real.pi / 2 →
      (∑' n, convolutionTerm x n) =
        ∑' n, A n * x ^ (2 * n) := by
  exact local_gap4

theorem gap5 :
    ∀ x : ℝ, |x| < Real.pi / 2 →
      1 = ∑' n, A n * x ^ (2 * n) := by
  exact local_gap5

theorem gap6 :
    A 0 = E 0 := by
  norm_num [A]

theorem gap7 :
    E 0 = 1 := by
  norm_num [E, sec]

theorem gap8 :
    A 0 = 1 := by
  norm_num [A, E, sec]

theorem gap9 :
    ∀ n : ℕ, 0 < n → A n = 0 := by
  exact A_eq_zero_of_pos

theorem gap10 :
    ∀ n : ℕ, A n =
      ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * E (n - k) /
          ((Nat.factorial (2 * k) : ℝ) *
            (Nat.factorial (2 * (n - k)) : ℝ)) := by
  intro n
  rfl

theorem gap11 :
    ∀ n : ℕ, 0 < n →
      (∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * E (n - k) /
          ((Nat.factorial (2 * k) : ℝ) *
            (Nat.factorial (2 * (n - k)) : ℝ))) = 0 := by
  exact A_eq_zero_of_pos

theorem gap12 :
    E 1 - E 0 = 0 := by
  exact E_one_sub_E_zero

theorem gap13 :
    E 1 = E 0 := by
  linarith [E_one_sub_E_zero]

theorem gap14 :
    E 0 = 1 := by
  norm_num [E, sec]

theorem gap15 :
    E 1 = 1 := by
  have h0 : E 0 = 1 := by norm_num [E, sec]
  linarith [E_one_sub_E_zero]

theorem gap16 :
    ∀ n : ℕ, 0 < n →
      (∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * E (n - k) /
          ((Nat.factorial (2 * k) : ℝ) *
            (Nat.factorial (2 * (n - k)) : ℝ))) = 0 := by
  exact A_eq_zero_of_pos

end

end ProofGap.Exercise2894
