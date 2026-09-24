import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

namespace ProofGap.Exercise2798

noncomputable section

open scoped BigOperators

def u (n : ℤ) (x : ℝ) : ℝ :=
  Real.exp (-Real.pi * (n : ℝ) ^ 2 * x)

def theta (x : ℝ) : ℝ :=
  ∑' n : ℤ, u n x

def positiveTerm (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-Real.pi * (n : ℝ) ^ 2 * x)

def derivativeMagnitude (n : ℕ) (x : ℝ) : ℝ :=
  Real.pi * (n : ℝ) ^ 2 * positiveTerm n x

def SeriesUniformlyConvergesOn
    (v : ℕ → ℝ → ℝ) (s : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (n + 1), v k x) - g x| < ε

private theorem theta_eq_re_jacobiTheta (x : ℝ) (hx : 0 < x) :
    theta x = (jacobiTheta (Complex.I * (x : ℂ))).re := by
  have him : 0 < (Complex.I * (x : ℂ)).im := by
    simpa using hx
  have hsum : Summable (fun n : ℤ =>
      Complex.exp
        (Real.pi * Complex.I * (n : ℂ) ^ 2 *
          (Complex.I * (x : ℂ)))) := by
    simpa [jacobiTheta₂_term] using
      (summable_jacobiTheta₂_term_iff (0 : ℂ)
        (Complex.I * (x : ℂ))).2 him
  unfold theta jacobiTheta
  rw [Complex.re_tsum hsum]
  apply tsum_congr
  intro n
  unfold u
  have hexponent :
      (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 *
          (Complex.I * (x : ℂ)) =
        ((-Real.pi * (n : ℝ) ^ 2 * x : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  rw [hexponent, Complex.exp_ofReal_re]

private theorem theta_contDiffOn :
    ContDiffOn ℝ ⊤ theta (Set.Ioi (0 : ℝ)) := by
  let U : Set ℂ := {z | 0 < z.im}
  have hUopen : IsOpen U := by
    exact isOpen_lt continuous_const Complex.continuous_im
  have hjdiff : DifferentiableOn ℂ jacobiTheta U := by
    intro z hz
    exact (differentiableAt_jacobiTheta hz).differentiableWithinAt
  intro x hx
  have hmap : Complex.I * (x : ℂ) ∈ U := by
    change 0 < (Complex.I * (x : ℂ)).im
    simpa using hx
  have hjat : ContDiffAt ℂ ⊤ jacobiTheta
      (Complex.I * (x : ℂ)) :=
    (hjdiff.contDiffOn hUopen).contDiffAt (hUopen.mem_nhds hmap)
  have hinner : ContDiffAt ℂ ⊤ (fun z : ℂ => Complex.I * z) (x : ℂ) :=
    (contDiff_const.mul contDiff_id).contDiffAt
  have hcomplex : ContDiffAt ℂ ⊤
      (fun z : ℂ => jacobiTheta (Complex.I * z)) (x : ℂ) := by
    simpa [Function.comp_def] using hjat.comp (x : ℂ) hinner
  have hreal : ContDiffAt ℝ ⊤
      (fun y : ℝ => (jacobiTheta (Complex.I * (y : ℂ))).re) x := by
    simpa using hcomplex.real_of_complex
  exact hreal.contDiffWithinAt.congr_of_mem
    (fun y hy => theta_eq_re_jacobiTheta y hy) hx

private theorem gaussian_eventually_lt_recip
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N,
      (Real.pi * (n : ℝ) ^ 2) ^ k *
          Real.exp (-Real.pi * (n : ℝ) ^ 2 * ε) <
        1 / ((n : ℝ) ^ 2 * ε) := by
  have ht : Filter.Tendsto
      (fun n : ℕ => Real.pi * ε * (n : ℝ) ^ 2)
      Filter.atTop Filter.atTop := by
    have hsquare : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 2)
        Filter.atTop Filter.atTop :=
      by simpa [pow_two] using
        tendsto_natCast_atTop_atTop.atTop_mul_atTop₀
          tendsto_natCast_atTop_atTop
    exact hsquare.const_mul_atTop (mul_pos Real.pi_pos hε)
  have hzero : Filter.Tendsto
      (fun n : ℕ =>
        (1 / (Real.pi * ε ^ k)) *
          ((Real.pi * ε * (n : ℝ) ^ 2) ^ (k + 1) *
            Real.exp (-(Real.pi * ε * (n : ℝ) ^ 2))))
      Filter.atTop (nhds 0) := by
    have hc : Filter.Tendsto
        (fun _ : ℕ => 1 / (Real.pi * ε ^ k)) Filter.atTop
        (nhds (1 / (Real.pi * ε ^ k))) := tendsto_const_nhds
    have hp := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (k + 1)).comp ht
    simpa [Function.comp_def] using hc.mul hp
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hzero) 1 zero_lt_one
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hnN : N ≤ n := (le_max_left N 1).trans hn
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hden : 0 < (n : ℝ) ^ 2 * ε :=
    mul_pos (sq_pos_of_pos hnpos) hε
  have hscaled :
      (1 / (Real.pi * ε ^ k)) *
          ((Real.pi * ε * (n : ℝ) ^ 2) ^ (k + 1) *
            Real.exp (-(Real.pi * ε * (n : ℝ) ^ 2))) < 1 := by
    have hnonneg : 0 ≤
        (1 / (Real.pi * ε ^ k)) *
          ((Real.pi * ε * (n : ℝ) ^ 2) ^ (k + 1) *
            Real.exp (-(Real.pi * ε * (n : ℝ) ^ 2))) := by
      positivity
    have hclose := hN n hnN
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hclose
    exact hclose
  apply (lt_div_iff₀ hden).2
  calc
    (Real.pi * (n : ℝ) ^ 2) ^ k *
          Real.exp (-Real.pi * (n : ℝ) ^ 2 * ε) *
          ((n : ℝ) ^ 2 * ε) =
        (1 / (Real.pi * ε ^ k)) *
          ((Real.pi * ε * (n : ℝ) ^ 2) ^ (k + 1) *
            Real.exp (-(Real.pi * ε * (n : ℝ) ^ 2))) := by
      simp only [pow_succ, mul_pow]
      field_simp [Real.pi_ne_zero, hε.ne']
    _ < 1 := hscaled

theorem gap1 (n : ℤ) (x : ℝ) :
    u (-n) x = u n x := by
  simp [u]

theorem gap2 :
    ∀ k : ℕ, ContDiffOn ℝ k theta (Set.Ioi (0 : ℝ)) := by
  intro k
  exact theta_contDiffOn.of_le le_top

theorem gap3 (n : ℕ) (x : ℝ) :
    0 < Real.exp (-((n : ℝ) ^ 2 * x)) := by
  exact Real.exp_pos _

theorem gap4 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) (hx : 0 < x) :
    Real.exp (-((n : ℝ) ^ 2 * x)) <
      1 / ((n : ℝ) ^ 2 * x) := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have ht : 0 < (n : ℝ) ^ 2 * x :=
    mul_pos (sq_pos_of_pos hnpos) hx
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_lt_one_div_of_lt ht
    (lt_trans (lt_add_one _) (Real.add_one_lt_exp ht.ne'))

theorem gap5 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) (hx : 0 < x) :
    0 < 1 / ((n : ℝ) ^ 2 * x) := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  exact one_div_pos.mpr (mul_pos (sq_pos_of_pos hnpos) hx)

theorem gap6 (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2 * x)) := by
  have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift : Summable (fun n : ℕ =>
      1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa using (summable_nat_add_iff 1).2 hbase
  simpa [div_eq_mul_inv, mul_comm] using hshift.mul_left (1 / x)

theorem gap7 (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => positiveTerm (n + 1) x) := by
  refine (gap6 x hx).of_norm_bounded ?_
  intro n
  unfold positiveTerm
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hnx : 0 ≤ (((n + 1 : ℕ) : ℝ) ^ 2 * x) :=
    mul_nonneg (sq_nonneg _) hx.le
  have hscale :
      (((n + 1 : ℕ) : ℝ) ^ 2 * x) ≤
        Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2 * x) := by
    have hpi : (1 : ℝ) ≤ Real.pi := by
      linarith [Real.one_le_pi_div_two]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hpi hnx
  calc
    Real.exp (-Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2) * x) ≤
        Real.exp (-(((n + 1 : ℕ) : ℝ) ^ 2 * x)) := by
      apply Real.exp_le_exp.mpr
      simpa [mul_assoc] using neg_le_neg hscale
    _ ≤ 1 / (((n + 1 : ℕ) : ℝ) ^ 2 * x) :=
      (gap4 (n + 1) x (Nat.succ_le_succ (Nat.zero_le n)) hx).le

theorem gap8 (n : ℕ) (x : ℝ) :
    HasDerivAt (positiveTerm n)
      (-Real.pi * (n : ℝ) ^ 2 * positiveTerm n x) x := by
  convert (Real.hasDerivAt_exp
      (-Real.pi * (n : ℝ) ^ 2 * x)).comp x
      ((hasDerivAt_id x).const_mul (-Real.pi * (n : ℝ) ^ 2)) using 1 <;>
    simp [positiveTerm] <;> ring

theorem gap9 (ε x : ℝ) (n : ℕ)
    (hε : 0 < ε) (hεx : ε ≤ x) (hn : 1 ≤ n) :
    0 < derivativeMagnitude n x := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  unfold derivativeMagnitude positiveTerm
  positivity

theorem gap10 (ε x : ℝ) (n : ℕ)
    (hε : 0 < ε) (hεx : ε ≤ x) (hn : 1 ≤ n) :
    derivativeMagnitude n x ≤ derivativeMagnitude n ε := by
  unfold derivativeMagnitude positiveTerm
  have hcoef : 0 ≤ Real.pi * (n : ℝ) ^ 2 :=
    mul_nonneg Real.pi_pos.le (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ hcoef
  apply Real.exp_le_exp.mpr
  simpa [mul_assoc] using neg_le_neg (mul_le_mul_of_nonneg_left hεx hcoef)

theorem gap11 (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      derivativeMagnitude n ε < 1 / ((n : ℝ) ^ 2 * ε) := by
  simpa [derivativeMagnitude, positiveTerm, pow_one, mul_assoc] using
    gaussian_eventually_lt_recip ε hε 1

theorem gap12 (ε : ℝ) (n : ℕ) (hε : 0 < ε) (hn : 1 ≤ n) :
    0 < 1 / ((n : ℝ) ^ 2 * ε) := by
  exact gap5 n ε hn hε

theorem gap13 (ε : ℝ) (hε : 0 < ε) :
    SeriesUniformlyConvergesOn
      (fun n x => derivativeMagnitude (n + 1) x)
      (Set.Ici ε)
      (fun x => ∑' n : ℕ, derivativeMagnitude (n + 1) x) := by
  have hmajor : Summable (fun n : ℕ => derivativeMagnitude (n + 1) ε) := by
    obtain ⟨N, hN⟩ := gap11 ε hε
    refine (gap6 ε hε).of_norm_bounded_eventually_nat ?_
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    have hpos : 0 < derivativeMagnitude (n + 1) ε :=
      gap9 ε ε (n + 1) hε le_rfl
        (Nat.succ_le_succ (Nat.zero_le n))
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    exact (hN (n + 1) (hn.trans (Nat.le_succ n))).le
  have huniform := tendstoUniformlyOn_tsum_nat hmajor (s := Set.Ici ε)
    (fun n x hx => by
      have hpos : 0 < derivativeMagnitude (n + 1) x :=
        gap9 ε x (n + 1) hε hx
          (Nat.succ_le_succ (Nat.zero_le n))
      rw [Real.norm_eq_abs, abs_of_pos hpos]
      exact gap10 ε x (n + 1) hε hx
        (Nat.succ_le_succ (Nat.zero_le n)))
  unfold SeriesUniformlyConvergesOn
  intro δ hδ
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((Metric.tendstoUniformlyOn_iff.1 huniform) δ hδ)
  refine ⟨N, ?_⟩
  intro n hn x hx
  have hn' : N ≤ n + 1 := hn.trans (Nat.le_succ n)
  simpa [Real.dist_eq, abs_sub_comm] using hN (n + 1) hn' x hx

theorem gap14 (ε : ℝ) (hε : 0 < ε) :
    ContDiffOn ℝ 1 theta (Set.Ici ε) := by
  exact (gap2 1).mono (fun x hx => hε.trans_le hx)

theorem gap15 :
    ContDiffOn ℝ 1 theta (Set.Ioi (0 : ℝ)) := by
  exact gap2 1

theorem gap16 :
    DifferentiableOn ℝ (deriv theta) (Set.Ioi (0 : ℝ)) := by
  have hderiv : ContDiffOn ℝ 1 (deriv theta) (Set.Ioi (0 : ℝ)) :=
    theta_contDiffOn.deriv_of_isOpen isOpen_Ioi (by simp)
  exact hderiv.differentiableOn (by simp)

theorem gap17 :
    ∀ ε > 0, ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ Set.Ici ε,
      0 < (Real.pi * (n : ℝ) ^ 2) ^ k * positiveTerm n x ∧
      (Real.pi * (n : ℝ) ^ 2) ^ k * positiveTerm n x <
        1 / ((n : ℝ) ^ 2 * ε) := by
  intro ε hε k
  obtain ⟨N, hN⟩ := gaussian_eventually_lt_recip ε hε k
  refine ⟨N, ?_⟩
  intro n hn x hx
  have hn1 : 1 ≤ n := by
    by_contra hnot
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hnot
    subst n
    have := hN 0 hn
    simp at this
    exact (not_lt_of_ge (pow_nonneg (by norm_num) k)) this
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  constructor
  · unfold positiveTerm
    positivity
  · have hexp : positiveTerm n x ≤ positiveTerm n ε := by
      unfold positiveTerm
      apply Real.exp_le_exp.mpr
      have hcoef : 0 ≤ Real.pi * (n : ℝ) ^ 2 :=
        mul_nonneg Real.pi_pos.le (sq_nonneg _)
      simpa [mul_assoc] using neg_le_neg (mul_le_mul_of_nonneg_left hx hcoef)
    calc
      (Real.pi * (n : ℝ) ^ 2) ^ k * positiveTerm n x ≤
          (Real.pi * (n : ℝ) ^ 2) ^ k * positiveTerm n ε :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ < 1 / ((n : ℝ) ^ 2 * ε) := by
        simpa [positiveTerm, mul_assoc] using hN n hn

theorem gap18 :
    ∀ k : ℕ, ContDiffOn ℝ k theta (Set.Ioi (0 : ℝ)) := by
  exact gap2

theorem gap19 (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => positiveTerm (n + 1) x) := by
  exact gap7 x hx

end

end ProofGap.Exercise2798
