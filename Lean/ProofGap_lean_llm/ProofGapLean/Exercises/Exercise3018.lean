import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

namespace ProofGap.Exercise3018

noncomputable section

open scoped BigOperators Topology

def unitPoint (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (x : ℂ))

def complexSeries (x : ℝ) : ℂ :=
  ∑' n : ℕ, unitPoint x ^ (n + 1) / ((n + 1 : ℕ) : ℂ)

def cosineSeries (x : ℝ) : ℝ :=
  ∑' n : ℕ, Real.cos (((n + 1 : ℕ) : ℝ) * x) / ((n + 1 : ℕ) : ℝ)

def sineSeries (x : ℝ) : ℝ :=
  ∑' n : ℕ, Real.sin (((n + 1 : ℕ) : ℝ) * x) / ((n + 1 : ℕ) : ℝ)

private theorem unitPoint_eq (x : ℝ) :
    unitPoint x =
      (Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ) := by
  unfold unitPoint
  rw [show Complex.I * (x : ℂ) = (x : ℂ) * Complex.I by ring,
    Complex.exp_ofReal_mul_I]
  ring

private theorem one_sub_unitPoint_eq (x : ℝ) :
    1 - unitPoint x =
      ((1 - Real.cos x : ℝ) : ℂ) -
        Complex.I * (Real.sin x : ℂ) := by
  rw [unitPoint_eq]
  push_cast
  ring

private theorem one_sub_cos_pos {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)) :
    0 < 1 - Real.cos x := by
  rcases hx with ⟨hx0, hx2⟩
  have hcos_ne : Real.cos x ≠ 1 := by
    intro hcos
    have hx0 :=
      (Real.cos_eq_one_iff_of_lt_of_lt
        (by linarith [Real.pi_pos]) hx2).mp hcos
    linarith
  have hcos_lt : Real.cos x < 1 :=
    lt_of_le_of_ne (Real.cos_le_one x) hcos_ne
  linarith

private theorem argument_formula
    (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)) :
    let w : ℂ :=
      ((1 - Real.cos x : ℝ) : ℂ) -
        Complex.I * (Real.sin x : ℂ)
    w.arg =
      -Real.arctan (Real.sin x / (1 - Real.cos x)) := by
  let w : ℂ :=
    ((1 - Real.cos x : ℝ) : ℂ) -
      Complex.I * (Real.sin x : ℂ)
  have hre : 0 < w.re := by
    dsimp [w]
    simpa using one_sub_cos_pos hx
  have hlo : -(Real.pi / 2) < w.arg :=
    Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hre)
  have hhi : w.arg < Real.pi / 2 :=
    Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have hatan := Real.arctan_tan hlo hhi
  rw [Complex.tan_arg] at hatan
  have hratio :
      w.im / w.re =
        -(Real.sin x / (1 - Real.cos x)) := by
    dsimp [w]
    ring
  rw [hratio, Real.arctan_neg] at hatan
  exact hatan.symm

private theorem normSq_formula
    (x : ℝ) :
    let w : ℂ :=
      ((1 - Real.cos x : ℝ) : ℂ) -
        Complex.I * (Real.sin x : ℂ)
    Complex.normSq w = 2 - 2 * Real.cos x := by
  dsimp
  rw [Complex.normSq_apply]
  norm_num [Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im]
  rw [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  change
    (1 - Real.cos x) * (1 - Real.cos x) +
      Real.sin x * Real.sin x =
        2 - 2 * Real.cos x
  nlinarith [Real.sin_sq_add_cos_sq x]

private theorem two_sub_two_cos_eq_sq (x : ℝ) :
    2 - 2 * Real.cos x = (2 * Real.sin (x / 2)) ^ 2 := by
  have hcos : Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
    calc
      Real.cos x = Real.cos (2 * (x / 2)) := by
        congr 1 <;> ring
      _ = 2 * Real.cos (x / 2) ^ 2 - 1 := Real.cos_two_mul _
  rw [hcos]
  nlinarith [Real.sin_sq_add_cos_sq (x / 2)]

private theorem one_sub_cos_eq_two_sin_sq (x : ℝ) :
    1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
  nlinarith [two_sub_two_cos_eq_sq x]

private def seriesTerm (x : ℝ) (n : ℕ) : ℂ :=
  unitPoint x ^ (n + 1) / ((n + 1 : ℕ) : ℂ)

private def realTerm (x : ℝ) (n : ℕ) : ℝ :=
  Real.cos (((n + 1 : ℕ) : ℝ) * x) / ((n + 1 : ℕ) : ℝ)

private def imagTerm (x : ℝ) (n : ℕ) : ℝ :=
  Real.sin (((n + 1 : ℕ) : ℝ) * x) / ((n + 1 : ℕ) : ℝ)

private theorem unitPoint_pow_formula (x : ℝ) (n : ℕ) :
    unitPoint x ^ n =
      (Real.cos ((n : ℝ) * x) : ℂ) +
        Complex.I * (Real.sin ((n : ℝ) * x) : ℂ) := by
  calc
    unitPoint x ^ n =
        Complex.exp ((n : ℂ) * (Complex.I * (x : ℂ))) := by
      rw [unitPoint, Complex.exp_nat_mul]
    _ = unitPoint ((n : ℝ) * x) := by
      unfold unitPoint
      congr 1
      push_cast
      ring
    _ = _ := unitPoint_eq _

private theorem unitPoint_norm (x : ℝ) :
    ‖unitPoint x‖ = 1 := by
  simpa [unitPoint] using Complex.norm_exp_I_mul_ofReal x

private theorem seriesTerm_decomposition (x : ℝ) (n : ℕ) :
    seriesTerm x n =
      (realTerm x n : ℂ) + Complex.I * (imagTerm x n : ℂ) := by
  unfold seriesTerm realTerm imagTerm
  rw [unitPoint_pow_formula]
  push_cast
  field_simp

private theorem seriesTerm_re (x : ℝ) (n : ℕ) :
    (seriesTerm x n).re = realTerm x n := by
  rw [seriesTerm_decomposition]
  simp

private theorem seriesTerm_im (x : ℝ) (n : ℕ) :
    (seriesTerm x n).im = imagTerm x n := by
  rw [seriesTerm_decomposition]
  simp

private theorem seriesTerm_norm (x : ℝ) (n : ℕ) :
    ‖seriesTerm x n‖ = 1 / (((n + 1 : ℕ) : ℝ)) := by
  unfold seriesTerm
  rw [norm_div, norm_pow, unitPoint_norm]
  rw [Complex.norm_natCast]
  norm_num

private theorem seriesTerm_not_summable (x : ℝ) :
    ¬ Summable (seriesTerm x) := by
  intro hsum
  have hnorm :
      Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ))) := by
    simpa only [seriesTerm_norm] using hsum.norm
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 1).mp
  simpa only [Nat.cast_add, Nat.cast_one] using hnorm

private def correctionTerm (x : ℝ) (n : ℕ) : ℂ :=
  unitPoint x * seriesTerm x n - seriesTerm x (n + 1)

private theorem correctionTerm_eq (x : ℝ) (n : ℕ) :
    correctionTerm x n =
      unitPoint x ^ (n + 2) /
        (((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ)) := by
  have hn1 : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hn2 : (((n + 2 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (by omega : n + 2 ≠ 0)
  unfold correctionTerm seriesTerm
  field_simp [hn1, hn2]
  push_cast
  ring

private theorem correctionTerm_norm_le (x : ℝ) (n : ℕ) :
    ‖correctionTerm x n‖ ≤
      1 / ((((n + 1 : ℕ) : ℝ)) ^ 2) := by
  rw [correctionTerm_eq, norm_div, norm_pow, unitPoint_norm]
  norm_num
  have hn1 : (↑n + 1 : ℂ) = ((n + 1 : ℕ) : ℂ) := by
    norm_num
  have hn2 : (↑n + 2 : ℂ) = ((n + 2 : ℕ) : ℂ) := by
    norm_num
  rw [hn1, hn2, Complex.norm_natCast, Complex.norm_natCast]
  have hden :
      (((n + 1 : ℕ) : ℝ)) ^ 2 ≤
        (((n + 2 : ℕ) : ℝ)) * (((n + 1 : ℕ) : ℝ)) := by
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    nlinarith
  have hinv :=
    one_div_le_one_div_of_le
      (show 0 < (((n + 1 : ℕ) : ℝ)) ^ 2 by positivity) hden
  simpa only [one_div, mul_inv, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat, mul_comm] using hinv

private theorem correctionTerm_summable (x : ℝ) :
    Summable (correctionTerm x) := by
  have hbase :
      Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift :
      Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr hbase
  exact hshift.of_norm_bounded (correctionTerm_norm_le x)

private theorem rotated_re (x : ℝ) (n : ℕ) :
    (unitPoint x * seriesTerm x n).re =
      Real.cos x * realTerm x n -
        Real.sin x * imagTerm x n := by
  rw [Complex.mul_re, seriesTerm_re, seriesTerm_im,
    unitPoint_eq]
  simp
  rw [Complex.cos_ofReal_re, Complex.sin_ofReal_re]

private theorem rotated_im (x : ℝ) (n : ℕ) :
    (unitPoint x * seriesTerm x n).im =
      Real.sin x * realTerm x n +
        Real.cos x * imagTerm x n := by
  rw [Complex.mul_im, seriesTerm_re, seriesTerm_im,
    unitPoint_eq]
  simp
  rw [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  ring

private theorem imagTerm_summable_of_realTerm_summable
    (x : ℝ) (hsin : Real.sin x ≠ 0)
    (hre : Summable (realTerm x)) :
    Summable (imagTerm x) := by
  have hshift :
      Summable (fun n : ℕ => realTerm x (n + 1)) := by
    simpa only [Nat.add_comm] using
      (summable_nat_add_iff 1).mpr hre
  have hcorrection :
      Summable (fun n : ℕ => (correctionTerm x n).re) :=
    Complex.reCLM.summable (correctionTerm_summable x)
  have hrotated :
      Summable (fun n : ℕ =>
        (unitPoint x * seriesTerm x n).re) := by
    apply (hshift.add hcorrection).congr
    intro n
    simp only [correctionTerm, Complex.sub_re, seriesTerm_re]
    ring
  have hscaled :
      Summable (fun n : ℕ => Real.sin x * imagTerm x n) := by
    apply ((hre.mul_left (Real.cos x)).sub hrotated).congr
    intro n
    rw [rotated_re]
    ring
  exact (summable_mul_left_iff hsin).mp hscaled

private theorem realTerm_summable_of_imagTerm_summable
    (x : ℝ) (hsin : Real.sin x ≠ 0)
    (him : Summable (imagTerm x)) :
    Summable (realTerm x) := by
  have hshift :
      Summable (fun n : ℕ => imagTerm x (n + 1)) := by
    simpa only [Nat.add_comm] using
      (summable_nat_add_iff 1).mpr him
  have hcorrection :
      Summable (fun n : ℕ => (correctionTerm x n).im) :=
    Complex.imCLM.summable (correctionTerm_summable x)
  have hrotated :
      Summable (fun n : ℕ =>
        (unitPoint x * seriesTerm x n).im) := by
    apply (hshift.add hcorrection).congr
    intro n
    simp only [correctionTerm, Complex.sub_im, seriesTerm_im]
    ring
  have hscaled :
      Summable (fun n : ℕ => Real.sin x * realTerm x n) := by
    apply (hrotated.sub (him.mul_left (Real.cos x))).congr
    intro n
    rw [rotated_im]
    ring
  exact (summable_mul_left_iff hsin).mp hscaled

private theorem seriesTerm_summable_of_components
    (x : ℝ) (hre : Summable (realTerm x))
    (him : Summable (imagTerm x)) :
    Summable (seriesTerm x) := by
  have hre' : Summable (fun n : ℕ => (realTerm x n : ℂ)) :=
    Complex.summable_ofReal.mpr hre
  have him' :
      Summable (fun n : ℕ => Complex.I * (imagTerm x n : ℂ)) :=
    (Complex.summable_ofReal.mpr him).mul_left Complex.I
  apply (hre'.add him').congr
  intro n
  exact (seriesTerm_decomposition x n).symm

private theorem eq_pi_of_sin_eq_zero
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (2 * Real.pi))
    (hsin : Real.sin x = 0) :
    x = Real.pi := by
  rcases hx with ⟨hx0, hx2⟩
  have hxle : x ≤ Real.pi := by
    by_contra h
    have harg0 : 0 < 2 * Real.pi - x := by linarith
    have hargpi : 2 * Real.pi - x < Real.pi := by
      have : Real.pi < x := lt_of_not_ge h
      linarith
    have hpos :=
      Real.sin_pos_of_pos_of_lt_pi harg0 hargpi
    rw [Real.sin_two_pi_sub, hsin] at hpos
    linarith
  have hxge : Real.pi ≤ x := by
    by_contra h
    have hxpi : x < Real.pi := lt_of_not_ge h
    have hpos :=
      Real.sin_pos_of_pos_of_lt_pi hx0 hxpi
    rw [hsin] at hpos
    linarith
  exact le_antisymm hxle hxge

private theorem abs_realTerm_pi (n : ℕ) :
    |realTerm Real.pi n| =
      1 / (((n + 1 : ℕ) : ℝ)) := by
  unfold realTerm
  rw [abs_div, Real.cos_nat_mul_pi, abs_pow, abs_neg,
    abs_one, one_pow]
  rw [abs_of_pos]
  positivity

private theorem realTerm_pi_not_summable :
    ¬ Summable (realTerm Real.pi) := by
  intro hsum
  have habs : Summable (fun n : ℕ => |realTerm Real.pi n|) := by
    simpa only [Real.norm_eq_abs] using hsum.norm
  have hshift :
      Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ))) :=
    habs.congr abs_realTerm_pi
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 1).mp
  simpa only [Nat.cast_add, Nat.cast_one] using hshift

private theorem realTerm_not_summable
    (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)) :
    ¬ Summable (realTerm x) := by
  intro hre
  by_cases hsin : Real.sin x = 0
  · have hxpi := eq_pi_of_sin_eq_zero hx hsin
    subst x
    exact realTerm_pi_not_summable hre
  · have him :=
      imagTerm_summable_of_realTerm_summable x hsin hre
    exact seriesTerm_not_summable x
      (seriesTerm_summable_of_components x hre him)

private theorem tsum_imagTerm_eq_zero
    (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)) :
    ∑' n : ℕ, imagTerm x n = 0 := by
  by_cases him : Summable (imagTerm x)
  · have hsin : Real.sin x = 0 := by
      by_contra hsin
      have hre :=
        realTerm_summable_of_imagTerm_summable x hsin him
      exact seriesTerm_not_summable x
        (seriesTerm_summable_of_components x hre him)
    have hxpi := eq_pi_of_sin_eq_zero hx hsin
    subst x
    have hzero : imagTerm Real.pi = fun _ => 0 := by
      funext n
      unfold imagTerm
      rw [Real.sin_nat_mul_pi]
      simp
    rw [hzero]
    simp
  · exact tsum_eq_zero_of_not_summable him

theorem gap1 (z : ℂ) (hz : ‖z‖ < 1) :
    (∑' n : ℕ, z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) =
      Complex.log (1 / (1 - z)) := by
  have htail :=
    (hasSum_nat_add_iff' 1).mpr
      (Complex.hasSum_taylorSeries_neg_log hz)
  have hsum :
      HasSum (fun n : ℕ => z ^ (n + 1) / ((n + 1 : ℕ) : ℂ))
        (-Complex.log (1 - z)) := by
    simpa using htail
  have hslit : 1 - z ∈ Complex.slitPlane := by
    simpa [sub_eq_add_neg] using
      (Complex.mem_slitPlane_of_norm_lt_one
        (z := -z) (by simpa using hz))
  rw [one_div, Complex.log_inv _
    (Complex.slitPlane_arg_ne_pi hslit)]
  exact hsum.tsum_eq

theorem gap2 (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)) :
    Complex.log (1 / (1 - unitPoint x)) =
      -Complex.log
        ((1 - Real.cos x : ℝ) - Complex.I * (Real.sin x : ℂ)) := by
  let w : ℂ :=
    ((1 - Real.cos x : ℝ) : ℂ) -
      Complex.I * (Real.sin x : ℂ)
  have hre : 0 < w.re := by
    dsimp [w]
    simpa using one_sub_cos_pos hx
  have harg : w.arg ≠ Real.pi := by
    intro h
    have hneg := (Complex.arg_eq_pi_iff.mp h).1
    linarith
  rw [one_sub_unitPoint_eq]
  change Complex.log (1 / w) = -Complex.log w
  rw [one_div, Complex.log_inv w harg]

theorem gap3 (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)) :
    -Complex.log
        ((1 - Real.cos x : ℝ) - Complex.I * (Real.sin x : ℂ)) =
      (-(1 / 2 : ℝ) * Real.log (2 - 2 * Real.cos x) : ℝ) +
        Complex.I * (Real.arctan (Real.sin x / (1 - Real.cos x)) : ℂ) := by
  let w : ℂ :=
    ((1 - Real.cos x : ℝ) : ℂ) -
      Complex.I * (Real.sin x : ℂ)
  have hrad : 0 ≤ 2 - 2 * Real.cos x := by
    linarith [Real.cos_le_one x]
  have hlognorm :
      Real.log ‖w‖ = Real.log (2 - 2 * Real.cos x) / 2 := by
    rw [Complex.norm_def, normSq_formula x, Real.log_sqrt hrad]
  have harg := argument_formula x hx
  dsimp at harg
  change -Complex.log w = _
  apply Complex.ext
  · simp [Complex.log_re, hlognorm]
    ring
  · simp only [Complex.neg_im, Complex.log_im, Complex.add_im,
      Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_mul, one_mul,
      zero_add]
    change w.arg =
      -Real.arctan (Real.sin x / (1 - Real.cos x)) at harg
    rw [harg]
    ring

theorem gap4 (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)) :
    Complex.log (1 / (1 - unitPoint x)) =
      (-(1 / 2 : ℝ) * Real.log (2 - 2 * Real.cos x) : ℝ) +
        Complex.I * (Real.arctan (Real.sin x / (1 - Real.cos x)) : ℂ) := by
  exact (gap2 x hx).trans (gap3 x hx)

theorem gap5 (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)) :
    Complex.log (1 / (1 - unitPoint x)) =
      (-Real.log |2 * Real.sin (x / 2)| : ℝ) +
        Complex.I * (Real.arctan (Real.sin x / (1 - Real.cos x)) : ℂ) := by
  rcases hx with ⟨hx0, hx2⟩
  have hhalf0 : 0 < x / 2 := by linarith
  have hhalfpi : x / 2 < Real.pi := by linarith
  have hsin : 0 < Real.sin (x / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hhalf0 hhalfpi
  rw [gap4 x ⟨hx0, hx2⟩]
  rw [two_sub_two_cos_eq_sq, Real.log_pow]
  rw [abs_of_pos (by positivity : 0 < 2 * Real.sin (x / 2))]
  norm_num
  ring

private theorem seriesTerm_hasSum_conditional
    (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)) :
    HasSum (seriesTerm x)
      (Complex.log (1 / (1 - unitPoint x)))
      (SummationFilter.conditional ℕ) := by
  have hu_ne_one : unitPoint x ≠ 1 := by
    intro hu
    have hwzero :
        ((1 - Real.cos x : ℝ) : ℂ) -
            Complex.I * (Real.sin x : ℂ) = 0 := by
      rw [← one_sub_unitPoint_eq x, hu]
      norm_num
    have hre := congrArg Complex.re hwzero
    norm_num [Complex.sub_re, Complex.mul_re] at hre
    rw [Complex.cos_ofReal_re] at hre
    linarith [one_sub_cos_pos hx]
  have hpartial_bounded : ∀ n : ℕ,
      ‖∑ i ∈ Finset.range n, unitPoint x ^ (i + 1)‖ ≤
        2 / ‖unitPoint x - 1‖ := by
    intro n
    have hfactor :
        (∑ i ∈ Finset.range n, unitPoint x ^ (i + 1)) =
          unitPoint x * ∑ i ∈ Finset.range n, unitPoint x ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_succ']
    rw [hfactor, norm_mul, unitPoint_norm, one_mul,
      geom_sum_eq hu_ne_one n, norm_div]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    calc
      ‖unitPoint x ^ n - 1‖ ≤
          ‖unitPoint x ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, unitPoint_norm]; norm_num
  let coeff : ℕ → ℝ := fun n => 1 / ((n + 1 : ℕ) : ℝ)
  have hcoeff_anti : Antitone coeff := by
    apply antitone_nat_of_succ_le
    intro n
    dsimp [coeff]
    apply one_div_le_one_div_of_le
    · positivity
    · norm_num
  have hcoeff_zero : Tendsto coeff atTop (𝓝 0) := by
    simpa only [coeff, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hcauchy_raw :=
    hcoeff_anti.cauchySeq_series_mul_of_tendsto_zero_of_bounded
      hcoeff_zero hpartial_bounded
  have hcauchy :
      CauchySeq (fun n => ∑ i ∈ Finset.range n, seriesTerm x i) := by
    convert hcauchy_raw using 1
    funext n
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [coeff, seriesTerm]
    change unitPoint x ^ (i + 1) / ((i + 1 : ℕ) : ℂ) =
      ((1 / ((i + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
        unitPoint x ^ (i + 1)
    push_cast
    ring
  obtain ⟨l, hsum⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hab := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hsum
  rw [Filter.tendsto_map'_iff] at hab
  change Tendsto
    (fun r : ℝ => ∑' n, seriesTerm x n * (r : ℂ) ^ n)
    (𝓝[<] (1 : ℝ)) (𝓝 l) at hab
  have hslit : 1 - unitPoint x ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    rw [one_sub_unitPoint_eq]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul,
      one_mul, sub_zero]
    exact one_sub_cos_pos hx
  have hboundary_log :
      Complex.log (1 / (1 - unitPoint x)) =
        -Complex.log (1 - unitPoint x) := by
    rw [one_div, Complex.log_inv _
      (Complex.slitPlane_arg_ne_pi hslit)]
  replace hab : Tendsto
      (fun r : ℝ =>
        (r : ℂ)⁻¹ * (-Complex.log (1 - (r : ℂ) * unitPoint x)))
      (𝓝[<] (1 : ℝ)) (𝓝 l) := by
    apply hab.congr'
    rw [eventuallyEq_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
    intro r hr_dist hr_lt
    rw [Real.dist_eq, abs_sub_lt_iff] at hr_dist
    have hr_pos : 0 < r := by linarith
    have hz : ‖(r : ℂ) * unitPoint x‖ < 1 := by
      rw [norm_mul, Complex.norm_real, unitPoint_norm, mul_one]
      simpa [Real.norm_eq_abs, abs_of_pos hr_pos] using hr_lt
    have hrseries :
        (∑' n : ℕ,
          ((r : ℂ) * unitPoint x) ^ (n + 1) /
            ((n + 1 : ℕ) : ℂ)) =
          -Complex.log (1 - (r : ℂ) * unitPoint x) := by
      calc
        _ = Complex.log
              (1 / (1 - (r : ℂ) * unitPoint x)) :=
          gap1 ((r : ℂ) * unitPoint x) hz
        _ = _ := by
          have hradial_slit :
              1 - (r : ℂ) * unitPoint x ∈ Complex.slitPlane := by
            simpa [sub_eq_add_neg] using
              (Complex.mem_slitPlane_of_norm_lt_one
                (z := -((r : ℂ) * unitPoint x)) (by simpa using hz))
          rw [one_div, Complex.log_inv _
            (Complex.slitPlane_arg_ne_pi hradial_slit)]
    rw [← hrseries, ← tsum_mul_left]
    apply tsum_congr
    intro n
    unfold seriesTerm
    rw [mul_pow, pow_succ']
    have hr_ne : (r : ℂ) ≠ 0 := by exact_mod_cast hr_pos.ne'
    have hn_ne : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    field_simp [hr_ne, hn_ne]
    ring
  have hinner : ContinuousAt
      (fun r : ℝ => 1 - (r : ℂ) * unitPoint x) 1 := by
    fun_prop
  have hlog : Tendsto
      (fun r : ℝ => Complex.log (1 - (r : ℂ) * unitPoint x))
      (𝓝 1) (𝓝 (Complex.log (1 - unitPoint x))) := by
    have := hinner.clog (by simpa using hslit)
    simpa using this.tendsto
  have hinv : Tendsto (fun r : ℝ => (r : ℂ)⁻¹)
      (𝓝 1) (𝓝 (1 : ℂ)) := by
    have hof : Tendsto (fun r : ℝ => (r : ℂ))
        (𝓝 1) (𝓝 (1 : ℂ)) :=
      Complex.ofRealCLM.continuous.tendsto 1
    simpa using hof.inv₀ (by norm_num : (1 : ℂ) ≠ 0)
  have hradial_limit : Tendsto
      (fun r : ℝ =>
        (r : ℂ)⁻¹ * (-Complex.log (1 - (r : ℂ) * unitPoint x)))
      (𝓝[<] (1 : ℝ))
      (𝓝 (-Complex.log (1 - unitPoint x))) := by
    have hfull := hinv.mul hlog.neg
    simpa using hfull.mono_left inf_le_left
  have hl : l = -Complex.log (1 - unitPoint x) :=
    tendsto_nhds_unique hab hradial_limit
  rw [hl, ← hboundary_log] at hsum
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    Filter.tendsto_map'_iff]
  simpa [Function.comp_def] using hsum

theorem gap6 (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)) :
    complexSeries x =
      (cosineSeries x : ℂ) + Complex.I * (sineSeries x : ℂ) := by
  unfold complexSeries cosineSeries sineSeries
  have hcomplex :
      (∑' n : ℕ,
        unitPoint x ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) = 0 := by
    change ∑' n : ℕ, seriesTerm x n = 0
    exact tsum_eq_zero_of_not_summable
      (seriesTerm_not_summable x)
  have hreal :
      (∑' n : ℕ,
        Real.cos (((n + 1 : ℕ) : ℝ) * x) /
          ((n + 1 : ℕ) : ℝ)) = 0 := by
    change ∑' n : ℕ, realTerm x n = 0
    exact tsum_eq_zero_of_not_summable
      (realTerm_not_summable x hx)
  have himag :
      (∑' n : ℕ,
        Real.sin (((n + 1 : ℕ) : ℝ) * x) /
          ((n + 1 : ℕ) : ℝ)) = 0 := by
    change ∑' n : ℕ, imagTerm x n = 0
    exact tsum_imagTerm_eq_zero x hx
  rw [hcomplex, hreal, himag]
  norm_num

theorem gap7 (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)) :
    ProofGap.SeriesHasSum (realTerm x)
      (-Real.log |2 * Real.sin (x / 2)|) := by
  unfold ProofGap.SeriesHasSum
  have h := Complex.hasSum_re (seriesTerm_hasSum_conditional x hx)
  rw [gap5 x hx] at h
  simpa only [seriesTerm_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
    zero_mul, one_mul, sub_zero, zero_add, add_zero] using h

theorem gap8 (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)) :
    ProofGap.SeriesHasSum (imagTerm x)
      (Real.arctan (Real.sin x / (1 - Real.cos x))) := by
  unfold ProofGap.SeriesHasSum
  have h := Complex.hasSum_im (seriesTerm_hasSum_conditional x hx)
  rw [gap5 x hx] at h
  simpa only [seriesTerm_im, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    zero_mul, one_mul, zero_add] using h

theorem gap9 (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)) :
    Real.arctan (Real.sin x / (1 - Real.cos x)) =
      Real.arctan (Real.cot (x / 2)) := by
  rcases hx with ⟨hx0, hx2⟩
  have hhalf0 : 0 < x / 2 := by linarith
  have hhalfpi : x / 2 < Real.pi := by linarith
  have hsin : Real.sin (x / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hhalf0 hhalfpi).ne'
  congr 1
  rw [Real.cot_eq_cos_div_sin]
  rw [show Real.sin x = 2 * Real.sin (x / 2) *
      Real.cos (x / 2) by
    nth_rw 1 [show x = 2 * (x / 2) by ring]
    rw [Real.sin_two_mul]]
  rw [one_sub_cos_eq_two_sin_sq]
  field_simp [hsin]

theorem gap10 (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)) :
    Real.arctan (Real.cot (x / 2)) =
      Real.arctan (Real.tan ((Real.pi - x) / 2)) := by
  rw [show (Real.pi - x) / 2 =
      Real.pi / 2 - x / 2 by ring,
    Real.tan_pi_div_two_sub, Real.tan_eq_sin_div_cos,
    inv_div, Real.cot_eq_cos_div_sin]

theorem gap11 (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)) :
    Real.arctan (Real.tan ((Real.pi - x) / 2)) =
      (Real.pi - x) / 2 := by
  rcases hx with ⟨hx0, hx2⟩
  apply Real.arctan_tan <;> linarith

theorem gap12 (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)) :
    ProofGap.SeriesHasSum (imagTerm x) ((Real.pi - x) / 2) := by
  have h := gap8 x hx
  rw [gap9 x hx, gap10 x hx, gap11 x hx] at h
  exact h

end

end ProofGap.Exercise3018
