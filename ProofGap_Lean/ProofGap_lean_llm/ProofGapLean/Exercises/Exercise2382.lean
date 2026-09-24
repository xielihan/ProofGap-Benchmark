import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise2382
noncomputable section

open Filter Set MeasureTheory
open scoped Interval

def phase (x : ℝ) : ℝ := x + 1 / x
def phaseDeriv (x : ℝ) : ℝ := 1 - 1 / x ^ 2
def integrand (n x : ℝ) : ℝ := Real.sin (phase x) / Real.rpow x n
def absIntegrand (n x : ℝ) : ℝ := |Real.sin (phase x)| / Real.rpow x n
def tailWeight (n x : ℝ) : ℝ := 1 / (Real.rpow x n * phaseDeriv x)
def ConvergesAtTopFrom (a n : ℝ) : Prop :=
  ∃ L : ℝ, Tendsto (fun A => ∫ x in a..A, integrand n x) atTop (nhds L)
def ConvergesAtZeroTo (a n : ℝ) : Prop :=
  ∃ L : ℝ,
    Tendsto (fun b => ∫ x in b..a, integrand n x)
      (nhdsWithin 0 (Ioi 0)) (nhds L)
def Converges (n : ℝ) : Prop :=
  ∃ a > 0, ConvergesAtZeroTo a n ∧ ConvergesAtTopFrom a n

private theorem phase_hasDerivAt (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt phase (phaseDeriv x) x := by
  have h := (hasDerivAt_id x).add ((hasDerivAt_id x).inv hx)
  convert h using 1
  · ext y
    simp [phase, one_div]
  · simp only [phaseDeriv, Function.id_def, one_div, pow_two]
    field_simp [hx]
    ring

private theorem phaseDeriv_pos (x : ℝ) (hx : 1 < x) :
    0 < phaseDeriv x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hx2 : 1 < x ^ 2 := by nlinarith
  unfold phaseDeriv
  rw [sub_pos, div_lt_one (sq_pos_of_pos hx0)]
  exact hx2

private theorem integrand_continuousAt (n x : ℝ) (hx : 0 < x) :
    ContinuousAt (integrand n) x := by
  have hphase : ContinuousAt phase x :=
    (phase_hasDerivAt x hx.ne').continuousAt
  have hpow : ContinuousAt (fun y : ℝ => Real.rpow y n) x :=
    continuousAt_id.rpow_const (Or.inl hx.ne')
  exact (Real.continuous_sin.continuousAt.comp hphase).div hpow
    (Real.rpow_pos_of_pos hx n).ne'

private theorem absIntegrand_continuousAt (n x : ℝ) (hx : 0 < x) :
    ContinuousAt (absIntegrand n) x := by
  have hphase : ContinuousAt phase x :=
    (phase_hasDerivAt x hx.ne').continuousAt
  have hpow : ContinuousAt (fun y : ℝ => Real.rpow y n) x :=
    continuousAt_id.rpow_const (Or.inl hx.ne')
  exact (Real.continuous_sin.continuousAt.comp hphase).abs.div hpow
    (Real.rpow_pos_of_pos hx n).ne'

private theorem one_div_hasDerivAt (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => 1 / y) (-1 / x ^ 2) x := by
  convert (hasDerivAt_id x).inv hx using 1
  ext y
  simp [one_div]

private theorem phase_one_div (x : ℝ) (hx : x ≠ 0) :
    phase (1 / x) = phase x := by
  unfold phase
  field_simp [hx]
  ring

private theorem rpow_one_div_sub_two (n x : ℝ) (hx : 0 < x) :
    Real.rpow (1 / x) (2 - n) = Real.rpow x (n - 2) := by
  simp only [Real.rpow_eq_pow, one_div]
  rw [← Real.rpow_neg_eq_inv_rpow]
  congr 1
  ring

private theorem rpow_sub_two_mul_sq (n x : ℝ) (hx : 0 < x) :
    Real.rpow x (n - 2) * x ^ 2 = Real.rpow x n := by
  calc
    Real.rpow x (n - 2) * x ^ 2 =
        Real.rpow x (n - 2) * Real.rpow x 2 := by
          congr 1
          exact (Real.rpow_two x).symm
    _ = Real.rpow x ((n - 2) + 2) := (Real.rpow_add hx _ _).symm
    _ = Real.rpow x n := by congr 1 <;> ring

private theorem reciprocal_integrand_mul_deriv (n x : ℝ) (hx : 0 < x) :
    integrand (2 - n) (1 / x) * (-1 / x ^ 2) = -integrand n x := by
  have hp := rpow_one_div_sub_two n x hx
  have hm := rpow_sub_two_mul_sq n x hx
  have hr₁ : Real.rpow x (n - 2) ≠ 0 :=
    (Real.rpow_pos_of_pos hx (n - 2)).ne'
  have hr₂ : Real.rpow x n ≠ 0 := (Real.rpow_pos_of_pos hx n).ne'
  unfold integrand
  rw [phase_one_div x hx.ne', hp]
  field_simp [hx.ne']
  rw [← hm]
  ring

private theorem reciprocal_absIntegrand_mul_deriv (n x : ℝ) (hx : 0 < x) :
    absIntegrand (2 - n) (1 / x) * (-1 / x ^ 2) = -absIntegrand n x := by
  have hp := rpow_one_div_sub_two n x hx
  have hm := rpow_sub_two_mul_sq n x hx
  have hr₁ : Real.rpow x (n - 2) ≠ 0 :=
    (Real.rpow_pos_of_pos hx (n - 2)).ne'
  have hr₂ : Real.rpow x n ≠ 0 := (Real.rpow_pos_of_pos hx n).ne'
  unfold absIntegrand
  rw [phase_one_div x hx.ne', hp]
  field_simp [hx.ne']
  rw [← hm]
  ring

private theorem integrand_intervalIntegrable_pos
    (n a b : ℝ) (ha : 0 < a) (hab : a < b) :
    IntervalIntegrable (integrand n) volume a b := by
  apply (continuousOn_of_forall_continuousAt _).intervalIntegrable
  intro x hx
  rw [uIcc_of_le hab.le] at hx
  exact integrand_continuousAt n x (ha.trans_le hx.1)

private theorem integrand_intervalIntegrable_pos_ends
    (n a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (integrand n) volume a b := by
  apply (continuousOn_of_forall_continuousAt _).intervalIntegrable
  intro x hx
  have hx0 : 0 < x := by
    rcases mem_uIcc.mp hx with hx | hx
    · exact ha.trans_le hx.1
    · exact hb.trans_le hx.1
  exact integrand_continuousAt n x hx0

private theorem absIntegrand_intervalIntegrable_pos_ends
    (n a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (absIntegrand n) volume a b := by
  apply (continuousOn_of_forall_continuousAt _).intervalIntegrable
  intro x hx
  have hx0 : 0 < x := by
    rcases mem_uIcc.mp hx with hx | hx
    · exact ha.trans_le hx.1
    · exact hb.trans_le hx.1
  exact absIntegrand_continuousAt n x hx0

private theorem not_convergesAtTopFrom_of_nonpos
    (n a : ℝ) (hn : n ≤ 0) (ha : 0 < a) :
    ¬ ConvergesAtTopFrom a n := by
  let left : ℕ → ℝ :=
    fun k => (k : ℝ) * (2 * Real.pi) + Real.pi / 6
  let right : ℕ → ℝ :=
    fun k => (k : ℝ) * (2 * Real.pi) + Real.pi / 3
  have hleft_top : Tendsto left atTop atTop := by
    have hmul : Tendsto (fun k : ℕ => (k : ℝ) * (2 * Real.pi)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const (mul_pos two_pos Real.pi_pos)
    exact tendsto_atTop_add_const_right atTop (Real.pi / 6) hmul
  have hright_top : Tendsto right atTop atTop := by
    have hmul : Tendsto (fun k : ℕ => (k : ℝ) * (2 * Real.pi)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const (mul_pos two_pos Real.pi_pos)
    exact tendsto_atTop_add_const_right atTop (Real.pi / 3) hmul
  have hblock : ∀ k : ℕ, 1 ≤ k →
      Real.pi / 12 ≤ ∫ x in left k..right k, integrand n x := by
    intro k hk
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hmulge : 2 * Real.pi ≤ (k : ℝ) * (2 * Real.pi) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hkR (mul_nonneg zero_le_two Real.pi_pos.le)
    have hleft2 : 2 < left k := by
      dsimp [left]
      nlinarith [Real.pi_gt_three]
    have hlr : left k < right k := by
      dsimp [left, right]
      linarith [Real.pi_pos]
    have hpoint : ∀ x ∈ Icc (left k) (right k), (1 / 2 : ℝ) ≤ integrand n x := by
      intro x hx
      have hx0 : 0 < x := by linarith [hleft2, hx.1]
      have hx1 : 1 ≤ x := by linarith [hleft2, hx.1]
      have hx2 : 2 < x := hleft2.trans_le hx.1
      let r : ℝ := x - (k : ℝ) * (2 * Real.pi)
      let z : ℝ := r + 1 / x
      have hrlo : Real.pi / 6 ≤ r := by
        dsimp [r, left] at *
        linarith [hx.1]
      have hrhi : r ≤ Real.pi / 3 := by
        dsimp [r, right] at *
        linarith [hx.2]
      have hinv_half : 1 / x ≤ (1 / 2 : ℝ) := by
        rw [div_le_iff₀ hx0]
        nlinarith [hx2]
      have hinv : 1 / x ≤ Real.pi / 6 := by
        linarith [Real.pi_gt_three]
      have hzlo : Real.pi / 6 ≤ z := by
        dsimp [z]
        have : 0 < 1 / x := one_div_pos.mpr hx0
        linarith
      have hzhi : z ≤ Real.pi / 2 := by
        dsimp [z]
        linarith
      have hphase : phase x = z + (k : ℝ) * (2 * Real.pi) := by
        dsimp [phase, z, r]
        ring
      have hperiod : Real.sin (phase x) = Real.sin z := by
        rw [hphase, Real.sin_add_nat_mul_two_pi]
      have hsin : (1 / 2 : ℝ) ≤ Real.sin z := by
        have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
          (x := Real.pi / 6) (y := z) (by linarith [Real.pi_pos]) hzhi hzlo
        simpa only [Real.sin_pi_div_six] using hs
      have hrpow_pos : 0 < Real.rpow x n := Real.rpow_pos_of_pos hx0 n
      have hrpow_le : Real.rpow x n ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hx1 hn
      unfold integrand
      rw [hperiod]
      apply (le_div_iff₀ hrpow_pos).2
      calc
        (1 / 2 : ℝ) * Real.rpow x n ≤ (1 / 2 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hrpow_le (by norm_num)
        _ = (1 / 2 : ℝ) := by ring
        _ ≤ Real.sin z := hsin
    have hconst : IntervalIntegrable (fun _ : ℝ => (1 / 2 : ℝ))
        volume (left k) (right k) :=
      continuous_const.intervalIntegrable _ _
    have hint : IntervalIntegrable (integrand n) volume (left k) (right k) :=
      integrand_intervalIntegrable_pos n (left k) (right k)
        (by linarith [hleft2]) hlr
    have hmono := intervalIntegral.integral_mono_on hlr.le hconst hint hpoint
    have hconst_eq :
        (∫ _x in left k..right k, (1 / 2 : ℝ)) = Real.pi / 12 := by
      rw [intervalIntegral.integral_const]
      dsimp [left, right]
      ring
    rwa [hconst_eq] at hmono
  rintro ⟨L, hconv⟩
  have hleft_lim : Tendsto
      (fun k => ∫ x in a..left k, integrand n x) atTop (nhds L) :=
    hconv.comp hleft_top
  have hright_lim : Tendsto
      (fun k => ∫ x in a..right k, integrand n x) atTop (nhds L) :=
    hconv.comp hright_top
  have hdiff : Tendsto
      (fun k => (∫ x in a..right k, integrand n x) -
        ∫ x in a..left k, integrand n x) atTop (nhds 0) := by
    simpa using hright_lim.sub hleft_lim
  have hsmall : ∀ᶠ k : ℕ in atTop,
      (∫ x in a..right k, integrand n x) -
        ∫ x in a..left k, integrand n x < Real.pi / 24 :=
    hdiff.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < Real.pi / 24))
  have hlower : ∀ᶠ k : ℕ in atTop,
      Real.pi / 12 ≤
        (∫ x in a..right k, integrand n x) -
          ∫ x in a..left k, integrand n x := by
    have haleft : ∀ᶠ k : ℕ in atTop, a < left k :=
      hleft_top.eventually (eventually_gt_atTop a)
    filter_upwards [eventually_ge_atTop (1 : ℕ), haleft] with k hk hak
    have hlr : left k < right k := by
      dsimp [left, right]
      linarith [Real.pi_pos]
    have ha_left : IntervalIntegrable (integrand n) volume a (left k) :=
      integrand_intervalIntegrable_pos n a (left k) ha hak
    have hleft_right : IntervalIntegrable (integrand n) volume (left k) (right k) :=
      integrand_intervalIntegrable_pos n (left k) (right k)
        (ha.trans hak) hlr
    have hadd :=
      intervalIntegral.integral_add_adjacent_intervals ha_left hleft_right
    calc
      Real.pi / 12 ≤ ∫ x in left k..right k, integrand n x := hblock k hk
      _ = (∫ x in a..right k, integrand n x) -
          ∫ x in a..left k, integrand n x := by linarith
  rcases (hsmall.and hlower).exists with ⟨k, hsmallk, hlowerk⟩
  linarith [Real.pi_pos]

theorem gap1 (n : ℝ) (hn : n ≤ 0) : ¬ Converges n := by
  rintro ⟨a, ha, _hzero, htop⟩
  exact not_convergesAtTopFrom_of_nonpos n a hn ha htop

theorem gap2 (n x : ℝ) (hx : 1 < x) :
    integrand n x =
      tailWeight n x * (phaseDeriv x * Real.sin (phase x)) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hp : phaseDeriv x ≠ 0 := (phaseDeriv_pos x hx).ne'
  have hr : Real.rpow x n ≠ 0 := (Real.rpow_pos_of_pos hx0 n).ne'
  unfold integrand tailWeight
  field_simp

theorem gap3 (a A : ℝ) (ha : 1 < a) (hA : a < A) :
    |∫ x in a..A, phaseDeriv x * Real.sin (phase x)| ≤ 2 := by
  have hder : ∀ x ∈ uIcc a A,
      HasDerivAt (fun y => -Real.cos (phase y))
        (phaseDeriv x * Real.sin (phase x)) x := by
    intro x hx
    rw [uIcc_of_le hA.le] at hx
    have hx0 : 0 < x := zero_lt_one.trans (ha.trans_le hx.1)
    convert (Real.hasDerivAt_cos (phase x)).neg.comp x
      (phase_hasDerivAt x hx0.ne') using 1 <;> ring
  have hcont : ContinuousOn
      (fun x => phaseDeriv x * Real.sin (phase x)) (uIcc a A) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    rw [uIcc_of_le hA.le] at hx
    have hx0 : 0 < x := zero_lt_one.trans (ha.trans_le hx.1)
    have hpd : ContinuousAt phaseDeriv x := by
      exact continuousAt_const.sub
        (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hx0.ne'))
    exact hpd.mul
      (Real.continuous_sin.continuousAt.comp
        (phase_hasDerivAt x hx0.ne').continuousAt)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hcont.intervalIntegrable]
  calc
    |(-Real.cos (phase A)) - (-Real.cos (phase a))| ≤
        |Real.cos (phase A)| + |Real.cos (phase a)| := by
          rw [show (-Real.cos (phase A)) - (-Real.cos (phase a)) =
            -(Real.cos (phase A) - Real.cos (phase a)) by ring, abs_neg]
          exact abs_sub (Real.cos (phase A)) (Real.cos (phase a))
    _ ≤ 2 := by
      linarith [Real.abs_cos_le_one (phase A), Real.abs_cos_le_one (phase a)]

theorem gap4 (n x : ℝ) (hn : 0 < n) (hx : 0 < x) :
    HasDerivAt
      (fun y => Real.rpow y n * phaseDeriv y)
      (n * Real.rpow x (n - 3) * (x ^ 2 - (n - 2) / n)) x := by
  have hr := (hasDerivAt_id x).rpow_const (p := n) (Or.inl hx.ne')
  have hr' : HasDerivAt (fun y : ℝ => Real.rpow y n)
      (n * Real.rpow x (n - 1)) x := by
    convert hr using 1
    simp only [Function.id_def, Real.rpow_eq_pow]
    ring
  have hs : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1
    norm_num
  have hi := hs.inv (pow_ne_zero 2 hx.ne')
  have hp : HasDerivAt phaseDeriv (2 / x ^ 3) x := by
    have h := (hasDerivAt_const x (1 : ℝ)).sub hi
    convert h using 1
    · ext y
      simp [phaseDeriv, one_div]
    · field_simp [hx.ne']
      ring
  have hm := hr'.mul hp
  convert hm using 1
  have hpow₁ : Real.rpow x (n - 1) =
      Real.rpow x (n - 3) * x ^ 2 := by
    calc
      Real.rpow x (n - 1) =
          Real.rpow x ((n - 3) + 2) := by congr 1 <;> ring
      _ = Real.rpow x (n - 3) * Real.rpow x 2 := Real.rpow_add hx _ _
      _ = Real.rpow x (n - 3) * x ^ 2 := by
        congr 1
        exact Real.rpow_two x
  have hpow₂ : Real.rpow x n =
      Real.rpow x (n - 3) * x ^ 3 := by
    calc
      Real.rpow x n =
          Real.rpow x ((n - 3) + 3) := by congr 1 <;> ring
      _ = Real.rpow x (n - 3) * Real.rpow x 3 := Real.rpow_add hx _ _
      _ = Real.rpow x (n - 3) * x ^ 3 := by
        congr 1
        exact Real.rpow_natCast x 3
  rw [hpow₁, hpow₂]
  unfold phaseDeriv
  field_simp [hx.ne', hn.ne']
  ring

private def tailWeightDeriv (n x : ℝ) : ℝ :=
  -(n * Real.rpow x (n - 3) * (x ^ 2 - (n - 2) / n)) /
    (Real.rpow x n * phaseDeriv x) ^ 2

private theorem tailWeight_hasDerivAt (n x : ℝ) (hn : 0 < n) (hx : 1 < x) :
    HasDerivAt (tailWeight n) (tailWeightDeriv n x) x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hg := gap4 n x hn hx0
  have hgne : Real.rpow x n * phaseDeriv x ≠ 0 :=
    mul_ne_zero (Real.rpow_pos_of_pos hx0 n).ne' (phaseDeriv_pos x hx).ne'
  have hi := hg.inv hgne
  convert hi using 1
  ext y
  simp [tailWeight, one_div]

private theorem tailWeightDeriv_nonpos (n x : ℝ) (hn : 0 < n) (hx : 2 ≤ x) :
    tailWeightDeriv n x ≤ 0 := by
  have hratio : (n - 2) / n < 1 := by
    rw [div_lt_one hn]
    linarith
  have hbracket : 0 < x ^ 2 - (n - 2) / n := by
    nlinarith
  unfold tailWeightDeriv
  exact div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr
      (mul_nonneg (mul_nonneg hn.le (Real.rpow_nonneg (by linarith) _))
        hbracket.le))
    (sq_nonneg _)

theorem gap5 (n : ℝ) (hn : 0 < n) :
    ∃ a > 1, AntitoneOn (tailWeight n) (Ici a) := by
  let g : ℝ → ℝ := fun x => Real.rpow x n * phaseDeriv x
  have hgcont : ContinuousOn g (Ici (2 : ℝ)) := by
    intro x hx
    have hx2 : (2 : ℝ) ≤ x := hx
    exact (gap4 n x hn (by linarith)).continuousAt.continuousWithinAt
  have hgdiff : DifferentiableOn ℝ g (interior (Ici (2 : ℝ))) := by
    intro x hx
    have hx2 : 2 < x := by simpa using hx
    exact (gap4 n x hn (by linarith)).differentiableAt.differentiableWithinAt
  have hgderiv : ∀ x ∈ interior (Ici (2 : ℝ)), 0 ≤ deriv g x := by
    intro x hx
    have hx2 : 2 < x := by simpa using hx
    have hratio : (n - 2) / n < 1 := by
      rw [div_lt_one hn]
      linarith
    rw [(gap4 n x hn (by linarith)).deriv]
    have hbracket : 0 < x ^ 2 - (n - 2) / n := by
      nlinarith
    exact mul_nonneg (mul_nonneg hn.le (Real.rpow_nonneg (by linarith) _))
      hbracket.le
  have hgmono : MonotoneOn g (Ici (2 : ℝ)) :=
    monotoneOn_of_deriv_nonneg (convex_Ici (2 : ℝ)) hgcont hgdiff hgderiv
  refine ⟨2, by norm_num, ?_⟩
  intro x hx y hy hxy
  have hx2 : (2 : ℝ) ≤ x := hx
  have hy2 : (2 : ℝ) ≤ y := hy
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hgx : 0 < g x :=
    mul_pos (Real.rpow_pos_of_pos hx0 n) (phaseDeriv_pos x hx1)
  have hxyg : g x ≤ g y := hgmono hx hy hxy
  unfold tailWeight
  exact one_div_le_one_div_of_le hgx hxyg

theorem gap6 (n : ℝ) (hn : 0 < n) :
    Tendsto (tailWeight n) atTop (nhds 0) := by
  have hp : Tendsto (fun x : ℝ => Real.rpow x (-n)) atTop (nhds 0) := by
    simpa only [Real.rpow_eq_pow] using tendsto_rpow_neg_atTop hn
  have hi : Tendsto (fun x : ℝ => 1 / x ^ 2) atTop (nhds 0) := by
    convert (tendsto_inv_atTop_zero.pow 2 :
      Tendsto (fun x : ℝ => x⁻¹ ^ 2) atTop (nhds (0 ^ 2))) using 1 <;>
      norm_num [one_div, inv_pow]
  have hpd : Tendsto phaseDeriv atTop (nhds 1) := by
    simpa only [phaseDeriv, sub_zero] using tendsto_const_nhds.sub hi
  have hlim : Tendsto
      (fun x : ℝ => Real.rpow x (-n) / phaseDeriv x) atTop (nhds 0) := by
    simpa using hp.div hpd one_ne_zero
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hr : Real.rpow x n ≠ 0 := (Real.rpow_pos_of_pos hx0 n).ne'
  have hd : phaseDeriv x ≠ 0 := (phaseDeriv_pos x hx).ne'
  unfold tailWeight
  rw [Real.rpow_eq_pow]
  rw [Real.rpow_neg hx0.le]
  field_simp
  exact Real.rpow_eq_pow x n

theorem gap7 (n : ℝ) (hn : 0 < n) :
    ∃ a > 1, ConvergesAtTopFrom a n := by
  let v : ℝ → ℝ := fun x => -Real.cos (phase x)
  let v' : ℝ → ℝ := fun x => phaseDeriv x * Real.sin (phase x)
  have hu_deriv : ∀ x ∈ Ici (2 : ℝ),
      HasDerivAt (tailWeight n) (tailWeightDeriv n x) x := by
    intro x hx
    exact tailWeight_hasDerivAt n x hn (by
      have hx2 : (2 : ℝ) ≤ x := hx
      linarith)
  have hu'_nonpos : ∀ x ∈ Ioi (2 : ℝ), tailWeightDeriv n x ≤ 0 := by
    intro x hx
    exact tailWeightDeriv_nonpos n x hn hx.le
  have hu'int : IntegrableOn (tailWeightDeriv n) (Ioi (2 : ℝ)) :=
    integrableOn_Ioi_deriv_of_nonpos' hu_deriv hu'_nonpos (gap6 n hn)
  have hv_meas : AEStronglyMeasurable v (volume.restrict (Ioi (2 : ℝ))) := by
    apply Measurable.aestronglyMeasurable
    dsimp [v, phase]
    measurability
  have hv_bound : ∀ᵐ x ∂(volume.restrict (Ioi (2 : ℝ))), ‖v x‖ ≤ 1 := by
    filter_upwards [] with x
    simpa [v, Real.norm_eq_abs] using Real.abs_cos_le_one (phase x)
  have huv_int : IntegrableOn (fun x => tailWeightDeriv n x * v x) (Ioi (2 : ℝ)) :=
    hu'int.mul_bdd hv_meas hv_bound
  have htail :
      Tendsto (fun A => ∫ x in (2 : ℝ)..A, tailWeightDeriv n x * v x)
        atTop (nhds (∫ x in Ioi (2 : ℝ), tailWeightDeriv n x * v x)) :=
    intervalIntegral_tendsto_integral_Ioi 2 huv_int tendsto_id
  have hboundary : Tendsto (fun A => tailWeight n A * v A) atTop (nhds 0) := by
    apply Asymptotics.IsBigO.trans_tendsto
      (g'' := tailWeight n)
    · apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [] with A
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      have hvA : |v A| ≤ 1 := by
        simpa [v] using Real.abs_cos_le_one (phase A)
      calc
        |tailWeight n A| * |v A| ≤ |tailWeight n A| * 1 :=
          mul_le_mul_of_nonneg_left hvA (abs_nonneg _)
        _ = 1 * |tailWeight n A| := by ring
    · exact gap6 n hn
  let L : ℝ :=
    -tailWeight n 2 * v 2 -
      ∫ x in Ioi (2 : ℝ), tailWeightDeriv n x * v x
  have hformula : ∀ᶠ A : ℝ in atTop,
      (∫ x in (2 : ℝ)..A, integrand n x) =
        tailWeight n A * v A - tailWeight n 2 * v 2 -
          ∫ x in (2 : ℝ)..A, tailWeightDeriv n x * v x := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with A hA
    have hucont : ContinuousOn (tailWeight n) (uIcc (2 : ℝ) A) := by
      intro x hx
      rw [uIcc_of_le hA] at hx
      exact (tailWeight_hasDerivAt n x hn (by linarith [hx.1])).continuousAt.continuousWithinAt
    have hvcont : ContinuousOn v (uIcc (2 : ℝ) A) := by
      intro x hx
      rw [uIcc_of_le hA] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      exact ((Real.hasDerivAt_cos (phase x)).neg.comp x
        (phase_hasDerivAt x hx0.ne')).continuousAt.continuousWithinAt
    have hv_deriv : ∀ x ∈ Ioo (min (2 : ℝ) A) (max (2 : ℝ) A),
        HasDerivAt v (v' x) x := by
      intro x hx
      rw [min_eq_left hA, max_eq_right hA] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      convert (Real.hasDerivAt_cos (phase x)).neg.comp x
        (phase_hasDerivAt x hx0.ne') using 1 <;> ring
    have hu_deriv' : ∀ x ∈ Ioo (min (2 : ℝ) A) (max (2 : ℝ) A),
        HasDerivAt (tailWeight n) (tailWeightDeriv n x) x := by
      intro x hx
      rw [min_eq_left hA, max_eq_right hA] at hx
      exact tailWeight_hasDerivAt n x hn (by linarith [hx.1])
    have hu'intv : IntervalIntegrable (tailWeightDeriv n) volume (2 : ℝ) A := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hA]
      exact hu'int.mono_set (Ioo_subset_Ioi_self)
    have hv'cont : ContinuousOn v' (uIcc (2 : ℝ) A) := by
      apply continuousOn_of_forall_continuousAt
      intro x hx
      rw [uIcc_of_le hA] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      have hpd : ContinuousAt phaseDeriv x := by
        exact continuousAt_const.sub
          (continuousAt_const.div (continuousAt_id.pow 2)
            (pow_ne_zero 2 hx0.ne'))
      exact hpd.mul
        (Real.continuous_sin.continuousAt.comp
          (phase_hasDerivAt x hx0.ne').continuousAt)
    have hip :=
      intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
        hucont hvcont hu_deriv' hv_deriv hu'intv hv'cont.intervalIntegrable
    calc
      (∫ x in (2 : ℝ)..A, integrand n x) =
          ∫ x in (2 : ℝ)..A, tailWeight n x * v' x := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [uIcc_of_le hA] at hx
            exact gap2 n x (by linarith [hx.1])
      _ = tailWeight n A * v A - tailWeight n 2 * v 2 -
          ∫ x in (2 : ℝ)..A, tailWeightDeriv n x * v x := hip
  refine ⟨2, by norm_num, ?_⟩
  unfold ConvergesAtTopFrom
  refine ⟨L, ?_⟩
  have hlim :
      Tendsto
        (fun A => tailWeight n A * v A - tailWeight n 2 * v 2 -
          ∫ x in (2 : ℝ)..A, tailWeightDeriv n x * v x)
        atTop (nhds L) := by
    simpa [L] using (hboundary.sub_const (tailWeight n 2 * v 2)).sub htail
  exact hlim.congr' (Filter.EventuallyEq.symm hformula)

theorem gap8 (n a b : ℝ) (hb : 0 < b) (hba : b < a) :
    (∫ x in b..a, integrand n x) =
      ∫ t in (1 / a)..(1 / b), integrand (2 - n) t := by
  let f : ℝ → ℝ := fun x => 1 / x
  let f' : ℝ → ℝ := fun x => -1 / x ^ 2
  have hf : ∀ x ∈ uIcc b a, HasDerivAt f (f' x) x := by
    intro x hx
    rw [uIcc_of_le hba.le] at hx
    exact one_div_hasDerivAt x (ne_of_gt (hb.trans_le hx.1))
  have hf' : ContinuousOn f' (uIcc b a) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    rw [uIcc_of_le hba.le] at hx
    have hx0 : 0 < x := hb.trans_le hx.1
    exact continuousAt_const.neg.div (continuousAt_id.pow 2)
      (pow_ne_zero 2 hx0.ne')
  have hg : ContinuousOn (integrand (2 - n)) (f '' uIcc b a) := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    rw [uIcc_of_le hba.le] at hx
    have hx0 : 0 < x := hb.trans_le hx.1
    exact (integrand_continuousAt (2 - n) (1 / x) (one_div_pos.mpr hx0)).continuousWithinAt
  have hsubst :=
    intervalIntegral.integral_comp_mul_deriv'
      (a := b) (b := a) (f := f) (f' := f') (g := integrand (2 - n))
      hf hf' hg
  have hleft :
      (∫ x in b..a, (integrand (2 - n) ∘ f) x * f' x) =
        -(∫ x in b..a, integrand n x) := by
    calc
      (∫ x in b..a, (integrand (2 - n) ∘ f) x * f' x) =
          ∫ x in b..a, -integrand n x := by
            apply intervalIntegral.integral_congr
            intro x hx
            have hx0 : 0 < x := by
              rw [uIcc_of_le hba.le] at hx
              exact hb.trans_le hx.1
            exact reciprocal_integrand_mul_deriv n x hx0
      _ = -(∫ x in b..a, integrand n x) := intervalIntegral.integral_neg
  have hneg :
      -(∫ x in b..a, integrand n x) =
        -(∫ t in (1 / a)..(1 / b), integrand (2 - n) t) := by
    calc
      -(∫ x in b..a, integrand n x) =
          ∫ x in b..a, (integrand (2 - n) ∘ f) x * f' x := hleft.symm
      _ = ∫ t in f b..f a, integrand (2 - n) t := hsubst
      _ = -(∫ t in (1 / a)..(1 / b), integrand (2 - n) t) := by
        change (∫ t in (1 / b)..(1 / a), integrand (2 - n) t) =
          -(∫ t in (1 / a)..(1 / b), integrand (2 - n) t)
        exact intervalIntegral.integral_symm (1 / a) (1 / b)
  linarith

theorem gap9 (n a : ℝ) (ha : 0 < a) :
    ConvergesAtZeroTo a n ↔ n < 2 := by
  let p : ℝ := 2 - n
  let d : ℝ := 1 / a
  have hd : 0 < d := one_div_pos.mpr ha
  constructor
  · rintro ⟨L, hzero⟩
    have hinv0 : Tendsto (fun B : ℝ => 1 / B) atTop (nhds 0) := by
      simpa only [one_div] using
        (tendsto_inv_atTop_zero : Tendsto (fun B : ℝ => B⁻¹) atTop (nhds 0))
    have hinvpos : ∀ᶠ B : ℝ in atTop, 0 < 1 / B := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
      exact one_div_pos.mpr hB
    have hinvWithin :
        Tendsto (fun B : ℝ => 1 / B) atTop (nhdsWithin 0 (Ioi 0)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hinv0, by simpa only [mem_Ioi] using hinvpos⟩
    have hcomp :
        Tendsto (fun B => ∫ x in (1 / B)..a, integrand n x)
          atTop (nhds L) := hzero.comp hinvWithin
    have heq : ∀ᶠ B : ℝ in atTop,
        (∫ x in (1 / B)..a, integrand n x) =
          ∫ x in d..B, integrand p x := by
      filter_upwards [eventually_gt_atTop (max 0 (1 / a))] with B hB
      have hB0 : 0 < B := (le_max_left 0 (1 / a)).trans_lt hB
      have hb : 0 < 1 / B := one_div_pos.mpr hB0
      have hba : 1 / B < a := by
        rw [div_lt_iff₀ hB0]
        have hBd : 1 / a < B := (le_max_right 0 (1 / a)).trans_lt hB
        rw [div_lt_iff₀ ha] at hBd
        nlinarith
      have h := gap8 n a (1 / B) hb hba
      dsimp [d, p]
      convert h using 1
      field_simp [hB0.ne']
    have htop : ConvergesAtTopFrom d p :=
      ⟨L, hcomp.congr' heq⟩
    by_contra hnp
    have hpnonpos : p ≤ 0 := by
      dsimp [p]
      linarith
    exact not_convergesAtTopFrom_of_nonpos p d hpnonpos hd htop
  · intro hn
    have hp : 0 < p := by
      dsimp [p]
      linarith
    obtain ⟨c, hc, L, htop⟩ := gap7 p hp
    have hc0 : 0 < c := zero_lt_one.trans hc
    let K : ℝ := ∫ x in d..c, integrand p x
    have hdc : IntervalIntegrable (integrand p) volume d c :=
      integrand_intervalIntegrable_pos_ends p d c hd hc0
    have htop_d :
        Tendsto (fun B => ∫ x in d..B, integrand p x)
          atTop (nhds (K + L)) := by
      have hshift : Tendsto
          (fun B => K + ∫ x in c..B, integrand p x)
          atTop (nhds (K + L)) := tendsto_const_nhds.add htop
      apply hshift.congr'
      filter_upwards [eventually_gt_atTop c] with B hB
      have hcb : IntervalIntegrable (integrand p) volume c B :=
        integrand_intervalIntegrable_pos p c B hc0 hB
      unfold K
      exact intervalIntegral.integral_add_adjacent_intervals hdc hcb
    have hinv :
        Tendsto (fun b : ℝ => 1 / b) (nhdsWithin 0 (Ioi 0)) atTop := by
      simpa only [one_div] using
        (tendsto_inv_nhdsGT_zero :
          Tendsto (fun b : ℝ => b⁻¹) (nhdsWithin 0 (Ioi 0)) atTop)
    have hcomp :
        Tendsto (fun b => ∫ x in d..(1 / b), integrand p x)
          (nhdsWithin 0 (Ioi 0)) (nhds (K + L)) :=
      htop_d.comp hinv
    refine ⟨K + L, ?_⟩
    apply hcomp.congr'
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with b hb hba
    simpa only [d, p] using (gap8 n a b hb hba).symm

theorem gap10 (n a₁ a₂ : ℝ) (h₁ : 0 < a₁) (h₂ : a₁ < a₂) :
    IntervalIntegrable (integrand n) volume a₁ a₂ := by
  exact integrand_intervalIntegrable_pos n a₁ a₂ h₁ h₂

theorem gap11 (n : ℝ) :
    Converges n ↔ 0 < n ∧ n < 2 := by
  constructor
  · rintro ⟨a, ha, hzero, htop⟩
    have hnlt : n < 2 := (gap9 n a ha).mp hzero
    have hnpos : 0 < n := by
      by_contra hn
      exact gap1 n (le_of_not_gt hn) ⟨a, ha, hzero, htop⟩
    exact ⟨hnpos, hnlt⟩
  · rintro ⟨hnpos, hnlt⟩
    obtain ⟨a, ha, htop⟩ := gap7 n hnpos
    have ha0 : 0 < a := zero_lt_one.trans ha
    exact ⟨a, ha0, (gap9 n a ha0).mpr hnlt, htop⟩

theorem gap12 (n x : ℝ) (hx : 0 < x) :
    Real.sin (phase x) ^ 2 / Real.rpow x n ≤ absIntegrand n x := by
  have hs : Real.sin (phase x) ^ 2 ≤ |Real.sin (phase x)| := by
    calc
      Real.sin (phase x) ^ 2 = |Real.sin (phase x)| ^ 2 := by
        rw [sq_abs]
      _ ≤ |Real.sin (phase x)| * 1 := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _)
          (abs_nonneg (Real.sin (phase x)))
      _ = |Real.sin (phase x)| := by ring
  unfold absIntegrand
  exact div_le_div_of_nonneg_right hs (Real.rpow_nonneg hx.le n)

theorem gap13 (n x : ℝ) (hx : 0 < x) :
    Real.sin (phase x) ^ 2 / Real.rpow x n =
      (1 - Real.cos (2 * x + 2 / x)) / (2 * Real.rpow x n) := by
  rw [Real.sin_sq_eq_half_sub]
  unfold phase
  ring

theorem gap14 (n x : ℝ) (hx : 0 < x) :
    (1 - Real.cos (2 * x + 2 / x)) / (2 * Real.rpow x n) ≤
      absIntegrand n x := by
  rw [← gap13 n x hx]
  exact gap12 n x hx

theorem gap15 (n a : ℝ) (hn₀ : 0 < n) (hn₁ : n ≤ 1) (ha : 0 < a) :
    Tendsto (fun A => ∫ x in a..A, 1 / Real.rpow x n) atTop atTop := by
  rcases hn₁.eq_or_lt with rfl | hnlt
  · have hlim : Tendsto (fun A : ℝ => Real.log A - Real.log a) atTop atTop := by
      simpa [sub_eq_add_neg] using
        atTop.tendsto_atTop_add_const_right (-Real.log a) Real.tendsto_log_atTop
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop a] with A hA
    have hA0 : 0 < A := ha.trans hA
    simp only [Real.rpow_eq_pow, Real.rpow_one]
    rw [integral_one_div_of_pos ha hA0]
    rw [Real.log_div hA0.ne' ha.ne']
  · have hp : 0 < 1 - n := by linarith
    have hrpow : Tendsto (fun A : ℝ => A ^ (1 - n)) atTop atTop :=
      tendsto_rpow_atTop hp
    have hsub : Tendsto
        (fun A : ℝ => A ^ (1 - n) - a ^ (1 - n)) atTop atTop := by
      simpa [sub_eq_add_neg] using
        atTop.tendsto_atTop_add_const_right (-a ^ (1 - n)) hrpow
    have hlim : Tendsto
        (fun A : ℝ => (A ^ (1 - n) - a ^ (1 - n)) / (1 - n))
        atTop atTop := hsub.atTop_div_const hp
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop a] with A hA
    have hA0 : 0 < A := ha.trans hA
    have heq :
        (∫ x in a..A, 1 / Real.rpow x n) = ∫ x in a..A, x ^ (-n) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hA.le] at hx
      have hx0 : 0 < x := ha.trans_le hx.1
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_neg hx0.le]
      simp only [one_div]
    rw [heq, integral_rpow (Or.inl (by linarith : -1 < -n))]
    congr 1 <;> ring

theorem gap16 (n a : ℝ) (hn : 0 < n) (ha : 1 < a) :
    ∃ L : ℝ,
      Tendsto
        (fun A => ∫ x in a..A, Real.cos (2 * x + 2 / x) / Real.rpow x n)
        atTop (nhds L) := by
  let u : ℝ → ℝ := fun x => tailWeight n x / 2
  let u' : ℝ → ℝ := fun x => tailWeightDeriv n x / 2
  let v : ℝ → ℝ := fun x => Real.sin (2 * phase x)
  let v' : ℝ → ℝ := fun x => 2 * phaseDeriv x * Real.cos (2 * phase x)
  have htw_deriv : ∀ x ∈ Ici (2 : ℝ),
      HasDerivAt (tailWeight n) (tailWeightDeriv n x) x := by
    intro x hx
    have hx2 : (2 : ℝ) ≤ x := hx
    exact tailWeight_hasDerivAt n x hn (by linarith)
  have hu_deriv : ∀ x ∈ Ici (2 : ℝ), HasDerivAt u (u' x) x := by
    intro x hx
    simpa [u, u'] using (htw_deriv x hx).div_const 2
  have htw'_nonpos : ∀ x ∈ Ioi (2 : ℝ), tailWeightDeriv n x ≤ 0 := by
    intro x hx
    exact tailWeightDeriv_nonpos n x hn hx.le
  have htw'int : IntegrableOn (tailWeightDeriv n) (Ioi (2 : ℝ)) :=
    integrableOn_Ioi_deriv_of_nonpos' htw_deriv htw'_nonpos (gap6 n hn)
  have hu'int : IntegrableOn u' (Ioi (2 : ℝ)) := by
    simpa [u'] using htw'int.div_const 2
  have hv_meas : AEStronglyMeasurable v (volume.restrict (Ioi (2 : ℝ))) := by
    apply Measurable.aestronglyMeasurable
    dsimp [v, phase]
    measurability
  have hv_bound : ∀ᵐ x ∂(volume.restrict (Ioi (2 : ℝ))), ‖v x‖ ≤ 1 := by
    filter_upwards [] with x
    simpa [v, Real.norm_eq_abs] using Real.abs_sin_le_one (2 * phase x)
  have huv_int : IntegrableOn (fun x => u' x * v x) (Ioi (2 : ℝ)) :=
    hu'int.mul_bdd hv_meas hv_bound
  have htail :
      Tendsto (fun A => ∫ x in (2 : ℝ)..A, u' x * v x)
        atTop (nhds (∫ x in Ioi (2 : ℝ), u' x * v x)) :=
    intervalIntegral_tendsto_integral_Ioi 2 huv_int tendsto_id
  have hu_lim : Tendsto u atTop (nhds 0) := by
    simpa [u] using (gap6 n hn).div_const 2
  have hboundary : Tendsto (fun A => u A * v A) atTop (nhds 0) := by
    apply Asymptotics.IsBigO.trans_tendsto (g'' := u)
    · apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [] with A
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      have hvA : |v A| ≤ 1 := by
        simpa [v] using Real.abs_sin_le_one (2 * phase A)
      calc
        |u A| * |v A| ≤ |u A| * 1 :=
          mul_le_mul_of_nonneg_left hvA (abs_nonneg _)
        _ = 1 * |u A| := by ring
    · exact hu_lim
  let L₂ : ℝ := -u 2 * v 2 - ∫ x in Ioi (2 : ℝ), u' x * v x
  have hformula : ∀ᶠ A : ℝ in atTop,
      (∫ x in (2 : ℝ)..A, Real.cos (2 * x + 2 / x) / Real.rpow x n) =
        u A * v A - u 2 * v 2 - ∫ x in (2 : ℝ)..A, u' x * v x := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with A hA
    have hucont : ContinuousOn u (uIcc (2 : ℝ) A) := by
      intro x hx
      rw [uIcc_of_le hA] at hx
      exact (hu_deriv x (by exact hx.1)).continuousAt.continuousWithinAt
    have hvcont : ContinuousOn v (uIcc (2 : ℝ) A) := by
      intro x hx
      rw [uIcc_of_le hA] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      have harg := (phase_hasDerivAt x hx0.ne').const_mul 2
      exact ((Real.hasDerivAt_sin (2 * phase x)).comp x harg).continuousAt.continuousWithinAt
    have hu_deriv' : ∀ x ∈ Ioo (min (2 : ℝ) A) (max (2 : ℝ) A),
        HasDerivAt u (u' x) x := by
      intro x hx
      rw [min_eq_left hA, max_eq_right hA] at hx
      exact hu_deriv x hx.1.le
    have hv_deriv : ∀ x ∈ Ioo (min (2 : ℝ) A) (max (2 : ℝ) A),
        HasDerivAt v (v' x) x := by
      intro x hx
      rw [min_eq_left hA, max_eq_right hA] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      have harg := (phase_hasDerivAt x hx0.ne').const_mul 2
      convert (Real.hasDerivAt_sin (2 * phase x)).comp x harg using 1 <;> ring
    have hu'intv : IntervalIntegrable u' volume (2 : ℝ) A := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hA]
      exact hu'int.mono_set Ioo_subset_Ioi_self
    have hv'cont : ContinuousOn v' (uIcc (2 : ℝ) A) := by
      apply continuousOn_of_forall_continuousAt
      intro x hx
      rw [uIcc_of_le hA] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      have hpd : ContinuousAt phaseDeriv x := by
        exact continuousAt_const.sub
          (continuousAt_const.div (continuousAt_id.pow 2)
            (pow_ne_zero 2 hx0.ne'))
      have hphase := (phase_hasDerivAt x hx0.ne').continuousAt
      exact (continuousAt_const.mul hpd).mul
        (Real.continuous_cos.continuousAt.comp (continuousAt_const.mul hphase))
    have hip :=
      intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
        hucont hvcont hu_deriv' hv_deriv hu'intv hv'cont.intervalIntegrable
    calc
      (∫ x in (2 : ℝ)..A, Real.cos (2 * x + 2 / x) / Real.rpow x n) =
          ∫ x in (2 : ℝ)..A, u x * v' x := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [uIcc_of_le hA] at hx
            have hx1 : 1 < x := by linarith [hx.1]
            have hx0 : 0 < x := zero_lt_one.trans hx1
            have hr : Real.rpow x n ≠ 0 :=
              (Real.rpow_pos_of_pos hx0 n).ne'
            have hd : phaseDeriv x ≠ 0 := (phaseDeriv_pos x hx1).ne'
            have hphase : 2 * phase x = 2 * x + 2 / x := by
              unfold phase
              ring
            dsimp [u, v']
            rw [hphase]
            unfold tailWeight
            field_simp
            rw [Real.rpow_eq_pow]
      _ = u A * v A - u 2 * v 2 - ∫ x in (2 : ℝ)..A, u' x * v x := hip
  have hbase : Tendsto
      (fun A => ∫ x in (2 : ℝ)..A,
        Real.cos (2 * x + 2 / x) / Real.rpow x n)
      atTop (nhds L₂) := by
    have hlim :
        Tendsto
          (fun A => u A * v A - u 2 * v 2 - ∫ x in (2 : ℝ)..A, u' x * v x)
          atTop (nhds L₂) := by
      simpa [L₂] using (hboundary.sub_const (u 2 * v 2)).sub htail
    exact hlim.congr' (Filter.EventuallyEq.symm hformula)
  let c : ℝ := ∫ x in a..(2 : ℝ),
    Real.cos (2 * x + 2 / x) / Real.rpow x n
  refine ⟨c + L₂, ?_⟩
  have hshift : Tendsto
      (fun A => c + ∫ x in (2 : ℝ)..A,
        Real.cos (2 * x + 2 / x) / Real.rpow x n)
      atTop (nhds (c + L₂)) := tendsto_const_nhds.add hbase
  apply hshift.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with A hA
  have hcont_a2 : IntervalIntegrable
      (fun x => Real.cos (2 * x + 2 / x) / Real.rpow x n) volume a 2 := by
    apply (continuousOn_of_forall_continuousAt _).intervalIntegrable
    intro x hx
    have hx0 : 0 < x := by
      rcases mem_uIcc.mp hx with hx | hx
      · exact (zero_lt_one.trans ha).trans_le hx.1
      · exact (by linarith [hx.1])
    have harg : ContinuousAt (fun y : ℝ => 2 * y + 2 / y) x :=
      (continuousAt_const.mul continuousAt_id).add
        (continuousAt_const.div continuousAt_id hx0.ne')
    have hr := continuousAt_id.rpow_const (p := n) (Or.inl hx0.ne')
    exact (Real.continuous_cos.continuousAt.comp harg).div hr
      (Real.rpow_pos_of_pos hx0 n).ne'
  have hcont_2A : IntervalIntegrable
      (fun x => Real.cos (2 * x + 2 / x) / Real.rpow x n) volume 2 A := by
    apply (continuousOn_of_forall_continuousAt _).intervalIntegrable
    intro x hx
    rw [uIcc_of_le hA] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    have harg : ContinuousAt (fun y : ℝ => 2 * y + 2 / y) x :=
      (continuousAt_const.mul continuousAt_id).add
        (continuousAt_const.div continuousAt_id hx0.ne')
    have hr := continuousAt_id.rpow_const (p := n) (Or.inl hx0.ne')
    exact (Real.continuous_cos.continuousAt.comp harg).div hr
      (Real.rpow_pos_of_pos hx0 n).ne'
  unfold c
  exact intervalIntegral.integral_add_adjacent_intervals hcont_a2 hcont_2A

theorem gap17 (n a : ℝ) (hn₀ : 0 < n) (hn₁ : n ≤ 1) (ha : 1 < a) :
    Tendsto (fun A => ∫ x in a..A, absIntegrand n x) atTop atTop := by
  have hpow := gap15 n a hn₀ hn₁ (zero_lt_one.trans ha)
  have hpowScaled :
      Tendsto (fun A => (1 / 2 : ℝ) *
        ∫ x in a..A, 1 / Real.rpow x n) atTop atTop := by
    have h := hpow.atTop_mul_const (by norm_num : (0 : ℝ) < 1 / 2)
    simpa only [mul_comm] using h
  obtain ⟨C, hcos⟩ := gap16 n a hn₀ ha
  have hcosScaled :
      Tendsto (fun A => (1 / 2 : ℝ) *
        ∫ x in a..A, Real.cos (2 * x + 2 / x) / Real.rpow x n)
        atTop (nhds ((1 / 2 : ℝ) * C)) :=
    tendsto_const_nhds.mul hcos
  have hcombined :
      Tendsto
        (fun A => (1 / 2 : ℝ) * (∫ x in a..A, 1 / Real.rpow x n) -
          (1 / 2 : ℝ) *
            ∫ x in a..A, Real.cos (2 * x + 2 / x) / Real.rpow x n)
        atTop atTop := by
    have h := hcosScaled.neg.add_atTop hpowScaled
    simpa only [sub_eq_add_neg, add_comm] using h
  have hmodel :
      Tendsto
        (fun A => ∫ x in a..A,
          (1 - Real.cos (2 * x + 2 / x)) / (2 * Real.rpow x n))
        atTop atTop := by
    apply hcombined.congr'
    filter_upwards [eventually_ge_atTop a] with A hA
    have hpowInt : IntervalIntegrable
        (fun x : ℝ => 1 / Real.rpow x n) volume a A := by
      apply (continuousOn_of_forall_continuousAt _).intervalIntegrable
      intro x hx
      rw [uIcc_of_le hA] at hx
      have hx0 : 0 < x := (zero_lt_one.trans ha).trans_le hx.1
      exact continuousAt_const.div
        (continuousAt_id.rpow_const (p := n) (Or.inl hx0.ne'))
        (Real.rpow_pos_of_pos hx0 n).ne'
    have hcosInt : IntervalIntegrable
        (fun x : ℝ => Real.cos (2 * x + 2 / x) / Real.rpow x n)
        volume a A := by
      apply (continuousOn_of_forall_continuousAt _).intervalIntegrable
      intro x hx
      rw [uIcc_of_le hA] at hx
      have hx0 : 0 < x := (zero_lt_one.trans ha).trans_le hx.1
      have harg : ContinuousAt (fun y : ℝ => 2 * y + 2 / y) x :=
        (continuousAt_const.mul continuousAt_id).add
          (continuousAt_const.div continuousAt_id hx0.ne')
      exact (Real.continuous_cos.continuousAt.comp harg).div
        (continuousAt_id.rpow_const (p := n) (Or.inl hx0.ne'))
        (Real.rpow_pos_of_pos hx0 n).ne'
    calc
      (1 / 2 : ℝ) * (∫ x in a..A, 1 / Real.rpow x n) -
          (1 / 2 : ℝ) *
            ∫ x in a..A, Real.cos (2 * x + 2 / x) / Real.rpow x n =
          ∫ x in a..A,
            (1 / 2 : ℝ) * (1 / Real.rpow x n) -
              (1 / 2 : ℝ) *
                (Real.cos (2 * x + 2 / x) / Real.rpow x n) := by
            rw [intervalIntegral.integral_sub (hpowInt.const_mul (1 / 2))
              (hcosInt.const_mul (1 / 2)),
              intervalIntegral.integral_const_mul,
              intervalIntegral.integral_const_mul]
      _ = ∫ x in a..A,
          (1 - Real.cos (2 * x + 2 / x)) / (2 * Real.rpow x n) := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [uIcc_of_le hA] at hx
            have hx0 : 0 < x := (zero_lt_one.trans ha).trans_le hx.1
            have hr : Real.rpow x n ≠ 0 := (Real.rpow_pos_of_pos hx0 n).ne'
            field_simp
  have hle : ∀ᶠ A : ℝ in atTop,
      (∫ x in a..A,
        (1 - Real.cos (2 * x + 2 / x)) / (2 * Real.rpow x n)) ≤
        ∫ x in a..A, absIntegrand n x := by
    filter_upwards [eventually_ge_atTop a] with A hA
    have hleft : IntervalIntegrable
        (fun x : ℝ =>
          (1 - Real.cos (2 * x + 2 / x)) / (2 * Real.rpow x n))
        volume a A := by
      apply (continuousOn_of_forall_continuousAt _).intervalIntegrable
      intro x hx
      rw [uIcc_of_le hA] at hx
      have hx0 : 0 < x := (zero_lt_one.trans ha).trans_le hx.1
      have harg : ContinuousAt (fun y : ℝ => 2 * y + 2 / y) x :=
        (continuousAt_const.mul continuousAt_id).add
          (continuousAt_const.div continuousAt_id hx0.ne')
      exact (continuousAt_const.sub (Real.continuous_cos.continuousAt.comp harg)).div
        (continuousAt_const.mul
          (continuousAt_id.rpow_const (p := n) (Or.inl hx0.ne')))
        (mul_ne_zero two_ne_zero (Real.rpow_pos_of_pos hx0 n).ne')
    have hright : IntervalIntegrable (absIntegrand n) volume a A := by
      apply (continuousOn_of_forall_continuousAt _).intervalIntegrable
      intro x hx
      rw [uIcc_of_le hA] at hx
      exact absIntegrand_continuousAt n x
        ((zero_lt_one.trans ha).trans_le hx.1)
    exact intervalIntegral.integral_mono_on hA hleft hright
      (fun x hx => gap14 n x ((zero_lt_one.trans ha).trans_le hx.1))
  exact tendsto_atTop_mono' atTop hle hmodel

theorem gap18 (n a b : ℝ) (hb : 0 < b) (hba : b < a) :
    (∫ x in b..a, absIntegrand n x) =
      ∫ t in (1 / a)..(1 / b), absIntegrand (2 - n) t := by
  let f : ℝ → ℝ := fun x => 1 / x
  let f' : ℝ → ℝ := fun x => -1 / x ^ 2
  have hf : ∀ x ∈ uIcc b a, HasDerivAt f (f' x) x := by
    intro x hx
    rw [uIcc_of_le hba.le] at hx
    exact one_div_hasDerivAt x (ne_of_gt (hb.trans_le hx.1))
  have hf' : ContinuousOn f' (uIcc b a) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    rw [uIcc_of_le hba.le] at hx
    have hx0 : 0 < x := hb.trans_le hx.1
    exact continuousAt_const.neg.div (continuousAt_id.pow 2)
      (pow_ne_zero 2 hx0.ne')
  have hg : ContinuousOn (absIntegrand (2 - n)) (f '' uIcc b a) := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    rw [uIcc_of_le hba.le] at hx
    have hx0 : 0 < x := hb.trans_le hx.1
    exact (absIntegrand_continuousAt (2 - n) (1 / x)
      (one_div_pos.mpr hx0)).continuousWithinAt
  have hsubst :=
    intervalIntegral.integral_comp_mul_deriv'
      (a := b) (b := a) (f := f) (f' := f') (g := absIntegrand (2 - n))
      hf hf' hg
  have hleft :
      (∫ x in b..a, (absIntegrand (2 - n) ∘ f) x * f' x) =
        -(∫ x in b..a, absIntegrand n x) := by
    calc
      (∫ x in b..a, (absIntegrand (2 - n) ∘ f) x * f' x) =
          ∫ x in b..a, -absIntegrand n x := by
            apply intervalIntegral.integral_congr
            intro x hx
            have hx0 : 0 < x := by
              rw [uIcc_of_le hba.le] at hx
              exact hb.trans_le hx.1
            exact reciprocal_absIntegrand_mul_deriv n x hx0
      _ = -(∫ x in b..a, absIntegrand n x) := intervalIntegral.integral_neg
  have hneg :
      -(∫ x in b..a, absIntegrand n x) =
        -(∫ t in (1 / a)..(1 / b), absIntegrand (2 - n) t) := by
    calc
      -(∫ x in b..a, absIntegrand n x) =
          ∫ x in b..a, (absIntegrand (2 - n) ∘ f) x * f' x := hleft.symm
      _ = ∫ t in f b..f a, absIntegrand (2 - n) t := hsubst
      _ = -(∫ t in (1 / a)..(1 / b), absIntegrand (2 - n) t) := by
        change (∫ t in (1 / b)..(1 / a), absIntegrand (2 - n) t) =
          -(∫ t in (1 / a)..(1 / b), absIntegrand (2 - n) t)
        exact intervalIntegral.integral_symm (1 / a) (1 / b)
  linarith

theorem gap19 (n a : ℝ) (hn₁ : 1 < n) (hn₂ : n < 2) (ha : 0 < a) :
    Tendsto (fun b => ∫ x in b..a, absIntegrand n x)
      (nhdsWithin 0 (Ioi 0)) atTop := by
  let p : ℝ := 2 - n
  let d : ℝ := 1 / a
  have hp0 : 0 < p := by
    dsimp [p]
    linarith
  have hp1 : p ≤ 1 := by
    dsimp [p]
    linarith
  have hd : 0 < d := by
    dsimp [d]
    exact one_div_pos.mpr ha
  have hbase :
      Tendsto (fun A => ∫ x in (2 : ℝ)..A, absIntegrand p x)
        atTop atTop :=
    gap17 p 2 hp0 hp1 (by norm_num)
  let K : ℝ := ∫ x in d..(2 : ℝ), absIntegrand p x
  have hd2 : IntervalIntegrable (absIntegrand p) volume d 2 :=
    absIntegrand_intervalIntegrable_pos_ends p d 2 hd (by norm_num)
  have htop_d :
      Tendsto (fun A => ∫ x in d..A, absIntegrand p x)
        atTop atTop := by
    have hshift :
        Tendsto (fun A => K + ∫ x in (2 : ℝ)..A, absIntegrand p x)
          atTop atTop :=
      tendsto_const_nhds.add_atTop hbase
    apply hshift.congr'
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with A hA
    have h2A : IntervalIntegrable (absIntegrand p) volume 2 A :=
      absIntegrand_intervalIntegrable_pos_ends p 2 A (by norm_num) (by linarith)
    unfold K
    exact intervalIntegral.integral_add_adjacent_intervals hd2 h2A
  have hinv :
      Tendsto (fun b : ℝ => 1 / b) (nhdsWithin 0 (Ioi 0)) atTop := by
    simpa only [one_div] using
      (tendsto_inv_nhdsGT_zero :
        Tendsto (fun b : ℝ => b⁻¹) (nhdsWithin 0 (Ioi 0)) atTop)
  have hcomp :
      Tendsto (fun b => ∫ x in d..(1 / b), absIntegrand p x)
        (nhdsWithin 0 (Ioi 0)) atTop :=
    htop_d.comp hinv
  apply hcomp.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with b hb hba
  simpa only [d, p] using (gap18 n a b hb hba).symm

theorem gap20 (n : ℝ) :
    n ∈ {q : ℝ | 0 < q ∧ q < 2} ↔ Converges n := by
  simpa only [mem_setOf_eq] using (gap11 n).symm

end
end ProofGap.Exercise2382
