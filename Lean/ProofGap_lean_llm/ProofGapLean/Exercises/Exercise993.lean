import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise993

noncomputable section

def f (m n x : ℝ) : ℝ :=
  if x = 0 then 0
  else Real.rpow |x| n * Real.sin (1 / Real.rpow |x| m)

def rawDerivative (m n x : ℝ) : ℝ :=
  n * Real.rpow |x| (n - 1) * (|x| / x) *
      Real.sin (1 / Real.rpow |x| m) -
    m / Real.rpow |x| (m + 1) * (|x| / x) *
      Real.rpow |x| n * Real.cos (1 / Real.rpow |x| m)

def finalDerivative (m n x : ℝ) : ℝ :=
  |x| / x *
    (n * Real.rpow |x| (n - 1) * Real.sin (1 / Real.rpow |x| m) -
      m * Real.rpow |x| (n - (m + 1)) * Real.cos (1 / Real.rpow |x| m))

def BoundedFn (g : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |g x| ≤ C

def BoundedOn (g : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ s, |g x| ≤ C

def ball0 (δ : ℝ) : Set ℝ := {x | |x| < δ}

private theorem hasDerivAt_abs_rpow_ne (p x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.rpow |y| p)
      (p * Real.rpow |x| (p - 1) * (|x| / x)) x := by
  rcases hx.lt_or_gt with hxneg | hxpos
  · have h :=
      (Real.hasDerivAt_rpow_const
        (x := |x|) (p := p) (Or.inl (abs_ne_zero.mpr hx))).comp x
        (hasDerivAt_abs_neg hxneg)
    convert h using 1
    simp only [Real.rpow_eq_pow]
    rw [abs_of_neg hxneg]
    field_simp
  · have h :=
      (Real.hasDerivAt_rpow_const
        (x := |x|) (p := p) (Or.inl (abs_ne_zero.mpr hx))).comp x
        (hasDerivAt_abs_pos hxpos)
    convert h using 1
    simp only [Real.rpow_eq_pow]
    rw [abs_of_pos hxpos]
    field_simp

private theorem hasDerivAt_phase (m x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => 1 / Real.rpow |y| m)
      (-m / Real.rpow |x| (m + 1) * (|x| / x)) x := by
  have h := hasDerivAt_abs_rpow_ne (-m) x hx
  have hfun :
      (fun y : ℝ => Real.rpow |y| (-m)) =
        fun y : ℝ => 1 / Real.rpow |y| m := by
    funext y
    simpa only [one_div] using Real.rpow_neg (abs_nonneg y) m
  rw [hfun] at h
  convert h using 1
  have hax : 0 < |x| := abs_pos.mpr hx
  have hr :
      Real.rpow |x| (-m - 1) =
        (Real.rpow |x| (m + 1))⁻¹ := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_def_of_pos hax, Real.rpow_def_of_pos hax]
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [hr]
  simp only [div_eq_mul_inv]

private noncomputable def phasePoint (m t : ℝ) : ℝ :=
  Real.rpow t (-(1 / m))

private theorem phasePoint_pos (m t : ℝ) (ht : 0 < t) :
    0 < phasePoint m t := by
  dsimp [phasePoint]
  simpa only [Real.rpow_eq_pow] using
    Real.rpow_pos_of_pos ht (-(1 / m))

private theorem phasePoint_rpow (m t a : ℝ) (ht : 0 < t) :
    Real.rpow (phasePoint m t) a =
      Real.rpow t (-a / m) := by
  have h :=
    (Real.rpow_mul (le_of_lt ht) (-(1 / m)) a).symm
  dsimp [phasePoint]
  simpa only [Real.rpow_eq_pow, show -(1 / m) * a = -a / m by ring] using h

private theorem phasePoint_phase (m t : ℝ) (hm : 0 < m) (ht : 0 < t) :
    1 / Real.rpow |phasePoint m t| m = t := by
  have hxp : 0 < phasePoint m t := phasePoint_pos m t ht
  rw [abs_of_pos hxp, phasePoint_rpow m t m ht]
  have he : -m / m = -1 := by
    field_simp
  rw [he]
  have hr : Real.rpow t (-1) = t⁻¹ := by
    simpa only [Real.rpow_eq_pow] using Real.rpow_neg_one t
  rw [hr]
  simp

theorem gap1 (m n x : ℝ) (hm : 0 < m) (hx : x ≠ 0) :
    HasDerivAt (f m n) (rawDerivative m n x) x := by
  have hpow := hasDerivAt_abs_rpow_ne n x hx
  have hphase := hasDerivAt_phase m x hx
  have hproduct := hpow.mul hphase.sin
  have hlocal :
      (fun y : ℝ =>
        Real.rpow |y| n * Real.sin (1 / Real.rpow |y| m)) =ᶠ[nhds x]
        f m n := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [f, hy]
  have hlocal' :
      f m n =ᶠ[nhds x]
        ((fun y : ℝ => Real.rpow |y| n) *
          fun y : ℝ => Real.sin (1 / Real.rpow |y| m)) := by
    simpa only [Pi.mul_apply] using hlocal.symm
  convert hproduct.congr_of_eventuallyEq hlocal' using 1
  simp only [rawDerivative]
  ring

theorem gap2 (m n x : ℝ) (hm : 0 < m) (hx : x ≠ 0) :
    HasDerivAt (f m n) (finalDerivative m n x) x := by
  convert gap1 m n x hm hx using 1
  unfold rawDerivative finalDerivative
  have hax : 0 < |x| := abs_pos.mpr hx
  have hr :
      Real.rpow |x| (n - (m + 1)) =
        Real.rpow |x| n / Real.rpow |x| (m + 1) := by
    simpa only [Real.rpow_eq_pow] using
      Real.rpow_sub hax n (m + 1)
  rw [hr]
  simp only [div_eq_mul_inv]
  ring

theorem gap3 :
    BoundedFn (fun x : ℝ => |x| / x) := by
  refine ⟨1, zero_le_one, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · rw [abs_div, abs_abs]
    simp [hx]

theorem gap4 (m : ℝ) :
    BoundedFn (fun x : ℝ => Real.sin (1 / Real.rpow |x| m)) := by
  exact ⟨1, zero_le_one, fun x => Real.abs_sin_le_one _⟩

theorem gap5 (m : ℝ) :
    BoundedFn (fun x : ℝ => Real.cos (1 / Real.rpow |x| m)) := by
  exact ⟨1, zero_le_one, fun x => Real.abs_cos_le_one _⟩

private theorem hasDerivAt_zero_of_one_lt (m n : ℝ) (hn : 1 < n) :
    HasDerivAt (f m n) 0 0 := by
  rw [hasDerivAt_iff_tendsto]
  have hpow :
      Tendsto (fun x : ℝ => Real.rpow |x| (n - 1))
        (nhds 0) (nhds 0) := by
    have habs :
        Tendsto (fun x : ℝ => |x|) (nhds 0) (nhds 0) :=
      by
        have h : ContinuousAt (fun x : ℝ => |x|) 0 :=
          continuous_abs.continuousAt
        simpa using h.tendsto
    have h := habs.rpow_const
        (p := n - 1) (Or.inr (by linarith : 0 ≤ n - 1))
    simpa only [Real.rpow_eq_pow, abs_zero,
      Real.zero_rpow (by linarith : n - 1 ≠ 0)] using h
  apply squeeze_zero
    (fun x => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    ?_ hpow
  intro x
  have hf0 : f m n 0 = 0 := by simp [f]
  by_cases hx : x = 0
  · simp [hx, hf0, Real.zero_rpow (by linarith : n - 1 ≠ 0)]
  · have hax : 0 < |x| := abs_pos.mpr hx
    have hshift :
        Real.rpow |x| n =
          Real.rpow |x| (n - 1) * |x| := by
      have h := Real.rpow_add hax (n - 1) 1
      simpa only [Real.rpow_eq_pow, Real.rpow_one, sub_add_cancel] using h
    simp only [sub_zero, hf0, smul_zero]
    simp only [f, hx, if_false, Real.norm_eq_abs]
    have hrnonneg : 0 ≤ Real.rpow |x| n := by
      simpa only [Real.rpow_eq_pow] using
        Real.rpow_nonneg (abs_nonneg x) n
    rw [abs_mul, abs_of_nonneg hrnonneg]
    rw [hshift]
    calc
      |x|⁻¹ * (Real.rpow |x| (n - 1) * |x| *
          |Real.sin (1 / Real.rpow |x| m)|) =
          Real.rpow |x| (n - 1) *
            |Real.sin (1 / Real.rpow |x| m)| := by
              field_simp
      _ ≤ Real.rpow |x| (n - 1) :=
        mul_le_of_le_one_right
          (Real.rpow_nonneg (abs_nonneg x) (n - 1))
          (Real.abs_sin_le_one _)

theorem gap6 (m n δ : ℝ) (hm : 0 < m) (hδ : 0 < δ)
    (hn : m + 1 ≤ n) :
    BoundedOn (fun x => deriv (f m n) x) (ball0 δ) := by
  let D : ℝ := max 1 δ
  let C : ℝ :=
    |n| * Real.rpow D (n - 1) +
      |m| * Real.rpow D (n - (m + 1))
  have hD0 : 0 ≤ D := by
    dsimp [D]
    exact hδ.le.trans (le_max_right _ _)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    have hp0 : 0 ≤ Real.rpow D (n - 1) := by
      simpa only [Real.rpow_eq_pow] using Real.rpow_nonneg hD0 (n - 1)
    have hq0 : 0 ≤ Real.rpow D (n - (m + 1)) := by
      simpa only [Real.rpow_eq_pow] using
        Real.rpow_nonneg hD0 (n - (m + 1))
    positivity
  refine ⟨C, hC0, ?_⟩
  intro x hxball
  by_cases hx : x = 0
  · subst x
    have hd0 : deriv (f m n) 0 = 0 :=
      (hasDerivAt_zero_of_one_lt m n (by linarith)).deriv
    simpa [hd0] using hC0
  · have haxD : |x| ≤ D := by
      exact hxball.le.trans (le_max_right 1 δ)
    have hp :
        Real.rpow |x| (n - 1) ≤ Real.rpow D (n - 1) := by
      simpa only [Real.rpow_eq_pow] using
        Real.rpow_le_rpow (abs_nonneg x) haxD (by linarith : 0 ≤ n - 1)
    have hq :
        Real.rpow |x| (n - (m + 1)) ≤
          Real.rpow D (n - (m + 1)) := by
      simpa only [Real.rpow_eq_pow] using
        Real.rpow_le_rpow (abs_nonneg x) haxD
          (by linarith : 0 ≤ n - (m + 1))
    have hp0 : 0 ≤ Real.rpow |x| (n - 1) := by
      simpa only [Real.rpow_eq_pow] using
        Real.rpow_nonneg (abs_nonneg x) (n - 1)
    have hq0 : 0 ≤ Real.rpow |x| (n - (m + 1)) := by
      simpa only [Real.rpow_eq_pow] using
        Real.rpow_nonneg (abs_nonneg x) (n - (m + 1))
    have hA :
        |n * Real.rpow |x| (n - 1) *
            Real.sin (1 / Real.rpow |x| m)| ≤
          |n| * Real.rpow D (n - 1) := by
      calc
        _ = |n| * Real.rpow |x| (n - 1) *
            |Real.sin (1 / Real.rpow |x| m)| := by
              rw [abs_mul, abs_mul,
                abs_of_nonneg hp0]
        _ ≤ |n| * Real.rpow |x| (n - 1) := by
              exact mul_le_of_le_one_right
                (mul_nonneg (abs_nonneg n) hp0)
                (Real.abs_sin_le_one _)
        _ ≤ |n| * Real.rpow D (n - 1) :=
              mul_le_mul_of_nonneg_left hp (abs_nonneg n)
    have hB :
        |m * Real.rpow |x| (n - (m + 1)) *
            Real.cos (1 / Real.rpow |x| m)| ≤
          |m| * Real.rpow D (n - (m + 1)) := by
      calc
        _ = |m| * Real.rpow |x| (n - (m + 1)) *
            |Real.cos (1 / Real.rpow |x| m)| := by
              rw [abs_mul, abs_mul,
                abs_of_nonneg hq0]
        _ ≤ |m| * Real.rpow |x| (n - (m + 1)) := by
              exact mul_le_of_le_one_right
                (mul_nonneg (abs_nonneg m) hq0)
                (Real.abs_cos_le_one _)
        _ ≤ |m| * Real.rpow D (n - (m + 1)) :=
              mul_le_mul_of_nonneg_left hq (abs_nonneg m)
    have hderiv : deriv (f m n) x = finalDerivative m n x :=
      (gap2 m n x hm hx).deriv
    change |deriv (f m n) x| ≤ C
    rw [hderiv, finalDerivative, abs_mul]
    have hsign : |(|x| / x)| = 1 := by
      rw [abs_div, abs_abs]
      simp [hx]
    rw [hsign, one_mul]
    exact (abs_sub _ _).trans (add_le_add hA hB)

theorem gap7 (m n : ℝ) (hm : 0 < m) (hn : m + 1 ≤ n) :
    HasDerivAt (f m n) 0 0 := by
  exact hasDerivAt_zero_of_one_lt m n (by linarith)

private theorem unbounded_derivative_of_lt (m n δ : ℝ)
    (hm : 0 < m) (hδ : 0 < δ) (hn2 : n < m + 1) :
    ¬ BoundedOn (fun x => deriv (f m n) x) (ball0 δ) := by
  rintro ⟨C, hC0, hbound⟩
  let t : ℕ → ℝ := fun k => ((k : ℝ) + 1) * (2 * Real.pi)
  let x : ℕ → ℝ := fun k => phasePoint m (t k)
  let q : ℝ := (m + 1 - n) / m
  have htpos (k : ℕ) : 0 < t k := by
    dsimp [t]
    positivity
  have ht_top : Tendsto t atTop atTop := by
    dsimp [t]
    exact
      (Filter.tendsto_atTop_add_const_right atTop 1
        tendsto_natCast_atTop_atTop).atTop_mul_const
          (mul_pos two_pos Real.pi_pos)
  have hx_zero : Tendsto x atTop (nhds 0) := by
    have h :=
      (tendsto_rpow_neg_atTop (one_div_pos.mpr hm)).comp ht_top
    simpa only [x, phasePoint, Real.rpow_eq_pow] using h
  have hq : 0 < q := by
    dsimp [q]
    exact div_pos (sub_pos.mpr hn2) hm
  have hmag_top :
      Tendsto (fun k => m * Real.rpow (t k) q) atTop atTop := by
    have h := (tendsto_rpow_atTop hq).comp ht_top
    have h' :
        Tendsto (fun k => Real.rpow (t k) q) atTop atTop := by
      simpa only [Real.rpow_eq_pow] using h
    exact h'.const_mul_atTop hm
  have hxsmall : ∀ᶠ k in atTop, x k < δ :=
    hx_zero.eventually (Iio_mem_nhds hδ)
  have hmagbig : ∀ᶠ k in atTop, C < m * Real.rpow (t k) q :=
    hmag_top.eventually (Filter.eventually_gt_atTop C)
  obtain ⟨k, hxsmallk, hmagbigk⟩ := (hxsmall.and hmagbig).exists
  have hxpos : 0 < x k := phasePoint_pos m (t k) (htpos k)
  have hxne : x k ≠ 0 := hxpos.ne'
  have hxball : x k ∈ ball0 δ := by
    change |x k| < δ
    simpa [abs_of_pos hxpos] using hxsmallk
  have hbounded := hbound (x k) hxball
  have ht_trig :
      t k = (((k + 1 : ℕ) : ℝ) * (2 * Real.pi)) := by
    dsimp [t]
    norm_num
  have hsin : Real.sin (t k) = 0 := by
    rw [ht_trig]
    simpa using Real.sin_add_nat_mul_two_pi 0 (k + 1)
  have hcos : Real.cos (t k) = 1 := by
    rw [ht_trig]
    exact Real.cos_nat_mul_two_pi (k + 1)
  have hexp :
      -(n - (m + 1)) / m = q := by
    dsimp [q]
    ring
  have hpower :
      Real.rpow (x k) (n - (m + 1)) =
        Real.rpow (t k) q := by
    rw [show x k = phasePoint m (t k) by rfl]
    rw [phasePoint_rpow m (t k) (n - (m + 1)) (htpos k)]
    rw [hexp]
  have htpow0 : 0 ≤ Real.rpow (t k) q := by
    simpa only [Real.rpow_eq_pow] using
      Real.rpow_nonneg (le_of_lt (htpos k)) q
  have hphasek :
      1 / Real.rpow (x k) m = t k := by
    have h :=
      phasePoint_phase m (t k) hm (htpos k)
    simpa only [x, abs_of_pos (phasePoint_pos m (t k) (htpos k))] using h
  have hvalue :
      |deriv (f m n) (x k)| = m * Real.rpow (t k) q := by
    have hd :
        deriv (f m n) (x k) = finalDerivative m n (x k) :=
      (gap2 m n (x k) hm hxne).deriv
    rw [hd, finalDerivative, abs_of_pos hxpos,
      hphasek, hsin, hcos, hpower]
    simp only [mul_zero, mul_one, zero_sub, div_self hxne, one_mul,
      abs_neg, abs_mul, abs_of_pos hm, abs_of_nonneg htpow0]
  rw [hvalue] at hbounded
  linarith

theorem gap8 (m n δ : ℝ) (hm : 0 < m) (hδ : 0 < δ)
    (hn1 : 1 < n) (hn2 : n < m + 1) :
    ¬ BoundedOn (fun x => deriv (f m n) x) (ball0 δ) := by
  by_cases h : 1 < n
  · exact unbounded_derivative_of_lt m n δ hm hδ hn2
  · exact (h hn1).elim

theorem gap9 (m n : ℝ) :
    n - (m + 1) < 0 ↔ n < m + 1 := by
  constructor <;> intro h <;> linarith

private theorem f_neg (m n x : ℝ) :
    f m n (-x) = f m n x := by
  simp [f]

theorem gap10 (m n : ℝ) (hm : 0 < m) :
    DifferentiableAt ℝ (f m n) 0 ↔ 1 < n := by
  constructor
  · intro hdiff
    have hd := hdiff.hasDerivAt
    have hcomp :=
      hd.comp_of_eq (0 : ℝ) (hasDerivAt_neg (0 : ℝ)) (by norm_num)
    have hcomp' :
        HasDerivAt (f m n) (-(deriv (f m n) 0)) 0 := by
      have heq :
          f m n =ᶠ[nhds 0] (f m n ∘ Neg.neg) :=
        Filter.Eventually.of_forall fun y => by
          simp only [Function.comp_apply, f_neg]
      convert hcomp.congr_of_eventuallyEq heq using 1
      ring
    have hderiv0 : deriv (f m n) 0 = 0 := by
      have hu := hd.unique hcomp'
      linarith
    have hzero : HasDerivAt (f m n) 0 0 := by
      simpa only [hderiv0] using hd
    by_contra hn
    have hnle : n ≤ 1 := le_of_not_gt hn
    let t : ℕ → ℝ :=
      fun k => ((k : ℝ) + 1 / 4) * (2 * Real.pi)
    let x : ℕ → ℝ := fun k => phasePoint m (t k)
    let q : ℝ := (1 - n) / m
    have htpos (k : ℕ) : 0 < t k := by
      dsimp [t]
      positivity
    have ht_top : Tendsto t atTop atTop := by
      dsimp [t]
      exact
        (Filter.tendsto_atTop_add_const_right atTop (1 / 4 : ℝ)
          tendsto_natCast_atTop_atTop).atTop_mul_const
            (mul_pos two_pos Real.pi_pos)
    have hx_zero : Tendsto x atTop (nhds 0) := by
      have h :=
        (tendsto_rpow_neg_atTop (one_div_pos.mpr hm)).comp ht_top
      simpa only [x, phasePoint, Real.rpow_eq_pow] using h
    have hxpos (k : ℕ) : 0 < x k :=
      phasePoint_pos m (t k) (htpos k)
    have hx_within :
        Tendsto x atTop (nhdsWithin 0 (Set.Ioi 0)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hx_zero, Filter.Eventually.of_forall hxpos⟩
    have hslope :
        Tendsto
          (fun k => (x k)⁻¹ • (f m n (0 + x k) - f m n 0))
          atTop (nhds 0) :=
      hzero.tendsto_slope_zero_right.comp hx_within
    have hq0 : 0 ≤ q := by
      dsimp [q]
      exact div_nonneg (sub_nonneg.mpr hnle) (le_of_lt hm)
    have hslope_value (k : ℕ) :
        (x k)⁻¹ • (f m n (0 + x k) - f m n 0) =
          Real.rpow (t k) q := by
      have hxkpos := hxpos k
      have hxkne : x k ≠ 0 := hxkpos.ne'
      have hphasek :
          1 / Real.rpow (x k) m = t k := by
        have h := phasePoint_phase m (t k) hm (htpos k)
        simpa only [x, abs_of_pos
          (phasePoint_pos m (t k) (htpos k))] using h
      have ht_trig :
          t k = Real.pi / 2 + (k : ℝ) * (2 * Real.pi) := by
        dsimp [t]
        ring
      have hsink : Real.sin (t k) = 1 := by
        rw [ht_trig]
        simpa using Real.sin_add_nat_mul_two_pi (Real.pi / 2) k
      have hshift :
          Real.rpow (x k) n =
            Real.rpow (x k) (n - 1) * x k := by
        have h := Real.rpow_add hxkpos (n - 1) 1
        simpa only [Real.rpow_eq_pow, Real.rpow_one,
          sub_add_cancel] using h
      have hexp : -(n - 1) / m = q := by
        dsimp [q]
        ring
      have hpower :
          Real.rpow (x k) (n - 1) =
            Real.rpow (t k) q := by
        rw [show x k = phasePoint m (t k) by rfl]
        rw [phasePoint_rpow m (t k) (n - 1) (htpos k)]
        rw [hexp]
      rw [zero_add]
      have hf0 : f m n 0 = 0 := by simp [f]
      rw [hf0, sub_zero]
      simp only [smul_eq_mul, f, hxkne, if_false,
        abs_of_pos hxkpos, hphasek, hsink, mul_one, hshift]
      rw [hpower]
      field_simp
    have hslope_lt :
        ∀ᶠ k in atTop,
          (x k)⁻¹ • (f m n (0 + x k) - f m n 0) < 1 / 2 :=
      hslope.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    have ht_one : ∀ᶠ k in atTop, 1 ≤ t k :=
      ht_top.eventually (Filter.eventually_ge_atTop 1)
    obtain ⟨k, hsl, htk⟩ := (hslope_lt.and ht_one).exists
    rw [hslope_value k] at hsl
    have hone : 1 ≤ Real.rpow (t k) q := by
      simpa only [Real.rpow_eq_pow] using Real.one_le_rpow htk hq0
    linarith
  · intro hn
    exact (hasDerivAt_zero_of_one_lt m n hn).differentiableAt

theorem gap11 (m δ : ℝ) (hm : 0 < m) (hδ : 0 < δ) :
    {n : ℝ | BoundedOn (fun x => deriv (f m n) x) (ball0 δ)} =
      {n : ℝ | m + 1 ≤ n} := by
  ext n
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hbounded
    by_contra hn
    exact
      (unbounded_derivative_of_lt m n δ hm hδ (lt_of_not_ge hn))
        hbounded
  · intro hn
    exact gap6 m n δ hm hδ hn

theorem gap12 (m δ : ℝ) (hm : 0 < m) (hδ : 0 < δ) :
    {n : ℝ | ¬ BoundedOn (fun x => deriv (f m n) x) (ball0 δ) ∧
      DifferentiableAt ℝ (f m n) 0} =
      {n : ℝ | 1 < n ∧ n < m + 1} := by
  ext n
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hunbounded, hdifferentiable⟩
    have hn1 : 1 < n := (gap10 m n hm).mp hdifferentiable
    have hn2 : n < m + 1 := by
      by_contra hn
      exact hunbounded (gap6 m n δ hm hδ (le_of_not_gt hn))
    exact ⟨hn1, hn2⟩
  · rintro ⟨hn1, hn2⟩
    exact
      ⟨unbounded_derivative_of_lt m n δ hm hδ hn2,
        (gap10 m n hm).mpr hn1⟩

end

end ProofGap.Exercise993
