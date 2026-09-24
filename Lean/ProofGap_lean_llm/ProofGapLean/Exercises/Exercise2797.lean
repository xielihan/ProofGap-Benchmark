import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise2797

noncomputable section

open scoped BigOperators

def term (n : ℕ) (x : ℝ) : ℝ :=
  1 / Real.rpow n x

def logTerm (k n : ℕ) (x : ℝ) : ℝ :=
  Real.log n ^ k / Real.rpow n x

def zeta (x : ℝ) : ℝ :=
  ∑' n : ℕ, term (n + 1) x

def derivativeSum (x : ℝ) : ℝ :=
  -(∑' n : ℕ, logTerm 1 (n + 1) x)

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (n + 1), u k x) - g x| < ε

private theorem pg_hasDerivAt_term (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    HasDerivAt (term n) (-Real.log n / Real.rpow n x) x := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hpow :
      HasDerivAt (fun y : ℝ => Real.rpow n y)
        (Real.rpow n x * Real.log n) x :=
    (Real.hasStrictDerivAt_const_rpow hnpos x).hasDerivAt
  have hinv := hpow.inv (Real.rpow_pos_of_pos hnpos x).ne'
  convert hinv using 1
  · funext y
    simp [term]
  · field_simp [Real.rpow_pos_of_pos hnpos x |>.ne']

private theorem pg_hasDerivAt_logTerm (k n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    HasDerivAt (logTerm k n) (-logTerm (k + 1) n x) x := by
  have h := (pg_hasDerivAt_term n x hn).const_mul (Real.log n ^ k)
  convert h using 1
  · funext y
    simp [logTerm, term, div_eq_mul_inv]
  · simp only [logTerm, pow_succ]
    ring

private theorem pg_continuous_logTerm (k n : ℕ) (hn : 1 ≤ n) :
    Continuous (logTerm k n) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (pg_hasDerivAt_logTerm k n x hn).continuousAt

private theorem pg_summable_logTerm (a : ℝ) (k : ℕ) (ha : 1 < a) :
    Summable (fun n : ℕ => logTerm k (n + 1) a) := by
  let δ : ℝ := (a - 1) / (2 * ((k : ℝ) + 1))
  let p : ℝ := a - δ * k
  have hden : 0 < 2 * ((k : ℝ) + 1) := by positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos (sub_pos.mpr ha) hden
  have hkbound : (k : ℝ) < 2 * ((k : ℝ) + 1) := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hδden : δ * (2 * ((k : ℝ) + 1)) = a - 1 := by
    dsimp [δ]
    exact div_mul_cancel₀ (a - 1) hden.ne'
  have hδk : δ * (k : ℝ) < a - 1 := by
    calc
      δ * (k : ℝ) < δ * (2 * ((k : ℝ) + 1)) :=
        mul_lt_mul_of_pos_left hkbound hδ
      _ = a - 1 := hδden
  have hp : 1 < p := by
    dsimp [p]
    linarith
  have hbase :
      Summable (fun n : ℕ =>
        1 / Real.rpow (((n + 1 : ℕ) : ℝ)) p) := by
    convert (Real.summable_one_div_nat_add_rpow 1 p).mpr hp using 1
    funext n
    rw [abs_of_nonneg (by positivity)]
    simp [Nat.cast_add]
  have hmajor :
      Summable (fun n : ℕ =>
        δ⁻¹ ^ k * (1 / Real.rpow (((n + 1 : ℕ) : ℝ)) p)) :=
    hbase.mul_left (δ⁻¹ ^ k)
  refine hmajor.of_norm_bounded ?_
  intro n
  have hnpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hnone : (1 : ℝ) ≤ (n + 1 : ℕ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hlog0 : 0 ≤ Real.log (((n + 1 : ℕ) : ℝ)) :=
    Real.log_nonneg hnone
  have hlog :
      Real.log (((n + 1 : ℕ) : ℝ)) ≤
        Real.rpow (((n + 1 : ℕ) : ℝ)) δ / δ :=
    Real.log_natCast_le_rpow_div (n + 1) hδ
  have hpow :
      Real.log (((n + 1 : ℕ) : ℝ)) ^ k ≤
        (Real.rpow (((n + 1 : ℕ) : ℝ)) δ / δ) ^ k :=
    pow_le_pow_left₀ hlog0 hlog k
  have hdenpow : 0 ≤ Real.rpow (((n + 1 : ℕ) : ℝ)) a :=
    (Real.rpow_pos_of_pos hnpos a).le
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · calc
      Real.log (((n + 1 : ℕ) : ℝ)) ^ k /
            Real.rpow (((n + 1 : ℕ) : ℝ)) a ≤
          (Real.rpow (((n + 1 : ℕ) : ℝ)) δ / δ) ^ k /
            Real.rpow (((n + 1 : ℕ) : ℝ)) a :=
        div_le_div_of_nonneg_right hpow hdenpow
      _ = δ⁻¹ ^ k *
          (1 / Real.rpow (((n + 1 : ℕ) : ℝ)) p) := by
        dsimp [p]
        rw [div_pow, ← Real.rpow_mul_natCast hnpos.le δ k,
          Real.rpow_sub hnpos]
        field_simp [hδ.ne', (Real.rpow_pos_of_pos hnpos _).ne']
        rw [← mul_pow]
        simp [hδ.ne']
  · exact div_nonneg (pow_nonneg hlog0 k) hdenpow

private theorem pg_logTerm_nonneg (k n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    0 ≤ logTerm k n x := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_nonneg (pow_nonneg (Real.log_nonneg hnone) k)
    (Real.rpow_pos_of_pos hnpos x).le

private theorem pg_logTerm_antitone
    (k n : ℕ) (a x : ℝ) (hn : 1 ≤ n) (hax : a ≤ x) :
    logTerm k n x ≤ logTerm k n a := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hrpow : Real.rpow n a ≤ Real.rpow n x :=
    Real.rpow_le_rpow_of_exponent_le hnone hax
  exact div_le_div_of_nonneg_left (pow_nonneg (Real.log_nonneg hnone) k)
    (Real.rpow_pos_of_pos hnpos a) hrpow

private theorem pg_continuousOn_logTsum (a : ℝ) (k : ℕ) (ha : 1 < a) :
    ContinuousOn (fun x => ∑' n : ℕ, logTerm k (n + 1) x) (Set.Ici a) := by
  apply continuousOn_tsum
      (fun n => (pg_continuous_logTerm k (n + 1) (by omega)).continuousOn)
      (pg_summable_logTerm a k ha)
  intro n x hx
  rw [Real.norm_eq_abs, abs_of_nonneg
    (pg_logTerm_nonneg k (n + 1) x (by omega))]
  exact pg_logTerm_antitone k (n + 1) a x (by omega) hx

private theorem pg_hasDerivAt_logTsum (k : ℕ) (x : ℝ) (hx : 1 < x) :
    HasDerivAt (fun y => ∑' n : ℕ, logTerm k (n + 1) y)
      (-(∑' n : ℕ, logTerm (k + 1) (n + 1) x)) x := by
  let a : ℝ := (x + 1) / 2
  have ha : 1 < a := by
    dsimp [a]
    linarith
  have hax : a < x := by
    dsimp [a]
    linarith
  have hu := pg_summable_logTerm a (k + 1) ha
  have hderiv :
      ∀ n y, y ∈ Set.Ioi a →
        HasDerivAt (logTerm k (n + 1))
          (-logTerm (k + 1) (n + 1) y) y := by
    intro n y hy
    exact pg_hasDerivAt_logTerm k (n + 1) y (by omega)
  have hbound :
      ∀ n y, y ∈ Set.Ioi a →
        ‖-logTerm (k + 1) (n + 1) y‖ ≤
          logTerm (k + 1) (n + 1) a := by
    intro n y hy
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg
      (pg_logTerm_nonneg (k + 1) (n + 1) y (by omega))]
    exact pg_logTerm_antitone (k + 1) (n + 1) a y (by omega) hy.le
  have h :=
    hasDerivAt_tsum_of_isPreconnected
      (g := fun n y => logTerm k (n + 1) y)
      (g' := fun n y => -logTerm (k + 1) (n + 1) y)
      hu isOpen_Ioi isPreconnected_Ioi hderiv hbound
      (show x ∈ Set.Ioi a from hax)
      (pg_summable_logTerm x k hx)
      (show x ∈ Set.Ioi a from hax)
  simpa only [tsum_neg] using h

theorem gap1 (x : ℝ) (hx : 1 < x) :
    Summable (fun n : ℕ => term (n + 1) x) := by
  simpa [logTerm, term] using pg_summable_logTerm x 0 hx

theorem gap2 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    HasDerivAt (term n) (-Real.log n / Real.rpow n x) x := by
  exact pg_hasDerivAt_term n x hn

theorem gap3 (a x : ℝ) (n : ℕ) (ha : 1 < a) (hax : a ≤ x)
    (hn : 1 ≤ n) :
    0 ≤ Real.log n / Real.rpow n x := by
  simpa [logTerm] using pg_logTerm_nonneg 1 n x hn

theorem gap4 (a x : ℝ) (n : ℕ) (ha : 1 < a) (hax : a ≤ x)
    (hn : 1 ≤ n) :
    Real.log n / Real.rpow n x ≤ Real.log n / Real.rpow n a := by
  simpa [logTerm] using pg_logTerm_antitone 1 n a x hn hax

theorem gap5 (a : ℝ) (n : ℕ) (ha : 1 < a) (hn : 1 ≤ n) :
    0 ≤ Real.log n / Real.rpow n a := by
  simpa [logTerm] using pg_logTerm_nonneg 1 n a hn

theorem gap6 (a : ℝ) (ha : 1 < a) :
    Summable (fun n : ℕ => logTerm 1 (n + 1) a) := by
  exact pg_summable_logTerm a 1 ha

theorem gap7 (a : ℝ) (ha : 1 < a) :
    SeriesUniformlyConvergesOn
      (fun n x => logTerm 1 (n + 1) x)
      (Set.Ici a)
      (fun x => ∑' n : ℕ, logTerm 1 (n + 1) x) := by
  have hu : TendstoUniformlyOn
      (fun N x => ∑ n ∈ Finset.range N, logTerm 1 (n + 1) x)
      (fun x => ∑' n : ℕ, logTerm 1 (n + 1) x)
      atTop (Set.Ici a) := by
    apply tendstoUniformlyOn_tsum_nat_eventually
      (pg_summable_logTerm a 1 ha)
    filter_upwards with n x hx
    rw [Real.norm_eq_abs, abs_of_nonneg
      (pg_logTerm_nonneg 1 (n + 1) x (by omega))]
    exact pg_logTerm_antitone 1 (n + 1) a x (by omega)
      (show a ≤ x from hx)
  rw [Metric.tendstoUniformlyOn_iff] at hu
  intro ε hε
  rcases Filter.eventually_atTop.1 (hu ε hε) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn x hx
  have hn' : N ≤ n + 1 := le_trans hn (Nat.le_succ n)
  simpa [Real.dist_eq, abs_sub_comm] using hN (n + 1) hn' x hx

theorem gap8 (x : ℝ) (hx : 1 < x) :
    HasDerivAt zeta (derivativeSum x) x := by
  have h := pg_hasDerivAt_logTsum 0 x hx
  unfold derivativeSum
  convert h using 1

theorem gap9 (a : ℝ) (ha : 1 < a) :
    ContinuousOn derivativeSum (Set.Ici a) := by
  simpa [derivativeSum] using
    (pg_continuousOn_logTsum a 1 ha).neg

theorem gap10 :
    ContinuousOn derivativeSum (Set.Ioi (1 : ℝ)) := by
  intro x hx
  have hx' : 1 < x := hx
  let a : ℝ := (x + 1) / 2
  have ha : 1 < a := by
    dsimp [a]
    linarith
  have hax : a < x := by
    dsimp [a]
    linarith
  have hcont : ContinuousOn derivativeSum (Set.Ioi a) :=
    (gap9 a ha).mono Set.Ioi_subset_Ici_self
  exact (hcont.continuousAt (isOpen_Ioi.mem_nhds hax)).continuousWithinAt

theorem gap11 :
    ContinuousOn zeta (Set.Ioi (1 : ℝ)) := by
  intro x hx
  exact (gap8 x hx).continuousAt.continuousWithinAt

theorem gap12 (a : ℝ) (k : ℕ) (ha : 1 < a) :
    Summable (fun n : ℕ => logTerm k (n + 1) a) := by
  exact pg_summable_logTerm a k ha

theorem gap13 (x : ℝ) (k : ℕ) (hx : 1 < x) :
    iteratedDeriv k zeta x =
      (-1 : ℝ) ^ k * (∑' n : ℕ, logTerm k (n + 1) x) := by
  induction k generalizing x with
  | zero =>
      simp [zeta, logTerm, term]
  | succ k ih =>
      have hsum := pg_hasDerivAt_logTsum k x hx
      have hscaled :=
        hsum.const_mul ((-1 : ℝ) ^ k)
      have hscaled' :
          HasDerivAt
            (fun y => (-1 : ℝ) ^ k *
              (∑' n : ℕ, logTerm k (n + 1) y))
            ((-1 : ℝ) ^ (k + 1) *
              (∑' n : ℕ, logTerm (k + 1) (n + 1) x)) x := by
        convert hscaled using 1
        simp [pow_succ]
      have heq :
          iteratedDeriv k zeta =ᶠ[nhds x]
            (fun y => (-1 : ℝ) ^ k *
              (∑' n : ℕ, logTerm k (n + 1) y)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
        exact ih y hy
      rw [iteratedDeriv_succ]
      exact (hscaled'.congr_of_eventuallyEq heq).deriv

theorem gap14 (k : ℕ) :
    ContinuousOn (iteratedDeriv k zeta) (Set.Ioi (1 : ℝ)) := by
  intro x hx
  have hx' : 1 < x := hx
  let a : ℝ := (x + 1) / 2
  have ha : 1 < a := by
    dsimp [a]
    linarith
  have hax : a < x := by
    dsimp [a]
    linarith
  have hcontSum :
      ContinuousOn
        (fun y => (-1 : ℝ) ^ k *
          (∑' n : ℕ, logTerm k (n + 1) y))
        (Set.Ioi a) := by
    exact (continuousOn_const.mul
      ((pg_continuousOn_logTsum a k ha).mono
        Set.Ioi_subset_Ici_self))
  have hcontAt :
      ContinuousAt
        (fun y => (-1 : ℝ) ^ k *
          (∑' n : ℕ, logTerm k (n + 1) y)) x :=
    hcontSum.continuousAt (isOpen_Ioi.mem_nhds hax)
  have heq :
      iteratedDeriv k zeta =ᶠ[nhds x]
        (fun y => (-1 : ℝ) ^ k *
          (∑' n : ℕ, logTerm k (n + 1) y)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact gap13 y k hy
  exact (hcontAt.congr_of_eventuallyEq heq).continuousWithinAt

theorem gap15 :
    ContinuousOn zeta (Set.Ioi (1 : ℝ)) ∧
    ∀ k : ℕ, ContinuousOn (iteratedDeriv k zeta) (Set.Ioi (1 : ℝ)) := by
  exact ⟨gap11, gap14⟩

end

end ProofGap.Exercise2797
