import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2827

noncomputable section

open Filter
open scoped BigOperators Topology

def harmonicCoefficient (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ)

def powerTerm (n : ℕ) (x : ℝ) : ℝ :=
  harmonicCoefficient n * x ^ n

def SeriesConvergesAt (x : ℝ) : Prop :=
  Summable (fun k : ℕ => powerTerm (k + 1) x)

def HasConvergenceRadiusOne : Prop :=
  (∀ x : ℝ, |x| < 1 → SeriesConvergesAt x) ∧
    (∀ x : ℝ, 1 < |x| → ¬ SeriesConvergesAt x)

private theorem harmonicCoefficient_succ (n : ℕ) :
    harmonicCoefficient (n + 1) =
      harmonicCoefficient n + 1 / ((n + 1 : ℕ) : ℝ) := by
  unfold harmonicCoefficient
  have hset :
      Finset.Icc 1 (n + 1) =
        insert (n + 1) (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : n + 1 ∉ Finset.Icc 1 n := by
    simp
  rw [hset, Finset.sum_insert hnot]
  exact add_comm _ _

private theorem harmonicCoefficient_nonneg (n : ℕ) :
    0 ≤ harmonicCoefficient n := by
  unfold harmonicCoefficient
  apply Finset.sum_nonneg
  intro k hk
  exact div_nonneg zero_le_one (Nat.cast_nonneg k)

private theorem harmonicCoefficient_one_le (n : ℕ) :
    1 ≤ harmonicCoefficient (n + 1) := by
  induction n with
  | zero => norm_num [harmonicCoefficient]
  | succ n ih =>
      rw [harmonicCoefficient_succ]
      exact ih.trans
        (le_add_of_nonneg_right
          (div_nonneg zero_le_one (Nat.cast_nonneg _)))

private theorem harmonicCoefficient_le_nat (n : ℕ) :
    harmonicCoefficient n ≤ (n : ℝ) := by
  induction n with
  | zero => simp [harmonicCoefficient]
  | succ n ih =>
      have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hcast : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hfrac : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ 1 := by
        apply (div_le_iff₀ hpos).2
        simpa using hcast
      calc
        harmonicCoefficient (Nat.succ n) =
            harmonicCoefficient n + 1 / ((n + 1 : ℕ) : ℝ) := by
          simpa [Nat.succ_eq_add_one] using harmonicCoefficient_succ n
        _ ≤ (n : ℝ) + 1 := add_le_add ih hfrac
        _ = (Nat.succ n : ℝ) := by norm_num

private theorem harmonicCoefficient_add_lower
    (m r k : ℕ) (hm : 0 < m) (hk : k ≤ r) :
    harmonicCoefficient m +
        (k : ℝ) / ((m + r : ℕ) : ℝ) ≤
      harmonicCoefficient (m + k) := by
  revert hk
  induction k with
  | zero =>
      intro hk
      simp
  | succ k ih =>
      intro hk
      have hk' : k ≤ r := by omega
      have hmr : 0 < m + r := by omega
      have hcur : 0 < m + k + 1 := by omega
      have hmr_pos : (0 : ℝ) < ((m + r : ℕ) : ℝ) := by
        exact_mod_cast hmr
      have hcur_pos : (0 : ℝ) < ((m + k + 1 : ℕ) : ℝ) := by
        exact_mod_cast hcur
      have hden_le :
          ((m + k + 1 : ℕ) : ℝ) ≤ ((m + r : ℕ) : ℝ) := by
        exact_mod_cast (show m + k + 1 ≤ m + r by omega)
      have hfrac :
          (1 : ℝ) / ((m + r : ℕ) : ℝ) ≤
            1 / ((m + k + 1 : ℕ) : ℝ) := by
        apply (div_le_div_iff₀ hmr_pos hcur_pos).2
        simpa only [one_mul] using hden_le
      have hcast_succ :
          ((Nat.succ k : ℕ) : ℝ) / ((m + r : ℕ) : ℝ) =
            (k : ℝ) / ((m + r : ℕ) : ℝ) +
              (1 : ℝ) / ((m + r : ℕ) : ℝ) := by
        rw [Nat.cast_succ, add_div]
      calc
        harmonicCoefficient m +
              ((Nat.succ k : ℕ) : ℝ) / ((m + r : ℕ) : ℝ) =
            (harmonicCoefficient m +
                (k : ℝ) / ((m + r : ℕ) : ℝ)) +
              (1 : ℝ) / ((m + r : ℕ) : ℝ) := by
          rw [hcast_succ]
          ring
        _ ≤ harmonicCoefficient (m + k) +
              1 / ((m + k + 1 : ℕ) : ℝ) :=
          add_le_add (ih hk') hfrac
        _ = harmonicCoefficient (m + Nat.succ k) := by
          exact (harmonicCoefficient_succ (m + k)).symm

private theorem harmonicCoefficient_double_lower
    (m : ℕ) (hm : 0 < m) :
    harmonicCoefficient m + (1 : ℝ) / 2 ≤
      harmonicCoefficient (m + m) := by
  have h :=
    harmonicCoefficient_add_lower m m m hm (le_refl m)
  have hm_pos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast hm
  have hfrac :
      (m : ℝ) / ((m + m : ℕ) : ℝ) = (1 : ℝ) / 2 := by
    rw [Nat.cast_add]
    apply (div_eq_iff (ne_of_gt (add_pos hm_pos hm_pos))).2
    ring
  rw [hfrac] at h
  exact h

private theorem harmonicCoefficient_pow_two_lower (r : ℕ) :
    1 + (r : ℝ) / 2 ≤ harmonicCoefficient ((2 : ℕ) ^ r) := by
  induction r with
  | zero =>
      norm_num [harmonicCoefficient]
  | succ r ih =>
      have hp : 0 < (2 : ℕ) ^ r := by positivity
      have hblock :=
        harmonicCoefficient_double_lower ((2 : ℕ) ^ r) hp
      have hpow :
          (2 : ℕ) ^ Nat.succ r = 2 ^ r + 2 ^ r := by
        simp [pow_succ, mul_two]
      rw [hpow]
      rw [Nat.cast_succ]
      linarith

private theorem harmonicCoefficient_mono_of_pos
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    harmonicCoefficient m ≤ harmonicCoefficient n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hbound :=
    harmonicCoefficient_add_lower m k k hm (le_refl k)
  have hfrac :
      0 ≤ (k : ℝ) / ((m + k : ℕ) : ℝ) :=
    div_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg (m + k))
  exact (le_add_of_nonneg_right hfrac).trans hbound

private theorem harmonicCoefficient_tendsto_atTop :
    Tendsto harmonicCoefficient atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  obtain ⟨r, hr⟩ := exists_nat_gt (2 * (b - 1))
  have hbr : b ≤ 1 + (r : ℝ) / 2 := by
    linarith
  have hp : 0 < (2 : ℕ) ^ r := by positivity
  refine eventually_atTop.2 ⟨(2 : ℕ) ^ r, ?_⟩
  intro n hn
  exact hbr.trans
    ((harmonicCoefficient_pow_two_lower r).trans
      (harmonicCoefficient_mono_of_pos hp hn))

private theorem seriesConvergesAt_of_abs_lt_one :
    ∀ x : ℝ, |x| < 1 → SeriesConvergesAt x := by
  intro x hx
  let r : ℝ := |x|
  have hr_nonneg : 0 ≤ r := by simp [r]
  have hrnorm : ‖r‖ < 1 := by
    simpa [r, Real.norm_eq_abs, abs_of_nonneg (abs_nonneg x)] using hx
  have hs0 : Summable (fun k : ℕ => r ^ k) :=
    summable_geometric_of_norm_lt_one hrnorm
  have hs1 : Summable (fun k : ℕ => (k : ℝ) * r ^ k) := by
    simpa using
      (summable_pow_mul_geometric_of_norm_lt_one (k := 1) hrnorm)
  have hmajor : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * r ^ k) := by
    simpa [Nat.cast_add, Nat.cast_one, add_mul] using hs1.add hs0
  unfold SeriesConvergesAt
  refine Summable.of_norm_bounded
    (g := fun k : ℕ => ((k + 1 : ℕ) : ℝ) * r ^ k) hmajor ?_
  intro k
  have hcoeff :
      harmonicCoefficient (k + 1) ≤ ((k + 1 : ℕ) : ℝ) :=
    harmonicCoefficient_le_nat (k + 1)
  have hrpow : r ^ (k + 1) ≤ r ^ k := by
    rw [pow_succ]
    calc
      r ^ k * r ≤ r ^ k * 1 :=
        mul_le_mul_of_nonneg_left (le_of_lt hx) (pow_nonneg hr_nonneg k)
      _ = r ^ k := mul_one _
  rw [Real.norm_eq_abs]
  change |harmonicCoefficient (k + 1) * x ^ (k + 1)| ≤
    ((k + 1 : ℕ) : ℝ) * r ^ k
  rw [abs_mul, abs_pow, abs_of_nonneg (harmonicCoefficient_nonneg (k + 1))]
  change harmonicCoefficient (k + 1) * r ^ (k + 1) ≤
    ((k + 1 : ℕ) : ℝ) * r ^ k
  calc
    harmonicCoefficient (k + 1) * r ^ (k + 1) ≤
        ((k + 1 : ℕ) : ℝ) * r ^ (k + 1) :=
      mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hr_nonneg _)
    _ ≤ ((k + 1 : ℕ) : ℝ) * r ^ k :=
      mul_le_mul_of_nonneg_left hrpow (by positivity)

private theorem not_seriesConvergesAt_of_one_le_abs
    (x : ℝ) (hx : 1 ≤ |x|) : ¬ SeriesConvergesAt x := by
  intro hs
  have ht :
      Tendsto (fun k : ℕ => powerTerm (k + 1) x) atTop (𝓝 0) :=
    hs.tendsto_atTop_zero
  have habs :
      Tendsto (fun k : ℕ => |powerTerm (k + 1) x|) atTop (𝓝 0) := by
    simpa using ht.abs
  have hev : ∀ᶠ k : ℕ in atTop, |powerTerm (k + 1) x| < 1 :=
    (tendsto_order.1 habs).2 1 zero_lt_one
  rcases (eventually_atTop.1 hev) with ⟨N, hN⟩
  have hk := hN N (le_refl N)
  have hpow_all : ∀ m : ℕ, 1 ≤ |x| ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        have hmul : (1 : ℝ) * 1 ≤ |x| ^ m * |x| :=
          mul_le_mul ih hx zero_le_one (zero_le_one.trans ih)
        simpa [pow_succ] using hmul
  have hterm : 1 ≤ |powerTerm (N + 1) x| := by
    rw [powerTerm, abs_mul, abs_pow,
      abs_of_nonneg (harmonicCoefficient_nonneg (N + 1))]
    have hc : (1 : ℝ) ≤ harmonicCoefficient (N + 1) :=
      harmonicCoefficient_one_le N
    have hp : (1 : ℝ) ≤ |x| ^ (N + 1) := hpow_all (N + 1)
    have hmul :
        (1 : ℝ) * 1 ≤
          harmonicCoefficient (N + 1) * |x| ^ (N + 1) :=
      mul_le_mul hc hp zero_le_one (zero_le_one.trans hc)
    simpa using hmul
  exact (not_lt_of_ge hterm) hk

theorem gap1 :
    Tendsto
      (fun n : ℕ =>
        |harmonicCoefficient (n + 1) / harmonicCoefficient (n + 2)|)
      atTop (𝓝 1) := by
  have hzero' :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hzero :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 0) := by
    simpa [Nat.cast_add, Nat.cast_one] using hzero'
  have hone :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := by
    exact tendsto_const_nhds
  have hlower :
      Tendsto (fun n : ℕ => 1 - (1 : ℝ) / ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 1) := by
    simpa using hone.sub hzero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hone ?_ ?_
  · intro n
    let a : ℝ := harmonicCoefficient (n + 1)
    let b : ℝ := harmonicCoefficient (n + 2)
    let d : ℝ := (1 : ℝ) / ((n + 2 : ℕ) : ℝ)
    let q : ℝ := (1 : ℝ) / ((n + 1 : ℕ) : ℝ)
    have ha : 1 ≤ a := by
      simpa [a] using harmonicCoefficient_one_le n
    have ha_pos : 0 < a := lt_of_lt_of_le zero_lt_one ha
    have ha_nonneg : 0 ≤ a := le_trans zero_le_one ha
    have hd : 0 ≤ d := by positivity
    have hb_rec : b = a + d := by
      simpa [a, b, d, Nat.add_assoc] using
        harmonicCoefficient_succ (n + 1)
    have hb_pos : 0 < b := by
      rw [hb_rec]
      linarith
    have hb_nonneg : 0 ≤ b := le_of_lt hb_pos
    have hdq : d ≤ q := by
      dsimp [d, q]
      rw [div_le_div_iff₀
        (by positivity : (0 : ℝ) < ((n + 2 : ℕ) : ℝ))
        (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))]
      norm_num [Nat.cast_add, Nat.cast_one]
    have hratio_nonneg : 0 ≤ a / b :=
      div_nonneg ha_nonneg hb_nonneg
    have hratio_lower : 1 - d ≤ a / b := by
      apply (le_div_iff₀ hb_pos).2
      rw [hb_rec]
      have hp : 0 ≤ d * (a + d - 1) := by
        apply mul_nonneg hd
        linarith
      nlinarith
    change 1 - q ≤ |a / b|
    rw [abs_of_nonneg hratio_nonneg]
    linarith
  · intro n
    let a : ℝ := harmonicCoefficient (n + 1)
    let b : ℝ := harmonicCoefficient (n + 2)
    let d : ℝ := (1 : ℝ) / ((n + 2 : ℕ) : ℝ)
    have ha : 1 ≤ a := by
      simpa [a] using harmonicCoefficient_one_le n
    have ha_nonneg : 0 ≤ a := le_trans zero_le_one ha
    have hd : 0 ≤ d := by positivity
    have hb_rec : b = a + d := by
      simpa [a, b, d, Nat.add_assoc] using
        harmonicCoefficient_succ (n + 1)
    have hb_pos : 0 < b := by
      rw [hb_rec]
      linarith
    have hb_nonneg : 0 ≤ b := le_of_lt hb_pos
    have hratio_nonneg : 0 ≤ a / b :=
      div_nonneg ha_nonneg hb_nonneg
    change |a / b| ≤ (1 : ℝ)
    rw [abs_of_nonneg hratio_nonneg]
    apply (div_le_iff₀ hb_pos).2
    simpa [hb_rec] using (le_add_of_nonneg_right hd : a ≤ a + d)

theorem gap2 :
    HasConvergenceRadiusOne := by
  constructor
  · exact seriesConvergesAt_of_abs_lt_one
  · intro x hx
    exact not_seriesConvergesAt_of_one_le_abs x (le_of_lt hx)

theorem gap3 :
    ∀ x : ℝ, |x| < 1 → SeriesConvergesAt x := by
  exact gap2.1

theorem gap4 :
    Tendsto harmonicCoefficient atTop atTop := by
  exact harmonicCoefficient_tendsto_atTop

theorem gap5 :
    ∀ x : ℝ, |x| = 1 → ¬ SeriesConvergesAt x := by
  intro x hx
  apply not_seriesConvergesAt_of_one_le_abs x
  exact le_of_eq hx.symm

theorem gap6 :
    ∀ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 1 ↔ SeriesConvergesAt x := by
  intro x
  constructor
  · intro hx
    apply gap3 x
    exact (abs_lt).2 hx
  · intro hs
    have hle : |x| ≤ 1 := by
      apply le_of_not_gt
      intro hx
      exact (gap2.2 x hx) hs
    have hne : |x| ≠ 1 := by
      intro hx
      exact (gap5 x hx) hs
    have hlt : |x| < 1 := lt_of_le_of_ne hle hne
    exact (abs_lt).1 hlt

end

end ProofGap.Exercise2827
