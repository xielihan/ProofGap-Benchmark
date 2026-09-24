import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise2917

noncomputable section

open Filter
open scoped BigOperators Topology

def coefficient (n : ℕ) : ℂ :=
  ((1 : ℂ) + Complex.I) ^ n /
    ((n : ℂ) * ((n + 1 : ℕ) : ℂ))

def ratioSeq (n : ℕ) : ℝ :=
  ‖coefficient n / coefficient (n + 1)‖

def seriesTerm (n : ℕ) (z : ℂ) : ℂ :=
  (((1 : ℂ) + Complex.I) ^ n * z ^ n) /
    (((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ))

def SeriesConvergesAt (z : ℂ) : Prop :=
  Summable (fun k : ℕ => seriesTerm (k + 1) z)

def convergenceSet : Set ℂ :=
  {z | SeriesConvergesAt z}

def closedDisk : Set ℂ :=
  {z | ‖z‖ ≤ 1 / Real.sqrt 2}

def openDisk : Set ℂ :=
  {z | ‖z‖ < 1 / Real.sqrt 2}

def coordinateOpenDisk : Set ℂ :=
  {z | z.re ^ 2 + z.im ^ 2 < 1 / 2}

def coordinateClosedDisk : Set ℂ :=
  {z | z.re ^ 2 + z.im ^ 2 ≤ 1 / 2}

private theorem summable_weighted_powers {w : ℂ} (hw : ‖w‖ ≤ 1) :
    Summable (fun n : ℕ =>
      w ^ (n + 1) /
        (((n + 2 : ℕ) : ℂ) * ((n + 3 : ℕ) : ℂ))) := by
  have hp0 : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) := by
    first
    | simpa [one_div, Real.rpow_natCast, inv_pow] using
        (Real.summable_nat_rpow_inv
          (p := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2))
    | simpa [one_div, Real.rpow_natCast, inv_pow] using
        ((Real.summable_nat_rpow_inv (p := (2 : ℝ))).2
          (by norm_num : (1 : ℝ) < 2))
  have hi : Function.Injective (fun n : ℕ => n + 2) := by
    intro m n h
    exact Nat.add_right_cancel h
  have hp :
      Summable (fun n : ℕ => 1 / (((n + 2 : ℕ) : ℝ) ^ 2)) := by
    simpa only [Function.comp_apply] using hp0.comp_injective hi
  refine hp.of_norm_bounded (fun n => ?_)
  have hpow : ‖w‖ ^ (n + 1) ≤ 1 :=
    pow_le_one₀ (norm_nonneg w) hw
  have hDpos :
      0 < ((n + 2 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ) := by
    positivity
  have hXpos : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
  have hbound :
      ‖w ^ (n + 1) /
          (((n + 2 : ℕ) : ℂ) * ((n + 3 : ℕ) : ℂ))‖ ≤
        1 / (((n + 2 : ℕ) : ℝ) ^ 2) := by
    rw [norm_div, norm_pow, norm_mul]
    simp only [Complex.norm_natCast]
    calc
      ‖w‖ ^ (n + 1) /
            (((n + 2 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ)) ≤
          1 / (((n + 2 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right hpow hDpos.le
      _ ≤ 1 / (((n + 2 : ℕ) : ℝ) ^ 2) := by
        apply (div_le_div_iff₀ hDpos (sq_pos_of_pos hXpos)).2
        norm_num [Nat.cast_add]
        nlinarith
  have hmaj : 0 ≤ 1 / (((n + 2 : ℕ) : ℝ) ^ 2) := by positivity
  simpa [Real.norm_eq_abs, abs_of_nonneg hmaj] using hbound

private theorem not_summable_weighted_powers {w : ℂ} (hw : 1 < ‖w‖) :
    ¬ Summable (fun n : ℕ =>
      w ^ (n + 1) /
        (((n + 2 : ℕ) : ℂ) * ((n + 3 : ℕ) : ℂ))) := by
  let f : ℕ → ℂ := fun n =>
    w ^ (n + 1) /
      (((n + 2 : ℕ) : ℂ) * ((n + 3 : ℕ) : ℂ))
  have hw0 : w ≠ 0 := by
    intro h
    subst w
    norm_num at hw
  have hq : 0 < ‖w‖ - 1 := sub_pos.2 hw
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / (‖w‖ - 1))
  have hstep : ∀ᶠ n : ℕ in atTop, ‖f n‖ ≤ ‖f (n + 1)‖ := by
    refine (eventually_ge_atTop N).mono ?_
    intro n hn
    have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hN' : 2 < (‖w‖ - 1) * (N : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ hq).1 hN
    have hprod :
        (‖w‖ - 1) * (N : ℝ) ≤ (‖w‖ - 1) * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hn' hq.le
    have htwo :
        2 < (‖w‖ - 1) * (((n + 2 : ℕ) : ℝ)) := by
      norm_num [Nat.cast_add]
      nlinarith
    have hcross :
        ((n + 4 : ℕ) : ℝ) ≤ ‖w‖ * ((n + 2 : ℕ) : ℝ) := by
      norm_num [Nat.cast_add] at htwo ⊢
      nlinarith
    have hnorm (m : ℕ) :
        ‖f m‖ =
          ‖w‖ ^ (m + 1) /
            (((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ)) := by
      simp only [f, norm_div, norm_pow, norm_mul, Complex.norm_natCast]
    rw [hnorm n, hnorm (n + 1)]
    norm_num [Nat.cast_add]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hfac :
        0 ≤ ‖w‖ ^ (n + 1) * ((n + 3 : ℕ) : ℝ) := by
      positivity
    have hm := mul_le_mul_of_nonneg_left hcross hfac
    convert hm using 1 <;>
      norm_num [Nat.cast_add, pow_succ] <;>
      ring
  intro hs
  obtain ⟨M, hM⟩ := eventually_atTop.1 hstep
  have hlower : ∀ n, M ≤ n → ‖f M‖ ≤ ‖f n‖ := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih => exact ih.trans (hM n hn)
  have hfM : f M ≠ 0 := by
    dsimp [f]
    apply div_ne_zero (pow_ne_zero _ hw0)
    apply mul_ne_zero
    · exact_mod_cast (show M + 2 ≠ 0 by omega)
    · exact_mod_cast (show M + 3 ≠ 0 by omega)
  have hfMpos : 0 < ‖f M‖ := norm_pos_iff.2 hfM
  have hfzero : Tendsto f atTop (𝓝 (0 : ℂ)) := by
    simpa only [f] using hs.tendsto_atTop_zero
  have hnormzero : Tendsto (fun n : ℕ => ‖f n‖) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, norm_zero] using hfzero.norm
  have hlt : ∀ᶠ n : ℕ in atTop, ‖f n‖ < ‖f M‖ :=
    (tendsto_order.1 hnormzero).2 _ hfMpos
  obtain ⟨K, hK⟩ := eventually_atTop.1 hlt
  let n := max M K
  have hnM : M ≤ n := Nat.le_max_left M K
  have hnK : K ≤ n := Nat.le_max_right M K
  exact (not_lt_of_ge (hlower n hnM)) (hK n hnK)

theorem gap1 :
    Tendsto ratioSeq atTop
      (𝓝 (1 / ‖(1 : ℂ) + Complex.I‖)) := by
  let a : ℂ := (1 : ℂ) + Complex.I
  have ha : a ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [a] at hr
  have hratio :
      ∀ᶠ n : ℕ in atTop,
        ratioSeq n = (1 + 2 / (n : ℝ)) / ‖a‖ := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    have hn1 : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (by omega : n + 1 ≠ 0)
    have hn2 : ((n + 2 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (by omega : n + 2 ≠ 0)
    have hquot :
        coefficient n / coefficient (n + 1) =
          (((n + 2 : ℕ) : ℂ) / (n : ℂ)) / a := by
      unfold coefficient
      change
        a ^ n / ((n : ℂ) * ((n + 1 : ℕ) : ℂ)) /
            (a ^ (n + 1) /
              (((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ))) = _
      rw [pow_succ]
      field_simp [ha, hn0, hn1, hn2] <;> ring
    have hn0r : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    unfold ratioSeq
    rw [hquot]
    simp only [norm_div, Complex.norm_natCast]
    rw [Nat.cast_add, Nat.cast_ofNat]
    congr 1
    field_simp [hn0r]
  have hcast :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hzero :
      Tendsto (fun n : ℕ => (2 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hcast
  have hmain :
      Tendsto (fun n : ℕ => (1 + 2 / (n : ℝ)) / ‖a‖) atTop
        (𝓝 (1 / ‖a‖)) := by
    convert (tendsto_const_nhds.add hzero).div_const ‖a‖ using 1 <;>
      norm_num
  apply hmain.congr'
  filter_upwards [hratio] with n hn
  exact hn.symm

theorem gap2 :
    (1 / ‖(1 : ℂ) + Complex.I‖ : ℝ) =
      1 / Real.sqrt 2 := by
  norm_num [Complex.norm_def, Complex.normSq_apply]

theorem gap3 :
    Tendsto ratioSeq atTop (𝓝 (1 / Real.sqrt 2)) := by
  simpa only [gap2] using gap1

theorem gap4 :
    ∃ R : ℝ, R = 1 / Real.sqrt 2 := by
  exact ⟨1 / Real.sqrt 2, rfl⟩

theorem gap5 :
    convergenceSet = closedDisk := by
  ext z
  simp only [convergenceSet, closedDisk, Set.mem_setOf_eq,
    SeriesConvergesAt]
  have ha : ‖(1 : ℂ) + Complex.I‖ = Real.sqrt 2 := by
    norm_num [Complex.norm_def, Complex.normSq_apply]
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt0 : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt
  constructor
  · intro hs
    by_contra hz
    have hz' : 1 / Real.sqrt 2 < ‖z‖ := lt_of_not_ge hz
    have hbase : 1 < ‖((1 : ℂ) + Complex.I) * z‖ := by
      rw [norm_mul, ha]
      calc
        1 = Real.sqrt 2 * (1 / Real.sqrt 2) := by
          field_simp
        _ < Real.sqrt 2 * ‖z‖ :=
          mul_lt_mul_of_pos_left hz' hsqrt
    apply not_summable_weighted_powers hbase
    simpa [seriesTerm, mul_pow, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hs
  · intro hz
    have hbase : ‖((1 : ℂ) + Complex.I) * z‖ ≤ 1 := by
      rw [norm_mul, ha]
      calc
        Real.sqrt 2 * ‖z‖ ≤
            Real.sqrt 2 * (1 / Real.sqrt 2) :=
          mul_le_mul_of_nonneg_left hz hsqrt.le
        _ = 1 := by field_simp
    simpa [seriesTerm, mul_pow, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using summable_weighted_powers hbase

theorem gap6 :
    openDisk = coordinateOpenDisk := by
  ext z
  simp only [openDisk, coordinateOpenDisk, Set.mem_setOf_eq]
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hrnonneg : 0 ≤ (1 / Real.sqrt 2 : ℝ) :=
    (one_div_pos.2 hsqrt).le
  have hsquare : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
    have hsq : (Real.sqrt 2) ^ 2 = 2 :=
      Real.sq_sqrt (by norm_num)
    field_simp [ne_of_gt hsqrt]
    nlinarith
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    calc
      ‖z‖ ^ 2 = Complex.normSq z := Complex.sq_norm z
      _ = z.re ^ 2 + z.im ^ 2 := by
        rw [Complex.normSq_apply]
        ring
  have hznonneg : 0 ≤ ‖z‖ := norm_nonneg z
  constructor
  · intro h
    have hsq_lt :
        ‖z‖ * ‖z‖ <
          (1 / Real.sqrt 2) * (1 / Real.sqrt 2) :=
      (mul_le_mul_of_nonneg_left h.le hznonneg).trans_lt
        (mul_lt_mul_of_pos_right h (one_div_pos.2 hsqrt))
    nlinarith
  · intro h
    by_contra hz
    have hrle : 1 / Real.sqrt 2 ≤ ‖z‖ := le_of_not_gt hz
    have hsq_le :
        (1 / Real.sqrt 2) * (1 / Real.sqrt 2) ≤ ‖z‖ * ‖z‖ :=
      (mul_le_mul_of_nonneg_right hrle hrnonneg).trans
        (mul_le_mul_of_nonneg_left hrle hznonneg)
    nlinarith

theorem gap7 :
    convergenceSet = coordinateClosedDisk := by
  rw [gap5]
  ext z
  simp only [closedDisk, coordinateClosedDisk, Set.mem_setOf_eq]
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hrnonneg : 0 ≤ (1 / Real.sqrt 2 : ℝ) :=
    (one_div_pos.2 hsqrt).le
  have hsquare : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
    have hsq : (Real.sqrt 2) ^ 2 = 2 :=
      Real.sq_sqrt (by norm_num)
    field_simp [ne_of_gt hsqrt]
    nlinarith
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    calc
      ‖z‖ ^ 2 = Complex.normSq z := Complex.sq_norm z
      _ = z.re ^ 2 + z.im ^ 2 := by
        rw [Complex.normSq_apply]
        ring
  have hznonneg : 0 ≤ ‖z‖ := norm_nonneg z
  constructor
  · intro h
    have hsq_le :
        ‖z‖ * ‖z‖ ≤
          (1 / Real.sqrt 2) * (1 / Real.sqrt 2) :=
      (mul_le_mul_of_nonneg_left h hznonneg).trans
        (mul_le_mul_of_nonneg_right h hrnonneg)
    nlinarith
  · intro h
    by_contra hz
    have hrlt : 1 / Real.sqrt 2 < ‖z‖ := lt_of_not_ge hz
    have hsq_lt :
        (1 / Real.sqrt 2) * (1 / Real.sqrt 2) < ‖z‖ * ‖z‖ :=
      (mul_lt_mul_of_pos_right hrlt (one_div_pos.2 hsqrt)).trans_le
        (mul_le_mul_of_nonneg_left hrlt.le hznonneg)
    nlinarith

end

end ProofGap.Exercise2917
